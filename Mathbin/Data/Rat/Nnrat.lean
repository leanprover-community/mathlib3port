/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module data.rat.nnrat
! leanprover-community/mathlib commit b3f4f007a962e3787aa0f3b5c7942a1317f7d88e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Nonneg.Field
import Mathbin.Algebra.Order.Nonneg.Floor

/-!
# Nonnegative rationals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the nonnegative rationals as a subtype of `rat` and provides its algebraic order
structure.

We also define an instance `can_lift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `nnrat` in locale `nnrat`.
-/


open Function

open BigOperators

#print NNRat /-
/-- Nonnegative rational numbers. -/
def NNRat :=
  { q : ℚ // 0 ≤ q }deriving CanonicallyOrderedCommSemiring, CanonicallyLinearOrderedSemifield,
  LinearOrderedCommGroupWithZero, Sub, OrderedSub, DenselyOrdered, Archimedean, Inhabited
#align nnrat NNRat
-/

-- mathport name: nnrat
scoped[NNRat] notation "ℚ≥0" => NNRat

namespace NNRat

variable {α : Type _} {p q : ℚ≥0}

instance : Coe ℚ≥0 ℚ :=
  ⟨Subtype.val⟩

/- warning: nnrat.val_eq_coe clashes with [anonymous] -> [anonymous]
warning: nnrat.val_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (q : NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) q) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)
but is expected to have type
  forall {q : Type.{u}} {β : Type.{v}}, (Nat -> q -> β) -> Nat -> (List.{u} q) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align nnrat.val_eq_coe [anonymous]ₓ'. -/
-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem [anonymous] (q : ℚ≥0) : q.val = q :=
  rfl
#align nnrat.val_eq_coe [anonymous]

/- warning: nnrat.can_lift -> NNRat.canLift is a dubious translation:
lean 3 declaration is
  CanLift.{1, 1} Rat NNRat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe)))) (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q)
but is expected to have type
  CanLift.{1, 1} Rat NNRat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)
Case conversion may be inaccurate. Consider using '#align nnrat.can_lift NNRat.canLiftₓ'. -/
instance canLift : CanLift ℚ ℚ≥0 coe fun q => 0 ≤ q where prf q hq := ⟨⟨q, hq⟩, rfl⟩
#align nnrat.can_lift NNRat.canLift

/- warning: nnrat.ext -> NNRat.ext is a dubious translation:
lean 3 declaration is
  forall {p : NNRat} {q : NNRat}, (Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)) -> (Eq.{1} NNRat p q)
but is expected to have type
  forall {p : NNRat} {q : NNRat}, (Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)) -> (Eq.{1} NNRat p q)
Case conversion may be inaccurate. Consider using '#align nnrat.ext NNRat.extₓ'. -/
@[ext]
theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
  Subtype.ext
#align nnrat.ext NNRat.ext

/- warning: nnrat.coe_injective -> NNRat.coe_injective is a dubious translation:
lean 3 declaration is
  Function.Injective.{1, 1} NNRat Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))))
but is expected to have type
  Function.Injective.{1, 1} (Subtype.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_injective NNRat.coe_injectiveₓ'. -/
protected theorem coe_injective : Injective (coe : ℚ≥0 → ℚ) :=
  Subtype.coe_injective
#align nnrat.coe_injective NNRat.coe_injective

/- warning: nnrat.coe_inj -> NNRat.coe_inj is a dubious translation:
lean 3 declaration is
  forall {p : NNRat} {q : NNRat}, Iff (Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)) (Eq.{1} NNRat p q)
but is expected to have type
  forall {p : NNRat} {q : NNRat}, Iff (Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)) (Eq.{1} NNRat p q)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_inj NNRat.coe_injₓ'. -/
@[simp, norm_cast]
theorem coe_inj : (p : ℚ) = q ↔ p = q :=
  Subtype.coe_inj
#align nnrat.coe_inj NNRat.coe_inj

/- warning: nnrat.ext_iff -> NNRat.ext_iff is a dubious translation:
lean 3 declaration is
  forall {p : NNRat} {q : NNRat}, Iff (Eq.{1} NNRat p q) (Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))
but is expected to have type
  forall {p : NNRat} {q : NNRat}, Iff (Eq.{1} NNRat p q) (Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q))
Case conversion may be inaccurate. Consider using '#align nnrat.ext_iff NNRat.ext_iffₓ'. -/
theorem ext_iff : p = q ↔ (p : ℚ) = q :=
  Subtype.ext_iff
#align nnrat.ext_iff NNRat.ext_iff

/- warning: nnrat.ne_iff -> NNRat.ne_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNRat} {y : NNRat}, Iff (Ne.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) y)) (Ne.{1} NNRat x y)
but is expected to have type
  forall {x : NNRat} {y : NNRat}, Iff (Ne.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) x) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) y)) (Ne.{1} NNRat x y)
Case conversion may be inaccurate. Consider using '#align nnrat.ne_iff NNRat.ne_iffₓ'. -/
theorem ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
  NNRat.coe_inj.Not
#align nnrat.ne_iff NNRat.ne_iff

/- warning: nnrat.coe_mk -> NNRat.coe_mk is a dubious translation:
lean 3 declaration is
  forall (q : Rat) (hq : LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Subtype.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q)) Rat (HasLiftT.mk.{1, 1} (Subtype.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q)) Rat (CoeTCₓ.coe.{1, 1} (Subtype.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q)) Rat (coeBase.{1, 1} (Subtype.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q)) Rat (coeSubtype.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q))))) (Subtype.mk.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) q hq)) q
but is expected to have type
  forall (q : Rat) (hq : LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Subtype.mk.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q hq)) q
Case conversion may be inaccurate. Consider using '#align nnrat.coe_mk NNRat.coe_mkₓ'. -/
@[norm_cast]
theorem coe_mk (q : ℚ) (hq) : ((⟨q, hq⟩ : ℚ≥0) : ℚ) = q :=
  rfl
#align nnrat.coe_mk NNRat.coe_mk

#print Rat.toNNRat /-
/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def Rat.toNNRat (q : ℚ) : ℚ≥0 :=
  ⟨max q 0, le_max_right _ _⟩
#align rat.to_nnrat Rat.toNNRat
-/

/- warning: rat.coe_to_nnrat -> Rat.coe_toNNRat is a dubious translation:
lean 3 declaration is
  forall (q : Rat), (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) -> (Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Rat.toNNRat q)) q)
but is expected to have type
  forall (q : Rat), (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) -> (Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Rat.toNNRat q)) q)
Case conversion may be inaccurate. Consider using '#align rat.coe_to_nnrat Rat.coe_toNNRatₓ'. -/
theorem Rat.coe_toNNRat (q : ℚ) (hq : 0 ≤ q) : (q.toNNRat : ℚ) = q :=
  max_eq_left hq
#align rat.coe_to_nnrat Rat.coe_toNNRat

/- warning: rat.le_coe_to_nnrat -> Rat.le_coe_toNNRat is a dubious translation:
lean 3 declaration is
  forall (q : Rat), LE.le.{0} Rat Rat.hasLe q ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Rat.toNNRat q))
but is expected to have type
  forall (q : Rat), LE.le.{0} Rat Rat.instLERat q (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Rat.toNNRat q))
Case conversion may be inaccurate. Consider using '#align rat.le_coe_to_nnrat Rat.le_coe_toNNRatₓ'. -/
theorem Rat.le_coe_toNNRat (q : ℚ) : q ≤ q.toNNRat :=
  le_max_left _ _
#align rat.le_coe_to_nnrat Rat.le_coe_toNNRat

open _Root_.Rat (toNNRat)

/- warning: nnrat.coe_nonneg -> NNRat.coe_nonneg is a dubious translation:
lean 3 declaration is
  forall (q : NNRat), LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)
but is expected to have type
  forall (q : NNRat), LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_nonneg NNRat.coe_nonnegₓ'. -/
@[simp]
theorem coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q :=
  q.2
#align nnrat.coe_nonneg NNRat.coe_nonneg

/- warning: nnrat.coe_zero -> NNRat.coe_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))))))) (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))
but is expected to have type
  Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero))))) (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_zero NNRat.coe_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_zero : ((0 : ℚ≥0) : ℚ) = 0 :=
  rfl
#align nnrat.coe_zero NNRat.coe_zero

/- warning: nnrat.coe_one -> NNRat.coe_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (OfNat.ofNat.{0} NNRat 1 (OfNat.mk.{0} NNRat 1 (One.one.{0} NNRat (AddMonoidWithOne.toOne.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))))))) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))
but is expected to have type
  Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (OfNat.ofNat.{0} NNRat 1 (One.toOfNat1.{0} NNRat (CanonicallyOrderedCommSemiring.toOne.{0} NNRat instNNRatCanonicallyOrderedCommSemiring)))) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_one NNRat.coe_oneₓ'. -/
@[simp, norm_cast]
theorem coe_one : ((1 : ℚ≥0) : ℚ) = 1 :=
  rfl
#align nnrat.coe_one NNRat.coe_one

/- warning: nnrat.coe_add -> NNRat.coe_add is a dubious translation:
lean 3 declaration is
  forall (p : NNRat) (q : NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (HAdd.hAdd.{0, 0, 0} NNRat NNRat NNRat (instHAdd.{0} NNRat (Distrib.toHasAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))) p q)) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))
but is expected to have type
  forall (p : NNRat) (q : NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (HAdd.hAdd.{0, 0, 0} NNRat NNRat NNRat (instHAdd.{0} NNRat (Distrib.toAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))))))) p q)) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_add NNRat.coe_addₓ'. -/
@[simp, norm_cast]
theorem coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q :=
  rfl
#align nnrat.coe_add NNRat.coe_add

/- warning: nnrat.coe_mul -> NNRat.coe_mul is a dubious translation:
lean 3 declaration is
  forall (p : NNRat) (q : NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (HMul.hMul.{0, 0, 0} NNRat NNRat NNRat (instHMul.{0} NNRat (Distrib.toHasMul.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))) p q)) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))
but is expected to have type
  forall (p : NNRat) (q : NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (HMul.hMul.{0, 0, 0} NNRat NNRat NNRat (instHMul.{0} NNRat (CanonicallyOrderedCommSemiring.toMul.{0} NNRat instNNRatCanonicallyOrderedCommSemiring)) p q)) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_mul NNRat.coe_mulₓ'. -/
@[simp, norm_cast]
theorem coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q :=
  rfl
#align nnrat.coe_mul NNRat.coe_mul

/- warning: nnrat.coe_inv -> NNRat.coe_inv is a dubious translation:
lean 3 declaration is
  forall (q : NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Inv.inv.{0} NNRat (DivInvMonoid.toHasInv.{0} NNRat (GroupWithZero.toDivInvMonoid.{0} NNRat (DivisionSemiring.toGroupWithZero.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))) q)) (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))
but is expected to have type
  forall (q : NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Inv.inv.{0} NNRat (CanonicallyLinearOrderedSemifield.toInv.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield) q)) (Inv.inv.{0} Rat Rat.instInvRat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_inv NNRat.coe_invₓ'. -/
@[simp, norm_cast]
theorem coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = q⁻¹ :=
  rfl
#align nnrat.coe_inv NNRat.coe_inv

/- warning: nnrat.coe_div -> NNRat.coe_div is a dubious translation:
lean 3 declaration is
  forall (p : NNRat) (q : NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (DivInvMonoid.toHasDiv.{0} NNRat (GroupWithZero.toDivInvMonoid.{0} NNRat (DivisionSemiring.toGroupWithZero.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) p q)) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))
but is expected to have type
  forall (p : NNRat) (q : NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (CanonicallyLinearOrderedSemifield.toDiv.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)) p q)) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_div NNRat.coe_divₓ'. -/
@[simp, norm_cast]
theorem coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q :=
  rfl
#align nnrat.coe_div NNRat.coe_div

/- warning: nnrat.coe_bit0 clashes with [anonymous] -> [anonymous]
warning: nnrat.coe_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (q : NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (bit0.{0} NNRat (Distrib.toHasAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) q)) (bit0.{0} Rat Rat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))
but is expected to have type
  forall {q : Type.{u}} {β : Type.{v}}, (Nat -> q -> β) -> Nat -> (List.{u} q) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_bit0 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (q : ℚ≥0) : ((bit0 q : ℚ≥0) : ℚ) = bit0 q :=
  rfl
#align nnrat.coe_bit0 [anonymous]

/- warning: nnrat.coe_bit1 clashes with [anonymous] -> [anonymous]
warning: nnrat.coe_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (q : NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (bit1.{0} NNRat (AddMonoidWithOne.toOne.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Distrib.toHasAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) q)) (bit1.{0} Rat Rat.hasOne Rat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))
but is expected to have type
  forall {q : Type.{u}} {β : Type.{v}}, (Nat -> q -> β) -> Nat -> (List.{u} q) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_bit1 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (q : ℚ≥0) : ((bit1 q : ℚ≥0) : ℚ) = bit1 q :=
  rfl
#align nnrat.coe_bit1 [anonymous]

/- warning: nnrat.coe_sub -> NNRat.coe_sub is a dubious translation:
lean 3 declaration is
  forall {p : NNRat} {q : NNRat}, (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) q p) -> (Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (HSub.hSub.{0, 0, 0} NNRat NNRat NNRat (instHSub.{0} NNRat NNRat.hasSub) p q)) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)))
but is expected to have type
  forall {p : NNRat} {q : NNRat}, (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) q p) -> (Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (HSub.hSub.{0, 0, 0} NNRat NNRat NNRat (instHSub.{0} NNRat instNNRatSub) p q)) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_sub NNRat.coe_subₓ'. -/
@[simp, norm_cast]
theorem coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
  max_eq_left <| le_sub_comm.2 <| by simp [show (q : ℚ) ≤ p from h]
#align nnrat.coe_sub NNRat.coe_sub

/- warning: nnrat.coe_eq_zero -> NNRat.coe_eq_zero is a dubious translation:
lean 3 declaration is
  forall {q : NNRat}, Iff (Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q) (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) (Eq.{1} NNRat q (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))))
but is expected to have type
  forall {q : NNRat}, Iff (Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q) (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) (Eq.{1} NNRat q (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero)))))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_eq_zero NNRat.coe_eq_zeroₓ'. -/
@[simp]
theorem coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast
#align nnrat.coe_eq_zero NNRat.coe_eq_zero

/- warning: nnrat.coe_ne_zero -> NNRat.coe_ne_zero is a dubious translation:
lean 3 declaration is
  forall {q : NNRat}, Iff (Ne.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q) (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) (Ne.{1} NNRat q (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))))
but is expected to have type
  forall {q : NNRat}, Iff (Ne.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q) (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) (Ne.{1} NNRat q (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero)))))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_ne_zero NNRat.coe_ne_zeroₓ'. -/
theorem coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 :=
  coe_eq_zero.Not
#align nnrat.coe_ne_zero NNRat.coe_ne_zero

/- warning: nnrat.coe_le_coe -> NNRat.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {p : NNRat} {q : NNRat}, Iff (LE.le.{0} Rat Rat.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)) (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) p q)
but is expected to have type
  forall {p : NNRat} {q : NNRat}, Iff (LE.le.{0} Rat Rat.instLERat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)) (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) p q)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_le_coe NNRat.coe_le_coeₓ'. -/
@[simp, norm_cast]
theorem coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align nnrat.coe_le_coe NNRat.coe_le_coe

/- warning: nnrat.coe_lt_coe -> NNRat.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {p : NNRat} {q : NNRat}, Iff (LT.lt.{0} Rat Rat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)) (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) p q)
but is expected to have type
  forall {p : NNRat} {q : NNRat}, Iff (LT.lt.{0} Rat Rat.instLTRat_1 (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)) (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) p q)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_lt_coe NNRat.coe_lt_coeₓ'. -/
@[simp, norm_cast]
theorem coe_lt_coe : (p : ℚ) < q ↔ p < q :=
  Iff.rfl
#align nnrat.coe_lt_coe NNRat.coe_lt_coe

/- warning: nnrat.coe_pos -> NNRat.coe_pos is a dubious translation:
lean 3 declaration is
  forall {q : NNRat}, Iff (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)) (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) q)
but is expected to have type
  forall {q : NNRat}, Iff (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)) (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero)))) q)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_pos NNRat.coe_posₓ'. -/
@[simp, norm_cast]
theorem coe_pos : (0 : ℚ) < q ↔ 0 < q :=
  Iff.rfl
#align nnrat.coe_pos NNRat.coe_pos

/- warning: nnrat.coe_mono -> NNRat.coe_mono is a dubious translation:
lean 3 declaration is
  Monotone.{0, 0} NNRat Rat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) Rat.preorder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))))
but is expected to have type
  Monotone.{0, 0} (Subtype.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) Rat (Subtype.preorder.{0} Rat Rat.instPreorderRat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) Rat.instPreorderRat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_mono NNRat.coe_monoₓ'. -/
theorem coe_mono : Monotone (coe : ℚ≥0 → ℚ) := fun _ _ => coe_le_coe.2
#align nnrat.coe_mono NNRat.coe_mono

/- warning: nnrat.to_nnrat_mono -> NNRat.toNNRat_mono is a dubious translation:
lean 3 declaration is
  Monotone.{0, 0} Rat NNRat Rat.preorder (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) Rat.toNNRat
but is expected to have type
  Monotone.{0, 0} Rat NNRat Rat.instPreorderRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) Rat.toNNRat
Case conversion may be inaccurate. Consider using '#align nnrat.to_nnrat_mono NNRat.toNNRat_monoₓ'. -/
theorem toNNRat_mono : Monotone toNNRat := fun x y h => max_le_max h le_rfl
#align nnrat.to_nnrat_mono NNRat.toNNRat_mono

/- warning: nnrat.to_nnrat_coe -> NNRat.toNNRat_coe is a dubious translation:
lean 3 declaration is
  forall (q : NNRat), Eq.{1} NNRat (Rat.toNNRat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)) q
but is expected to have type
  forall (q : NNRat), Eq.{1} NNRat (Rat.toNNRat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)) q
Case conversion may be inaccurate. Consider using '#align nnrat.to_nnrat_coe NNRat.toNNRat_coeₓ'. -/
@[simp]
theorem toNNRat_coe (q : ℚ≥0) : toNNRat q = q :=
  ext <| max_eq_left q.2
#align nnrat.to_nnrat_coe NNRat.toNNRat_coe

/- warning: nnrat.to_nnrat_coe_nat -> NNRat.toNNRat_coe_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} NNRat (Rat.toNNRat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNRat (HasLiftT.mk.{1, 1} Nat NNRat (CoeTCₓ.coe.{1, 1} Nat NNRat (Nat.castCoe.{0} NNRat (AddMonoidWithOne.toNatCast.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} NNRat (Rat.toNNRat (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n)) (Nat.cast.{0} NNRat (CanonicallyOrderedCommSemiring.toNatCast.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) n)
Case conversion may be inaccurate. Consider using '#align nnrat.to_nnrat_coe_nat NNRat.toNNRat_coe_natₓ'. -/
@[simp]
theorem toNNRat_coe_nat (n : ℕ) : toNNRat n = n :=
  ext <| by simp [Rat.coe_toNNRat]
#align nnrat.to_nnrat_coe_nat NNRat.toNNRat_coe_nat

/- warning: nnrat.gi -> NNRat.gi is a dubious translation:
lean 3 declaration is
  GaloisInsertion.{0, 0} Rat NNRat Rat.preorder (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) Rat.toNNRat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))))
but is expected to have type
  GaloisInsertion.{0, 0} Rat NNRat Rat.instPreorderRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) Rat.toNNRat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q))
Case conversion may be inaccurate. Consider using '#align nnrat.gi NNRat.giₓ'. -/
/-- `to_nnrat` and `coe : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : GaloisInsertion toNNRat coe :=
  GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe
#align nnrat.gi NNRat.gi

/- warning: nnrat.coe_hom -> NNRat.coeHom is a dubious translation:
lean 3 declaration is
  RingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))
but is expected to have type
  RingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_hom NNRat.coeHomₓ'. -/
/-- Coercion `ℚ≥0 → ℚ` as a `ring_hom`. -/
def coeHom : ℚ≥0 →+* ℚ :=
  ⟨coe, coe_one, coe_mul, coe_zero, coe_add⟩
#align nnrat.coe_hom NNRat.coeHom

/- warning: nnrat.coe_nat_cast -> NNRat.coe_natCast is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNRat (HasLiftT.mk.{1, 1} Nat NNRat (CoeTCₓ.coe.{1, 1} Nat NNRat (Nat.castCoe.{0} NNRat (AddMonoidWithOne.toNatCast.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Nat.cast.{0} NNRat (CanonicallyOrderedCommSemiring.toNatCast.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) n)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_nat_cast NNRat.coe_natCastₓ'. -/
@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n :=
  map_natCast coeHom n
#align nnrat.coe_nat_cast NNRat.coe_natCast

/- warning: nnrat.mk_coe_nat -> NNRat.mk_coe_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} NNRat (Subtype.mk.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) n) (Nat.cast_nonneg.{0} Rat Rat.orderedSemiring n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNRat (HasLiftT.mk.{1, 1} Nat NNRat (CoeTCₓ.coe.{1, 1} Nat NNRat (Nat.castCoe.{0} NNRat (AddMonoidWithOne.toNatCast.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} NNRat (Subtype.mk.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n) (Nat.cast_nonneg.{0} Rat Rat.instOrderedSemiringRat n)) (Nat.cast.{0} NNRat (CanonicallyOrderedCommSemiring.toNatCast.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) n)
Case conversion may be inaccurate. Consider using '#align nnrat.mk_coe_nat NNRat.mk_coe_natₓ'. -/
@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
  ext (coe_natCast n).symm
#align nnrat.mk_coe_nat NNRat.mk_coe_nat

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : Algebra ℚ≥0 ℚ :=
  coeHom.toAlgebra

/-- A `mul_action` over `ℚ` restricts to a `mul_action` over `ℚ≥0`. -/
instance [MulAction ℚ α] : MulAction ℚ≥0 α :=
  MulAction.compHom α coeHom.toMonoidHom

/-- A `distrib_mul_action` over `ℚ` restricts to a `distrib_mul_action` over `ℚ≥0`. -/
instance [AddCommMonoid α] [DistribMulAction ℚ α] : DistribMulAction ℚ≥0 α :=
  DistribMulAction.compHom α coeHom.toMonoidHom

/-- A `module` over `ℚ` restricts to a `module` over `ℚ≥0`. -/
instance [AddCommMonoid α] [Module ℚ α] : Module ℚ≥0 α :=
  Module.compHom α coeHom

/- warning: nnrat.coe_coe_hom -> NNRat.coe_coeHom is a dubious translation:
lean 3 declaration is
  Eq.{1} (NNRat -> Rat) (coeFn.{1, 1} (RingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))) (fun (_x : RingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))) => NNRat -> Rat) (RingHom.hasCoeToFun.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))) NNRat.coeHom) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))))
but is expected to have type
  Eq.{1} (forall (ᾰ : NNRat), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : NNRat) => Rat) ᾰ) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) NNRat (fun (_x : NNRat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : NNRat) => Rat) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) NNRat Rat (NonUnitalNonAssocSemiring.toMul.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))))) (NonUnitalNonAssocSemiring.toMul.{0} Rat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) NNRat Rat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Rat (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat))))) NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (RingHom.instRingHomClassRingHom.{0, 0} NNRat Rat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) (NonAssocRing.toNonAssocSemiring.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))))))) NNRat.coeHom) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_coe_hom NNRat.coe_coeHomₓ'. -/
@[simp]
theorem coe_coeHom : ⇑coeHom = coe :=
  rfl
#align nnrat.coe_coe_hom NNRat.coe_coeHom

/- warning: nnrat.coe_indicator -> NNRat.coe_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (f : α -> NNRat) (a : α), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Set.indicator.{u1, 0} α NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) s f a)) (Set.indicator.{u1, 0} α Rat Rat.hasZero s (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (f x)) a)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (f : α -> NNRat) (a : α), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Set.indicator.{u1, 0} α NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero)) s f a)) (Set.indicator.{u1, 0} α Rat (CommMonoidWithZero.toZero.{0} Rat (CommGroupWithZero.toCommMonoidWithZero.{0} Rat Rat.commGroupWithZero)) s (fun (x : α) => Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (f x)) a)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_indicator NNRat.coe_indicatorₓ'. -/
@[simp, norm_cast]
theorem coe_indicator (s : Set α) (f : α → ℚ≥0) (a : α) :
    ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (fun x => f x) a :=
  (coeHom : ℚ≥0 →+ ℚ).map_indicator _ _ _
#align nnrat.coe_indicator NNRat.coe_indicator

/- warning: nnrat.coe_pow -> NNRat.coe_pow is a dubious translation:
lean 3 declaration is
  forall (q : NNRat) (n : Nat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (HPow.hPow.{0, 0, 0} NNRat Nat NNRat (instHPow.{0, 0} NNRat Nat (Monoid.Pow.{0} NNRat (MonoidWithZero.toMonoid.{0} NNRat (Semiring.toMonoidWithZero.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) q n)) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q) n)
but is expected to have type
  forall (q : NNRat) (n : Nat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (HPow.hPow.{0, 0, 0} NNRat Nat NNRat (instHPow.{0, 0} NNRat Nat (Monoid.Pow.{0} NNRat (MonoidWithZero.toMonoid.{0} NNRat (Semiring.toMonoidWithZero.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))))) q n)) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q) n)
Case conversion may be inaccurate. Consider using '#align nnrat.coe_pow NNRat.coe_powₓ'. -/
@[simp, norm_cast]
theorem coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = q ^ n :=
  coeHom.map_pow _ _
#align nnrat.coe_pow NNRat.coe_pow

/- warning: nnrat.coe_list_sum -> NNRat.coe_list_sum is a dubious translation:
lean 3 declaration is
  forall (l : List.{0} NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (List.sum.{0} NNRat (Distrib.toHasAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) l)) (List.sum.{0} Rat Rat.hasAdd Rat.hasZero (List.map.{0, 0} NNRat Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe)))) l))
but is expected to have type
  forall (l : List.{0} NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (List.sum.{0} NNRat (Distrib.toAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))))) (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero)) l)) (List.sum.{0} Rat Rat.instAddRat (CommMonoidWithZero.toZero.{0} Rat (CommGroupWithZero.toCommMonoidWithZero.{0} Rat Rat.commGroupWithZero)) (List.map.{0, 0} NNRat Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) l))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_list_sum NNRat.coe_list_sumₓ'. -/
@[norm_cast]
theorem coe_list_sum (l : List ℚ≥0) : (l.Sum : ℚ) = (l.map coe).Sum :=
  coeHom.map_list_sum _
#align nnrat.coe_list_sum NNRat.coe_list_sum

/- warning: nnrat.coe_list_prod -> NNRat.coe_list_prod is a dubious translation:
lean 3 declaration is
  forall (l : List.{0} NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (List.prod.{0} NNRat (Distrib.toHasMul.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (AddMonoidWithOne.toOne.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) l)) (List.prod.{0} Rat Rat.hasMul Rat.hasOne (List.map.{0, 0} NNRat Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe)))) l))
but is expected to have type
  forall (l : List.{0} NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (List.prod.{0} NNRat (CanonicallyOrderedCommSemiring.toMul.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) (CanonicallyOrderedCommSemiring.toOne.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) l)) (List.prod.{0} Rat Rat.instMulRat (NonAssocRing.toOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) (List.map.{0, 0} NNRat Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) l))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_list_prod NNRat.coe_list_prodₓ'. -/
@[norm_cast]
theorem coe_list_prod (l : List ℚ≥0) : (l.Prod : ℚ) = (l.map coe).Prod :=
  coeHom.map_list_prod _
#align nnrat.coe_list_prod NNRat.coe_list_prod

/- warning: nnrat.coe_multiset_sum -> NNRat.coe_multiset_sum is a dubious translation:
lean 3 declaration is
  forall (s : Multiset.{0} NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Multiset.sum.{0} NNRat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))) s)) (Multiset.sum.{0} Rat Rat.addCommMonoid (Multiset.map.{0, 0} NNRat Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe)))) s))
but is expected to have type
  forall (s : Multiset.{0} NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Multiset.sum.{0} NNRat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) s)) (Multiset.sum.{0} Rat Rat.addCommMonoid (Multiset.map.{0, 0} NNRat Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) s))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_multiset_sum NNRat.coe_multiset_sumₓ'. -/
@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℚ≥0) : (s.Sum : ℚ) = (s.map coe).Sum :=
  coeHom.map_multiset_sum _
#align nnrat.coe_multiset_sum NNRat.coe_multiset_sum

/- warning: nnrat.coe_multiset_prod -> NNRat.coe_multiset_prod is a dubious translation:
lean 3 declaration is
  forall (s : Multiset.{0} NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Multiset.prod.{0} NNRat (OrderedCommMonoid.toCommMonoid.{0} NNRat (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{0} NNRat NNRat.canonicallyOrderedCommSemiring)) s)) (Multiset.prod.{0} Rat Rat.commMonoid (Multiset.map.{0, 0} NNRat Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe)))) s))
but is expected to have type
  forall (s : Multiset.{0} NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Multiset.prod.{0} NNRat (LinearOrderedCommMonoid.toCommMonoid.{0} NNRat (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero))) s)) (Multiset.prod.{0} Rat Rat.commMonoid (Multiset.map.{0, 0} NNRat Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) s))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_multiset_prod NNRat.coe_multiset_prodₓ'. -/
@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℚ≥0) : (s.Prod : ℚ) = (s.map coe).Prod :=
  coeHom.map_multiset_prod _
#align nnrat.coe_multiset_prod NNRat.coe_multiset_prod

/- warning: nnrat.coe_sum -> NNRat.coe_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> NNRat}, Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Finset.sum.{0, u1} NNRat α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))) s (fun (a : α) => f a))) (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> NNRat}, Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Finset.sum.{0, u1} NNRat α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) s (fun (a : α) => f a))) (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (a : α) => Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (f a)))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_sum NNRat.coe_sumₓ'. -/
@[norm_cast]
theorem coe_sum {s : Finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
  coeHom.map_sum _ _
#align nnrat.coe_sum NNRat.coe_sum

/- warning: nnrat.to_nnrat_sum_of_nonneg -> NNRat.toNNRat_sum_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> Rat}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) (f a))) -> (Eq.{1} NNRat (Rat.toNNRat (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (a : α) => f a))) (Finset.sum.{0, u1} NNRat α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))) s (fun (a : α) => Rat.toNNRat (f a))))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> Rat}, (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (f a))) -> (Eq.{1} NNRat (Rat.toNNRat (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (a : α) => f a))) (Finset.sum.{0, u1} NNRat α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) s (fun (a : α) => Rat.toNNRat (f a))))
Case conversion may be inaccurate. Consider using '#align nnrat.to_nnrat_sum_of_nonneg NNRat.toNNRat_sum_of_nonnegₓ'. -/
theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a in s, f a).toNNRat = ∑ a in s, (f a).toNNRat :=
  by
  rw [← coe_inj, coe_sum, Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Rat.coe_toNNRat _ (hf x hxs)]
#align nnrat.to_nnrat_sum_of_nonneg NNRat.toNNRat_sum_of_nonneg

/- warning: nnrat.coe_prod -> NNRat.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> NNRat}, Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Finset.prod.{0, u1} NNRat α (OrderedCommMonoid.toCommMonoid.{0} NNRat (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{0} NNRat NNRat.canonicallyOrderedCommSemiring)) s (fun (a : α) => f a))) (Finset.prod.{0, u1} Rat α Rat.commMonoid s (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> NNRat}, Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Finset.prod.{0, u1} NNRat α (LinearOrderedCommMonoid.toCommMonoid.{0} NNRat (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero))) s (fun (a : α) => f a))) (Finset.prod.{0, u1} Rat α Rat.commMonoid s (fun (a : α) => Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (f a)))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_prod NNRat.coe_prodₓ'. -/
@[norm_cast]
theorem coe_prod {s : Finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
  coeHom.map_prod _ _
#align nnrat.coe_prod NNRat.coe_prod

/- warning: nnrat.to_nnrat_prod_of_nonneg -> NNRat.toNNRat_prod_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> Rat}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) (f a))) -> (Eq.{1} NNRat (Rat.toNNRat (Finset.prod.{0, u1} Rat α Rat.commMonoid s (fun (a : α) => f a))) (Finset.prod.{0, u1} NNRat α (OrderedCommMonoid.toCommMonoid.{0} NNRat (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{0} NNRat NNRat.canonicallyOrderedCommSemiring)) s (fun (a : α) => Rat.toNNRat (f a))))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> Rat}, (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (f a))) -> (Eq.{1} NNRat (Rat.toNNRat (Finset.prod.{0, u1} Rat α Rat.commMonoid s (fun (a : α) => f a))) (Finset.prod.{0, u1} NNRat α (LinearOrderedCommMonoid.toCommMonoid.{0} NNRat (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero))) s (fun (a : α) => Rat.toNNRat (f a))))
Case conversion may be inaccurate. Consider using '#align nnrat.to_nnrat_prod_of_nonneg NNRat.toNNRat_prod_of_nonnegₓ'. -/
theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a in s, f a).toNNRat = ∏ a in s, (f a).toNNRat :=
  by
  rw [← coe_inj, coe_prod, Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Rat.coe_toNNRat _ (hf x hxs)]
#align nnrat.to_nnrat_prod_of_nonneg NNRat.toNNRat_prod_of_nonneg

/- warning: nnrat.nsmul_coe -> NNRat.nsmul_coe is a dubious translation:
lean 3 declaration is
  forall (q : NNRat) (n : Nat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (SMul.smul.{0, 0} Nat NNRat (AddMonoid.SMul.{0} NNRat (AddMonoidWithOne.toAddMonoid.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))) n q)) (SMul.smul.{0, 0} Nat Rat (AddMonoid.SMul.{0} Rat Rat.addMonoid) n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))
but is expected to have type
  forall (q : NNRat) (n : Nat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (HSMul.hSMul.{0, 0, 0} Nat NNRat NNRat (instHSMul.{0, 0} Nat NNRat (AddMonoid.SMul.{0} NNRat (AddMonoidWithOne.toAddMonoid.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))))))) n q)) (HSMul.hSMul.{0, 0, 0} Nat Rat Rat (instHSMul.{0, 0} Nat Rat (AddMonoid.SMul.{0} Rat Rat.addMonoid)) n (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q))
Case conversion may be inaccurate. Consider using '#align nnrat.nsmul_coe NNRat.nsmul_coeₓ'. -/
@[norm_cast]
theorem nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
  coeHom.toAddMonoidHom.map_nsmul _ _
#align nnrat.nsmul_coe NNRat.nsmul_coe

/- warning: nnrat.bdd_above_coe -> NNRat.bddAbove_coe is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} NNRat}, Iff (BddAbove.{0} Rat Rat.preorder (Set.image.{0, 0} NNRat Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe)))) s)) (BddAbove.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) s)
but is expected to have type
  forall {s : Set.{0} NNRat}, Iff (BddAbove.{0} Rat Rat.instPreorderRat (Set.image.{0, 0} NNRat Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) s)) (BddAbove.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))) s)
Case conversion may be inaccurate. Consider using '#align nnrat.bdd_above_coe NNRat.bddAbove_coeₓ'. -/
theorem bddAbove_coe {s : Set ℚ≥0} : BddAbove (coe '' s : Set ℚ) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ =>
    ⟨toNNRat b, fun ⟨y, hy⟩ hys =>
      show y ≤ max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans <| le_max_left _ _⟩,
    fun ⟨b, hb⟩ => ⟨b, fun y ⟨x, hx, Eq⟩ => Eq ▸ hb hx⟩⟩
#align nnrat.bdd_above_coe NNRat.bddAbove_coe

/- warning: nnrat.bdd_below_coe -> NNRat.bddBelow_coe is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} NNRat), BddBelow.{0} Rat Rat.preorder (Set.image.{0, 0} NNRat Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe)))) s)
but is expected to have type
  forall (s : Set.{0} NNRat), BddBelow.{0} Rat Rat.instPreorderRat (Set.image.{0, 0} (Subtype.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)) s)
Case conversion may be inaccurate. Consider using '#align nnrat.bdd_below_coe NNRat.bddBelow_coeₓ'. -/
theorem bddBelow_coe (s : Set ℚ≥0) : BddBelow ((coe : ℚ≥0 → ℚ) '' s) :=
  ⟨0, fun r ⟨q, _, h⟩ => h ▸ q.2⟩
#align nnrat.bdd_below_coe NNRat.bddBelow_coe

/- warning: nnrat.coe_max -> NNRat.coe_max is a dubious translation:
lean 3 declaration is
  forall (x : NNRat) (y : NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (LinearOrder.max.{0} NNRat (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{0} NNRat (CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)) x y)) (LinearOrder.max.{0} Rat Rat.linearOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) y))
but is expected to have type
  forall (x : NNRat) (y : NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Max.max.{0} NNRat (CanonicallyLinearOrderedSemifield.toMax.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield) x y)) (Max.max.{0} Rat (LinearOrderedRing.toMax.{0} Rat Rat.instLinearOrderedRingRat) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) x) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) y))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_max NNRat.coe_maxₓ'. -/
@[simp, norm_cast]
theorem coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
  coe_mono.map_max
#align nnrat.coe_max NNRat.coe_max

/- warning: nnrat.coe_min -> NNRat.coe_min is a dubious translation:
lean 3 declaration is
  forall (x : NNRat) (y : NNRat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (LinearOrder.min.{0} NNRat (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{0} NNRat (CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)) x y)) (LinearOrder.min.{0} Rat Rat.linearOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) y))
but is expected to have type
  forall (x : NNRat) (y : NNRat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Min.min.{0} NNRat (CanonicallyLinearOrderedSemifield.toMin.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield) x y)) (Min.min.{0} Rat (LinearOrderedRing.toMin.{0} Rat Rat.instLinearOrderedRingRat) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) x) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) y))
Case conversion may be inaccurate. Consider using '#align nnrat.coe_min NNRat.coe_minₓ'. -/
@[simp, norm_cast]
theorem coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
  coe_mono.map_min
#align nnrat.coe_min NNRat.coe_min

/- warning: nnrat.sub_def -> NNRat.sub_def is a dubious translation:
lean 3 declaration is
  forall (p : NNRat) (q : NNRat), Eq.{1} NNRat (HSub.hSub.{0, 0, 0} NNRat NNRat NNRat (instHSub.{0} NNRat NNRat.hasSub) p q) (Rat.toNNRat (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)))
but is expected to have type
  forall (p : NNRat) (q : NNRat), Eq.{1} NNRat (HSub.hSub.{0, 0, 0} NNRat NNRat NNRat (instHSub.{0} NNRat instNNRatSub) p q) (Rat.toNNRat (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)))
Case conversion may be inaccurate. Consider using '#align nnrat.sub_def NNRat.sub_defₓ'. -/
theorem sub_def (p q : ℚ≥0) : p - q = toNNRat (p - q) :=
  rfl
#align nnrat.sub_def NNRat.sub_def

/- warning: nnrat.abs_coe -> NNRat.abs_coe is a dubious translation:
lean 3 declaration is
  forall (q : NNRat), Eq.{1} Rat (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)
but is expected to have type
  forall (q : NNRat), Eq.{1} Rat (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)) (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)
Case conversion may be inaccurate. Consider using '#align nnrat.abs_coe NNRat.abs_coeₓ'. -/
@[simp]
theorem abs_coe (q : ℚ≥0) : |(q : ℚ)| = q :=
  abs_of_nonneg q.2
#align nnrat.abs_coe NNRat.abs_coe

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

/- warning: rat.to_nnrat_zero -> Rat.toNNRat_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} NNRat (Rat.toNNRat (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))))))
but is expected to have type
  Eq.{1} NNRat (Rat.toNNRat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero))))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_zero Rat.toNNRat_zeroₓ'. -/
@[simp]
theorem toNNRat_zero : toNNRat 0 = 0 := by simp [to_nnrat] <;> rfl
#align rat.to_nnrat_zero Rat.toNNRat_zero

/- warning: rat.to_nnrat_one -> Rat.toNNRat_one is a dubious translation:
lean 3 declaration is
  Eq.{1} NNRat (Rat.toNNRat (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))) (OfNat.ofNat.{0} NNRat 1 (OfNat.mk.{0} NNRat 1 (One.one.{0} NNRat (AddMonoidWithOne.toOne.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))))))
but is expected to have type
  Eq.{1} NNRat (Rat.toNNRat (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))) (OfNat.ofNat.{0} NNRat 1 (One.toOfNat1.{0} NNRat (CanonicallyOrderedCommSemiring.toOne.{0} NNRat instNNRatCanonicallyOrderedCommSemiring)))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_one Rat.toNNRat_oneₓ'. -/
@[simp]
theorem toNNRat_one : toNNRat 1 = 1 := by simp [to_nnrat, max_eq_left zero_le_one]
#align rat.to_nnrat_one Rat.toNNRat_one

/- warning: rat.to_nnrat_pos -> Rat.toNNRat_pos is a dubious translation:
lean 3 declaration is
  forall {q : Rat}, Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) (Rat.toNNRat q)) (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q)
but is expected to have type
  forall {q : Rat}, Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero)))) (Rat.toNNRat q)) (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q)
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_pos Rat.toNNRat_posₓ'. -/
@[simp]
theorem toNNRat_pos : 0 < toNNRat q ↔ 0 < q := by simp [to_nnrat, ← coe_lt_coe]
#align rat.to_nnrat_pos Rat.toNNRat_pos

/- warning: rat.to_nnrat_eq_zero -> Rat.toNNRat_eq_zero is a dubious translation:
lean 3 declaration is
  forall {q : Rat}, Iff (Eq.{1} NNRat (Rat.toNNRat q) (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))))))) (LE.le.{0} Rat Rat.hasLe q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))))
but is expected to have type
  forall {q : Rat}, Iff (Eq.{1} NNRat (Rat.toNNRat q) (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero))))) (LE.le.{0} Rat Rat.instLERat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_eq_zero Rat.toNNRat_eq_zeroₓ'. -/
@[simp]
theorem toNNRat_eq_zero : toNNRat q = 0 ↔ q ≤ 0 := by
  simpa [-to_nnrat_pos] using (@to_nnrat_pos q).Not
#align rat.to_nnrat_eq_zero Rat.toNNRat_eq_zero

/- warning: rat.to_nnrat_of_nonpos -> Rat.toNNRat_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {q : Rat}, (LE.le.{0} Rat Rat.hasLe q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) -> (Eq.{1} NNRat (Rat.toNNRat q) (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))))
but is expected to have type
  forall {q : Rat}, (LE.le.{0} Rat Rat.instLERat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) -> (Eq.{1} NNRat (Rat.toNNRat q) (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero)))))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_of_nonpos Rat.toNNRat_of_nonposₓ'. -/
alias to_nnrat_eq_zero ↔ _ to_nnrat_of_nonpos
#align rat.to_nnrat_of_nonpos Rat.toNNRat_of_nonpos

/- warning: rat.to_nnrat_le_to_nnrat_iff -> Rat.toNNRat_le_toNNRat_iff is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) p) -> (Iff (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat q) (Rat.toNNRat p)) (LE.le.{0} Rat Rat.hasLe q p))
but is expected to have type
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) p) -> (Iff (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (Rat.toNNRat q) (Rat.toNNRat p)) (LE.le.{0} Rat Rat.instLERat q p))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_le_to_nnrat_iff Rat.toNNRat_le_toNNRat_iffₓ'. -/
@[simp]
theorem toNNRat_le_toNNRat_iff (hp : 0 ≤ p) : toNNRat q ≤ toNNRat p ↔ q ≤ p := by
  simp [← coe_le_coe, to_nnrat, hp]
#align rat.to_nnrat_le_to_nnrat_iff Rat.toNNRat_le_toNNRat_iff

/- warning: rat.to_nnrat_lt_to_nnrat_iff' -> Rat.toNNRat_lt_toNNRat_iff' is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat q) (Rat.toNNRat p)) (And (LT.lt.{0} Rat Rat.hasLt q p) (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) p))
but is expected to have type
  forall {p : Rat} {q : Rat}, Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (Rat.toNNRat q) (Rat.toNNRat p)) (And (LT.lt.{0} Rat Rat.instLTRat_1 q p) (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) p))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_lt_to_nnrat_iff' Rat.toNNRat_lt_toNNRat_iff'ₓ'. -/
@[simp]
theorem toNNRat_lt_toNNRat_iff' : toNNRat q < toNNRat p ↔ q < p ∧ 0 < p :=
  by
  simp [← coe_lt_coe, to_nnrat, lt_irrefl]
  exact lt_trans'
#align rat.to_nnrat_lt_to_nnrat_iff' Rat.toNNRat_lt_toNNRat_iff'

/- warning: rat.to_nnrat_lt_to_nnrat_iff -> Rat.toNNRat_lt_toNNRat_iff is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) p) -> (Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat q) (Rat.toNNRat p)) (LT.lt.{0} Rat Rat.hasLt q p))
but is expected to have type
  forall {p : Rat} {q : Rat}, (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) p) -> (Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (Rat.toNNRat q) (Rat.toNNRat p)) (LT.lt.{0} Rat Rat.instLTRat_1 q p))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_lt_to_nnrat_iff Rat.toNNRat_lt_toNNRat_iffₓ'. -/
theorem toNNRat_lt_toNNRat_iff (h : 0 < p) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)
#align rat.to_nnrat_lt_to_nnrat_iff Rat.toNNRat_lt_toNNRat_iff

/- warning: rat.to_nnrat_lt_to_nnrat_iff_of_nonneg -> Rat.toNNRat_lt_toNNRat_iff_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) -> (Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat q) (Rat.toNNRat p)) (LT.lt.{0} Rat Rat.hasLt q p))
but is expected to have type
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) -> (Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (Rat.toNNRat q) (Rat.toNNRat p)) (LT.lt.{0} Rat Rat.instLTRat_1 q p))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_lt_to_nnrat_iff_of_nonneg Rat.toNNRat_lt_toNNRat_iff_of_nonnegₓ'. -/
theorem toNNRat_lt_toNNRat_iff_of_nonneg (hq : 0 ≤ q) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h => ⟨h, hq.trans_lt h⟩⟩
#align rat.to_nnrat_lt_to_nnrat_iff_of_nonneg Rat.toNNRat_lt_toNNRat_iff_of_nonneg

/- warning: rat.to_nnrat_add -> Rat.toNNRat_add is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) -> (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) p) -> (Eq.{1} NNRat (Rat.toNNRat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) q p)) (HAdd.hAdd.{0, 0, 0} NNRat NNRat NNRat (instHAdd.{0} NNRat (Distrib.toHasAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))) (Rat.toNNRat q) (Rat.toNNRat p)))
but is expected to have type
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) -> (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) p) -> (Eq.{1} NNRat (Rat.toNNRat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) q p)) (HAdd.hAdd.{0, 0, 0} NNRat NNRat NNRat (instHAdd.{0} NNRat (Distrib.toAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))))))) (Rat.toNNRat q) (Rat.toNNRat p)))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_add Rat.toNNRat_addₓ'. -/
@[simp]
theorem toNNRat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : toNNRat (q + p) = toNNRat q + toNNRat p :=
  NNRat.ext <| by simp [to_nnrat, hq, hp, add_nonneg]
#align rat.to_nnrat_add Rat.toNNRat_add

/- warning: rat.to_nnrat_add_le -> Rat.toNNRat_add_le is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) q p)) (HAdd.hAdd.{0, 0, 0} NNRat NNRat NNRat (instHAdd.{0} NNRat (Distrib.toHasAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))) (Rat.toNNRat q) (Rat.toNNRat p))
but is expected to have type
  forall {p : Rat} {q : Rat}, LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (Rat.toNNRat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) q p)) (HAdd.hAdd.{0, 0, 0} NNRat NNRat NNRat (instHAdd.{0} NNRat (Distrib.toAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (StrictOrderedSemiring.toSemiring.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)))))))))) (Rat.toNNRat q) (Rat.toNNRat p))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_add_le Rat.toNNRat_add_leₓ'. -/
theorem toNNRat_add_le : toNNRat (q + p) ≤ toNNRat q + toNNRat p :=
  coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) <| coe_nonneg _
#align rat.to_nnrat_add_le Rat.toNNRat_add_le

/- warning: rat.to_nnrat_le_iff_le_coe -> Rat.toNNRat_le_iff_le_coe is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {p : NNRat}, Iff (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat q) p) (LE.le.{0} Rat Rat.hasLe q ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p))
but is expected to have type
  forall {q : Rat} {p : NNRat}, Iff (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (Rat.toNNRat q) p) (LE.le.{0} Rat Rat.instLERat q (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_le_iff_le_coe Rat.toNNRat_le_iff_le_coeₓ'. -/
theorem toNNRat_le_iff_le_coe {p : ℚ≥0} : toNNRat q ≤ p ↔ q ≤ ↑p :=
  NNRat.gi.gc q p
#align rat.to_nnrat_le_iff_le_coe Rat.toNNRat_le_iff_le_coe

/- warning: rat.le_to_nnrat_iff_coe_le -> Rat.le_toNNRat_iff_coe_le is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : NNRat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) p) -> (Iff (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) q (Rat.toNNRat p)) (LE.le.{0} Rat Rat.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q) p))
but is expected to have type
  forall {p : Rat} {q : NNRat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) p) -> (Iff (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) q (Rat.toNNRat p)) (LE.le.{0} Rat Rat.instLERat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q) p))
Case conversion may be inaccurate. Consider using '#align rat.le_to_nnrat_iff_coe_le Rat.le_toNNRat_iff_coe_leₓ'. -/
theorem le_toNNRat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ toNNRat p ↔ ↑q ≤ p := by
  rw [← coe_le_coe, Rat.coe_toNNRat p hp]
#align rat.le_to_nnrat_iff_coe_le Rat.le_toNNRat_iff_coe_le

/- warning: rat.le_to_nnrat_iff_coe_le' -> Rat.le_toNNRat_iff_coe_le' is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : NNRat}, (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (OfNat.ofNat.{0} NNRat 0 (OfNat.mk.{0} NNRat 0 (Zero.zero.{0} NNRat (MulZeroClass.toHasZero.{0} NNRat (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) q) -> (Iff (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) q (Rat.toNNRat p)) (LE.le.{0} Rat Rat.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q) p))
but is expected to have type
  forall {p : Rat} {q : NNRat}, (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (OfNat.ofNat.{0} NNRat 0 (Zero.toOfNat0.{0} NNRat (LinearOrderedCommMonoidWithZero.toZero.{0} NNRat (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNRat instNNRatLinearOrderedCommGroupWithZero)))) q) -> (Iff (LE.le.{0} NNRat (Preorder.toLE.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) q (Rat.toNNRat p)) (LE.le.{0} Rat Rat.instLERat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q) p))
Case conversion may be inaccurate. Consider using '#align rat.le_to_nnrat_iff_coe_le' Rat.le_toNNRat_iff_coe_le'ₓ'. -/
theorem le_toNNRat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ toNNRat p ↔ ↑q ≤ p :=
  (le_or_lt 0 p).elim le_toNNRat_iff_coe_le fun hp => by
    simp only [(hp.trans_le q.coe_nonneg).not_le, to_nnrat_eq_zero.2 hp.le, hq.not_le]
#align rat.le_to_nnrat_iff_coe_le' Rat.le_toNNRat_iff_coe_le'

/- warning: rat.to_nnrat_lt_iff_lt_coe -> Rat.toNNRat_lt_iff_lt_coe is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {p : NNRat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) -> (Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat q) p) (LT.lt.{0} Rat Rat.hasLt q ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) p)))
but is expected to have type
  forall {q : Rat} {p : NNRat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) -> (Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) (Rat.toNNRat q) p) (LT.lt.{0} Rat Rat.instLTRat_1 q (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) p)))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_lt_iff_lt_coe Rat.toNNRat_lt_iff_lt_coeₓ'. -/
theorem toNNRat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : toNNRat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe, Rat.coe_toNNRat q hq]
#align rat.to_nnrat_lt_iff_lt_coe Rat.toNNRat_lt_iff_lt_coe

/- warning: rat.lt_to_nnrat_iff_coe_lt -> Rat.lt_toNNRat_iff_coe_lt is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : NNRat}, Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNRat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) q (Rat.toNNRat p)) (LT.lt.{0} Rat Rat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q) p)
but is expected to have type
  forall {p : Rat} {q : NNRat}, Iff (LT.lt.{0} NNRat (Preorder.toLT.{0} NNRat (PartialOrder.toPreorder.{0} NNRat (StrictOrderedSemiring.toPartialOrder.{0} NNRat (LinearOrderedSemiring.toStrictOrderedSemiring.{0} NNRat (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} NNRat (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield))))))) q (Rat.toNNRat p)) (LT.lt.{0} Rat Rat.instLTRat_1 (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q) p)
Case conversion may be inaccurate. Consider using '#align rat.lt_to_nnrat_iff_coe_lt Rat.lt_toNNRat_iff_coe_ltₓ'. -/
theorem lt_toNNRat_iff_coe_lt {q : ℚ≥0} : q < toNNRat p ↔ ↑q < p :=
  NNRat.gi.gc.lt_iff_lt
#align rat.lt_to_nnrat_iff_coe_lt Rat.lt_toNNRat_iff_coe_lt

/- warning: rat.to_nnrat_bit0 clashes with [anonymous] -> [anonymous]
warning: rat.to_nnrat_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {q : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) -> (Eq.{1} NNRat (Rat.toNNRat (bit0.{0} Rat Rat.hasAdd q)) (bit0.{0} NNRat (Distrib.toHasAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat q)))
but is expected to have type
  forall {q : Type.{u}} {hq : Type.{v}}, (Nat -> q -> hq) -> Nat -> (List.{u} q) -> (List.{v} hq)
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_bit0 [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (hq : 0 ≤ q) : toNNRat (bit0 q) = bit0 (toNNRat q) :=
  toNNRat_add hq hq
#align rat.to_nnrat_bit0 [anonymous]

/- warning: rat.to_nnrat_bit1 clashes with [anonymous] -> [anonymous]
warning: rat.to_nnrat_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {q : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) -> (Eq.{1} NNRat (Rat.toNNRat (bit1.{0} Rat Rat.hasOne Rat.hasAdd q)) (bit1.{0} NNRat (AddMonoidWithOne.toOne.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Distrib.toHasAdd.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))))) (Rat.toNNRat q)))
but is expected to have type
  forall {q : Type.{u}} {hq : Type.{v}}, (Nat -> q -> hq) -> Nat -> (List.{u} q) -> (List.{v} hq)
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_bit1 [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (hq : 0 ≤ q) : toNNRat (bit1 q) = bit1 (toNNRat q) :=
  (toNNRat_add (by simp [hq]) zero_le_one).trans <| by simp [to_nnrat_one, bit1, hq]
#align rat.to_nnrat_bit1 [anonymous]

/- warning: rat.to_nnrat_mul -> Rat.toNNRat_mul is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) p) -> (Eq.{1} NNRat (Rat.toNNRat (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) p q)) (HMul.hMul.{0, 0, 0} NNRat NNRat NNRat (instHMul.{0} NNRat (Distrib.toHasMul.{0} NNRat (NonUnitalNonAssocSemiring.toDistrib.{0} NNRat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))) (Rat.toNNRat p) (Rat.toNNRat q)))
but is expected to have type
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) p) -> (Eq.{1} NNRat (Rat.toNNRat (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) p q)) (HMul.hMul.{0, 0, 0} NNRat NNRat NNRat (instHMul.{0} NNRat (CanonicallyOrderedCommSemiring.toMul.{0} NNRat instNNRatCanonicallyOrderedCommSemiring)) (Rat.toNNRat p) (Rat.toNNRat q)))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_mul Rat.toNNRat_mulₓ'. -/
theorem toNNRat_mul (hp : 0 ≤ p) : toNNRat (p * q) = toNNRat p * toNNRat q :=
  by
  cases' le_total 0 q with hq hq
  · ext <;> simp [to_nnrat, hp, hq, max_eq_left, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [to_nnrat_eq_zero.2 hq, to_nnrat_eq_zero.2 hpq, MulZeroClass.mul_zero]
#align rat.to_nnrat_mul Rat.toNNRat_mul

/- warning: rat.to_nnrat_inv -> Rat.toNNRat_inv is a dubious translation:
lean 3 declaration is
  forall (q : Rat), Eq.{1} NNRat (Rat.toNNRat (Inv.inv.{0} Rat Rat.hasInv q)) (Inv.inv.{0} NNRat (DivInvMonoid.toHasInv.{0} NNRat (GroupWithZero.toDivInvMonoid.{0} NNRat (DivisionSemiring.toGroupWithZero.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield)))))) (Rat.toNNRat q))
but is expected to have type
  forall (q : Rat), Eq.{1} NNRat (Rat.toNNRat (Inv.inv.{0} Rat Rat.instInvRat q)) (Inv.inv.{0} NNRat (CanonicallyLinearOrderedSemifield.toInv.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield) (Rat.toNNRat q))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_inv Rat.toNNRat_invₓ'. -/
theorem toNNRat_inv (q : ℚ) : toNNRat q⁻¹ = (toNNRat q)⁻¹ :=
  by
  obtain hq | hq := le_total q 0
  · rw [to_nnrat_eq_zero.mpr hq, inv_zero, to_nnrat_eq_zero.mpr (inv_nonpos.mpr hq)]
  · nth_rw 1 [← Rat.coe_toNNRat q hq]
    rw [← coe_inv, to_nnrat_coe]
#align rat.to_nnrat_inv Rat.toNNRat_inv

/- warning: rat.to_nnrat_div -> Rat.toNNRat_div is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) p) -> (Eq.{1} NNRat (Rat.toNNRat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) p q)) (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (DivInvMonoid.toHasDiv.{0} NNRat (GroupWithZero.toDivInvMonoid.{0} NNRat (DivisionSemiring.toGroupWithZero.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) (Rat.toNNRat p) (Rat.toNNRat q)))
but is expected to have type
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) p) -> (Eq.{1} NNRat (Rat.toNNRat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) p q)) (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (CanonicallyLinearOrderedSemifield.toDiv.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)) (Rat.toNNRat p) (Rat.toNNRat q)))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_div Rat.toNNRat_divₓ'. -/
theorem toNNRat_div (hp : 0 ≤ p) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← to_nnrat_inv, ← to_nnrat_mul hp]
#align rat.to_nnrat_div Rat.toNNRat_div

/- warning: rat.to_nnrat_div' -> Rat.toNNRat_div' is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) -> (Eq.{1} NNRat (Rat.toNNRat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) p q)) (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (DivInvMonoid.toHasDiv.{0} NNRat (GroupWithZero.toDivInvMonoid.{0} NNRat (DivisionSemiring.toGroupWithZero.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) (Rat.toNNRat p) (Rat.toNNRat q)))
but is expected to have type
  forall {p : Rat} {q : Rat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) -> (Eq.{1} NNRat (Rat.toNNRat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) p q)) (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (CanonicallyLinearOrderedSemifield.toDiv.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)) (Rat.toNNRat p) (Rat.toNNRat q)))
Case conversion may be inaccurate. Consider using '#align rat.to_nnrat_div' Rat.toNNRat_div'ₓ'. -/
theorem toNNRat_div' (hq : 0 ≤ q) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_inv_mul, div_eq_inv_mul, to_nnrat_mul (inv_nonneg.2 hq), to_nnrat_inv]
#align rat.to_nnrat_div' Rat.toNNRat_div'

end Rat

#print Rat.nnabs /-
/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot]
def Rat.nnabs (x : ℚ) : ℚ≥0 :=
  ⟨abs x, abs_nonneg x⟩
#align rat.nnabs Rat.nnabs
-/

/- warning: rat.coe_nnabs -> Rat.coe_nnabs is a dubious translation:
lean 3 declaration is
  forall (x : Rat), Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) (Rat.nnabs x)) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup) x)
but is expected to have type
  forall (x : Rat), Eq.{1} Rat (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (Rat.nnabs x)) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat) x)
Case conversion may be inaccurate. Consider using '#align rat.coe_nnabs Rat.coe_nnabsₓ'. -/
@[norm_cast, simp]
theorem Rat.coe_nnabs (x : ℚ) : (Rat.nnabs x : ℚ) = abs x := by simp [Rat.nnabs]
#align rat.coe_nnabs Rat.coe_nnabs

/-! ### Numerator and denominator -/


namespace NNRat

variable {p q : ℚ≥0}

#print NNRat.num /-
/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ :=
  (q : ℚ).num.natAbs
#align nnrat.num NNRat.num
-/

#print NNRat.den /-
/-- The denominator of a nonnegative rational. -/
def den (q : ℚ≥0) : ℕ :=
  (q : ℚ).den
#align nnrat.denom NNRat.den
-/

/- warning: nnrat.nat_abs_num_coe -> NNRat.natAbs_num_coe is a dubious translation:
lean 3 declaration is
  forall {q : NNRat}, Eq.{1} Nat (Int.natAbs (Rat.num ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q))) (NNRat.num q)
but is expected to have type
  forall {q : NNRat}, Eq.{1} Nat (Int.natAbs (Rat.num (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q))) (NNRat.num q)
Case conversion may be inaccurate. Consider using '#align nnrat.nat_abs_num_coe NNRat.natAbs_num_coeₓ'. -/
@[simp]
theorem natAbs_num_coe : (q : ℚ).num.natAbs = q.num :=
  rfl
#align nnrat.nat_abs_num_coe NNRat.natAbs_num_coe

/- warning: nnrat.denom_coe -> NNRat.den_coe is a dubious translation:
lean 3 declaration is
  forall {q : NNRat}, Eq.{1} Nat (Rat.den ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNRat Rat (HasLiftT.mk.{1, 1} NNRat Rat (CoeTCₓ.coe.{1, 1} NNRat Rat (coeBase.{1, 1} NNRat Rat NNRat.Rat.hasCoe))) q)) (NNRat.den q)
but is expected to have type
  forall {q : NNRat}, Eq.{1} Nat (Rat.den (Subtype.val.{1} Rat (fun (q : Rat) => LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) q)) (NNRat.den q)
Case conversion may be inaccurate. Consider using '#align nnrat.denom_coe NNRat.den_coeₓ'. -/
@[simp]
theorem den_coe : (q : ℚ).den = q.den :=
  rfl
#align nnrat.denom_coe NNRat.den_coe

#print NNRat.ext_num_den /-
theorem ext_num_den (hn : p.num = q.num) (hd : p.den = q.den) : p = q :=
  ext <|
    Rat.ext
      ((Int.natAbs_inj_of_nonneg_of_nonneg (Rat.num_nonneg_iff_zero_le.2 p.2) <|
            Rat.num_nonneg_iff_zero_le.2 q.2).1
        hn)
      hd
#align nnrat.ext_num_denom NNRat.ext_num_den
-/

#print NNRat.ext_num_den_iff /-
theorem ext_num_den_iff : p = q ↔ p.num = q.num ∧ p.den = q.den :=
  ⟨by
    rintro rfl
    exact ⟨rfl, rfl⟩, fun h => ext_num_den h.1 h.2⟩
#align nnrat.ext_num_denom_iff NNRat.ext_num_den_iff
-/

/- warning: nnrat.num_div_denom -> NNRat.num_div_den is a dubious translation:
lean 3 declaration is
  forall (q : NNRat), Eq.{1} NNRat (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (DivInvMonoid.toHasDiv.{0} NNRat (GroupWithZero.toDivInvMonoid.{0} NNRat (DivisionSemiring.toGroupWithZero.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNRat (HasLiftT.mk.{1, 1} Nat NNRat (CoeTCₓ.coe.{1, 1} Nat NNRat (Nat.castCoe.{0} NNRat (AddMonoidWithOne.toNatCast.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) (NNRat.num q)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNRat (HasLiftT.mk.{1, 1} Nat NNRat (CoeTCₓ.coe.{1, 1} Nat NNRat (Nat.castCoe.{0} NNRat (AddMonoidWithOne.toNatCast.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) (NNRat.den q))) q
but is expected to have type
  forall (q : NNRat), Eq.{1} NNRat (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (CanonicallyLinearOrderedSemifield.toDiv.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)) (Nat.cast.{0} NNRat (CanonicallyOrderedCommSemiring.toNatCast.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) (NNRat.num q)) (Nat.cast.{0} NNRat (CanonicallyOrderedCommSemiring.toNatCast.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) (NNRat.den q))) q
Case conversion may be inaccurate. Consider using '#align nnrat.num_div_denom NNRat.num_div_denₓ'. -/
@[simp]
theorem num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q :=
  by
  ext1
  rw [coe_div, coe_nat_cast, coe_nat_cast, Num, ← Int.cast_ofNat,
    Int.natAbs_of_nonneg (Rat.num_nonneg_iff_zero_le.2 q.prop)]
  exact Rat.num_div_den q
#align nnrat.num_div_denom NNRat.num_div_den

/- warning: nnrat.rec -> NNRat.rec is a dubious translation:
lean 3 declaration is
  forall {α : NNRat -> Sort.{u1}}, (forall (m : Nat) (n : Nat), α (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (DivInvMonoid.toHasDiv.{0} NNRat (GroupWithZero.toDivInvMonoid.{0} NNRat (DivisionSemiring.toGroupWithZero.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNRat (HasLiftT.mk.{1, 1} Nat NNRat (CoeTCₓ.coe.{1, 1} Nat NNRat (Nat.castCoe.{0} NNRat (AddMonoidWithOne.toNatCast.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNRat (HasLiftT.mk.{1, 1} Nat NNRat (CoeTCₓ.coe.{1, 1} Nat NNRat (Nat.castCoe.{0} NNRat (AddMonoidWithOne.toNatCast.{0} NNRat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat (Semiring.toNonAssocSemiring.{0} NNRat (DivisionSemiring.toSemiring.{0} NNRat (Semifield.toDivisionSemiring.{0} NNRat (LinearOrderedSemifield.toSemifield.{0} NNRat (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNRat NNRat.canonicallyLinearOrderedSemifield))))))))))) n))) -> (forall (q : NNRat), α q)
but is expected to have type
  forall {α : NNRat -> Sort.{u1}}, (forall (m : Nat) (n : Nat), α (HDiv.hDiv.{0, 0, 0} NNRat NNRat NNRat (instHDiv.{0} NNRat (CanonicallyLinearOrderedSemifield.toDiv.{0} NNRat instNNRatCanonicallyLinearOrderedSemifield)) (Nat.cast.{0} NNRat (CanonicallyOrderedCommSemiring.toNatCast.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) m) (Nat.cast.{0} NNRat (CanonicallyOrderedCommSemiring.toNatCast.{0} NNRat instNNRatCanonicallyOrderedCommSemiring) n))) -> (forall (q : NNRat), α q)
Case conversion may be inaccurate. Consider using '#align nnrat.rec NNRat.recₓ'. -/
/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort _} (h : ∀ m n : ℕ, α (m / n)) (q : ℚ≥0) : α q :=
  (num_div_den _).rec (h _ _)
#align nnrat.rec NNRat.rec

end NNRat

