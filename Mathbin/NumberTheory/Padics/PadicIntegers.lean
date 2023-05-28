/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin

! This file was ported from Lean 3 source module number_theory.padics.padic_integers
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.Padics.PadicNumbers
import Mathbin.RingTheory.DiscreteValuationRing.Basic

/-!
# p-adic integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `zmod p` is established in another file.

## Important definitions

* `padic_int` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact p.prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/


open Padic Metric LocalRing

noncomputable section

open Classical

#print PadicInt /-
/-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. -/
def PadicInt (p : ℕ) [Fact p.Prime] :=
  { x : ℚ_[p] // ‖x‖ ≤ 1 }
#align padic_int PadicInt
-/

-- mathport name: «exprℤ_[ ]»
notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt

/-! ### Ring structure and coercion to `ℚ_[p]` -/


variable {p : ℕ} [Fact p.Prime]

instance : Coe ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val⟩

/- warning: padic_int.ext -> PadicInt.ext is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {x : PadicInt p _inst_1} {y : PadicInt p _inst_1}, (Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) y)) -> (Eq.{1} (PadicInt p _inst_1) x y)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {x : PadicInt p _inst_1} {y : PadicInt p _inst_1}, (Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) y)) -> (Eq.{1} (PadicInt p _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align padic_int.ext PadicInt.extₓ'. -/
theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
  Subtype.ext
#align padic_int.ext PadicInt.ext

variable (p)

/- warning: padic_int.subring -> PadicInt.subring is a dubious translation:
lean 3 declaration is
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)], Subring.{0} (Padic p _inst_1) (Padic.ring p _inst_1)
but is expected to have type
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)], Subring.{0} (Padic p _inst_1) (Padic.instRingPadic p _inst_1)
Case conversion may be inaccurate. Consider using '#align padic_int.subring PadicInt.subringₓ'. -/
/-- The `p`-adic integers as a subring of `ℚ_[p]`. -/
def subring : Subring ℚ_[p] where
  carrier := { x : ℚ_[p] | ‖x‖ ≤ 1 }
  zero_mem' := by norm_num
  one_mem' := by norm_num
  add_mem' x y hx hy := (padicNormE.nonarchimedean _ _).trans <| max_le_iff.2 ⟨hx, hy⟩
  mul_mem' x y hx hy := (padicNormE.mul _ _).trans_le <| mul_le_one hx (norm_nonneg _) hy
  neg_mem' x hx := (norm_neg _).trans_le hx
#align padic_int.subring PadicInt.subring

/- warning: padic_int.mem_subring_iff -> PadicInt.mem_subring_iff is a dubious translation:
lean 3 declaration is
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)] {x : Padic p _inst_1}, Iff (Membership.Mem.{0, 0} (Padic p _inst_1) (Subring.{0} (Padic p _inst_1) (Padic.ring p _inst_1)) (SetLike.hasMem.{0, 0} (Subring.{0} (Padic p _inst_1) (Padic.ring p _inst_1)) (Padic p _inst_1) (Subring.setLike.{0} (Padic p _inst_1) (Padic.ring p _inst_1))) x (PadicInt.subring p _inst_1)) (LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)] {x : Padic p _inst_1}, Iff (Membership.mem.{0, 0} (Padic p _inst_1) (Subring.{0} (Padic p _inst_1) (Padic.instRingPadic p _inst_1)) (SetLike.instMembership.{0, 0} (Subring.{0} (Padic p _inst_1) (Padic.instRingPadic p _inst_1)) (Padic p _inst_1) (Subring.instSetLikeSubring.{0} (Padic p _inst_1) (Padic.instRingPadic p _inst_1))) x (PadicInt.subring p _inst_1)) (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align padic_int.mem_subring_iff PadicInt.mem_subring_iffₓ'. -/
@[simp]
theorem mem_subring_iff {x : ℚ_[p]} : x ∈ subring p ↔ ‖x‖ ≤ 1 :=
  Iff.rfl
#align padic_int.mem_subring_iff PadicInt.mem_subring_iff

variable {p}

/-- Addition on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Add ℤ_[p] :=
  (by infer_instance : Add (subring p))

/-- Multiplication on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Mul ℤ_[p] :=
  (by infer_instance : Mul (subring p))

/-- Negation on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Neg ℤ_[p] :=
  (by infer_instance : Neg (subring p))

/-- Subtraction on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Sub ℤ_[p] :=
  (by infer_instance : Sub (subring p))

/-- Zero on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Zero ℤ_[p] :=
  (by infer_instance : Zero (subring p))

instance : Inhabited ℤ_[p] :=
  ⟨0⟩

/-- One on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : One ℤ_[p] :=
  ⟨⟨1, by norm_num⟩⟩

/- warning: padic_int.mk_zero -> PadicInt.mk_zero is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {h : LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (OfNat.mk.{0} (Padic p _inst_1) 0 (Zero.zero.{0} (Padic p _inst_1) (Padic.hasZero p _inst_1))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))}, Eq.{1} (Subtype.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.mk.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (OfNat.mk.{0} (Padic p _inst_1) 0 (Zero.zero.{0} (Padic p _inst_1) (Padic.hasZero p _inst_1)))) h) (OfNat.ofNat.{0} (PadicInt p _inst_1) 0 (OfNat.mk.{0} (PadicInt p _inst_1) 0 (Zero.zero.{0} (PadicInt p _inst_1) (PadicInt.hasZero p _inst_1))))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {h : LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (Zero.toOfNat0.{0} (Padic p _inst_1) (Padic.instZeroPadic p _inst_1)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))}, Eq.{1} (Subtype.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.mk.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (Zero.toOfNat0.{0} (Padic p _inst_1) (Padic.instZeroPadic p _inst_1))) h) (OfNat.ofNat.{0} (PadicInt p _inst_1) 0 (Zero.toOfNat0.{0} (PadicInt p _inst_1) (PadicInt.instZeroPadicInt p _inst_1)))
Case conversion may be inaccurate. Consider using '#align padic_int.mk_zero PadicInt.mk_zeroₓ'. -/
@[simp]
theorem mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) :=
  rfl
#align padic_int.mk_zero PadicInt.mk_zero

@[simp]
theorem val_eq_coe (z : ℤ_[p]) : z.val = z :=
  rfl
#align padic_int.val_eq_coe PadicInt.val_eq_coe

/- warning: padic_int.coe_add -> PadicInt.coe_add is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1) (z2 : PadicInt p _inst_1), Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.hasAdd p _inst_1)) z1 z2)) (HAdd.hAdd.{0, 0, 0} (Padic p _inst_1) (Padic p _inst_1) (Padic p _inst_1) (instHAdd.{0} (Padic p _inst_1) (Padic.hasAdd p _inst_1)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z2))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1) (z2 : PadicInt p _inst_1), Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.instAddPadicInt p _inst_1)) z1 z2)) (HAdd.hAdd.{0, 0, 0} (Padic p _inst_1) (Padic p _inst_1) (Padic p _inst_1) (instHAdd.{0} (Padic p _inst_1) (Padic.instAddPadic p _inst_1)) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z2))
Case conversion may be inaccurate. Consider using '#align padic_int.coe_add PadicInt.coe_addₓ'. -/
@[simp, norm_cast]
theorem coe_add (z1 z2 : ℤ_[p]) : ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2 :=
  rfl
#align padic_int.coe_add PadicInt.coe_add

/- warning: padic_int.coe_mul -> PadicInt.coe_mul is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1) (z2 : PadicInt p _inst_1), Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) (HMul.hMul.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHMul.{0} (PadicInt p _inst_1) (PadicInt.hasMul p _inst_1)) z1 z2)) (HMul.hMul.{0, 0, 0} (Padic p _inst_1) (Padic p _inst_1) (Padic p _inst_1) (instHMul.{0} (Padic p _inst_1) (Padic.hasMul p _inst_1)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z2))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1) (z2 : PadicInt p _inst_1), Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (HMul.hMul.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHMul.{0} (PadicInt p _inst_1) (PadicInt.instMulPadicInt p _inst_1)) z1 z2)) (HMul.hMul.{0, 0, 0} (Padic p _inst_1) (Padic p _inst_1) (Padic p _inst_1) (instHMul.{0} (Padic p _inst_1) (Padic.instMulPadic p _inst_1)) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z2))
Case conversion may be inaccurate. Consider using '#align padic_int.coe_mul PadicInt.coe_mulₓ'. -/
@[simp, norm_cast]
theorem coe_mul (z1 z2 : ℤ_[p]) : ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2 :=
  rfl
#align padic_int.coe_mul PadicInt.coe_mul

/- warning: padic_int.coe_neg -> PadicInt.coe_neg is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1), Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) (Neg.neg.{0} (PadicInt p _inst_1) (PadicInt.hasNeg p _inst_1) z1)) (Neg.neg.{0} (Padic p _inst_1) (Padic.hasNeg p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z1))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1), Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Neg.neg.{0} (PadicInt p _inst_1) (PadicInt.instNegPadicInt p _inst_1) z1)) (Neg.neg.{0} (Padic p _inst_1) (Padic.instNegPadic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z1))
Case conversion may be inaccurate. Consider using '#align padic_int.coe_neg PadicInt.coe_negₓ'. -/
@[simp, norm_cast]
theorem coe_neg (z1 : ℤ_[p]) : ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1 :=
  rfl
#align padic_int.coe_neg PadicInt.coe_neg

/- warning: padic_int.coe_sub -> PadicInt.coe_sub is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1) (z2 : PadicInt p _inst_1), Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) (HSub.hSub.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHSub.{0} (PadicInt p _inst_1) (PadicInt.hasSub p _inst_1)) z1 z2)) (HSub.hSub.{0, 0, 0} (Padic p _inst_1) (Padic p _inst_1) (Padic p _inst_1) (instHSub.{0} (Padic p _inst_1) (Padic.hasSub p _inst_1)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z2))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1) (z2 : PadicInt p _inst_1), Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (HSub.hSub.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHSub.{0} (PadicInt p _inst_1) (PadicInt.instSubPadicInt p _inst_1)) z1 z2)) (HSub.hSub.{0, 0, 0} (Padic p _inst_1) (Padic p _inst_1) (Padic p _inst_1) (instHSub.{0} (Padic p _inst_1) (Padic.instSubPadic p _inst_1)) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z2))
Case conversion may be inaccurate. Consider using '#align padic_int.coe_sub PadicInt.coe_subₓ'. -/
@[simp, norm_cast]
theorem coe_sub (z1 z2 : ℤ_[p]) : ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2 :=
  rfl
#align padic_int.coe_sub PadicInt.coe_sub

/- warning: padic_int.coe_one -> PadicInt.coe_one is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) (OfNat.ofNat.{0} (PadicInt p _inst_1) 1 (OfNat.mk.{0} (PadicInt p _inst_1) 1 (One.one.{0} (PadicInt p _inst_1) (PadicInt.hasOne p _inst_1))))) (OfNat.ofNat.{0} (Padic p _inst_1) 1 (OfNat.mk.{0} (Padic p _inst_1) 1 (One.one.{0} (Padic p _inst_1) (Padic.hasOne p _inst_1))))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} (PadicInt p _inst_1) 1 (One.toOfNat1.{0} (PadicInt p _inst_1) (PadicInt.instOnePadicInt p _inst_1)))) (OfNat.ofNat.{0} (Padic p _inst_1) 1 (One.toOfNat1.{0} (Padic p _inst_1) (Padic.instOnePadic p _inst_1)))
Case conversion may be inaccurate. Consider using '#align padic_int.coe_one PadicInt.coe_oneₓ'. -/
@[simp, norm_cast]
theorem coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 :=
  rfl
#align padic_int.coe_one PadicInt.coe_one

/- warning: padic_int.coe_zero -> PadicInt.coe_zero is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) (OfNat.ofNat.{0} (PadicInt p _inst_1) 0 (OfNat.mk.{0} (PadicInt p _inst_1) 0 (Zero.zero.{0} (PadicInt p _inst_1) (PadicInt.hasZero p _inst_1))))) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (OfNat.mk.{0} (Padic p _inst_1) 0 (Zero.zero.{0} (Padic p _inst_1) (Padic.hasZero p _inst_1))))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} (PadicInt p _inst_1) 0 (Zero.toOfNat0.{0} (PadicInt p _inst_1) (PadicInt.instZeroPadicInt p _inst_1)))) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (Zero.toOfNat0.{0} (Padic p _inst_1) (Padic.instZeroPadic p _inst_1)))
Case conversion may be inaccurate. Consider using '#align padic_int.coe_zero PadicInt.coe_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 :=
  rfl
#align padic_int.coe_zero PadicInt.coe_zero

/- warning: padic_int.coe_eq_zero -> PadicInt.coe_eq_zero is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1), Iff (Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (OfNat.mk.{0} (Padic p _inst_1) 0 (Zero.zero.{0} (Padic p _inst_1) (Padic.hasZero p _inst_1))))) (Eq.{1} (PadicInt p _inst_1) z (OfNat.ofNat.{0} (PadicInt p _inst_1) 0 (OfNat.mk.{0} (PadicInt p _inst_1) 0 (Zero.zero.{0} (PadicInt p _inst_1) (PadicInt.hasZero p _inst_1)))))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1), Iff (Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (Zero.toOfNat0.{0} (Padic p _inst_1) (Padic.instZeroPadic p _inst_1)))) (Eq.{1} (PadicInt p _inst_1) z (OfNat.ofNat.{0} (PadicInt p _inst_1) 0 (Zero.toOfNat0.{0} (PadicInt p _inst_1) (PadicInt.instZeroPadicInt p _inst_1))))
Case conversion may be inaccurate. Consider using '#align padic_int.coe_eq_zero PadicInt.coe_eq_zeroₓ'. -/
theorem coe_eq_zero (z : ℤ_[p]) : (z : ℚ_[p]) = 0 ↔ z = 0 := by rw [← coe_zero, Subtype.coe_inj]
#align padic_int.coe_eq_zero PadicInt.coe_eq_zero

/- warning: padic_int.coe_ne_zero -> PadicInt.coe_ne_zero is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1), Iff (Ne.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (OfNat.mk.{0} (Padic p _inst_1) 0 (Zero.zero.{0} (Padic p _inst_1) (Padic.hasZero p _inst_1))))) (Ne.{1} (PadicInt p _inst_1) z (OfNat.ofNat.{0} (PadicInt p _inst_1) 0 (OfNat.mk.{0} (PadicInt p _inst_1) 0 (Zero.zero.{0} (PadicInt p _inst_1) (PadicInt.hasZero p _inst_1)))))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1), Iff (Ne.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z) (OfNat.ofNat.{0} (Padic p _inst_1) 0 (Zero.toOfNat0.{0} (Padic p _inst_1) (Padic.instZeroPadic p _inst_1)))) (Ne.{1} (PadicInt p _inst_1) z (OfNat.ofNat.{0} (PadicInt p _inst_1) 0 (Zero.toOfNat0.{0} (PadicInt p _inst_1) (PadicInt.instZeroPadicInt p _inst_1))))
Case conversion may be inaccurate. Consider using '#align padic_int.coe_ne_zero PadicInt.coe_ne_zeroₓ'. -/
theorem coe_ne_zero (z : ℤ_[p]) : (z : ℚ_[p]) ≠ 0 ↔ z ≠ 0 :=
  z.val_eq_zero.Not
#align padic_int.coe_ne_zero PadicInt.coe_ne_zero

instance : AddCommGroup ℤ_[p] :=
  (by infer_instance : AddCommGroup (subring p))

instance : CommRing ℤ_[p] :=
  (by infer_instance : CommRing (subring p))

/- warning: padic_int.coe_nat_cast -> PadicInt.coe_nat_cast is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (n : Nat), Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p _inst_1) (HasLiftT.mk.{1, 1} Nat (PadicInt p _inst_1) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p _inst_1) (Nat.castCoe.{0} (PadicInt p _inst_1) (AddMonoidWithOne.toNatCast.{0} (PadicInt p _inst_1) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p _inst_1) (Ring.toAddCommGroupWithOne.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.commRing p _inst_1))))))))) n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Padic p _inst_1) (HasLiftT.mk.{1, 1} Nat (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} Nat (Padic p _inst_1) (Nat.castCoe.{0} (Padic p _inst_1) (AddMonoidWithOne.toNatCast.{0} (Padic p _inst_1) (AddGroupWithOne.toAddMonoidWithOne.{0} (Padic p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (Padic p _inst_1) (Ring.toAddCommGroupWithOne.{0} (Padic p _inst_1) (Padic.ring p _inst_1)))))))) n)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (n : Nat), Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Nat.cast.{0} (PadicInt p _inst_1) (Semiring.toNatCast.{0} (PadicInt p _inst_1) (CommSemiring.toSemiring.{0} (PadicInt p _inst_1) (CommRing.toCommSemiring.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1)))) n)) (Nat.cast.{0} (Padic p _inst_1) (Semiring.toNatCast.{0} (Padic p _inst_1) (DivisionSemiring.toSemiring.{0} (Padic p _inst_1) (Semifield.toDivisionSemiring.{0} (Padic p _inst_1) (Field.toSemifield.{0} (Padic p _inst_1) (Padic.field p _inst_1))))) n)
Case conversion may be inaccurate. Consider using '#align padic_int.coe_nat_cast PadicInt.coe_nat_castₓ'. -/
@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : ((n : ℤ_[p]) : ℚ_[p]) = n :=
  rfl
#align padic_int.coe_nat_cast PadicInt.coe_nat_cast

/- warning: padic_int.coe_int_cast -> PadicInt.coe_int_cast is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : Int), Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (PadicInt p _inst_1) (HasLiftT.mk.{1, 1} Int (PadicInt p _inst_1) (CoeTCₓ.coe.{1, 1} Int (PadicInt p _inst_1) (Int.castCoe.{0} (PadicInt p _inst_1) (AddGroupWithOne.toHasIntCast.{0} (PadicInt p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p _inst_1) (Ring.toAddCommGroupWithOne.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.commRing p _inst_1)))))))) z)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Padic p _inst_1) (HasLiftT.mk.{1, 1} Int (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} Int (Padic p _inst_1) (Int.castCoe.{0} (Padic p _inst_1) (AddGroupWithOne.toHasIntCast.{0} (Padic p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (Padic p _inst_1) (Ring.toAddCommGroupWithOne.{0} (Padic p _inst_1) (Padic.ring p _inst_1))))))) z)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : Int), Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Int.cast.{0} (PadicInt p _inst_1) (Ring.toIntCast.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1))) z)) (Int.cast.{0} (Padic p _inst_1) (Ring.toIntCast.{0} (Padic p _inst_1) (Padic.instRingPadic p _inst_1)) z)
Case conversion may be inaccurate. Consider using '#align padic_int.coe_int_cast PadicInt.coe_int_castₓ'. -/
@[simp, norm_cast]
theorem coe_int_cast (z : ℤ) : ((z : ℤ_[p]) : ℚ_[p]) = z :=
  rfl
#align padic_int.coe_int_cast PadicInt.coe_int_cast

/- warning: padic_int.coe.ring_hom -> PadicInt.Coe.ringHom is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], RingHom.{0, 0} (PadicInt p _inst_1) (Padic p _inst_1) (NonAssocRing.toNonAssocSemiring.{0} (PadicInt p _inst_1) (Ring.toNonAssocRing.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.commRing p _inst_1)))) (NonAssocRing.toNonAssocSemiring.{0} (Padic p _inst_1) (Ring.toNonAssocRing.{0} (Padic p _inst_1) (Padic.ring p _inst_1)))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], RingHom.{0, 0} (PadicInt p _inst_1) (Padic p _inst_1) (Semiring.toNonAssocSemiring.{0} (PadicInt p _inst_1) (CommSemiring.toSemiring.{0} (PadicInt p _inst_1) (CommRing.toCommSemiring.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1)))) (Semiring.toNonAssocSemiring.{0} (Padic p _inst_1) (DivisionSemiring.toSemiring.{0} (Padic p _inst_1) (Semifield.toDivisionSemiring.{0} (Padic p _inst_1) (Field.toSemifield.{0} (Padic p _inst_1) (Padic.field p _inst_1)))))
Case conversion may be inaccurate. Consider using '#align padic_int.coe.ring_hom PadicInt.Coe.ringHomₓ'. -/
/-- The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism. -/
def Coe.ringHom : ℤ_[p] →+* ℚ_[p] :=
  (subring p).Subtype
#align padic_int.coe.ring_hom PadicInt.Coe.ringHom

/- warning: padic_int.coe_pow -> PadicInt.coe_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (x : PadicInt p _inst_1) (n : Nat), Eq.{1} (Padic p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) (HPow.hPow.{0, 0, 0} (PadicInt p _inst_1) Nat (PadicInt p _inst_1) (instHPow.{0, 0} (PadicInt p _inst_1) Nat (Monoid.Pow.{0} (PadicInt p _inst_1) (Ring.toMonoid.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.commRing p _inst_1))))) x n)) (HPow.hPow.{0, 0, 0} (Padic p _inst_1) Nat (Padic p _inst_1) (instHPow.{0, 0} (Padic p _inst_1) Nat (Monoid.Pow.{0} (Padic p _inst_1) (Ring.toMonoid.{0} (Padic p _inst_1) (Padic.ring p _inst_1)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) x) n)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (x : PadicInt p _inst_1) (n : Nat), Eq.{1} (Padic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (HPow.hPow.{0, 0, 0} (PadicInt p _inst_1) Nat (PadicInt p _inst_1) (instHPow.{0, 0} (PadicInt p _inst_1) Nat (Monoid.Pow.{0} (PadicInt p _inst_1) (MonoidWithZero.toMonoid.{0} (PadicInt p _inst_1) (Semiring.toMonoidWithZero.{0} (PadicInt p _inst_1) (CommSemiring.toSemiring.{0} (PadicInt p _inst_1) (CommRing.toCommSemiring.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1))))))) x n)) (HPow.hPow.{0, 0, 0} (Padic p _inst_1) Nat (Padic p _inst_1) (instHPow.{0, 0} (Padic p _inst_1) Nat (Monoid.Pow.{0} (Padic p _inst_1) (MonoidWithZero.toMonoid.{0} (Padic p _inst_1) (Semiring.toMonoidWithZero.{0} (Padic p _inst_1) (DivisionSemiring.toSemiring.{0} (Padic p _inst_1) (Semifield.toDivisionSemiring.{0} (Padic p _inst_1) (Field.toSemifield.{0} (Padic p _inst_1) (Padic.field p _inst_1)))))))) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x) n)
Case conversion may be inaccurate. Consider using '#align padic_int.coe_pow PadicInt.coe_powₓ'. -/
@[simp, norm_cast]
theorem coe_pow (x : ℤ_[p]) (n : ℕ) : (↑(x ^ n) : ℚ_[p]) = (↑x : ℚ_[p]) ^ n :=
  rfl
#align padic_int.coe_pow PadicInt.coe_pow

/- warning: padic_int.mk_coe -> PadicInt.mk_coe is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (k : PadicInt p _inst_1), Eq.{1} (Subtype.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.mk.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) k) (Subtype.property.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) k)) k
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (k : PadicInt p _inst_1), Eq.{1} (Subtype.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.mk.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) k) (Subtype.property.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) k)) k
Case conversion may be inaccurate. Consider using '#align padic_int.mk_coe PadicInt.mk_coeₓ'. -/
@[simp]
theorem mk_coe (k : ℤ_[p]) : (⟨k, k.2⟩ : ℤ_[p]) = k :=
  Subtype.coe_eta _ _
#align padic_int.mk_coe PadicInt.mk_coe

#print PadicInt.inv /-
/-- The inverse of a `p`-adic integer with norm equal to `1` is also a `p`-adic integer.
Otherwise, the inverse is defined to be `0`. -/
def inv : ℤ_[p] → ℤ_[p]
  | ⟨k, _⟩ => if h : ‖k‖ = 1 then ⟨k⁻¹, by simp [h]⟩ else 0
#align padic_int.inv PadicInt.inv
-/

instance : CharZero ℤ_[p]
    where cast_injective m n h :=
    Nat.cast_injective <|
      show (m : ℚ_[p]) = n by rw [Subtype.ext_iff] at h; norm_cast  at h; exact h

/- warning: padic_int.coe_int_eq -> PadicInt.coe_int_eq is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : Int) (z2 : Int), Iff (Eq.{1} (PadicInt p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (PadicInt p _inst_1) (HasLiftT.mk.{1, 1} Int (PadicInt p _inst_1) (CoeTCₓ.coe.{1, 1} Int (PadicInt p _inst_1) (Int.castCoe.{0} (PadicInt p _inst_1) (AddGroupWithOne.toHasIntCast.{0} (PadicInt p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p _inst_1) (Ring.toAddCommGroupWithOne.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.commRing p _inst_1)))))))) z1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (PadicInt p _inst_1) (HasLiftT.mk.{1, 1} Int (PadicInt p _inst_1) (CoeTCₓ.coe.{1, 1} Int (PadicInt p _inst_1) (Int.castCoe.{0} (PadicInt p _inst_1) (AddGroupWithOne.toHasIntCast.{0} (PadicInt p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p _inst_1) (Ring.toAddCommGroupWithOne.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.commRing p _inst_1)))))))) z2)) (Eq.{1} Int z1 z2)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : Int) (z2 : Int), Iff (Eq.{1} (PadicInt p _inst_1) (Int.cast.{0} (PadicInt p _inst_1) (Ring.toIntCast.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1))) z1) (Int.cast.{0} (PadicInt p _inst_1) (Ring.toIntCast.{0} (PadicInt p _inst_1) (CommRing.toRing.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1))) z2)) (Eq.{1} Int z1 z2)
Case conversion may be inaccurate. Consider using '#align padic_int.coe_int_eq PadicInt.coe_int_eqₓ'. -/
@[simp, norm_cast]
theorem coe_int_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 :=
  by
  suffices (z1 : ℚ_[p]) = z2 ↔ z1 = z2 from Iff.trans (by norm_cast) this
  norm_cast
#align padic_int.coe_int_eq PadicInt.coe_int_eq

/- warning: padic_int.of_int_seq -> PadicInt.ofIntSeq is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (seq : Nat -> Int), (IsCauSeq.{0, 0} Rat Rat.linearOrderedField Rat (NormedRing.toRing.{0} Rat (NormedCommRing.toNormedRing.{0} Rat (NormedField.toNormedCommRing.{0} Rat Rat.normedField))) (padicNorm p) (fun (n : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) (seq n))) -> (PadicInt p _inst_1)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (seq : Nat -> Int), (IsCauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (NormedRing.toRing.{0} Rat (NormedCommRing.toNormedRing.{0} Rat (NormedField.toNormedCommRing.{0} Rat Rat.normedField))) (padicNorm p) (fun (n : Nat) => Int.cast.{0} Rat Rat.instIntCastRat (seq n))) -> (PadicInt p _inst_1)
Case conversion may be inaccurate. Consider using '#align padic_int.of_int_seq PadicInt.ofIntSeqₓ'. -/
/-- A sequence of integers that is Cauchy with respect to the `p`-adic norm converges to a `p`-adic
integer. -/
def ofIntSeq (seq : ℕ → ℤ) (h : IsCauSeq (padicNorm p) fun n => seq n) : ℤ_[p] :=
  ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) ≤ (1 : ℝ) by
      rw [PadicSeq.norm]
      split_ifs with hne <;> norm_cast
      · exact zero_le_one
      · apply padicNorm.of_int⟩
#align padic_int.of_int_seq PadicInt.ofIntSeq

end PadicInt

namespace PadicInt

/-! ### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/


variable (p : ℕ) [Fact p.Prime]

instance : MetricSpace ℤ_[p] :=
  Subtype.metricSpace

/- warning: padic_int.complete_space -> PadicInt.completeSpace is a dubious translation:
lean 3 declaration is
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)], CompleteSpace.{0} (PadicInt p _inst_1) (PseudoMetricSpace.toUniformSpace.{0} (PadicInt p _inst_1) (MetricSpace.toPseudoMetricSpace.{0} (PadicInt p _inst_1) (PadicInt.metricSpace p _inst_1)))
but is expected to have type
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)], CompleteSpace.{0} (PadicInt p _inst_1) (PseudoMetricSpace.toUniformSpace.{0} (PadicInt p _inst_1) (MetricSpace.toPseudoMetricSpace.{0} (PadicInt p _inst_1) (PadicInt.instMetricSpacePadicInt p _inst_1)))
Case conversion may be inaccurate. Consider using '#align padic_int.complete_space PadicInt.completeSpaceₓ'. -/
instance completeSpace : CompleteSpace ℤ_[p] :=
  have : IsClosed { x : ℚ_[p] | ‖x‖ ≤ 1 } := isClosed_le continuous_norm continuous_const
  this.completeSpace_coe
#align padic_int.complete_space PadicInt.completeSpace

instance : Norm ℤ_[p] :=
  ⟨fun z => ‖(z : ℚ_[p])‖⟩

variable {p}

/- warning: padic_int.norm_def -> PadicInt.norm_def is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {z : PadicInt p _inst_1}, Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z) (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {z : PadicInt p _inst_1}, Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z) (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_def PadicInt.norm_defₓ'. -/
theorem norm_def {z : ℤ_[p]} : ‖z‖ = ‖(z : ℚ_[p])‖ :=
  rfl
#align padic_int.norm_def PadicInt.norm_def

variable (p)

instance : NormedCommRing ℤ_[p] :=
  { PadicInt.commRing,
    PadicInt.metricSpace p with
    dist_eq := fun ⟨_, _⟩ ⟨_, _⟩ => rfl
    norm_mul := by simp [norm_def]
    norm := norm }

instance : NormOneClass ℤ_[p] :=
  ⟨norm_def.trans norm_one⟩

/- warning: padic_int.is_absolute_value -> PadicInt.isAbsoluteValue is a dubious translation:
lean 3 declaration is
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)], IsAbsoluteValue.{0, 0} Real Real.orderedSemiring (PadicInt p _inst_1) (Ring.toSemiring.{0} (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.normedCommRing p _inst_1)))) (fun (z : PadicInt p _inst_1) => Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z)
but is expected to have type
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)], IsAbsoluteValue.{0, 0} Real Real.orderedSemiring (PadicInt p _inst_1) (CommSemiring.toSemiring.{0} (PadicInt p _inst_1) (CommRing.toCommSemiring.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1))) (fun (z : PadicInt p _inst_1) => Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z)
Case conversion may be inaccurate. Consider using '#align padic_int.is_absolute_value PadicInt.isAbsoluteValueₓ'. -/
instance isAbsoluteValue : IsAbsoluteValue fun z : ℤ_[p] => ‖z‖
    where
  abv_nonneg := norm_nonneg
  abv_eq_zero := fun ⟨_, _⟩ => by simp [norm_eq_zero]
  abv_add := fun ⟨_, _⟩ ⟨_, _⟩ => norm_add_le _ _
  abv_mul _ _ := by simp only [norm_def, padicNormE.mul, PadicInt.coe_mul]
#align padic_int.is_absolute_value PadicInt.isAbsoluteValue

variable {p}

instance : IsDomain ℤ_[p] :=
  Function.Injective.isDomain (subring p).Subtype Subtype.coe_injective

end PadicInt

namespace PadicInt

/-! ### Norm -/


variable {p : ℕ} [Fact p.Prime]

/- warning: padic_int.norm_le_one -> PadicInt.norm_le_one is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1), LE.le.{0} Real Real.hasLe (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1), LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_le_one PadicInt.norm_le_oneₓ'. -/
theorem norm_le_one (z : ℤ_[p]) : ‖z‖ ≤ 1 :=
  z.2
#align padic_int.norm_le_one PadicInt.norm_le_one

/- warning: padic_int.norm_mul -> PadicInt.norm_mul is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1) (z2 : PadicInt p _inst_1), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) (HMul.hMul.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHMul.{0} (PadicInt p _inst_1) (PadicInt.hasMul p _inst_1)) z1 z2)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z1) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z2))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z1 : PadicInt p _inst_1) (z2 : PadicInt p _inst_1), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (HMul.hMul.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHMul.{0} (PadicInt p _inst_1) (PadicInt.instMulPadicInt p _inst_1)) z1 z2)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z1) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z2))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_mul PadicInt.norm_mulₓ'. -/
@[simp]
theorem norm_mul (z1 z2 : ℤ_[p]) : ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp [norm_def]
#align padic_int.norm_mul PadicInt.norm_mul

/- warning: padic_int.norm_pow -> PadicInt.norm_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1) (n : Nat), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) (HPow.hPow.{0, 0, 0} (PadicInt p _inst_1) Nat (PadicInt p _inst_1) (instHPow.{0, 0} (PadicInt p _inst_1) Nat (Monoid.Pow.{0} (PadicInt p _inst_1) (Ring.toMonoid.{0} (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.normedCommRing p _inst_1)))))) z n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z) n)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1) (n : Nat), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (HPow.hPow.{0, 0, 0} (PadicInt p _inst_1) Nat (PadicInt p _inst_1) (instHPow.{0, 0} (PadicInt p _inst_1) Nat (Monoid.Pow.{0} (PadicInt p _inst_1) (MonoidWithZero.toMonoid.{0} (PadicInt p _inst_1) (Semiring.toMonoidWithZero.{0} (PadicInt p _inst_1) (CommSemiring.toSemiring.{0} (PadicInt p _inst_1) (CommRing.toCommSemiring.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1))))))) z n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z) n)
Case conversion may be inaccurate. Consider using '#align padic_int.norm_pow PadicInt.norm_powₓ'. -/
@[simp]
theorem norm_pow (z : ℤ_[p]) : ∀ n : ℕ, ‖z ^ n‖ = ‖z‖ ^ n
  | 0 => by simp
  | k + 1 => by rw [pow_succ, pow_succ, norm_mul]; congr ; apply norm_pow
#align padic_int.norm_pow PadicInt.norm_pow

/- warning: padic_int.nonarchimedean -> PadicInt.nonarchimedean is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (q : PadicInt p _inst_1) (r : PadicInt p _inst_1), LE.le.{0} Real Real.hasLe (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.hasAdd p _inst_1)) q r)) (LinearOrder.max.{0} Real Real.linearOrder (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) q) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) r))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (q : PadicInt p _inst_1) (r : PadicInt p _inst_1), LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.instAddPadicInt p _inst_1)) q r)) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) q) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) r))
Case conversion may be inaccurate. Consider using '#align padic_int.nonarchimedean PadicInt.nonarchimedeanₓ'. -/
theorem nonarchimedean (q r : ℤ_[p]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ :=
  padicNormE.nonarchimedean _ _
#align padic_int.nonarchimedean PadicInt.nonarchimedean

/- warning: padic_int.norm_add_eq_max_of_ne -> PadicInt.norm_add_eq_max_of_ne is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {q : PadicInt p _inst_1} {r : PadicInt p _inst_1}, (Ne.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) q) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) r)) -> (Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.hasAdd p _inst_1)) q r)) (LinearOrder.max.{0} Real Real.linearOrder (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) q) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) r)))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {q : PadicInt p _inst_1} {r : PadicInt p _inst_1}, (Ne.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) q) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) r)) -> (Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.instAddPadicInt p _inst_1)) q r)) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) q) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) r)))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_add_eq_max_of_ne PadicInt.norm_add_eq_max_of_neₓ'. -/
theorem norm_add_eq_max_of_ne {q r : ℤ_[p]} : ‖q‖ ≠ ‖r‖ → ‖q + r‖ = max ‖q‖ ‖r‖ :=
  padicNormE.add_eq_max_of_ne
#align padic_int.norm_add_eq_max_of_ne PadicInt.norm_add_eq_max_of_ne

/- warning: padic_int.norm_eq_of_norm_add_lt_right -> PadicInt.norm_eq_of_norm_add_lt_right is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {z1 : PadicInt p _inst_1} {z2 : PadicInt p _inst_1}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.hasAdd p _inst_1)) z1 z2)) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z2)) -> (Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z1) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z2))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {z1 : PadicInt p _inst_1} {z2 : PadicInt p _inst_1}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.instAddPadicInt p _inst_1)) z1 z2)) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z2)) -> (Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z1) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z2))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_eq_of_norm_add_lt_right PadicInt.norm_eq_of_norm_add_lt_rightₓ'. -/
theorem norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  by_contradiction fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne] <;> apply le_max_right) h
#align padic_int.norm_eq_of_norm_add_lt_right PadicInt.norm_eq_of_norm_add_lt_right

/- warning: padic_int.norm_eq_of_norm_add_lt_left -> PadicInt.norm_eq_of_norm_add_lt_left is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {z1 : PadicInt p _inst_1} {z2 : PadicInt p _inst_1}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.hasAdd p _inst_1)) z1 z2)) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z1)) -> (Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z1) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z2))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {z1 : PadicInt p _inst_1} {z2 : PadicInt p _inst_1}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (HAdd.hAdd.{0, 0, 0} (PadicInt p _inst_1) (PadicInt p _inst_1) (PadicInt p _inst_1) (instHAdd.{0} (PadicInt p _inst_1) (PadicInt.instAddPadicInt p _inst_1)) z1 z2)) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z1)) -> (Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z1) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z2))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_eq_of_norm_add_lt_left PadicInt.norm_eq_of_norm_add_lt_leftₓ'. -/
theorem norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  by_contradiction fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne] <;> apply le_max_left) h
#align padic_int.norm_eq_of_norm_add_lt_left PadicInt.norm_eq_of_norm_add_lt_left

/- warning: padic_int.padic_norm_e_of_padic_int -> PadicInt.padic_norm_e_of_padicInt is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1), Eq.{1} Real (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p _inst_1) (Padic p _inst_1) (HasLiftT.mk.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (coeBase.{1, 1} (PadicInt p _inst_1) (Padic p _inst_1) (PadicInt.Padic.hasCoe p _inst_1)))) z)) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) z)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : PadicInt p _inst_1), Eq.{1} Real (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) (Subtype.val.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) z)) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) z)
Case conversion may be inaccurate. Consider using '#align padic_int.padic_norm_e_of_padic_int PadicInt.padic_norm_e_of_padicIntₓ'. -/
@[simp]
theorem padic_norm_e_of_padicInt (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ = ‖z‖ := by simp [norm_def]
#align padic_int.padic_norm_e_of_padic_int PadicInt.padic_norm_e_of_padicInt

/- warning: padic_int.norm_int_cast_eq_padic_norm -> PadicInt.norm_int_cast_eq_padic_norm is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : Int), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (PadicInt p _inst_1) (HasLiftT.mk.{1, 1} Int (PadicInt p _inst_1) (CoeTCₓ.coe.{1, 1} Int (PadicInt p _inst_1) (Int.castCoe.{0} (PadicInt p _inst_1) (AddGroupWithOne.toHasIntCast.{0} (PadicInt p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p _inst_1) (Ring.toAddCommGroupWithOne.{0} (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.normedCommRing p _inst_1))))))))) z)) (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Padic p _inst_1) (HasLiftT.mk.{1, 1} Int (Padic p _inst_1) (CoeTCₓ.coe.{1, 1} Int (Padic p _inst_1) (Int.castCoe.{0} (Padic p _inst_1) (AddGroupWithOne.toHasIntCast.{0} (Padic p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (Padic p _inst_1) (Ring.toAddCommGroupWithOne.{0} (Padic p _inst_1) (Padic.ring p _inst_1))))))) z))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (z : Int), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (Int.cast.{0} (PadicInt p _inst_1) (Ring.toIntCast.{0} (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.instNormedCommRingPadicInt p _inst_1)))) z)) (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) (Int.cast.{0} (Padic p _inst_1) (Ring.toIntCast.{0} (Padic p _inst_1) (Padic.instRingPadic p _inst_1)) z))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_int_cast_eq_padic_norm PadicInt.norm_int_cast_eq_padic_normₓ'. -/
theorem norm_int_cast_eq_padic_norm (z : ℤ) : ‖(z : ℤ_[p])‖ = ‖(z : ℚ_[p])‖ := by simp [norm_def]
#align padic_int.norm_int_cast_eq_padic_norm PadicInt.norm_int_cast_eq_padic_norm

/- warning: padic_int.norm_eq_padic_norm -> PadicInt.norm_eq_padic_norm is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {q : Padic p _inst_1} (hq : LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) q) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) (Subtype.mk.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.hasLe (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) q hq)) (Norm.norm.{0} (Padic p _inst_1) (Padic.hasNorm p _inst_1) q)
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] {q : Padic p _inst_1} (hq : LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) q) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (Subtype.mk.{1} (Padic p _inst_1) (fun (x : Padic p _inst_1) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) q hq)) (Norm.norm.{0} (Padic p _inst_1) (Padic.instNormPadic p _inst_1) q)
Case conversion may be inaccurate. Consider using '#align padic_int.norm_eq_padic_norm PadicInt.norm_eq_padic_normₓ'. -/
@[simp]
theorem norm_eq_padic_norm {q : ℚ_[p]} (hq : ‖q‖ ≤ 1) : @norm ℤ_[p] _ ⟨q, hq⟩ = ‖q‖ :=
  rfl
#align padic_int.norm_eq_padic_norm PadicInt.norm_eq_padic_norm

/- warning: padic_int.norm_p -> PadicInt.norm_p is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p _inst_1) (HasLiftT.mk.{1, 1} Nat (PadicInt p _inst_1) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p _inst_1) (Nat.castCoe.{0} (PadicInt p _inst_1) (AddMonoidWithOne.toNatCast.{0} (PadicInt p _inst_1) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p _inst_1) (Ring.toAddCommGroupWithOne.{0} (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.normedCommRing p _inst_1)))))))))) p)) (Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (Nat.cast.{0} (PadicInt p _inst_1) (Semiring.toNatCast.{0} (PadicInt p _inst_1) (CommSemiring.toSemiring.{0} (PadicInt p _inst_1) (CommRing.toCommSemiring.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1)))) p)) (Inv.inv.{0} Real Real.instInvReal (Nat.cast.{0} Real Real.natCast p))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_p PadicInt.norm_pₓ'. -/
@[simp]
theorem norm_p : ‖(p : ℤ_[p])‖ = p⁻¹ :=
  padicNormE.norm_p
#align padic_int.norm_p PadicInt.norm_p

/- warning: padic_int.norm_p_pow -> PadicInt.norm_p_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (n : Nat), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1) (HPow.hPow.{0, 0, 0} (PadicInt p _inst_1) Nat (PadicInt p _inst_1) (instHPow.{0, 0} (PadicInt p _inst_1) Nat (Monoid.Pow.{0} (PadicInt p _inst_1) (Ring.toMonoid.{0} (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.normedCommRing p _inst_1)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p _inst_1) (HasLiftT.mk.{1, 1} Nat (PadicInt p _inst_1) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p _inst_1) (Nat.castCoe.{0} (PadicInt p _inst_1) (AddMonoidWithOne.toNatCast.{0} (PadicInt p _inst_1) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p _inst_1) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p _inst_1) (Ring.toAddCommGroupWithOne.{0} (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.normedCommRing p _inst_1)))))))))) p) n)) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)] (n : Nat), Eq.{1} Real (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1) (HPow.hPow.{0, 0, 0} (PadicInt p _inst_1) Nat (PadicInt p _inst_1) (instHPow.{0, 0} (PadicInt p _inst_1) Nat (Monoid.Pow.{0} (PadicInt p _inst_1) (MonoidWithZero.toMonoid.{0} (PadicInt p _inst_1) (Semiring.toMonoidWithZero.{0} (PadicInt p _inst_1) (CommSemiring.toSemiring.{0} (PadicInt p _inst_1) (CommRing.toCommSemiring.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1))))))) (Nat.cast.{0} (PadicInt p _inst_1) (Semiring.toNatCast.{0} (PadicInt p _inst_1) (CommSemiring.toSemiring.{0} (PadicInt p _inst_1) (CommRing.toCommSemiring.{0} (PadicInt p _inst_1) (PadicInt.instCommRingPadicInt p _inst_1)))) p) n)) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int instNatCastInt n)))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_p_pow PadicInt.norm_p_powₓ'. -/
@[simp]
theorem norm_p_pow (n : ℕ) : ‖(p : ℤ_[p]) ^ n‖ = p ^ (-n : ℤ) :=
  padicNormE.norm_p_pow n
#align padic_int.norm_p_pow PadicInt.norm_p_pow

private def cau_seq_to_rat_cau_seq (f : CauSeq ℤ_[p] norm) : CauSeq ℚ_[p] fun a => ‖a‖ :=
  ⟨fun n => f n, fun _ hε => by simpa [norm, norm_def] using f.cauchy hε⟩

variable (p)

/- warning: padic_int.complete -> PadicInt.complete is a dubious translation:
lean 3 declaration is
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)], CauSeq.IsComplete.{0, 0} Real Real.linearOrderedField (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.normedCommRing p _inst_1))) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.hasNorm p _inst_1)) (PadicInt.isAbsoluteValue p _inst_1)
but is expected to have type
  forall (p : Nat) [_inst_1 : Fact (Nat.Prime p)], CauSeq.IsComplete.{0, 0} Real Real.instLinearOrderedFieldReal (PadicInt p _inst_1) (NormedRing.toRing.{0} (PadicInt p _inst_1) (NormedCommRing.toNormedRing.{0} (PadicInt p _inst_1) (PadicInt.instNormedCommRingPadicInt p _inst_1))) (Norm.norm.{0} (PadicInt p _inst_1) (PadicInt.instNormPadicInt p _inst_1)) (PadicInt.isAbsoluteValue p _inst_1)
Case conversion may be inaccurate. Consider using '#align padic_int.complete PadicInt.completeₓ'. -/
instance complete : CauSeq.IsComplete ℤ_[p] norm :=
  ⟨fun f =>
    have hqn : ‖CauSeq.lim (cauSeqToRatCauSeq f)‖ ≤ 1 :=
      padicNormE_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [norm, norm_def] using CauSeq.equiv_lim (cau_seq_to_rat_cau_seq f) ε⟩⟩
#align padic_int.complete PadicInt.complete

end PadicInt

namespace PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

include hp

/- warning: padic_int.exists_pow_neg_lt -> PadicInt.exists_pow_neg_lt is a dubious translation:
lean 3 declaration is
  forall (p : Nat) [hp : Fact (Nat.Prime p)] {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{1} Nat (fun (k : Nat) => LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) k))) ε))
but is expected to have type
  forall (p : Nat) [hp : Fact (Nat.Prime p)] {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{1} Nat (fun (k : Nat) => LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int instNatCastInt k))) ε))
Case conversion may be inaccurate. Consider using '#align padic_int.exists_pow_neg_lt PadicInt.exists_pow_neg_ltₓ'. -/
theorem exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, ↑p ^ (-(k : ℤ)) < ε :=
  by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  use k
  rw [← inv_lt_inv hε (_root_.zpow_pos_of_pos _ _)]
  · rw [zpow_neg, inv_inv, zpow_ofNat]
    apply lt_of_lt_of_le hk
    norm_cast
    apply le_of_lt
    convert Nat.lt_pow_self _ _ using 1
    exact hp.1.one_lt
  · exact_mod_cast hp.1.Pos
#align padic_int.exists_pow_neg_lt PadicInt.exists_pow_neg_lt

/- warning: padic_int.exists_pow_neg_lt_rat -> PadicInt.exists_pow_neg_lt_rat is a dubious translation:
lean 3 declaration is
  forall (p : Nat) [hp : Fact (Nat.Prime p)] {ε : Rat}, (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) ε) -> (Exists.{1} Nat (fun (k : Nat) => LT.lt.{0} Rat Rat.hasLt (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (NormedRing.toRing.{0} Rat (NormedCommRing.toNormedRing.{0} Rat (NormedField.toNormedCommRing.{0} Rat Rat.normedField)))))))))) p) (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) k))) ε))
but is expected to have type
  forall (p : Nat) [hp : Fact (Nat.Prime p)] {ε : Rat}, (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) ε) -> (Exists.{1} Nat (fun (k : Nat) => LT.lt.{0} Rat Rat.instLTRat_1 (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p) (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int instNatCastInt k))) ε))
Case conversion may be inaccurate. Consider using '#align padic_int.exists_pow_neg_lt_rat PadicInt.exists_pow_neg_lt_ratₓ'. -/
theorem exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) : ∃ k : ℕ, ↑p ^ (-(k : ℤ)) < ε :=
  by
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (by exact_mod_cast hε)
  use k
  rw [show (p : ℝ) = (p : ℚ) by simp] at hk
  exact_mod_cast hk
#align padic_int.exists_pow_neg_lt_rat PadicInt.exists_pow_neg_lt_rat

variable {p}

/- warning: padic_int.norm_int_lt_one_iff_dvd -> PadicInt.norm_int_lt_one_iff_dvd is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (k : Int), Iff (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (PadicInt p hp) (HasLiftT.mk.{1, 1} Int (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Int (PadicInt p hp) (Int.castCoe.{0} (PadicInt p hp) (AddGroupWithOne.toHasIntCast.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))))))) k)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) k)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (k : Int), Iff (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) (Int.cast.{0} (PadicInt p hp) (Ring.toIntCast.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.instNormedCommRingPadicInt p hp)))) k)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) k)
Case conversion may be inaccurate. Consider using '#align padic_int.norm_int_lt_one_iff_dvd PadicInt.norm_int_lt_one_iff_dvdₓ'. -/
theorem norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ < 1 ↔ ↑p ∣ k by rwa [norm_int_cast_eq_padic_norm]
  padicNormE.norm_int_lt_one_iff_dvd k
#align padic_int.norm_int_lt_one_iff_dvd PadicInt.norm_int_lt_one_iff_dvd

/- warning: padic_int.norm_int_le_pow_iff_dvd -> PadicInt.norm_int_le_pow_iff_dvd is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {k : Int} {n : Nat}, Iff (LE.le.{0} Real Real.hasLe (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (PadicInt p hp) (HasLiftT.mk.{1, 1} Int (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Int (PadicInt p hp) (Int.castCoe.{0} (PadicInt p hp) (AddGroupWithOne.toHasIntCast.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))))))) k)) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) n) k)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {k : Int} {n : Nat}, Iff (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) (Int.cast.{0} (PadicInt p hp) (Ring.toIntCast.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.instNormedCommRingPadicInt p hp)))) k)) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int instNatCastInt n)))) (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)) k)
Case conversion may be inaccurate. Consider using '#align padic_int.norm_int_le_pow_iff_dvd PadicInt.norm_int_le_pow_iff_dvdₓ'. -/
theorem norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} : ‖(k : ℤ_[p])‖ ≤ p ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ ≤ p ^ (-n : ℤ) ↔ ↑(p ^ n) ∣ k by simpa [norm_int_cast_eq_padic_norm]
  padicNormE.norm_int_le_pow_iff_dvd _ _
#align padic_int.norm_int_le_pow_iff_dvd PadicInt.norm_int_le_pow_iff_dvd

/-! ### Valuation on `ℤ_[p]` -/


#print PadicInt.valuation /-
/-- `padic_int.valuation` lifts the `p`-adic valuation on `ℚ` to `ℤ_[p]`.  -/
def valuation (x : ℤ_[p]) :=
  Padic.valuation (x : ℚ_[p])
#align padic_int.valuation PadicInt.valuation
-/

/- warning: padic_int.norm_eq_pow_val -> PadicInt.norm_eq_pow_val is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {x : PadicInt p hp}, (Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (OfNat.mk.{0} (PadicInt p hp) 0 (Zero.zero.{0} (PadicInt p hp) (PadicInt.hasZero p hp))))) -> (Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) (Neg.neg.{0} Int Int.hasNeg (PadicInt.valuation p hp x))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {x : PadicInt p hp}, (Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (Zero.toOfNat0.{0} (PadicInt p hp) (PadicInt.instZeroPadicInt p hp)))) -> (Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) (Neg.neg.{0} Int Int.instNegInt (PadicInt.valuation p hp x))))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_eq_pow_val PadicInt.norm_eq_pow_valₓ'. -/
theorem norm_eq_pow_val {x : ℤ_[p]} (hx : x ≠ 0) : ‖x‖ = (p : ℝ) ^ (-x.Valuation) :=
  by
  convert Padic.norm_eq_pow_val _
  contrapose! hx
  exact Subtype.val_injective hx
#align padic_int.norm_eq_pow_val PadicInt.norm_eq_pow_val

/- warning: padic_int.valuation_zero -> PadicInt.valuation_zero is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Eq.{1} Int (PadicInt.valuation p hp (OfNat.ofNat.{0} (PadicInt p hp) 0 (OfNat.mk.{0} (PadicInt p hp) 0 (Zero.zero.{0} (PadicInt p hp) (PadicInt.hasZero p hp))))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Eq.{1} Int (PadicInt.valuation p hp (OfNat.ofNat.{0} (PadicInt p hp) 0 (Zero.toOfNat0.{0} (PadicInt p hp) (PadicInt.instZeroPadicInt p hp)))) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))
Case conversion may be inaccurate. Consider using '#align padic_int.valuation_zero PadicInt.valuation_zeroₓ'. -/
@[simp]
theorem valuation_zero : valuation (0 : ℤ_[p]) = 0 :=
  Padic.valuation_zero
#align padic_int.valuation_zero PadicInt.valuation_zero

/- warning: padic_int.valuation_one -> PadicInt.valuation_one is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Eq.{1} Int (PadicInt.valuation p hp (OfNat.ofNat.{0} (PadicInt p hp) 1 (OfNat.mk.{0} (PadicInt p hp) 1 (One.one.{0} (PadicInt p hp) (PadicInt.hasOne p hp))))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Eq.{1} Int (PadicInt.valuation p hp (OfNat.ofNat.{0} (PadicInt p hp) 1 (One.toOfNat1.{0} (PadicInt p hp) (PadicInt.instOnePadicInt p hp)))) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))
Case conversion may be inaccurate. Consider using '#align padic_int.valuation_one PadicInt.valuation_oneₓ'. -/
@[simp]
theorem valuation_one : valuation (1 : ℤ_[p]) = 0 :=
  Padic.valuation_one
#align padic_int.valuation_one PadicInt.valuation_one

/- warning: padic_int.valuation_p -> PadicInt.valuation_p is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Eq.{1} Int (PadicInt.valuation p hp ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p)) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Eq.{1} Int (PadicInt.valuation p hp (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p)) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))
Case conversion may be inaccurate. Consider using '#align padic_int.valuation_p PadicInt.valuation_pₓ'. -/
@[simp]
theorem valuation_p : valuation (p : ℤ_[p]) = 1 := by simp [Valuation]
#align padic_int.valuation_p PadicInt.valuation_p

#print PadicInt.valuation_nonneg /-
theorem valuation_nonneg (x : ℤ_[p]) : 0 ≤ x.Valuation :=
  by
  by_cases hx : x = 0
  · simp [hx]
  have h : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
  rw [← neg_nonpos, ← (zpow_strictMono h).le_iff_le]
  show (p : ℝ) ^ (-Valuation x) ≤ p ^ (0 : ℤ)
  rw [← norm_eq_pow_val hx]
  simpa using x.property
#align padic_int.valuation_nonneg PadicInt.valuation_nonneg
-/

/- warning: padic_int.valuation_p_pow_mul -> PadicInt.valuation_p_pow_mul is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (n : Nat) (c : PadicInt p hp), (Ne.{1} (PadicInt p hp) c (OfNat.ofNat.{0} (PadicInt p hp) 0 (OfNat.mk.{0} (PadicInt p hp) 0 (Zero.zero.{0} (PadicInt p hp) (PadicInt.hasZero p hp))))) -> (Eq.{1} Int (PadicInt.valuation p hp (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.hasMul p hp)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p) n) c)) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n) (PadicInt.valuation p hp c)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (n : Nat) (c : PadicInt p hp), (Ne.{1} (PadicInt p hp) c (OfNat.ofNat.{0} (PadicInt p hp) 0 (Zero.toOfNat0.{0} (PadicInt p hp) (PadicInt.instZeroPadicInt p hp)))) -> (Eq.{1} Int (PadicInt.valuation p hp (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.instMulPadicInt p hp)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p) n) c)) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (Nat.cast.{0} Int instNatCastInt n) (PadicInt.valuation p hp c)))
Case conversion may be inaccurate. Consider using '#align padic_int.valuation_p_pow_mul PadicInt.valuation_p_pow_mulₓ'. -/
@[simp]
theorem valuation_p_pow_mul (n : ℕ) (c : ℤ_[p]) (hc : c ≠ 0) :
    (↑p ^ n * c).Valuation = n + c.Valuation :=
  by
  have : ‖↑p ^ n * c‖ = ‖(p ^ n : ℤ_[p])‖ * ‖c‖ := norm_mul _ _
  have aux : ↑p ^ n * c ≠ 0 := by
    contrapose! hc; rw [mul_eq_zero] at hc; cases hc
    · refine' (hp.1.NeZero _).elim
      exact_mod_cast pow_eq_zero hc
    · exact hc
  rwa [norm_eq_pow_val aux, norm_p_pow, norm_eq_pow_val hc, ← zpow_add₀, ← neg_add, zpow_inj,
    neg_inj] at this
  · exact_mod_cast hp.1.Pos
  · exact_mod_cast hp.1.ne_one
  · exact_mod_cast hp.1.NeZero
#align padic_int.valuation_p_pow_mul PadicInt.valuation_p_pow_mul

section Units

/-! ### Units of `ℤ_[p]` -/


attribute [local reducible] PadicInt

/- warning: padic_int.mul_inv -> PadicInt.mul_inv is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z : PadicInt p hp}, (Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} (PadicInt p hp) (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.hasMul p hp)) z (PadicInt.inv p hp z)) (OfNat.ofNat.{0} (PadicInt p hp) 1 (OfNat.mk.{0} (PadicInt p hp) 1 (One.one.{0} (PadicInt p hp) (PadicInt.hasOne p hp)))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z : PadicInt p hp}, (Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} (PadicInt p hp) (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.instMulPadicInt p hp)) z (PadicInt.inv p hp z)) (OfNat.ofNat.{0} (PadicInt p hp) 1 (One.toOfNat1.{0} (PadicInt p hp) (PadicInt.instOnePadicInt p hp))))
Case conversion may be inaccurate. Consider using '#align padic_int.mul_inv PadicInt.mul_invₓ'. -/
theorem mul_inv : ∀ {z : ℤ_[p]}, ‖z‖ = 1 → z * z.inv = 1
  | ⟨k, _⟩, h =>
    by
    have hk : k ≠ 0 := fun h' => zero_ne_one' ℚ_[p] (by simpa [h'] using h)
    unfold PadicInt.inv
    rw [norm_eq_padic_norm] at h
    rw [dif_pos h]
    apply Subtype.ext_iff_val.2
    simp [mul_inv_cancel hk]
#align padic_int.mul_inv PadicInt.mul_inv

/- warning: padic_int.inv_mul -> PadicInt.inv_mul is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z : PadicInt p hp}, (Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} (PadicInt p hp) (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.hasMul p hp)) (PadicInt.inv p hp z) z) (OfNat.ofNat.{0} (PadicInt p hp) 1 (OfNat.mk.{0} (PadicInt p hp) 1 (One.one.{0} (PadicInt p hp) (PadicInt.hasOne p hp)))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z : PadicInt p hp}, (Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} (PadicInt p hp) (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.instMulPadicInt p hp)) (PadicInt.inv p hp z) z) (OfNat.ofNat.{0} (PadicInt p hp) 1 (One.toOfNat1.{0} (PadicInt p hp) (PadicInt.instOnePadicInt p hp))))
Case conversion may be inaccurate. Consider using '#align padic_int.inv_mul PadicInt.inv_mulₓ'. -/
theorem inv_mul {z : ℤ_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1 := by rw [mul_comm, mul_inv hz]
#align padic_int.inv_mul PadicInt.inv_mul

/- warning: padic_int.is_unit_iff -> PadicInt.isUnit_iff is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z : PadicInt p hp}, Iff (IsUnit.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))) z) (Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z : PadicInt p hp}, Iff (IsUnit.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))) z) (Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align padic_int.is_unit_iff PadicInt.isUnit_iffₓ'. -/
theorem isUnit_iff {z : ℤ_[p]} : IsUnit z ↔ ‖z‖ = 1 :=
  ⟨fun h => by
    rcases isUnit_iff_dvd_one.1 h with ⟨w, eq⟩
    refine' le_antisymm (norm_le_one _) _
    have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)
    rwa [mul_one, ← norm_mul, ← Eq, norm_one] at this, fun h =>
    ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩
#align padic_int.is_unit_iff PadicInt.isUnit_iff

/- warning: padic_int.norm_lt_one_add -> PadicInt.norm_lt_one_add is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z1 : PadicInt p hp} {z2 : PadicInt p hp}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) z1) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) z2) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) (HAdd.hAdd.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHAdd.{0} (PadicInt p hp) (PadicInt.hasAdd p hp)) z1 z2)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z1 : PadicInt p hp} {z2 : PadicInt p hp}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) z1) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) z2) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) (HAdd.hAdd.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHAdd.{0} (PadicInt p hp) (PadicInt.instAddPadicInt p hp)) z1 z2)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_lt_one_add PadicInt.norm_lt_one_addₓ'. -/
theorem norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1) : ‖z1 + z2‖ < 1 :=
  lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)
#align padic_int.norm_lt_one_add PadicInt.norm_lt_one_add

/- warning: padic_int.norm_lt_one_mul -> PadicInt.norm_lt_one_mul is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z1 : PadicInt p hp} {z2 : PadicInt p hp}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) z2) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.hasMul p hp)) z1 z2)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z1 : PadicInt p hp} {z2 : PadicInt p hp}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) z2) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.instMulPadicInt p hp)) z1 z2)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_lt_one_mul PadicInt.norm_lt_one_mulₓ'. -/
theorem norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ‖z2‖ < 1) : ‖z1 * z2‖ < 1 :=
  calc
    ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2
    
#align padic_int.norm_lt_one_mul PadicInt.norm_lt_one_mul

/- warning: padic_int.mem_nonunits -> PadicInt.mem_nonunits is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z : PadicInt p hp}, Iff (Membership.Mem.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.hasMem.{0} (PadicInt p hp)) z (nonunits.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))) (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {z : PadicInt p hp}, Iff (Membership.mem.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.instMembershipSet.{0} (PadicInt p hp)) z (nonunits.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align padic_int.mem_nonunits PadicInt.mem_nonunitsₓ'. -/
@[simp]
theorem mem_nonunits {z : ℤ_[p]} : z ∈ nonunits ℤ_[p] ↔ ‖z‖ < 1 := by
  rw [lt_iff_le_and_ne] <;> simp [norm_le_one z, nonunits, is_unit_iff]
#align padic_int.mem_nonunits PadicInt.mem_nonunits

/- warning: padic_int.mk_units -> PadicInt.mkUnits is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {u : Padic p hp}, (Eq.{1} Real (Norm.norm.{0} (Padic p hp) (Padic.hasNorm p hp) u) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {u : Padic p hp}, (Eq.{1} Real (Norm.norm.{0} (Padic p hp) (Padic.instNormPadic p hp) u) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Units.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))
Case conversion may be inaccurate. Consider using '#align padic_int.mk_units PadicInt.mkUnitsₓ'. -/
/-- A `p`-adic number `u` with `‖u‖ = 1` is a unit of `ℤ_[p]`. -/
def mkUnits {u : ℚ_[p]} (h : ‖u‖ = 1) : ℤ_[p]ˣ :=
  let z : ℤ_[p] := ⟨u, le_of_eq h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩
#align padic_int.mk_units PadicInt.mkUnits

/- warning: padic_int.mk_units_eq -> PadicInt.mkUnits_eq is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {u : Padic p hp} (h : Eq.{1} Real (Norm.norm.{0} (Padic p hp) (Padic.hasNorm p hp) u) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))), Eq.{1} (Padic p hp) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p hp) (Padic p hp) (HasLiftT.mk.{1, 1} (PadicInt p hp) (Padic p hp) (CoeTCₓ.coe.{1, 1} (PadicInt p hp) (Padic p hp) (coeBase.{1, 1} (PadicInt p hp) (Padic p hp) (PadicInt.Padic.hasCoe p hp)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (HasLiftT.mk.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (CoeTCₓ.coe.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (coeBase.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (Units.hasCoe.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))) (PadicInt.mkUnits p hp u h))) u
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {u : Padic p hp} (h : Eq.{1} Real (Norm.norm.{0} (Padic p hp) (Padic.instNormPadic p hp) u) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))), Eq.{1} (Padic p hp) (Subtype.val.{1} (Padic p hp) (fun (x : Padic p hp) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p hp) (Padic.instNormPadic p hp) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Units.val.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))) (PadicInt.mkUnits p hp u h))) u
Case conversion may be inaccurate. Consider using '#align padic_int.mk_units_eq PadicInt.mkUnits_eqₓ'. -/
@[simp]
theorem mkUnits_eq {u : ℚ_[p]} (h : ‖u‖ = 1) : ((mkUnits h : ℤ_[p]) : ℚ_[p]) = u :=
  rfl
#align padic_int.mk_units_eq PadicInt.mkUnits_eq

/- warning: padic_int.norm_units -> PadicInt.norm_units is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (u : Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))), Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (HasLiftT.mk.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (CoeTCₓ.coe.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (coeBase.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (Units.hasCoe.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))) u)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (u : Units.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))))), Eq.{1} Real (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) (Units.val.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))) u)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_units PadicInt.norm_unitsₓ'. -/
@[simp]
theorem norm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖ = 1 :=
  isUnit_iff.mp <| by simp
#align padic_int.norm_units PadicInt.norm_units

/- warning: padic_int.unit_coeff -> PadicInt.unitCoeff is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {x : PadicInt p hp}, (Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (OfNat.mk.{0} (PadicInt p hp) 0 (Zero.zero.{0} (PadicInt p hp) (PadicInt.hasZero p hp))))) -> (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {x : PadicInt p hp}, (Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (Zero.toOfNat0.{0} (PadicInt p hp) (PadicInt.instZeroPadicInt p hp)))) -> (Units.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))
Case conversion may be inaccurate. Consider using '#align padic_int.unit_coeff PadicInt.unitCoeffₓ'. -/
/-- `unit_coeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unit_coeff_spec`. -/
def unitCoeff {x : ℤ_[p]} (hx : x ≠ 0) : ℤ_[p]ˣ :=
  let u : ℚ_[p] := x * p ^ (-x.Valuation)
  have hu : ‖u‖ = 1 := by
    simp [hx, Nat.zpow_ne_zero_of_pos (by exact_mod_cast hp.1.Pos) x.valuation, norm_eq_pow_val,
      zpow_neg, inv_mul_cancel]
  mkUnits hu
#align padic_int.unit_coeff PadicInt.unitCoeff

/- warning: padic_int.unit_coeff_coe -> PadicInt.unitCoeff_coe is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {x : PadicInt p hp} (hx : Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (OfNat.mk.{0} (PadicInt p hp) 0 (Zero.zero.{0} (PadicInt p hp) (PadicInt.hasZero p hp))))), Eq.{1} (Padic p hp) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (Padic p hp) (HasLiftT.mk.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (Padic p hp) (CoeTCₓ.coe.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (Padic p hp) (coeTrans.{1, 1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (Padic p hp) (coeBase.{1, 1} (PadicInt p hp) (Padic p hp) (PadicInt.Padic.hasCoe p hp)) (Units.hasCoe.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))) (PadicInt.unitCoeff p hp x hx)) (HMul.hMul.{0, 0, 0} (Padic p hp) (Padic p hp) (Padic p hp) (instHMul.{0} (Padic p hp) (Padic.hasMul p hp)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p hp) (Padic p hp) (HasLiftT.mk.{1, 1} (PadicInt p hp) (Padic p hp) (CoeTCₓ.coe.{1, 1} (PadicInt p hp) (Padic p hp) (coeBase.{1, 1} (PadicInt p hp) (Padic p hp) (PadicInt.Padic.hasCoe p hp)))) x) (HPow.hPow.{0, 0, 0} (Padic p hp) Int (Padic p hp) (instHPow.{0, 0} (Padic p hp) Int (DivInvMonoid.Pow.{0} (Padic p hp) (DivisionRing.toDivInvMonoid.{0} (Padic p hp) (NormedDivisionRing.toDivisionRing.{0} (Padic p hp) (NormedField.toNormedDivisionRing.{0} (Padic p hp) (Padic.normedField p hp)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Padic p hp) (HasLiftT.mk.{1, 1} Nat (Padic p hp) (CoeTCₓ.coe.{1, 1} Nat (Padic p hp) (Nat.castCoe.{0} (Padic p hp) (AddMonoidWithOne.toNatCast.{0} (Padic p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (Padic p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (Padic p hp) (Ring.toAddCommGroupWithOne.{0} (Padic p hp) (Padic.ring p hp)))))))) p) (Neg.neg.{0} Int Int.hasNeg (PadicInt.valuation p hp x))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {x : PadicInt p hp} (hx : Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (Zero.toOfNat0.{0} (PadicInt p hp) (PadicInt.instZeroPadicInt p hp)))), Eq.{1} (Padic p hp) (Subtype.val.{1} (Padic p hp) (fun (x : Padic p hp) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p hp) (Padic.instNormPadic p hp) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Units.val.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))) (PadicInt.unitCoeff p hp x hx))) (HMul.hMul.{0, 0, 0} (Padic p hp) (Padic p hp) (Padic p hp) (instHMul.{0} (Padic p hp) (Padic.instMulPadic p hp)) (Subtype.val.{1} (Padic p hp) (fun (x : Padic p hp) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p hp) (Padic.instNormPadic p hp) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x) (HPow.hPow.{0, 0, 0} (Padic p hp) Int (Padic p hp) (instHPow.{0, 0} (Padic p hp) Int (DivInvMonoid.Pow.{0} (Padic p hp) (DivisionRing.toDivInvMonoid.{0} (Padic p hp) (NormedDivisionRing.toDivisionRing.{0} (Padic p hp) (NormedField.toNormedDivisionRing.{0} (Padic p hp) (Padic.normedField p hp)))))) (Nat.cast.{0} (Padic p hp) (Semiring.toNatCast.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp))))) p) (Neg.neg.{0} Int Int.instNegInt (PadicInt.valuation p hp x))))
Case conversion may be inaccurate. Consider using '#align padic_int.unit_coeff_coe PadicInt.unitCoeff_coeₓ'. -/
@[simp]
theorem unitCoeff_coe {x : ℤ_[p]} (hx : x ≠ 0) : (unitCoeff hx : ℚ_[p]) = x * p ^ (-x.Valuation) :=
  rfl
#align padic_int.unit_coeff_coe PadicInt.unitCoeff_coe

/- warning: padic_int.unit_coeff_spec -> PadicInt.unitCoeff_spec is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {x : PadicInt p hp} (hx : Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (OfNat.mk.{0} (PadicInt p hp) 0 (Zero.zero.{0} (PadicInt p hp) (PadicInt.hasZero p hp))))), Eq.{1} (PadicInt p hp) x (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.hasMul p hp)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (HasLiftT.mk.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (CoeTCₓ.coe.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (coeBase.{1, 1} (Units.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (Units.hasCoe.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))) (PadicInt.unitCoeff p hp x hx)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p) (Int.natAbs (PadicInt.valuation p hp x))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {x : PadicInt p hp} (hx : Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (Zero.toOfNat0.{0} (PadicInt p hp) (PadicInt.instZeroPadicInt p hp)))), Eq.{1} (PadicInt p hp) x (HMul.hMul.{0, 0, 0} (PadicInt p hp) (PadicInt p hp) (PadicInt p hp) (instHMul.{0} (PadicInt p hp) (PadicInt.instMulPadicInt p hp)) (Units.val.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))) (PadicInt.unitCoeff p hp x hx)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p) (Int.natAbs (PadicInt.valuation p hp x))))
Case conversion may be inaccurate. Consider using '#align padic_int.unit_coeff_spec PadicInt.unitCoeff_specₓ'. -/
theorem unitCoeff_spec {x : ℤ_[p]} (hx : x ≠ 0) :
    x = (unitCoeff hx : ℤ_[p]) * p ^ Int.natAbs (valuation x) :=
  by
  apply Subtype.coe_injective
  push_cast
  have repr : (x : ℚ_[p]) = unit_coeff hx * p ^ x.valuation :=
    by
    rw [unit_coeff_coe, mul_assoc, ← zpow_add₀]
    · simp
    · exact_mod_cast hp.1.NeZero
  convert repr using 2
  rw [← zpow_ofNat, Int.natAbs_of_nonneg (valuation_nonneg x)]
#align padic_int.unit_coeff_spec PadicInt.unitCoeff_spec

end Units

section NormLeIff

/-! ### Various characterizations of open unit balls -/


/- warning: padic_int.norm_le_pow_iff_le_valuation -> PadicInt.norm_le_pow_iff_le_valuation is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp), (Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (OfNat.mk.{0} (PadicInt p hp) 0 (Zero.zero.{0} (PadicInt p hp) (PadicInt.hasZero p hp))))) -> (forall (n : Nat), Iff (LE.le.{0} Real Real.hasLe (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (LE.le.{0} Int Int.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n) (PadicInt.valuation p hp x)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp), (Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (Zero.toOfNat0.{0} (PadicInt p hp) (PadicInt.instZeroPadicInt p hp)))) -> (forall (n : Nat), Iff (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int instNatCastInt n)))) (LE.le.{0} Int Int.instLEInt (Nat.cast.{0} Int instNatCastInt n) (PadicInt.valuation p hp x)))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_le_pow_iff_le_valuation PadicInt.norm_le_pow_iff_le_valuationₓ'. -/
theorem norm_le_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    ‖x‖ ≤ p ^ (-n : ℤ) ↔ ↑n ≤ x.Valuation :=
  by
  rw [norm_eq_pow_val hx]
  lift x.valuation to ℕ using x.valuation_nonneg with k hk
  simp only [Int.ofNat_le, zpow_neg, zpow_ofNat]
  have aux : ∀ n : ℕ, 0 < (p ^ n : ℝ) := by apply pow_pos; exact_mod_cast hp.1.Pos
  rw [inv_le_inv (aux _) (aux _)]
  have : p ^ n ≤ p ^ k ↔ n ≤ k := (pow_strictMono_right hp.1.one_lt).le_iff_le
  rw [← this]
  norm_cast
#align padic_int.norm_le_pow_iff_le_valuation PadicInt.norm_le_pow_iff_le_valuation

/- warning: padic_int.mem_span_pow_iff_le_valuation -> PadicInt.mem_span_pow_iff_le_valuation is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp), (Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (OfNat.mk.{0} (PadicInt p hp) 0 (Zero.zero.{0} (PadicInt p hp) (PadicInt.hasZero p hp))))) -> (forall (n : Nat), Iff (Membership.Mem.{0, 0} (PadicInt p hp) (Ideal.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (SetLike.hasMem.{0, 0} (Ideal.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (Submodule.setLike.{0, 0} (PadicInt p hp) (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (PadicInt p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (PadicInt p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))))) (Semiring.toModule.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))))) x (Ideal.span.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))) (Singleton.singleton.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.hasSingleton.{0} (PadicInt p hp)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p) n)))) (LE.le.{0} Int Int.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n) (PadicInt.valuation p hp x)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp), (Ne.{1} (PadicInt p hp) x (OfNat.ofNat.{0} (PadicInt p hp) 0 (Zero.toOfNat0.{0} (PadicInt p hp) (PadicInt.instZeroPadicInt p hp)))) -> (forall (n : Nat), Iff (Membership.mem.{0, 0} (PadicInt p hp) (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (SetLike.instMembership.{0, 0} (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (PadicInt p hp) (Submodule.setLike.{0, 0} (PadicInt p hp) (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (PadicInt p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (PadicInt p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))))) (Semiring.toModule.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))))) x (Ideal.span.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))) (Singleton.singleton.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.instSingletonSet.{0} (PadicInt p hp)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p) n)))) (LE.le.{0} Int Int.instLEInt (Nat.cast.{0} Int instNatCastInt n) (PadicInt.valuation p hp x)))
Case conversion may be inaccurate. Consider using '#align padic_int.mem_span_pow_iff_le_valuation PadicInt.mem_span_pow_iff_le_valuationₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([2]) } -/
theorem mem_span_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    x ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p]) ↔ ↑n ≤ x.Valuation :=
  by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    suffices c ≠ 0 by rw [valuation_p_pow_mul _ _ this, le_add_iff_nonneg_right];
      apply valuation_nonneg
    contrapose! hx; rw [hx, MulZeroClass.mul_zero]
  · rw [unit_coeff_spec hx]
    lift x.valuation to ℕ using x.valuation_nonneg with k hk
    simp only [Int.natAbs_ofNat, Units.isUnit, IsUnit.dvd_mul_left, Int.ofNat_le]
    intro H
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le H
    simp only [pow_add, dvd_mul_right]
#align padic_int.mem_span_pow_iff_le_valuation PadicInt.mem_span_pow_iff_le_valuation

/- warning: padic_int.norm_le_pow_iff_mem_span_pow -> PadicInt.norm_le_pow_iff_mem_span_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp) (n : Nat), Iff (LE.le.{0} Real Real.hasLe (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (Membership.Mem.{0, 0} (PadicInt p hp) (Ideal.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (SetLike.hasMem.{0, 0} (Ideal.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (PadicInt p hp) (Submodule.setLike.{0, 0} (PadicInt p hp) (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (PadicInt p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (PadicInt p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))))) (Semiring.toModule.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))))) x (Ideal.span.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))) (Singleton.singleton.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.hasSingleton.{0} (PadicInt p hp)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p) n))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp) (n : Nat), Iff (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int instNatCastInt n)))) (Membership.mem.{0, 0} (PadicInt p hp) (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (SetLike.instMembership.{0, 0} (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (PadicInt p hp) (Submodule.setLike.{0, 0} (PadicInt p hp) (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (PadicInt p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (PadicInt p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))))) (Semiring.toModule.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))))) x (Ideal.span.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))) (Singleton.singleton.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.instSingletonSet.{0} (PadicInt p hp)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p) n))))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_le_pow_iff_mem_span_pow PadicInt.norm_le_pow_iff_mem_span_powₓ'. -/
theorem norm_le_pow_iff_mem_span_pow (x : ℤ_[p]) (n : ℕ) :
    ‖x‖ ≤ p ^ (-n : ℤ) ↔ x ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p]) :=
  by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, zpow_neg, zpow_ofNat, inv_nonneg, iff_true_iff, Submodule.zero_mem]
    exact_mod_cast Nat.zero_le _
  rw [norm_le_pow_iff_le_valuation x hx, mem_span_pow_iff_le_valuation x hx]
#align padic_int.norm_le_pow_iff_mem_span_pow PadicInt.norm_le_pow_iff_mem_span_pow

/- warning: padic_int.norm_le_pow_iff_norm_lt_pow_add_one -> PadicInt.norm_le_pow_iff_norm_lt_pow_add_one is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp) (n : Int), Iff (LE.le.{0} Real Real.hasLe (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) n)) (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) n (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp) (n : Int), Iff (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) n)) (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) n (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_le_pow_iff_norm_lt_pow_add_one PadicInt.norm_le_pow_iff_norm_lt_pow_add_oneₓ'. -/
theorem norm_le_pow_iff_norm_lt_pow_add_one (x : ℤ_[p]) (n : ℤ) : ‖x‖ ≤ p ^ n ↔ ‖x‖ < p ^ (n + 1) :=
  by rw [norm_def]; exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _
#align padic_int.norm_le_pow_iff_norm_lt_pow_add_one PadicInt.norm_le_pow_iff_norm_lt_pow_add_one

/- warning: padic_int.norm_lt_pow_iff_norm_le_pow_sub_one -> PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp) (n : Int), Iff (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) n)) (LE.le.{0} Real Real.hasLe (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) n (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp) (n : Int), Iff (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) n)) (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) x) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (Nat.cast.{0} Real Real.natCast p) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) n (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))))
Case conversion may be inaccurate. Consider using '#align padic_int.norm_lt_pow_iff_norm_le_pow_sub_one PadicInt.norm_lt_pow_iff_norm_le_pow_sub_oneₓ'. -/
theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℤ_[p]) (n : ℤ) : ‖x‖ < p ^ n ↔ ‖x‖ ≤ p ^ (n - 1) :=
  by rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]
#align padic_int.norm_lt_pow_iff_norm_le_pow_sub_one PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one

/- warning: padic_int.norm_lt_one_iff_dvd -> PadicInt.norm_lt_one_iff_dvd is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp), Iff (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} (PadicInt p hp) (PadicInt.hasNorm p hp) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Dvd.Dvd.{0} (PadicInt p hp) (semigroupDvd.{0} (PadicInt p hp) (SemigroupWithZero.toSemigroup.{0} (PadicInt p hp) (NonUnitalSemiring.toSemigroupWithZero.{0} (PadicInt p hp) (NonUnitalRing.toNonUnitalSemiring.{0} (PadicInt p hp) (NonUnitalNormedRing.toNonUnitalRing.{0} (PadicInt p hp) (NormedRing.toNonUnitalNormedRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p) x)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp), Iff (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} (PadicInt p hp) (PadicInt.instNormPadicInt p hp) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Dvd.dvd.{0} (PadicInt p hp) (semigroupDvd.{0} (PadicInt p hp) (SemigroupWithZero.toSemigroup.{0} (PadicInt p hp) (NonUnitalSemiring.toSemigroupWithZero.{0} (PadicInt p hp) (NonUnitalCommSemiring.toNonUnitalSemiring.{0} (PadicInt p hp) (NonUnitalCommRing.toNonUnitalCommSemiring.{0} (PadicInt p hp) (CommRing.toNonUnitalCommRing.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p) x)
Case conversion may be inaccurate. Consider using '#align padic_int.norm_lt_one_iff_dvd PadicInt.norm_lt_one_iff_dvdₓ'. -/
theorem norm_lt_one_iff_dvd (x : ℤ_[p]) : ‖x‖ < 1 ↔ ↑p ∣ x :=
  by
  have := norm_le_pow_iff_mem_span_pow x 1
  rw [Ideal.mem_span_singleton, pow_one] at this
  rw [← this, norm_le_pow_iff_norm_lt_pow_add_one]
  simp only [zpow_zero, Int.ofNat_zero, Int.ofNat_succ, add_left_neg, zero_add]
#align padic_int.norm_lt_one_iff_dvd PadicInt.norm_lt_one_iff_dvd

/- warning: padic_int.pow_p_dvd_int_iff -> PadicInt.pow_p_dvd_int_iff is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (n : Nat) (a : Int), Iff (Dvd.Dvd.{0} (PadicInt p hp) (semigroupDvd.{0} (PadicInt p hp) (SemigroupWithZero.toSemigroup.{0} (PadicInt p hp) (NonUnitalSemiring.toSemigroupWithZero.{0} (PadicInt p hp) (NonUnitalRing.toNonUnitalSemiring.{0} (PadicInt p hp) (NonUnitalNormedRing.toNonUnitalRing.{0} (PadicInt p hp) (NormedRing.toNonUnitalNormedRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (PadicInt p hp) (HasLiftT.mk.{1, 1} Int (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Int (PadicInt p hp) (Int.castCoe.{0} (PadicInt p hp) (AddGroupWithOne.toHasIntCast.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))))))) a)) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) n) a)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (n : Nat) (a : Int), Iff (Dvd.dvd.{0} (PadicInt p hp) (semigroupDvd.{0} (PadicInt p hp) (SemigroupWithZero.toSemigroup.{0} (PadicInt p hp) (NonUnitalSemiring.toSemigroupWithZero.{0} (PadicInt p hp) (NonUnitalCommSemiring.toNonUnitalSemiring.{0} (PadicInt p hp) (NonUnitalCommRing.toNonUnitalCommSemiring.{0} (PadicInt p hp) (CommRing.toNonUnitalCommRing.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p) n) (Int.cast.{0} (PadicInt p hp) (Ring.toIntCast.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.instNormedCommRingPadicInt p hp)))) a)) (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)) a)
Case conversion may be inaccurate. Consider using '#align padic_int.pow_p_dvd_int_iff PadicInt.pow_p_dvd_int_iffₓ'. -/
@[simp]
theorem pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p ^ n : ℤ_[p]) ∣ a ↔ ↑p ^ n ∣ a := by
  rw [← norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
#align padic_int.pow_p_dvd_int_iff PadicInt.pow_p_dvd_int_iff

end NormLeIff

section Dvr

/-! ### Discrete valuation ring -/


instance : LocalRing ℤ_[p] :=
  LocalRing.of_nonunits_add <| by simp only [mem_nonunits] <;> exact fun x y => norm_lt_one_add

/- warning: padic_int.p_nonnunit -> PadicInt.p_nonnunit is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Membership.Mem.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.hasMem.{0} (PadicInt p hp)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p) (nonunits.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Membership.mem.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.instMembershipSet.{0} (PadicInt p hp)) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p) (nonunits.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))
Case conversion may be inaccurate. Consider using '#align padic_int.p_nonnunit PadicInt.p_nonnunitₓ'. -/
theorem p_nonnunit : (p : ℤ_[p]) ∈ nonunits ℤ_[p] :=
  by
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one <| by exact_mod_cast hp.1.one_lt
  simp [this]
#align padic_int.p_nonnunit PadicInt.p_nonnunit

/- warning: padic_int.maximal_ideal_eq_span_p -> PadicInt.maximalIdeal_eq_span_p is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Eq.{1} (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp)))) (LocalRing.maximalIdeal.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp)) (PadicInt.localRing p hp)) (Ideal.span.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp))) (Singleton.singleton.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.hasSingleton.{0} (PadicInt p hp)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Eq.{1} (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (LocalRing.maximalIdeal.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)) (PadicInt.instLocalRingPadicIntToSemiringToCommSemiringInstCommRingPadicInt p hp)) (Ideal.span.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))) (Singleton.singleton.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.instSingletonSet.{0} (PadicInt p hp)) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p)))
Case conversion may be inaccurate. Consider using '#align padic_int.maximal_ideal_eq_span_p PadicInt.maximalIdeal_eq_span_pₓ'. -/
theorem maximalIdeal_eq_span_p : maximalIdeal ℤ_[p] = Ideal.span {p} :=
  by
  apply le_antisymm
  · intro x hx
    simp only [LocalRing.mem_maximalIdeal, mem_nonunits] at hx
    rwa [Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact p_nonnunit
#align padic_int.maximal_ideal_eq_span_p PadicInt.maximalIdeal_eq_span_p

/- warning: padic_int.prime_p -> PadicInt.prime_p is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Prime.{0} (PadicInt p hp) (CommSemiring.toCommMonoidWithZero.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Prime.{0} (PadicInt p hp) (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} (PadicInt p hp) (IsDomain.toCancelCommMonoidWithZero.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)) (PadicInt.instIsDomainPadicIntToSemiringToCommSemiringInstCommRingPadicInt p hp))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p)
Case conversion may be inaccurate. Consider using '#align padic_int.prime_p PadicInt.prime_pₓ'. -/
theorem prime_p : Prime (p : ℤ_[p]) :=
  by
  rw [← Ideal.span_singleton_prime, ← maximal_ideal_eq_span_p]
  · infer_instance
  · exact_mod_cast hp.1.NeZero
#align padic_int.prime_p PadicInt.prime_p

/- warning: padic_int.irreducible_p -> PadicInt.irreducible_p is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Irreducible.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Irreducible.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p)
Case conversion may be inaccurate. Consider using '#align padic_int.irreducible_p PadicInt.irreducible_pₓ'. -/
theorem irreducible_p : Irreducible (p : ℤ_[p]) :=
  Prime.irreducible prime_p
#align padic_int.irreducible_p PadicInt.irreducible_p

instance : DiscreteValuationRing ℤ_[p] :=
  DiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, irreducible_p, fun x hx =>
      ⟨x.Valuation.natAbs, unitCoeff hx, by rw [mul_comm, ← unit_coeff_spec hx]⟩⟩

/- warning: padic_int.ideal_eq_span_pow_p -> PadicInt.ideal_eq_span_pow_p is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {s : Ideal.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))}, (Ne.{1} (Ideal.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) s (Bot.bot.{0} (Ideal.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) (Submodule.hasBot.{0, 0} (PadicInt p hp) (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (PadicInt p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (PadicInt p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))))) (Semiring.toModule.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))) -> (Exists.{1} Nat (fun (n : Nat) => Eq.{1} (Ideal.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp))))) s (Ideal.span.{0} (PadicInt p hp) (Ring.toSemiring.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))) (Singleton.singleton.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.hasSingleton.{0} (PadicInt p hp)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (Ring.toMonoid.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (PadicInt p hp) (HasLiftT.mk.{1, 1} Nat (PadicInt p hp) (CoeTCₓ.coe.{1, 1} Nat (PadicInt p hp) (Nat.castCoe.{0} (PadicInt p hp) (AddMonoidWithOne.toNatCast.{0} (PadicInt p hp) (AddGroupWithOne.toAddMonoidWithOne.{0} (PadicInt p hp) (AddCommGroupWithOne.toAddGroupWithOne.{0} (PadicInt p hp) (Ring.toAddCommGroupWithOne.{0} (PadicInt p hp) (NormedRing.toRing.{0} (PadicInt p hp) (NormedCommRing.toNormedRing.{0} (PadicInt p hp) (PadicInt.normedCommRing p hp)))))))))) p) n)))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {s : Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))}, (Ne.{1} (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) s (Bot.bot.{0} (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (Submodule.instBotSubmodule.{0, 0} (PadicInt p hp) (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (PadicInt p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (PadicInt p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))))) (Semiring.toModule.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) -> (Exists.{1} Nat (fun (n : Nat) => Eq.{1} (Ideal.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) s (Ideal.span.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))) (Singleton.singleton.{0, 0} (PadicInt p hp) (Set.{0} (PadicInt p hp)) (Set.instSingletonSet.{0} (PadicInt p hp)) (HPow.hPow.{0, 0, 0} (PadicInt p hp) Nat (PadicInt p hp) (instHPow.{0, 0} (PadicInt p hp) Nat (Monoid.Pow.{0} (PadicInt p hp) (MonoidWithZero.toMonoid.{0} (PadicInt p hp) (Semiring.toMonoidWithZero.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))))) (Nat.cast.{0} (PadicInt p hp) (Semiring.toNatCast.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) p) n)))))
Case conversion may be inaccurate. Consider using '#align padic_int.ideal_eq_span_pow_p PadicInt.ideal_eq_span_pow_pₓ'. -/
theorem ideal_eq_span_pow_p {s : Ideal ℤ_[p]} (hs : s ≠ ⊥) : ∃ n : ℕ, s = Ideal.span {p ^ n} :=
  DiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p
#align padic_int.ideal_eq_span_pow_p PadicInt.ideal_eq_span_pow_p

open CauSeq

instance : IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]
    where prec' x hx :=
    by
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, maximal_ideal_eq_span_p,
      Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx⊢
    let x' : CauSeq ℤ_[p] norm := ⟨x, _⟩; swap
    · intro ε hε; obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
      refine' ⟨m, fun n hn => lt_of_le_of_lt _ hm⟩; rw [← neg_sub, norm_neg]; exact hx hn
    · refine' ⟨x'.lim, fun n => _⟩
      have : (0 : ℝ) < p ^ (-n : ℤ) := by apply zpow_pos_of_pos; exact_mod_cast hp.1.Pos
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this
      by_cases hin : i ≤ n
      · exact (hi i le_rfl n hin).le
      · push_neg  at hin; specialize hi i le_rfl i le_rfl; specialize hx hin.le
        have := nonarchimedean (x n - x i) (x i - x'.lim)
        rw [sub_add_sub_cancel] at this
        refine' this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)

end Dvr

section FractionRing

/- warning: padic_int.algebra -> PadicInt.algebra is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Algebra.{0, 0} (PadicInt p hp) (Padic p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp)) (Ring.toSemiring.{0} (Padic p hp) (Padic.ring p hp))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], Algebra.{0, 0} (PadicInt p hp) (Padic p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp))))
Case conversion may be inaccurate. Consider using '#align padic_int.algebra PadicInt.algebraₓ'. -/
instance algebra : Algebra ℤ_[p] ℚ_[p] :=
  Algebra.ofSubring (subring p)
#align padic_int.algebra PadicInt.algebra

/- warning: padic_int.algebra_map_apply -> PadicInt.algebraMap_apply is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp), Eq.{1} (Padic p hp) (coeFn.{1, 1} (RingHom.{0, 0} (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (Ring.toSemiring.{0} (Padic p hp) (Padic.ring p hp)))) (fun (_x : RingHom.{0, 0} (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (Ring.toSemiring.{0} (Padic p hp) (Padic.ring p hp)))) => (PadicInt p hp) -> (Padic p hp)) (RingHom.hasCoeToFun.{0, 0} (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (Ring.toSemiring.{0} (Padic p hp) (Padic.ring p hp)))) (algebraMap.{0, 0} (PadicInt p hp) (Padic p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.commRing p hp)) (Ring.toSemiring.{0} (Padic p hp) (Padic.ring p hp)) (PadicInt.algebra p hp)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (PadicInt p hp) (Padic p hp) (HasLiftT.mk.{1, 1} (PadicInt p hp) (Padic p hp) (CoeTCₓ.coe.{1, 1} (PadicInt p hp) (Padic p hp) (coeBase.{1, 1} (PadicInt p hp) (Padic p hp) (PadicInt.Padic.hasCoe p hp)))) x)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (x : PadicInt p hp), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : PadicInt p hp) => Padic p hp) x) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp)))))) (PadicInt p hp) (fun (_x : PadicInt p hp) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : PadicInt p hp) => Padic p hp) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp)))))) (PadicInt p hp) (Padic p hp) (NonUnitalNonAssocSemiring.toMul.{0} (PadicInt p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (PadicInt p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))))) (NonUnitalNonAssocSemiring.toMul.{0} (Padic p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Padic p hp) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp))))))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp)))))) (PadicInt p hp) (Padic p hp) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (PadicInt p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Padic p hp) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp)))))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp)))))) (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp))))) (RingHom.instRingHomClassRingHom.{0, 0} (PadicInt p hp) (Padic p hp) (Semiring.toNonAssocSemiring.{0} (PadicInt p hp) (CommSemiring.toSemiring.{0} (PadicInt p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)))) (Semiring.toNonAssocSemiring.{0} (Padic p hp) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp))))))))) (algebraMap.{0, 0} (PadicInt p hp) (Padic p hp) (CommRing.toCommSemiring.{0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp)) (DivisionSemiring.toSemiring.{0} (Padic p hp) (Semifield.toDivisionSemiring.{0} (Padic p hp) (Field.toSemifield.{0} (Padic p hp) (Padic.field p hp)))) (PadicInt.algebra p hp)) x) (Subtype.val.{1} (Padic p hp) (fun (x : Padic p hp) => LE.le.{0} Real Real.instLEReal (Norm.norm.{0} (Padic p hp) (Padic.instNormPadic p hp) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x)
Case conversion may be inaccurate. Consider using '#align padic_int.algebra_map_apply PadicInt.algebraMap_applyₓ'. -/
@[simp]
theorem algebraMap_apply (x : ℤ_[p]) : algebraMap ℤ_[p] ℚ_[p] x = x :=
  rfl
#align padic_int.algebra_map_apply PadicInt.algebraMap_apply

/- warning: padic_int.is_fraction_ring -> PadicInt.isFractionRing is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)], IsFractionRing.{0, 0} (PadicInt p hp) (PadicInt.commRing p hp) (Padic p hp) (Padic.commRing p hp) (PadicInt.algebra p hp)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)], IsFractionRing.{0, 0} (PadicInt p hp) (PadicInt.instCommRingPadicInt p hp) (Padic p hp) (Padic.instCommRingPadic p hp) (PadicInt.algebra p hp)
Case conversion may be inaccurate. Consider using '#align padic_int.is_fraction_ring PadicInt.isFractionRingₓ'. -/
instance isFractionRing : IsFractionRing ℤ_[p] ℚ_[p]
    where
  map_units := fun ⟨x, hx⟩ => by
    rwa [[anonymous], algebraMap_apply, isUnit_iff_ne_zero, PadicInt.coe_ne_zero, ←
      mem_nonZeroDivisors_iff_ne_zero]
  surj x := by
    by_cases hx : ‖x‖ ≤ 1
    · use (⟨x, hx⟩, 1)
      rw [Submonoid.coe_one, map_one, mul_one, PadicInt.algebraMap_apply, Subtype.coe_mk]
    · set n := Int.toNat (-x.valuation) with hn
      have hn_coe : (n : ℤ) = -x.valuation :=
        by
        rw [hn, Int.toNat_of_nonneg]
        rw [Right.nonneg_neg_iff]
        rw [Padic.norm_le_one_iff_val_nonneg, not_le] at hx
        exact hx.le
      set a := x * p ^ n with ha
      have ha_norm : ‖a‖ = 1 :=
        by
        have hx : x ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hx
          exact hx zero_le_one
        rw [ha, padicNormE.mul, padicNormE.norm_p_pow, Padic.norm_eq_pow_val hx, ← zpow_add',
          hn_coe, neg_neg, add_left_neg, zpow_zero]
        exact Or.inl (nat.cast_ne_zero.mpr (NeZero.ne p))
      use
        (⟨a, le_of_eq ha_norm⟩,
          ⟨(p ^ n : ℤ_[p]), mem_non_zero_divisors_iff_ne_zero.mpr (NeZero.ne _)⟩)
      simp only [[anonymous], map_pow, map_natCast, algebraMap_apply, PadicInt.coe_pow,
        PadicInt.coe_nat_cast, Subtype.coe_mk]
  eq_iff_exists x y :=
    by
    rw [algebraMap_apply, algebraMap_apply, Subtype.coe_inj]
    refine' ⟨fun h => ⟨1, by rw [h]⟩, _⟩
    rintro ⟨⟨c, hc⟩, h⟩
    exact (mul_eq_mul_left_iff.mp h).resolve_right (mem_non_zero_divisors_iff_ne_zero.mp hc)
#align padic_int.is_fraction_ring PadicInt.isFractionRing

end FractionRing

end PadicInt

