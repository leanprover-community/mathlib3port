/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module number_theory.zsqrtd.basic
! leanprover-community/mathlib commit e8638a0fcaf73e4500469f368ef9494e495099b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.RingTheory.Int.Basic
import Mathbin.Tactic.Ring
import Mathbin.Algebra.Star.Unitary

/-! # ℤ[√d]

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The ring of integers adjoined with a square root of `d : ℤ`.

After defining the norm, we show that it is a linearly ordered commutative ring,
as well as an integral domain.

We provide the universal property, that ring homomorphisms `ℤ√d →+* R` correspond
to choices of square roots of `d` in `R`.

-/


#print Zsqrtd /-
/-- The ring of integers adjoined with a square root of `d`.
  These have the form `a + b √d` where `a b : ℤ`. The components
  are called `re` and `im` by analogy to the negative `d` case. -/
structure Zsqrtd (d : ℤ) where
  re : ℤ
  im : ℤ
#align zsqrtd Zsqrtd
-/

-- mathport name: «exprℤ√ »
prefix:100 "ℤ√" => Zsqrtd

namespace Zsqrtd

section

parameter {d : ℤ}

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
instance : DecidableEq (ℤ√d) := by
  run_tac
    tactic.mk_dec_eq_instance

#print Zsqrtd.ext /-
theorem ext : ∀ {z w : ℤ√d}, z = w ↔ z.re = w.re ∧ z.im = w.im
  | ⟨x, y⟩, ⟨x', y'⟩ =>
    ⟨fun h => by injection h <;> constructor <;> assumption, fun ⟨h₁, h₂⟩ => by
      congr <;> assumption⟩
#align zsqrtd.ext Zsqrtd.ext
-/

#print Zsqrtd.ofInt /-
/-- Convert an integer to a `ℤ√d` -/
def ofInt (n : ℤ) : ℤ√d :=
  ⟨n, 0⟩
#align zsqrtd.of_int Zsqrtd.ofInt
-/

#print Zsqrtd.ofInt_re /-
theorem ofInt_re (n : ℤ) : (of_int n).re = n :=
  rfl
#align zsqrtd.of_int_re Zsqrtd.ofInt_re
-/

#print Zsqrtd.ofInt_im /-
theorem ofInt_im (n : ℤ) : (of_int n).im = 0 :=
  rfl
#align zsqrtd.of_int_im Zsqrtd.ofInt_im
-/

/-- The zero of the ring -/
instance : Zero (ℤ√d) :=
  ⟨of_int 0⟩

#print Zsqrtd.zero_re /-
@[simp]
theorem zero_re : (0 : ℤ√d).re = 0 :=
  rfl
#align zsqrtd.zero_re Zsqrtd.zero_re
-/

#print Zsqrtd.zero_im /-
@[simp]
theorem zero_im : (0 : ℤ√d).im = 0 :=
  rfl
#align zsqrtd.zero_im Zsqrtd.zero_im
-/

instance : Inhabited (ℤ√d) :=
  ⟨0⟩

/-- The one of the ring -/
instance : One (ℤ√d) :=
  ⟨of_int 1⟩

#print Zsqrtd.one_re /-
@[simp]
theorem one_re : (1 : ℤ√d).re = 1 :=
  rfl
#align zsqrtd.one_re Zsqrtd.one_re
-/

#print Zsqrtd.one_im /-
@[simp]
theorem one_im : (1 : ℤ√d).im = 0 :=
  rfl
#align zsqrtd.one_im Zsqrtd.one_im
-/

#print Zsqrtd.sqrtd /-
/-- The representative of `√d` in the ring -/
def sqrtd : ℤ√d :=
  ⟨0, 1⟩
#align zsqrtd.sqrtd Zsqrtd.sqrtd
-/

#print Zsqrtd.sqrtd_re /-
@[simp]
theorem sqrtd_re : (sqrtd : ℤ√d).re = 0 :=
  rfl
#align zsqrtd.sqrtd_re Zsqrtd.sqrtd_re
-/

#print Zsqrtd.sqrtd_im /-
@[simp]
theorem sqrtd_im : (sqrtd : ℤ√d).im = 1 :=
  rfl
#align zsqrtd.sqrtd_im Zsqrtd.sqrtd_im
-/

/-- Addition of elements of `ℤ√d` -/
instance : Add (ℤ√d) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

#print Zsqrtd.add_def /-
@[simp]
theorem add_def (x y x' y' : ℤ) : (⟨x, y⟩ + ⟨x', y'⟩ : ℤ√d) = ⟨x + x', y + y'⟩ :=
  rfl
#align zsqrtd.add_def Zsqrtd.add_def
-/

#print Zsqrtd.add_re /-
@[simp]
theorem add_re (z w : ℤ√d) : (z + w).re = z.re + w.re :=
  rfl
#align zsqrtd.add_re Zsqrtd.add_re
-/

#print Zsqrtd.add_im /-
@[simp]
theorem add_im (z w : ℤ√d) : (z + w).im = z.im + w.im :=
  rfl
#align zsqrtd.add_im Zsqrtd.add_im
-/

#print Zsqrtd.bit0_re /-
@[simp]
theorem bit0_re (z) : (bit0 z : ℤ√d).re = bit0 z.re :=
  rfl
#align zsqrtd.bit0_re Zsqrtd.bit0_re
-/

#print Zsqrtd.bit0_im /-
@[simp]
theorem bit0_im (z) : (bit0 z : ℤ√d).im = bit0 z.im :=
  rfl
#align zsqrtd.bit0_im Zsqrtd.bit0_im
-/

#print Zsqrtd.bit1_re /-
@[simp]
theorem bit1_re (z) : (bit1 z : ℤ√d).re = bit1 z.re :=
  rfl
#align zsqrtd.bit1_re Zsqrtd.bit1_re
-/

#print Zsqrtd.bit1_im /-
@[simp]
theorem bit1_im (z) : (bit1 z : ℤ√d).im = bit0 z.im := by simp [bit1]
#align zsqrtd.bit1_im Zsqrtd.bit1_im
-/

/-- Negation in `ℤ√d` -/
instance : Neg (ℤ√d) :=
  ⟨fun z => ⟨-z.1, -z.2⟩⟩

#print Zsqrtd.neg_re /-
@[simp]
theorem neg_re (z : ℤ√d) : (-z).re = -z.re :=
  rfl
#align zsqrtd.neg_re Zsqrtd.neg_re
-/

#print Zsqrtd.neg_im /-
@[simp]
theorem neg_im (z : ℤ√d) : (-z).im = -z.im :=
  rfl
#align zsqrtd.neg_im Zsqrtd.neg_im
-/

/-- Multiplication in `ℤ√d` -/
instance : Mul (ℤ√d) :=
  ⟨fun z w => ⟨z.1 * w.1 + d * z.2 * w.2, z.1 * w.2 + z.2 * w.1⟩⟩

#print Zsqrtd.mul_re /-
@[simp]
theorem mul_re (z w : ℤ√d) : (z * w).re = z.re * w.re + d * z.im * w.im :=
  rfl
#align zsqrtd.mul_re Zsqrtd.mul_re
-/

#print Zsqrtd.mul_im /-
@[simp]
theorem mul_im (z w : ℤ√d) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl
#align zsqrtd.mul_im Zsqrtd.mul_im
-/

instance : AddCommGroup (ℤ√d) := by
  refine_struct
          { add := (· + ·)
            zero := (0 : ℤ√d)
            sub := fun a b => a + -b
            neg := Neg.neg
            zsmul := @zsmulRec (ℤ√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
            nsmul := @nsmulRec (ℤ√d) ⟨0⟩ ⟨(· + ·)⟩ } <;>
        intros <;>
      try rfl <;>
    simp [ext, add_comm, add_left_comm]

instance : AddGroupWithOne (ℤ√d) :=
  { Zsqrtd.addCommGroup with
    natCast := fun n => of_int n
    intCast := of_int
    one := 1 }

instance : CommRing (ℤ√d) := by
  refine_struct
          { Zsqrtd.addGroupWithOne with
            add := (· + ·)
            zero := (0 : ℤ√d)
            mul := (· * ·)
            one := 1
            npow := @npowRec (ℤ√d) ⟨1⟩ ⟨(· * ·)⟩ } <;>
        intros <;>
      try rfl <;>
    simp [ext, add_mul, mul_add, add_comm, add_left_comm, mul_comm, mul_left_comm]

instance : AddMonoid (ℤ√d) := by infer_instance

instance : Monoid (ℤ√d) := by infer_instance

instance : CommMonoid (ℤ√d) := by infer_instance

instance : CommSemigroup (ℤ√d) := by infer_instance

instance : Semigroup (ℤ√d) := by infer_instance

instance : AddCommSemigroup (ℤ√d) := by infer_instance

instance : AddSemigroup (ℤ√d) := by infer_instance

instance : CommSemiring (ℤ√d) := by infer_instance

instance : Semiring (ℤ√d) := by infer_instance

instance : Ring (ℤ√d) := by infer_instance

instance : Distrib (ℤ√d) := by infer_instance

/-- Conjugation in `ℤ√d`. The conjugate of `a + b √d` is `a - b √d`. -/
instance : Star (ℤ√d) where unit z := ⟨z.1, -z.2⟩

#print Zsqrtd.star_mk /-
@[simp]
theorem star_mk (x y : ℤ) : star (⟨x, y⟩ : ℤ√d) = ⟨x, -y⟩ :=
  rfl
#align zsqrtd.star_mk Zsqrtd.star_mk
-/

#print Zsqrtd.star_re /-
@[simp]
theorem star_re (z : ℤ√d) : (star z).re = z.re :=
  rfl
#align zsqrtd.star_re Zsqrtd.star_re
-/

#print Zsqrtd.star_im /-
@[simp]
theorem star_im (z : ℤ√d) : (star z).im = -z.im :=
  rfl
#align zsqrtd.star_im Zsqrtd.star_im
-/

instance : StarRing (ℤ√d)
    where
  star_involutive x := ext.mpr ⟨rfl, neg_neg _⟩
  star_mul a b := ext.mpr ⟨by simp <;> ring, by simp <;> ring⟩
  star_add a b := ext.mpr ⟨rfl, neg_add _ _⟩

instance : Nontrivial (ℤ√d) :=
  ⟨⟨0, 1, by decide⟩⟩

#print Zsqrtd.coe_nat_re /-
@[simp]
theorem coe_nat_re (n : ℕ) : (n : ℤ√d).re = n :=
  rfl
#align zsqrtd.coe_nat_re Zsqrtd.coe_nat_re
-/

#print Zsqrtd.coe_nat_im /-
@[simp]
theorem coe_nat_im (n : ℕ) : (n : ℤ√d).im = 0 :=
  rfl
#align zsqrtd.coe_nat_im Zsqrtd.coe_nat_im
-/

#print Zsqrtd.coe_nat_val /-
theorem coe_nat_val (n : ℕ) : (n : ℤ√d) = ⟨n, 0⟩ :=
  rfl
#align zsqrtd.coe_nat_val Zsqrtd.coe_nat_val
-/

/- warning: zsqrtd.coe_int_re -> Zsqrtd.coe_int_re is a dubious translation:
lean 3 declaration is
  forall {d : Int} (n : Int), Eq.{1} Int (Zsqrtd.re d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n)) n
but is expected to have type
  forall {d : Int} (n : Int), Eq.{1} Int (Zsqrtd.re d (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n)) n
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_re Zsqrtd.coe_int_reₓ'. -/
@[simp]
theorem coe_int_re (n : ℤ) : (n : ℤ√d).re = n := by cases n <;> rfl
#align zsqrtd.coe_int_re Zsqrtd.coe_int_re

/- warning: zsqrtd.coe_int_im -> Zsqrtd.coe_int_im is a dubious translation:
lean 3 declaration is
  forall {d : Int} (n : Int), Eq.{1} Int (Zsqrtd.im d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n)) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))
but is expected to have type
  forall {d : Int} (n : Int), Eq.{1} Int (Zsqrtd.im d (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n)) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_im Zsqrtd.coe_int_imₓ'. -/
@[simp]
theorem coe_int_im (n : ℤ) : (n : ℤ√d).im = 0 := by cases n <;> rfl
#align zsqrtd.coe_int_im Zsqrtd.coe_int_im

/- warning: zsqrtd.coe_int_val -> Zsqrtd.coe_int_val is a dubious translation:
lean 3 declaration is
  forall {d : Int} (n : Int), Eq.{1} (Zsqrtd d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n) (Zsqrtd.mk d n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {d : Int} (n : Int), Eq.{1} (Zsqrtd d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n) (Zsqrtd.mk d n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_val Zsqrtd.coe_int_valₓ'. -/
theorem coe_int_val (n : ℤ) : (n : ℤ√d) = ⟨n, 0⟩ := by simp [ext]
#align zsqrtd.coe_int_val Zsqrtd.coe_int_val

instance : CharZero (ℤ√d) where cast_injective m n := by simp [ext]

/- warning: zsqrtd.of_int_eq_coe -> Zsqrtd.ofInt_eq_coe is a dubious translation:
lean 3 declaration is
  forall {d : Int} (n : Int), Eq.{1} (Zsqrtd d) (Zsqrtd.ofInt d n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n)
but is expected to have type
  forall {d : Int} (n : Int), Eq.{1} (Zsqrtd d) (Zsqrtd.ofInt d n) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n)
Case conversion may be inaccurate. Consider using '#align zsqrtd.of_int_eq_coe Zsqrtd.ofInt_eq_coeₓ'. -/
@[simp]
theorem ofInt_eq_coe (n : ℤ) : (of_int n : ℤ√d) = n := by simp [ext, of_int_re, of_int_im]
#align zsqrtd.of_int_eq_coe Zsqrtd.ofInt_eq_coe

/- warning: zsqrtd.smul_val -> Zsqrtd.smul_val is a dubious translation:
lean 3 declaration is
  forall {d : Int} (n : Int) (x : Int) (y : Int), Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n) (Zsqrtd.mk d x y)) (Zsqrtd.mk d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) n x) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) n y))
but is expected to have type
  forall {d : Int} (n : Int) (x : Int) (y : Int), Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n) (Zsqrtd.mk d x y)) (Zsqrtd.mk d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) n x) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) n y))
Case conversion may be inaccurate. Consider using '#align zsqrtd.smul_val Zsqrtd.smul_valₓ'. -/
@[simp]
theorem smul_val (n x y : ℤ) : (n : ℤ√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by simp [ext]
#align zsqrtd.smul_val Zsqrtd.smul_val

/- warning: zsqrtd.smul_re -> Zsqrtd.smul_re is a dubious translation:
lean 3 declaration is
  forall {d : Int} (a : Int) (b : Zsqrtd d), Eq.{1} Int (Zsqrtd.re d (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) a) b)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a (Zsqrtd.re d b))
but is expected to have type
  forall {d : Int} (a : Int) (b : Zsqrtd d), Eq.{1} Int (Zsqrtd.re d (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) a) b)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a (Zsqrtd.re d b))
Case conversion may be inaccurate. Consider using '#align zsqrtd.smul_re Zsqrtd.smul_reₓ'. -/
theorem smul_re (a : ℤ) (b : ℤ√d) : (↑a * b).re = a * b.re := by simp
#align zsqrtd.smul_re Zsqrtd.smul_re

/- warning: zsqrtd.smul_im -> Zsqrtd.smul_im is a dubious translation:
lean 3 declaration is
  forall {d : Int} (a : Int) (b : Zsqrtd d), Eq.{1} Int (Zsqrtd.im d (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) a) b)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a (Zsqrtd.im d b))
but is expected to have type
  forall {d : Int} (a : Int) (b : Zsqrtd d), Eq.{1} Int (Zsqrtd.im d (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) a) b)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a (Zsqrtd.im d b))
Case conversion may be inaccurate. Consider using '#align zsqrtd.smul_im Zsqrtd.smul_imₓ'. -/
theorem smul_im (a : ℤ) (b : ℤ√d) : (↑a * b).im = a * b.im := by simp
#align zsqrtd.smul_im Zsqrtd.smul_im

#print Zsqrtd.muld_val /-
@[simp]
theorem muld_val (x y : ℤ) : sqrtd * ⟨x, y⟩ = ⟨d * y, x⟩ := by simp [ext]
#align zsqrtd.muld_val Zsqrtd.muld_val
-/

/- warning: zsqrtd.dmuld -> Zsqrtd.dmuld is a dubious translation:
lean 3 declaration is
  forall {d : Int}, Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) (Zsqrtd.sqrtd d) (Zsqrtd.sqrtd d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) d)
but is expected to have type
  forall {d : Int}, Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Zsqrtd.sqrtd d) (Zsqrtd.sqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) d)
Case conversion may be inaccurate. Consider using '#align zsqrtd.dmuld Zsqrtd.dmuldₓ'. -/
@[simp]
theorem dmuld : sqrtd * sqrtd = d := by simp [ext]
#align zsqrtd.dmuld Zsqrtd.dmuld

/- warning: zsqrtd.smuld_val -> Zsqrtd.smuld_val is a dubious translation:
lean 3 declaration is
  forall {d : Int} (n : Int) (x : Int) (y : Int), Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) (Zsqrtd.sqrtd d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n)) (Zsqrtd.mk d x y)) (Zsqrtd.mk d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) d n) y) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) n x))
but is expected to have type
  forall {d : Int} (n : Int) (x : Int) (y : Int), Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Zsqrtd.sqrtd d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n)) (Zsqrtd.mk d x y)) (Zsqrtd.mk d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) d n) y) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) n x))
Case conversion may be inaccurate. Consider using '#align zsqrtd.smuld_val Zsqrtd.smuld_valₓ'. -/
@[simp]
theorem smuld_val (n x y : ℤ) : sqrtd * (n : ℤ√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩ := by simp [ext]
#align zsqrtd.smuld_val Zsqrtd.smuld_val

/- warning: zsqrtd.decompose -> Zsqrtd.decompose is a dubious translation:
lean 3 declaration is
  forall {d : Int} {x : Int} {y : Int}, Eq.{1} (Zsqrtd d) (Zsqrtd.mk d x y) (HAdd.hAdd.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHAdd.{0} (Zsqrtd d) (Zsqrtd.hasAdd d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) x) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) (Zsqrtd.sqrtd d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) y)))
but is expected to have type
  forall {d : Int} {x : Int} {y : Int}, Eq.{1} (Zsqrtd d) (Zsqrtd.mk d x y) (HAdd.hAdd.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHAdd.{0} (Zsqrtd d) (Zsqrtd.instAddZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) x) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Zsqrtd.sqrtd d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) y)))
Case conversion may be inaccurate. Consider using '#align zsqrtd.decompose Zsqrtd.decomposeₓ'. -/
theorem decompose {x y : ℤ} : (⟨x, y⟩ : ℤ√d) = x + sqrtd * y := by simp [ext]
#align zsqrtd.decompose Zsqrtd.decompose

/- warning: zsqrtd.mul_star -> Zsqrtd.mul_star is a dubious translation:
lean 3 declaration is
  forall {d : Int} {x : Int} {y : Int}, Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) (Zsqrtd.mk d x y) (Star.star.{0} (Zsqrtd d) (Zsqrtd.hasStar d) (Zsqrtd.mk d x y))) (HSub.hSub.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHSub.{0} (Zsqrtd d) (SubNegMonoid.toHasSub.{0} (Zsqrtd d) (AddGroup.toSubNegMonoid.{0} (Zsqrtd d) (AddGroupWithOne.toAddGroup.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) x)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) y)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) y)))
but is expected to have type
  forall {d : Int} {x : Int} {y : Int}, Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Zsqrtd.mk d x y) (Star.star.{0} (Zsqrtd d) (Zsqrtd.instStarZsqrtd d) (Zsqrtd.mk d x y))) (HSub.hSub.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHSub.{0} (Zsqrtd d) (Ring.toSub.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) x) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) x)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) y)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) y)))
Case conversion may be inaccurate. Consider using '#align zsqrtd.mul_star Zsqrtd.mul_starₓ'. -/
theorem mul_star {x y : ℤ} : (⟨x, y⟩ * star ⟨x, y⟩ : ℤ√d) = x * x - d * y * y := by
  simp [ext, sub_eq_add_neg, mul_comm]
#align zsqrtd.mul_star Zsqrtd.mul_star

/- warning: zsqrtd.coe_int_add -> Zsqrtd.coe_int_add is a dubious translation:
lean 3 declaration is
  forall {d : Int} (m : Int) (n : Int), Eq.{1} (Zsqrtd d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) (HAdd.hAdd.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHAdd.{0} (Zsqrtd d) (Zsqrtd.hasAdd d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n))
but is expected to have type
  forall {d : Int} (m : Int) (n : Int), Eq.{1} (Zsqrtd d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) (HAdd.hAdd.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHAdd.{0} (Zsqrtd d) (Zsqrtd.instAddZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) m) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n))
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_add Zsqrtd.coe_int_addₓ'. -/
protected theorem coe_int_add (m n : ℤ) : (↑(m + n) : ℤ√d) = ↑m + ↑n :=
  (Int.castRingHom _).map_add _ _
#align zsqrtd.coe_int_add Zsqrtd.coe_int_add

/- warning: zsqrtd.coe_int_sub -> Zsqrtd.coe_int_sub is a dubious translation:
lean 3 declaration is
  forall {d : Int} (m : Int) (n : Int), Eq.{1} (Zsqrtd d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) m n)) (HSub.hSub.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHSub.{0} (Zsqrtd d) (SubNegMonoid.toHasSub.{0} (Zsqrtd d) (AddGroup.toSubNegMonoid.{0} (Zsqrtd d) (AddGroupWithOne.toAddGroup.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n))
but is expected to have type
  forall {d : Int} (m : Int) (n : Int), Eq.{1} (Zsqrtd d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) m n)) (HSub.hSub.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHSub.{0} (Zsqrtd d) (Ring.toSub.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) m) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n))
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_sub Zsqrtd.coe_int_subₓ'. -/
protected theorem coe_int_sub (m n : ℤ) : (↑(m - n) : ℤ√d) = ↑m - ↑n :=
  (Int.castRingHom _).map_sub _ _
#align zsqrtd.coe_int_sub Zsqrtd.coe_int_sub

/- warning: zsqrtd.coe_int_mul -> Zsqrtd.coe_int_mul is a dubious translation:
lean 3 declaration is
  forall {d : Int} (m : Int) (n : Int), Eq.{1} (Zsqrtd d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) m n)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n))
but is expected to have type
  forall {d : Int} (m : Int) (n : Int), Eq.{1} (Zsqrtd d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) m n)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) m) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n))
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_mul Zsqrtd.coe_int_mulₓ'. -/
protected theorem coe_int_mul (m n : ℤ) : (↑(m * n) : ℤ√d) = ↑m * ↑n :=
  (Int.castRingHom _).map_mul _ _
#align zsqrtd.coe_int_mul Zsqrtd.coe_int_mul

/- warning: zsqrtd.coe_int_inj -> Zsqrtd.coe_int_inj is a dubious translation:
lean 3 declaration is
  forall {d : Int} {m : Int} {n : Int}, (Eq.{1} (Zsqrtd d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n)) -> (Eq.{1} Int m n)
but is expected to have type
  forall {d : Int} {m : Int} {n : Int}, (Eq.{1} (Zsqrtd d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) m) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n)) -> (Eq.{1} Int m n)
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_inj Zsqrtd.coe_int_injₓ'. -/
protected theorem coe_int_inj {m n : ℤ} (h : (↑m : ℤ√d) = ↑n) : m = n := by
  simpa using congr_arg re h
#align zsqrtd.coe_int_inj Zsqrtd.coe_int_inj

/- warning: zsqrtd.coe_int_dvd_iff -> Zsqrtd.coe_int_dvd_iff is a dubious translation:
lean 3 declaration is
  forall {d : Int} (z : Int) (a : Zsqrtd d), Iff (Dvd.Dvd.{0} (Zsqrtd d) (semigroupDvd.{0} (Zsqrtd d) (Zsqrtd.semigroup d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) z) a) (And (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) z (Zsqrtd.re d a)) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) z (Zsqrtd.im d a)))
but is expected to have type
  forall {d : Int} (z : Int) (a : Zsqrtd d), Iff (Dvd.dvd.{0} (Zsqrtd d) (semigroupDvd.{0} (Zsqrtd d) (Zsqrtd.instSemigroupZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) z) a) (And (Dvd.dvd.{0} Int Int.instDvdInt z (Zsqrtd.re d a)) (Dvd.dvd.{0} Int Int.instDvdInt z (Zsqrtd.im d a)))
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_dvd_iff Zsqrtd.coe_int_dvd_iffₓ'. -/
theorem coe_int_dvd_iff (z : ℤ) (a : ℤ√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im :=
  by
  constructor
  · rintro ⟨x, rfl⟩
    simp only [add_zero, coe_int_re, MulZeroClass.zero_mul, mul_im, dvd_mul_right, and_self_iff,
      mul_re, MulZeroClass.mul_zero, coe_int_im]
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    rw [smul_val, ext]
    exact ⟨hr, hi⟩
#align zsqrtd.coe_int_dvd_iff Zsqrtd.coe_int_dvd_iff

/- warning: zsqrtd.coe_int_dvd_coe_int -> Zsqrtd.coe_int_dvd_coe_int is a dubious translation:
lean 3 declaration is
  forall {d : Int} (a : Int) (b : Int), Iff (Dvd.Dvd.{0} (Zsqrtd d) (semigroupDvd.{0} (Zsqrtd d) (Zsqrtd.semigroup d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) b)) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) a b)
but is expected to have type
  forall {d : Int} (a : Int) (b : Int), Iff (Dvd.dvd.{0} (Zsqrtd d) (semigroupDvd.{0} (Zsqrtd d) (Zsqrtd.instSemigroupZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) a) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) b)) (Dvd.dvd.{0} Int Int.instDvdInt a b)
Case conversion may be inaccurate. Consider using '#align zsqrtd.coe_int_dvd_coe_int Zsqrtd.coe_int_dvd_coe_intₓ'. -/
@[simp, norm_cast]
theorem coe_int_dvd_coe_int (a b : ℤ) : (a : ℤ√d) ∣ b ↔ a ∣ b :=
  by
  rw [coe_int_dvd_iff]
  constructor
  · rintro ⟨hre, -⟩
    rwa [coe_int_re] at hre
  · rw [coe_int_re, coe_int_im]
    exact fun hc => ⟨hc, dvd_zero a⟩
#align zsqrtd.coe_int_dvd_coe_int Zsqrtd.coe_int_dvd_coe_int

/- warning: zsqrtd.eq_of_smul_eq_smul_left -> Zsqrtd.eq_of_smul_eq_smul_left is a dubious translation:
lean 3 declaration is
  forall {d : Int} {a : Int} {b : Zsqrtd d} {c : Zsqrtd d}, (Ne.{1} Int a (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) a) b) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) a) c)) -> (Eq.{1} (Zsqrtd d) b c)
but is expected to have type
  forall {d : Int} {a : Int} {b : Zsqrtd d} {c : Zsqrtd d}, (Ne.{1} Int a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Eq.{1} (Zsqrtd d) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) a) b) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) a) c)) -> (Eq.{1} (Zsqrtd d) b c)
Case conversion may be inaccurate. Consider using '#align zsqrtd.eq_of_smul_eq_smul_left Zsqrtd.eq_of_smul_eq_smul_leftₓ'. -/
protected theorem eq_of_smul_eq_smul_left {a : ℤ} {b c : ℤ√d} (ha : a ≠ 0) (h : ↑a * b = a * c) :
    b = c := by
  rw [ext] at h⊢
  apply And.imp _ _ h <;> · simpa only [smul_re, smul_im] using mul_left_cancel₀ ha
#align zsqrtd.eq_of_smul_eq_smul_left Zsqrtd.eq_of_smul_eq_smul_left

section Gcd

#print Zsqrtd.gcd_eq_zero_iff /-
theorem gcd_eq_zero_iff (a : ℤ√d) : Int.gcd a.re a.im = 0 ↔ a = 0 := by
  simp only [Int.gcd_eq_zero_iff, ext, eq_self_iff_true, zero_im, zero_re]
#align zsqrtd.gcd_eq_zero_iff Zsqrtd.gcd_eq_zero_iff
-/

#print Zsqrtd.gcd_pos_iff /-
theorem gcd_pos_iff (a : ℤ√d) : 0 < Int.gcd a.re a.im ↔ a ≠ 0 :=
  pos_iff_ne_zero.trans <| not_congr a.gcd_eq_zero_iff
#align zsqrtd.gcd_pos_iff Zsqrtd.gcd_pos_iff
-/

/- warning: zsqrtd.coprime_of_dvd_coprime -> Zsqrtd.coprime_of_dvd_coprime is a dubious translation:
lean 3 declaration is
  forall {d : Int} {a : Zsqrtd d} {b : Zsqrtd d}, (IsCoprime.{0} Int Int.commSemiring (Zsqrtd.re d a) (Zsqrtd.im d a)) -> (Dvd.Dvd.{0} (Zsqrtd d) (semigroupDvd.{0} (Zsqrtd d) (Zsqrtd.semigroup d)) b a) -> (IsCoprime.{0} Int Int.commSemiring (Zsqrtd.re d b) (Zsqrtd.im d b))
but is expected to have type
  forall {d : Int} {a : Zsqrtd d} {b : Zsqrtd d}, (IsCoprime.{0} Int Int.instCommSemiringInt (Zsqrtd.re d a) (Zsqrtd.im d a)) -> (Dvd.dvd.{0} (Zsqrtd d) (semigroupDvd.{0} (Zsqrtd d) (Zsqrtd.instSemigroupZsqrtd d)) b a) -> (IsCoprime.{0} Int Int.instCommSemiringInt (Zsqrtd.re d b) (Zsqrtd.im d b))
Case conversion may be inaccurate. Consider using '#align zsqrtd.coprime_of_dvd_coprime Zsqrtd.coprime_of_dvd_coprimeₓ'. -/
theorem coprime_of_dvd_coprime {a b : ℤ√d} (hcoprime : IsCoprime a.re a.im) (hdvd : b ∣ a) :
    IsCoprime b.re b.im := by
  apply isCoprime_of_dvd
  · rintro ⟨hre, him⟩
    obtain rfl : b = 0 := by
      simp only [ext, hre, eq_self_iff_true, zero_im, him, and_self_iff, zero_re]
    rw [zero_dvd_iff] at hdvd
    simpa only [hdvd, zero_im, zero_re, not_isCoprime_zero_zero] using hcoprime
  · intro z hz hznezero hzdvdu hzdvdv
    apply hz
    obtain ⟨ha, hb⟩ : z ∣ a.re ∧ z ∣ a.im :=
      by
      rw [← coe_int_dvd_iff]
      apply dvd_trans _ hdvd
      rw [coe_int_dvd_iff]
      exact ⟨hzdvdu, hzdvdv⟩
    exact hcoprime.is_unit_of_dvd' ha hb
#align zsqrtd.coprime_of_dvd_coprime Zsqrtd.coprime_of_dvd_coprime

/- warning: zsqrtd.exists_coprime_of_gcd_pos -> Zsqrtd.exists_coprime_of_gcd_pos is a dubious translation:
lean 3 declaration is
  forall {d : Int} {a : Zsqrtd d}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Int.gcd (Zsqrtd.re d a) (Zsqrtd.im d a))) -> (Exists.{1} (Zsqrtd d) (fun (b : Zsqrtd d) => And (Eq.{1} (Zsqrtd d) a (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Int.gcd (Zsqrtd.re d a) (Zsqrtd.im d a)))) b)) (IsCoprime.{0} Int Int.commSemiring (Zsqrtd.re d b) (Zsqrtd.im d b))))
but is expected to have type
  forall {d : Int} {a : Zsqrtd d}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Int.gcd (Zsqrtd.re d a) (Zsqrtd.im d a))) -> (Exists.{1} (Zsqrtd d) (fun (b : Zsqrtd d) => And (Eq.{1} (Zsqrtd d) a (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) (Nat.cast.{0} Int instNatCastInt (Int.gcd (Zsqrtd.re d a) (Zsqrtd.im d a)))) b)) (IsCoprime.{0} Int Int.instCommSemiringInt (Zsqrtd.re d b) (Zsqrtd.im d b))))
Case conversion may be inaccurate. Consider using '#align zsqrtd.exists_coprime_of_gcd_pos Zsqrtd.exists_coprime_of_gcd_posₓ'. -/
theorem exists_coprime_of_gcd_pos {a : ℤ√d} (hgcd : 0 < Int.gcd a.re a.im) :
    ∃ b : ℤ√d, a = ((Int.gcd a.re a.im : ℤ) : ℤ√d) * b ∧ IsCoprime b.re b.im :=
  by
  obtain ⟨re, im, H1, Hre, Him⟩ := Int.exists_gcd_one hgcd
  rw [mul_comm] at Hre Him
  refine' ⟨⟨re, im⟩, _, _⟩
  · rw [smul_val, ext, ← Hre, ← Him]
    constructor <;> rfl
  · rw [← Int.gcd_eq_one_iff_coprime, H1]
#align zsqrtd.exists_coprime_of_gcd_pos Zsqrtd.exists_coprime_of_gcd_pos

end Gcd

#print Zsqrtd.SqLe /-
/-- Read `sq_le a c b d` as `a √c ≤ b √d` -/
def SqLe (a c b d : ℕ) : Prop :=
  c * a * a ≤ d * b * b
#align zsqrtd.sq_le Zsqrtd.SqLe
-/

#print Zsqrtd.sqLe_of_le /-
theorem sqLe_of_le {c d x y z w : ℕ} (xz : z ≤ x) (yw : y ≤ w) (xy : SqLe x c y d) : SqLe z c w d :=
  le_trans (mul_le_mul (Nat.mul_le_mul_left _ xz) xz (Nat.zero_le _) (Nat.zero_le _)) <|
    le_trans xy (mul_le_mul (Nat.mul_le_mul_left _ yw) yw (Nat.zero_le _) (Nat.zero_le _))
#align zsqrtd.sq_le_of_le Zsqrtd.sqLe_of_le
-/

#print Zsqrtd.sqLe_add_mixed /-
theorem sqLe_add_mixed {c d x y z w : ℕ} (xy : SqLe x c y d) (zw : SqLe z c w d) :
    c * (x * z) ≤ d * (y * w) :=
  Nat.mul_self_le_mul_self_iff.2 <| by
    simpa [mul_comm, mul_left_comm] using mul_le_mul xy zw (Nat.zero_le _) (Nat.zero_le _)
#align zsqrtd.sq_le_add_mixed Zsqrtd.sqLe_add_mixed
-/

#print Zsqrtd.sqLe_add /-
theorem sqLe_add {c d x y z w : ℕ} (xy : SqLe x c y d) (zw : SqLe z c w d) :
    SqLe (x + z) c (y + w) d := by
  have xz := sq_le_add_mixed xy zw
  simp [sq_le, mul_assoc] at xy zw
  simp [sq_le, mul_add, mul_comm, mul_left_comm, add_le_add, *]
#align zsqrtd.sq_le_add Zsqrtd.sqLe_add
-/

#print Zsqrtd.sqLe_cancel /-
theorem sqLe_cancel {c d x y z w : ℕ} (zw : SqLe y d x c) (h : SqLe (x + z) c (y + w) d) :
    SqLe z c w d := by
  apply le_of_not_gt
  intro l
  refine' not_le_of_gt _ h
  simp [sq_le, mul_add, mul_comm, mul_left_comm, add_assoc]
  have hm := sq_le_add_mixed zw (le_of_lt l)
  simp [sq_le, mul_assoc] at l zw
  exact
    lt_of_le_of_lt (add_le_add_right zw _)
      (add_lt_add_left (add_lt_add_of_le_of_lt hm (add_lt_add_of_le_of_lt hm l)) _)
#align zsqrtd.sq_le_cancel Zsqrtd.sqLe_cancel
-/

#print Zsqrtd.sqLe_smul /-
theorem sqLe_smul {c d x y : ℕ} (n : ℕ) (xy : SqLe x c y d) : SqLe (n * x) c (n * y) d := by
  simpa [sq_le, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left (n * n) xy
#align zsqrtd.sq_le_smul Zsqrtd.sqLe_smul
-/

#print Zsqrtd.sqLe_mul /-
theorem sqLe_mul {d x y z w : ℕ} :
    (SqLe x 1 y d → SqLe z 1 w d → SqLe (x * w + y * z) d (x * z + d * y * w) 1) ∧
      (SqLe x 1 y d → SqLe w d z 1 → SqLe (x * z + d * y * w) 1 (x * w + y * z) d) ∧
        (SqLe y d x 1 → SqLe z 1 w d → SqLe (x * z + d * y * w) 1 (x * w + y * z) d) ∧
          (SqLe y d x 1 → SqLe w d z 1 → SqLe (x * w + y * z) d (x * z + d * y * w) 1) :=
  by
  refine' ⟨_, _, _, _⟩ <;>
    · intro xy zw
      have :=
        Int.mul_nonneg (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le xy))
          (sub_nonneg_of_le (Int.ofNat_le_ofNat_of_le zw))
      refine' Int.le_of_ofNat_le_ofNat (le_of_sub_nonneg _)
      convert this
      simp only [one_mul, Int.ofNat_add, Int.ofNat_mul]
      ring
#align zsqrtd.sq_le_mul Zsqrtd.sqLe_mul
-/

#print Zsqrtd.Nonnegg /-
/-- "Generalized" `nonneg`. `nonnegg c d x y` means `a √c + b √d ≥ 0`;
  we are interested in the case `c = 1` but this is more symmetric -/
def Nonnegg (c d : ℕ) : ℤ → ℤ → Prop
  | (a : ℕ), (b : ℕ) => True
  | (a : ℕ), -[b+1] => SqLe (b + 1) c a d
  | -[a+1], (b : ℕ) => SqLe (a + 1) d b c
  | -[a+1], -[b+1] => False
#align zsqrtd.nonnegg Zsqrtd.Nonnegg
-/

#print Zsqrtd.nonnegg_comm /-
theorem nonnegg_comm {c d : ℕ} {x y : ℤ} : Nonnegg c d x y = Nonnegg d c y x := by
  induction x <;> induction y <;> rfl
#align zsqrtd.nonnegg_comm Zsqrtd.nonnegg_comm
-/

#print Zsqrtd.nonnegg_neg_pos /-
theorem nonnegg_neg_pos {c d} : ∀ {a b : ℕ}, Nonnegg c d (-a) b ↔ SqLe a d b c
  | 0, b => ⟨by simp [sq_le, Nat.zero_le], fun a => trivial⟩
  | a + 1, b => by rw [← Int.negSucc_coe] <;> rfl
#align zsqrtd.nonnegg_neg_pos Zsqrtd.nonnegg_neg_pos
-/

#print Zsqrtd.nonnegg_pos_neg /-
theorem nonnegg_pos_neg {c d} {a b : ℕ} : Nonnegg c d a (-b) ↔ SqLe b c a d := by
  rw [nonnegg_comm] <;> exact nonnegg_neg_pos
#align zsqrtd.nonnegg_pos_neg Zsqrtd.nonnegg_pos_neg
-/

#print Zsqrtd.nonnegg_cases_right /-
theorem nonnegg_cases_right {c d} {a : ℕ} :
    ∀ {b : ℤ}, (∀ x : ℕ, b = -x → SqLe x c a d) → Nonnegg c d a b
  | (b : Nat), h => trivial
  | -[b+1], h => h (b + 1) rfl
#align zsqrtd.nonnegg_cases_right Zsqrtd.nonnegg_cases_right
-/

#print Zsqrtd.nonnegg_cases_left /-
theorem nonnegg_cases_left {c d} {b : ℕ} {a : ℤ} (h : ∀ x : ℕ, a = -x → SqLe x d b c) :
    Nonnegg c d a b :=
  cast nonnegg_comm (nonnegg_cases_right h)
#align zsqrtd.nonnegg_cases_left Zsqrtd.nonnegg_cases_left
-/

section Norm

#print Zsqrtd.norm /-
/-- The norm of an element of `ℤ[√d]`. -/
def norm (n : ℤ√d) : ℤ :=
  n.re * n.re - d * n.im * n.im
#align zsqrtd.norm Zsqrtd.norm
-/

#print Zsqrtd.norm_def /-
theorem norm_def (n : ℤ√d) : n.norm = n.re * n.re - d * n.im * n.im :=
  rfl
#align zsqrtd.norm_def Zsqrtd.norm_def
-/

#print Zsqrtd.norm_zero /-
@[simp]
theorem norm_zero : norm 0 = 0 := by simp [norm]
#align zsqrtd.norm_zero Zsqrtd.norm_zero
-/

#print Zsqrtd.norm_one /-
@[simp]
theorem norm_one : norm 1 = 1 := by simp [norm]
#align zsqrtd.norm_one Zsqrtd.norm_one
-/

/- warning: zsqrtd.norm_int_cast -> Zsqrtd.norm_int_cast is a dubious translation:
lean 3 declaration is
  forall {d : Int} (n : Int), Eq.{1} Int (Zsqrtd.norm d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) n)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) n n)
but is expected to have type
  forall {d : Int} (n : Int), Eq.{1} Int (Zsqrtd.norm d (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) n)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) n n)
Case conversion may be inaccurate. Consider using '#align zsqrtd.norm_int_cast Zsqrtd.norm_int_castₓ'. -/
@[simp]
theorem norm_int_cast (n : ℤ) : norm n = n * n := by simp [norm]
#align zsqrtd.norm_int_cast Zsqrtd.norm_int_cast

#print Zsqrtd.norm_nat_cast /-
@[simp]
theorem norm_nat_cast (n : ℕ) : norm n = n * n :=
  norm_int_cast n
#align zsqrtd.norm_nat_cast Zsqrtd.norm_nat_cast
-/

#print Zsqrtd.norm_mul /-
@[simp]
theorem norm_mul (n m : ℤ√d) : norm (n * m) = norm n * norm m :=
  by
  simp only [norm, mul_im, mul_re]
  ring
#align zsqrtd.norm_mul Zsqrtd.norm_mul
-/

/- warning: zsqrtd.norm_monoid_hom -> Zsqrtd.normMonoidHom is a dubious translation:
lean 3 declaration is
  forall {d : Int}, MonoidHom.{0, 0} (Zsqrtd d) Int (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))))
but is expected to have type
  forall {d : Int}, MonoidHom.{0, 0} (Zsqrtd d) Int (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))
Case conversion may be inaccurate. Consider using '#align zsqrtd.norm_monoid_hom Zsqrtd.normMonoidHomₓ'. -/
/-- `norm` as a `monoid_hom`. -/
def normMonoidHom : ℤ√d →* ℤ where
  toFun := norm
  map_mul' := norm_mul
  map_one' := norm_one
#align zsqrtd.norm_monoid_hom Zsqrtd.normMonoidHom

/- warning: zsqrtd.norm_eq_mul_conj -> Zsqrtd.norm_eq_mul_conj is a dubious translation:
lean 3 declaration is
  forall {d : Int} (n : Zsqrtd d), Eq.{1} (Zsqrtd d) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (Zsqrtd d) (HasLiftT.mk.{1, 1} Int (Zsqrtd d) (CoeTCₓ.coe.{1, 1} Int (Zsqrtd d) (Int.castCoe.{0} (Zsqrtd d) (AddGroupWithOne.toHasIntCast.{0} (Zsqrtd d) (Zsqrtd.addGroupWithOne d))))) (Zsqrtd.norm d n)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.hasMul d)) n (Star.star.{0} (Zsqrtd d) (Zsqrtd.hasStar d) n))
but is expected to have type
  forall {d : Int} (n : Zsqrtd d), Eq.{1} (Zsqrtd d) (Int.cast.{0} (Zsqrtd d) (Ring.toIntCast.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)) (Zsqrtd.norm d n)) (HMul.hMul.{0, 0, 0} (Zsqrtd d) (Zsqrtd d) (Zsqrtd d) (instHMul.{0} (Zsqrtd d) (Zsqrtd.instMulZsqrtd d)) n (Star.star.{0} (Zsqrtd d) (Zsqrtd.instStarZsqrtd d) n))
Case conversion may be inaccurate. Consider using '#align zsqrtd.norm_eq_mul_conj Zsqrtd.norm_eq_mul_conjₓ'. -/
theorem norm_eq_mul_conj (n : ℤ√d) : (norm n : ℤ√d) = n * star n := by
  cases n <;> simp [norm, star, Zsqrtd.ext, mul_comm, sub_eq_add_neg]
#align zsqrtd.norm_eq_mul_conj Zsqrtd.norm_eq_mul_conj

#print Zsqrtd.norm_neg /-
@[simp]
theorem norm_neg (x : ℤ√d) : (-x).norm = x.norm :=
  coe_int_inj <| by simp only [norm_eq_mul_conj, star_neg, neg_mul, mul_neg, neg_neg]
#align zsqrtd.norm_neg Zsqrtd.norm_neg
-/

#print Zsqrtd.norm_conj /-
@[simp]
theorem norm_conj (x : ℤ√d) : (star x).norm = x.norm :=
  coe_int_inj <| by simp only [norm_eq_mul_conj, star_star, mul_comm]
#align zsqrtd.norm_conj Zsqrtd.norm_conj
-/

#print Zsqrtd.norm_nonneg /-
theorem norm_nonneg (hd : d ≤ 0) (n : ℤ√d) : 0 ≤ n.norm :=
  add_nonneg (mul_self_nonneg _)
    (by
      rw [mul_assoc, neg_mul_eq_neg_mul] <;> exact mul_nonneg (neg_nonneg.2 hd) (mul_self_nonneg _))
#align zsqrtd.norm_nonneg Zsqrtd.norm_nonneg
-/

/- warning: zsqrtd.norm_eq_one_iff -> Zsqrtd.norm_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {d : Int} {x : Zsqrtd d}, Iff (Eq.{1} Nat (Int.natAbs (Zsqrtd.norm d x)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (IsUnit.{0} (Zsqrtd d) (Zsqrtd.monoid d) x)
but is expected to have type
  forall {d : Int} {x : Zsqrtd d}, Iff (Eq.{1} Nat (Int.natAbs (Zsqrtd.norm d x)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (IsUnit.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d) x)
Case conversion may be inaccurate. Consider using '#align zsqrtd.norm_eq_one_iff Zsqrtd.norm_eq_one_iffₓ'. -/
theorem norm_eq_one_iff {x : ℤ√d} : x.norm.natAbs = 1 ↔ IsUnit x :=
  ⟨fun h =>
    isUnit_iff_dvd_one.2 <|
      (le_total 0 (norm x)).casesOn
        (fun hx =>
          show x ∣ 1 from
            ⟨star x, by
              rwa [← Int.coe_nat_inj', Int.natAbs_of_nonneg hx, ← @Int.cast_inj (ℤ√d) _ _,
                norm_eq_mul_conj, eq_comm] at h⟩)
        fun hx =>
        show x ∣ 1 from
          ⟨-star x, by
            rwa [← Int.coe_nat_inj', Int.ofNat_natAbs_of_nonpos hx, ← @Int.cast_inj (ℤ√d) _ _,
              Int.cast_neg, norm_eq_mul_conj, neg_mul_eq_mul_neg, eq_comm] at h⟩,
    fun h => by
    let ⟨y, hy⟩ := isUnit_iff_dvd_one.1 h
    have := congr_arg (Int.natAbs ∘ norm) hy
    rw [Function.comp_apply, Function.comp_apply, norm_mul, Int.natAbs_mul, norm_one,
      Int.natAbs_one, eq_comm, mul_eq_one] at this
    exact this.1⟩
#align zsqrtd.norm_eq_one_iff Zsqrtd.norm_eq_one_iff

/- warning: zsqrtd.is_unit_iff_norm_is_unit -> Zsqrtd.isUnit_iff_norm_isUnit is a dubious translation:
lean 3 declaration is
  forall {d : Int} (z : Zsqrtd d), Iff (IsUnit.{0} (Zsqrtd d) (Zsqrtd.monoid d) z) (IsUnit.{0} Int Int.monoid (Zsqrtd.norm d z))
but is expected to have type
  forall {d : Int} (z : Zsqrtd d), Iff (IsUnit.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d) z) (IsUnit.{0} Int Int.instMonoidInt (Zsqrtd.norm d z))
Case conversion may be inaccurate. Consider using '#align zsqrtd.is_unit_iff_norm_is_unit Zsqrtd.isUnit_iff_norm_isUnitₓ'. -/
theorem isUnit_iff_norm_isUnit {d : ℤ} (z : ℤ√d) : IsUnit z ↔ IsUnit z.norm := by
  rw [Int.isUnit_iff_natAbs_eq, norm_eq_one_iff]
#align zsqrtd.is_unit_iff_norm_is_unit Zsqrtd.isUnit_iff_norm_isUnit

/- warning: zsqrtd.norm_eq_one_iff' -> Zsqrtd.norm_eq_one_iff' is a dubious translation:
lean 3 declaration is
  forall {d : Int}, (LE.le.{0} Int Int.hasLe d (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (forall (z : Zsqrtd d), Iff (Eq.{1} Int (Zsqrtd.norm d z) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (IsUnit.{0} (Zsqrtd d) (Zsqrtd.monoid d) z))
but is expected to have type
  forall {d : Int}, (LE.le.{0} Int Int.instLEInt d (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (forall (z : Zsqrtd d), Iff (Eq.{1} Int (Zsqrtd.norm d z) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (IsUnit.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d) z))
Case conversion may be inaccurate. Consider using '#align zsqrtd.norm_eq_one_iff' Zsqrtd.norm_eq_one_iff'ₓ'. -/
theorem norm_eq_one_iff' {d : ℤ} (hd : d ≤ 0) (z : ℤ√d) : z.norm = 1 ↔ IsUnit z := by
  rw [← norm_eq_one_iff, ← Int.coe_nat_inj', Int.natAbs_of_nonneg (norm_nonneg hd z), Int.ofNat_one]
#align zsqrtd.norm_eq_one_iff' Zsqrtd.norm_eq_one_iff'

#print Zsqrtd.norm_eq_zero_iff /-
theorem norm_eq_zero_iff {d : ℤ} (hd : d < 0) (z : ℤ√d) : z.norm = 0 ↔ z = 0 :=
  by
  constructor
  · intro h
    rw [ext, zero_re, zero_im]
    rw [norm_def, sub_eq_add_neg, mul_assoc] at h
    have left := mul_self_nonneg z.re
    have right := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg z.im))
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff' left right).mp h
    constructor <;> apply eq_zero_of_mul_self_eq_zero
    · exact ha
    · rw [neg_eq_zero, mul_eq_zero] at hb
      exact hb.resolve_left hd.ne
  · rintro rfl
    exact norm_zero
#align zsqrtd.norm_eq_zero_iff Zsqrtd.norm_eq_zero_iff
-/

/- warning: zsqrtd.norm_eq_of_associated -> Zsqrtd.norm_eq_of_associated is a dubious translation:
lean 3 declaration is
  forall {d : Int}, (LE.le.{0} Int Int.hasLe d (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (forall {x : Zsqrtd d} {y : Zsqrtd d}, (Associated.{0} (Zsqrtd d) (Zsqrtd.monoid d) x y) -> (Eq.{1} Int (Zsqrtd.norm d x) (Zsqrtd.norm d y)))
but is expected to have type
  forall {d : Int}, (LE.le.{0} Int Int.instLEInt d (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (forall {x : Zsqrtd d} {y : Zsqrtd d}, (Associated.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d) x y) -> (Eq.{1} Int (Zsqrtd.norm d x) (Zsqrtd.norm d y)))
Case conversion may be inaccurate. Consider using '#align zsqrtd.norm_eq_of_associated Zsqrtd.norm_eq_of_associatedₓ'. -/
theorem norm_eq_of_associated {d : ℤ} (hd : d ≤ 0) {x y : ℤ√d} (h : Associated x y) :
    x.norm = y.norm := by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul, (norm_eq_one_iff' hd _).mpr u.is_unit, mul_one]
#align zsqrtd.norm_eq_of_associated Zsqrtd.norm_eq_of_associated

end Norm

end

section

parameter {d : ℕ}

#print Zsqrtd.Nonneg /-
/-- Nonnegativity of an element of `ℤ√d`. -/
def Nonneg : ℤ√d → Prop
  | ⟨a, b⟩ => Nonnegg d 1 a b
#align zsqrtd.nonneg Zsqrtd.Nonneg
-/

instance : LE (ℤ√d) :=
  ⟨fun a b => nonneg (b - a)⟩

instance : LT (ℤ√d) :=
  ⟨fun a b => ¬b ≤ a⟩

#print Zsqrtd.decidableNonnegg /-
instance decidableNonnegg (c d a b) : Decidable (Nonnegg c d a b) := by
  cases a <;> cases b <;> repeat' rw [Int.ofNat_eq_coe] <;> unfold nonnegg sq_le <;> infer_instance
#align zsqrtd.decidable_nonnegg Zsqrtd.decidableNonnegg
-/

#print Zsqrtd.decidableNonneg /-
instance decidableNonneg : ∀ a : ℤ√d, Decidable (nonneg a)
  | ⟨a, b⟩ => Zsqrtd.decidableNonnegg _ _ _ _
#align zsqrtd.decidable_nonneg Zsqrtd.decidableNonneg
-/

/- warning: zsqrtd.decidable_le -> Zsqrtd.decidableLE is a dubious translation:
lean 3 declaration is
  forall {d : Nat}, DecidableRel.{1} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d))
but is expected to have type
  forall {d : Nat}, DecidableRel.{1} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (fun (x._@.Mathlib.NumberTheory.Zsqrtd.Basic._hyg.7357 : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (x._@.Mathlib.NumberTheory.Zsqrtd.Basic._hyg.7359 : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) => LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) x._@.Mathlib.NumberTheory.Zsqrtd.Basic._hyg.7357 x._@.Mathlib.NumberTheory.Zsqrtd.Basic._hyg.7359)
Case conversion may be inaccurate. Consider using '#align zsqrtd.decidable_le Zsqrtd.decidableLEₓ'. -/
instance decidableLE : @DecidableRel (ℤ√d) (· ≤ ·) := fun _ _ => decidable_nonneg _
#align zsqrtd.decidable_le Zsqrtd.decidableLE

#print Zsqrtd.nonneg_cases /-
theorem nonneg_cases : ∀ {a : ℤ√d}, nonneg a → ∃ x y : ℕ, a = ⟨x, y⟩ ∨ a = ⟨x, -y⟩ ∨ a = ⟨-x, y⟩
  | ⟨(x : ℕ), (y : ℕ)⟩, h => ⟨x, y, Or.inl rfl⟩
  | ⟨(x : ℕ), -[y+1]⟩, h => ⟨x, y + 1, Or.inr <| Or.inl rfl⟩
  | ⟨-[x+1], (y : ℕ)⟩, h => ⟨x + 1, y, Or.inr <| Or.inr rfl⟩
  | ⟨-[x+1], -[y+1]⟩, h => False.elim h
#align zsqrtd.nonneg_cases Zsqrtd.nonneg_cases
-/

#print Zsqrtd.nonneg_add_lem /-
theorem nonneg_add_lem {x y z w : ℕ} (xy : nonneg ⟨x, -y⟩) (zw : nonneg ⟨-z, w⟩) :
    nonneg (⟨x, -y⟩ + ⟨-z, w⟩) :=
  have : nonneg ⟨Int.subNatNat x z, Int.subNatNat w y⟩ :=
    Int.subNatNat_elim x z
      (fun m n i => SqLe y d m 1 → SqLe n 1 w d → nonneg ⟨i, Int.subNatNat w y⟩)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d (k + j) 1 → SqLe k 1 m d → nonneg ⟨Int.ofNat j, i⟩)
          (fun m n xy zw => trivial) fun m n xy zw => sqLe_cancel zw xy)
      (fun j k =>
        Int.subNatNat_elim w y
          (fun m n i => SqLe n d k 1 → SqLe (k + j + 1) 1 m d → nonneg ⟨-[j+1], i⟩)
          (fun m n xy zw => sqLe_cancel xy zw) fun m n xy zw =>
          let t := Nat.le_trans zw (sqLe_of_le (Nat.le_add_right n (m + 1)) le_rfl xy)
          have : k + j + 1 ≤ k :=
            Nat.mul_self_le_mul_self_iff.2 (by repeat' rw [one_mul] at t <;> exact t)
          absurd this (not_le_of_gt <| Nat.succ_le_succ <| Nat.le_add_right _ _))
      (nonnegg_pos_neg.1 xy) (nonnegg_neg_pos.1 zw)
  show nonneg ⟨_, _⟩ by
    rw [neg_add_eq_sub] <;> rwa [Int.subNatNat_eq_coe, Int.subNatNat_eq_coe] at this
#align zsqrtd.nonneg_add_lem Zsqrtd.nonneg_add_lem
-/

#print Zsqrtd.Nonneg.add /-
theorem Nonneg.add {a b : ℤ√d} (ha : nonneg a) (hb : nonneg b) : nonneg (a + b) :=
  by
  rcases nonneg_cases ha with ⟨x, y, rfl | rfl | rfl⟩ <;>
    rcases nonneg_cases hb with ⟨z, w, rfl | rfl | rfl⟩
  · trivial
  · refine' nonnegg_cases_right fun i h => sq_le_of_le _ _ (nonnegg_pos_neg.1 hb)
    · exact Int.ofNat_le.1 (le_of_neg_le_neg (@Int.le.intro _ _ y (by simp [add_comm, *])))
    · apply Nat.le_add_left
  · refine' nonnegg_cases_left fun i h => sq_le_of_le _ _ (nonnegg_neg_pos.1 hb)
    · exact Int.ofNat_le.1 (le_of_neg_le_neg (@Int.le.intro _ _ x (by simp [add_comm, *])))
    · apply Nat.le_add_left
  · refine' nonnegg_cases_right fun i h => sq_le_of_le _ _ (nonnegg_pos_neg.1 ha)
    · exact Int.ofNat_le.1 (le_of_neg_le_neg (@Int.le.intro _ _ w (by simp [*])))
    · apply Nat.le_add_right
  ·
    simpa [add_comm] using
      nonnegg_pos_neg.2 (sq_le_add (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
  · exact nonneg_add_lem ha hb
  · refine' nonnegg_cases_left fun i h => sq_le_of_le _ _ (nonnegg_neg_pos.1 ha)
    · exact Int.ofNat_le.1 (le_of_neg_le_neg (Int.le.intro h))
    · apply Nat.le_add_right
  · dsimp
    rw [add_comm, add_comm ↑y]
    exact nonneg_add_lem hb ha
  ·
    simpa [add_comm] using
      nonnegg_neg_pos.2 (sq_le_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
#align zsqrtd.nonneg.add Zsqrtd.Nonneg.add
-/

/- warning: zsqrtd.nonneg_iff_zero_le -> Zsqrtd.nonneg_iff_zero_le is a dubious translation:
lean 3 declaration is
  forall {d : Nat} {a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)}, Iff (Zsqrtd.Nonneg d a) (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) (OfNat.ofNat.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (OfNat.mk.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (Zero.zero.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasZero ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))))) a)
but is expected to have type
  forall {d : Nat} {a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)}, Iff (Zsqrtd.Nonneg d a) (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) (OfNat.ofNat.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) 0 (Zero.toOfNat0.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instZeroZsqrtd (Nat.cast.{0} Int instNatCastInt d)))) a)
Case conversion may be inaccurate. Consider using '#align zsqrtd.nonneg_iff_zero_le Zsqrtd.nonneg_iff_zero_leₓ'. -/
theorem nonneg_iff_zero_le {a : ℤ√d} : nonneg a ↔ 0 ≤ a :=
  show _ ↔ nonneg _ by simp
#align zsqrtd.nonneg_iff_zero_le Zsqrtd.nonneg_iff_zero_le

/- warning: zsqrtd.le_of_le_le -> Zsqrtd.le_of_le_le is a dubious translation:
lean 3 declaration is
  forall {d : Nat} {x : Int} {y : Int} {z : Int} {w : Int}, (LE.le.{0} Int Int.hasLe x z) -> (LE.le.{0} Int Int.hasLe y w) -> (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) (Zsqrtd.mk ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d) x y) (Zsqrtd.mk ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d) z w))
but is expected to have type
  forall {d : Nat} {x : Int} {y : Int} {z : Int} {w : Int}, (LE.le.{0} Int Int.instLEInt x z) -> (LE.le.{0} Int Int.instLEInt y w) -> (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) (Zsqrtd.mk (Nat.cast.{0} Int instNatCastInt d) x y) (Zsqrtd.mk (Nat.cast.{0} Int instNatCastInt d) z w))
Case conversion may be inaccurate. Consider using '#align zsqrtd.le_of_le_le Zsqrtd.le_of_le_leₓ'. -/
theorem le_of_le_le {x y z w : ℤ} (xz : x ≤ z) (yw : y ≤ w) : (⟨x, y⟩ : ℤ√d) ≤ ⟨z, w⟩ :=
  show nonneg ⟨z - x, w - y⟩ from
    match z - x, w - y, Int.le.dest_sub xz, Int.le.dest_sub yw with
    | _, _, ⟨a, rfl⟩, ⟨b, rfl⟩ => trivial
#align zsqrtd.le_of_le_le Zsqrtd.le_of_le_le

#print Zsqrtd.nonneg_total /-
protected theorem nonneg_total : ∀ a : ℤ√d, nonneg a ∨ nonneg (-a)
  | ⟨(x : ℕ), (y : ℕ)⟩ => Or.inl trivial
  | ⟨-[x+1], -[y+1]⟩ => Or.inr trivial
  | ⟨0, -[y+1]⟩ => Or.inr trivial
  | ⟨-[x+1], 0⟩ => Or.inr trivial
  | ⟨(x + 1 : ℕ), -[y+1]⟩ => Nat.le_total
  | ⟨-[x+1], (y + 1 : ℕ)⟩ => Nat.le_total
#align zsqrtd.nonneg_total Zsqrtd.nonneg_total
-/

/- warning: zsqrtd.le_total -> Zsqrtd.le_total is a dubious translation:
lean 3 declaration is
  forall {d : Nat} (a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (b : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), Or (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) a b) (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) b a)
but is expected to have type
  forall {d : Nat} (a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (b : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), Or (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) a b) (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) b a)
Case conversion may be inaccurate. Consider using '#align zsqrtd.le_total Zsqrtd.le_totalₓ'. -/
protected theorem le_total (a b : ℤ√d) : a ≤ b ∨ b ≤ a :=
  by
  have t := (b - a).nonneg_total
  rwa [neg_sub] at t
#align zsqrtd.le_total Zsqrtd.le_total

instance : Preorder (ℤ√d) where
  le := (· ≤ ·)
  le_refl a := show nonneg (a - a) by simp only [sub_self]
  le_trans a b c hab hbc := by simpa [sub_add_sub_cancel'] using hab.add hbc
  lt := (· < ·)
  lt_iff_le_not_le a b := (and_iff_right_of_imp (Zsqrtd.le_total _ _).resolve_left).symm

/- warning: zsqrtd.le_arch -> Zsqrtd.le_arch is a dubious translation:
lean 3 declaration is
  forall {d : Nat} (a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), Exists.{1} Nat (fun (n : Nat) => LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) a ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (HasLiftT.mk.{1, 1} Nat (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (CoeTCₓ.coe.{1, 1} Nat (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Nat.castCoe.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (AddMonoidWithOne.toNatCast.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (AddGroupWithOne.toAddMonoidWithOne.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.addGroupWithOne ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))))))) n))
but is expected to have type
  forall {d : Nat} (a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), Exists.{1} Nat (fun (n : Nat) => LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) a (Nat.cast.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (NonAssocRing.toNatCast.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Ring.toNonAssocRing.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instRingZsqrtd (Nat.cast.{0} Int instNatCastInt d)))) n))
Case conversion may be inaccurate. Consider using '#align zsqrtd.le_arch Zsqrtd.le_archₓ'. -/
theorem le_arch (a : ℤ√d) : ∃ n : ℕ, a ≤ n :=
  by
  let ⟨x, y, (h : a ≤ ⟨x, y⟩)⟩ :=
    show ∃ x y : ℕ, nonneg (⟨x, y⟩ + -a) from
      match -a with
      | ⟨Int.ofNat x, Int.ofNat y⟩ => ⟨0, 0, trivial⟩
      | ⟨Int.ofNat x, -[y+1]⟩ => ⟨0, y + 1, by simp [Int.negSucc_coe, add_assoc]⟩
      | ⟨-[x+1], Int.ofNat y⟩ => ⟨x + 1, 0, by simp [Int.negSucc_coe, add_assoc]⟩
      | ⟨-[x+1], -[y+1]⟩ => ⟨x + 1, y + 1, by simp [Int.negSucc_coe, add_assoc]⟩
  refine' ⟨x + d * y, h.trans _⟩
  change nonneg ⟨↑x + d * y - ↑x, 0 - ↑y⟩
  cases' y with y
  · simp
  have h : ∀ y, sq_le y d (d * y) 1 := fun y => by
    simpa [sq_le, mul_comm, mul_left_comm] using Nat.mul_le_mul_right (y * y) (Nat.le_mul_self d)
  rw [show (x : ℤ) + d * Nat.succ y - x = d * Nat.succ y by simp]
  exact h (y + 1)
#align zsqrtd.le_arch Zsqrtd.le_arch

/- warning: zsqrtd.add_le_add_left -> Zsqrtd.add_le_add_left is a dubious translation:
lean 3 declaration is
  forall {d : Nat} (a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (b : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) a b) -> (forall (c : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) (HAdd.hAdd.{0, 0, 0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (instHAdd.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))) c a) (HAdd.hAdd.{0, 0, 0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (instHAdd.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))) c b))
but is expected to have type
  forall {d : Nat} (a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (b : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) a b) -> (forall (c : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) (HAdd.hAdd.{0, 0, 0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (instHAdd.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instAddZsqrtd (Nat.cast.{0} Int instNatCastInt d))) c a) (HAdd.hAdd.{0, 0, 0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (instHAdd.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instAddZsqrtd (Nat.cast.{0} Int instNatCastInt d))) c b))
Case conversion may be inaccurate. Consider using '#align zsqrtd.add_le_add_left Zsqrtd.add_le_add_leftₓ'. -/
protected theorem add_le_add_left (a b : ℤ√d) (ab : a ≤ b) (c : ℤ√d) : c + a ≤ c + b :=
  show nonneg _ by rw [add_sub_add_left_eq_sub] <;> exact ab
#align zsqrtd.add_le_add_left Zsqrtd.add_le_add_left

/- warning: zsqrtd.le_of_add_le_add_left -> Zsqrtd.le_of_add_le_add_left is a dubious translation:
lean 3 declaration is
  forall {d : Nat} (a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (b : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (c : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) (HAdd.hAdd.{0, 0, 0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (instHAdd.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))) c a) (HAdd.hAdd.{0, 0, 0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (instHAdd.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))) c b)) -> (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) a b)
but is expected to have type
  forall {d : Nat} (a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (b : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (c : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) (HAdd.hAdd.{0, 0, 0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (instHAdd.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instAddZsqrtd (Nat.cast.{0} Int instNatCastInt d))) c a) (HAdd.hAdd.{0, 0, 0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (instHAdd.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instAddZsqrtd (Nat.cast.{0} Int instNatCastInt d))) c b)) -> (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) a b)
Case conversion may be inaccurate. Consider using '#align zsqrtd.le_of_add_le_add_left Zsqrtd.le_of_add_le_add_leftₓ'. -/
protected theorem le_of_add_le_add_left (a b c : ℤ√d) (h : c + a ≤ c + b) : a ≤ b := by
  simpa using Zsqrtd.add_le_add_left _ _ h (-c)
#align zsqrtd.le_of_add_le_add_left Zsqrtd.le_of_add_le_add_left

/- warning: zsqrtd.add_lt_add_left -> Zsqrtd.add_lt_add_left is a dubious translation:
lean 3 declaration is
  forall {d : Nat} (a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (b : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), (LT.lt.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLt d) a b) -> (forall (c : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), LT.lt.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLt d) (HAdd.hAdd.{0, 0, 0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (instHAdd.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))) c a) (HAdd.hAdd.{0, 0, 0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (instHAdd.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))) c b))
but is expected to have type
  forall {d : Nat} (a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (b : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), (LT.lt.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLTZsqrtdCastIntInstNatCastInt d) a b) -> (forall (c : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), LT.lt.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLTZsqrtdCastIntInstNatCastInt d) (HAdd.hAdd.{0, 0, 0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (instHAdd.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instAddZsqrtd (Nat.cast.{0} Int instNatCastInt d))) c a) (HAdd.hAdd.{0, 0, 0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (instHAdd.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instAddZsqrtd (Nat.cast.{0} Int instNatCastInt d))) c b))
Case conversion may be inaccurate. Consider using '#align zsqrtd.add_lt_add_left Zsqrtd.add_lt_add_leftₓ'. -/
protected theorem add_lt_add_left (a b : ℤ√d) (h : a < b) (c) : c + a < c + b := fun h' =>
  h (Zsqrtd.le_of_add_le_add_left _ _ _ h')
#align zsqrtd.add_lt_add_left Zsqrtd.add_lt_add_left

#print Zsqrtd.nonneg_smul /-
theorem nonneg_smul {a : ℤ√d} {n : ℕ} (ha : nonneg a) : nonneg (n * a) := by
  simp (config := { singlePass := true }) only [← Int.cast_ofNat] <;>
    exact
      match a, nonneg_cases ha, ha with
      | _, ⟨x, y, Or.inl rfl⟩, ha => by rw [smul_val] <;> trivial
      | _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ha => by
        rw [smul_val] <;> simpa using nonnegg_pos_neg.2 (sq_le_smul n <| nonnegg_pos_neg.1 ha)
      | _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ha => by
        rw [smul_val] <;> simpa using nonnegg_neg_pos.2 (sq_le_smul n <| nonnegg_neg_pos.1 ha)
#align zsqrtd.nonneg_smul Zsqrtd.nonneg_smul
-/

#print Zsqrtd.nonneg_muld /-
theorem nonneg_muld {a : ℤ√d} (ha : nonneg a) : nonneg (sqrtd * a) := by
  refine'
    match a, nonneg_cases ha, ha with
    | _, ⟨x, y, Or.inl rfl⟩, ha => trivial
    | _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ha => by
      simp <;> apply nonnegg_neg_pos.2 <;>
        simpa [sq_le, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_pos_neg.1 ha)
    | _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ha => by
      simp <;> apply nonnegg_pos_neg.2 <;>
        simpa [sq_le, mul_comm, mul_left_comm] using Nat.mul_le_mul_left d (nonnegg_neg_pos.1 ha)
#align zsqrtd.nonneg_muld Zsqrtd.nonneg_muld
-/

#print Zsqrtd.nonneg_mul_lem /-
theorem nonneg_mul_lem {x y : ℕ} {a : ℤ√d} (ha : nonneg a) : nonneg (⟨x, y⟩ * a) :=
  by
  have : (⟨x, y⟩ * a : ℤ√d) = x * a + sqrtd * (y * a) := by
    rw [decompose, right_distrib, mul_assoc] <;> rfl
  rw [this] <;> exact (nonneg_smul ha).add (nonneg_muld <| nonneg_smul ha)
#align zsqrtd.nonneg_mul_lem Zsqrtd.nonneg_mul_lem
-/

#print Zsqrtd.nonneg_mul /-
theorem nonneg_mul {a b : ℤ√d} (ha : nonneg a) (hb : nonneg b) : nonneg (a * b) :=
  match a, b, nonneg_cases ha, nonneg_cases hb, ha, hb with
  | _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, hb => trivial
  | _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, ha, hb => nonneg_mul_lem hb
  | _, _, ⟨x, y, Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, ha, hb => nonneg_mul_lem hb
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, hb => by
    rw [mul_comm] <;> exact nonneg_mul_lem ha
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inl rfl⟩, ha, hb => by
    rw [mul_comm] <;> exact nonneg_mul_lem ha
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨-x, y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨x * z + d * y * w, -(x * w + y * z)⟩ := by simp [add_comm]
          ] <;>
      exact nonnegg_pos_neg.2 (sq_le_mul.left (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
  | _, _, ⟨x, y, Or.inr <| Or.inr rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨-x, y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨-(x * z + d * y * w), x * w + y * z⟩ := by simp [add_comm]
          ] <;>
      exact nonnegg_neg_pos.2 (sq_le_mul.right.left (nonnegg_neg_pos.1 ha) (nonnegg_pos_neg.1 hb))
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inr rfl⟩, ha, hb => by
    rw [calc
          (⟨x, -y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨-(x * z + d * y * w), x * w + y * z⟩ := by simp [add_comm]
          ] <;>
      exact
        nonnegg_neg_pos.2 (sq_le_mul.right.right.left (nonnegg_pos_neg.1 ha) (nonnegg_neg_pos.1 hb))
  | _, _, ⟨x, y, Or.inr <| Or.inl rfl⟩, ⟨z, w, Or.inr <| Or.inl rfl⟩, ha, hb => by
    rw [calc
          (⟨x, -y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ := rfl
          _ = ⟨x * z + d * y * w, -(x * w + y * z)⟩ := by simp [add_comm]
          ] <;>
      exact
        nonnegg_pos_neg.2
          (sq_le_mul.right.right.right (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
#align zsqrtd.nonneg_mul Zsqrtd.nonneg_mul
-/

/- warning: zsqrtd.mul_nonneg -> Zsqrtd.mul_nonneg is a dubious translation:
lean 3 declaration is
  forall {d : Nat} (a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (b : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) (OfNat.ofNat.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (OfNat.mk.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (Zero.zero.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasZero ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))))) a) -> (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) (OfNat.ofNat.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (OfNat.mk.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (Zero.zero.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasZero ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))))) b) -> (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) (OfNat.ofNat.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (OfNat.mk.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (Zero.zero.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasZero ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))))) (HMul.hMul.{0, 0, 0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (instHMul.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasMul ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))) a b))
but is expected to have type
  forall {d : Nat} (a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (b : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) (OfNat.ofNat.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) 0 (Zero.toOfNat0.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instZeroZsqrtd (Nat.cast.{0} Int instNatCastInt d)))) a) -> (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) (OfNat.ofNat.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) 0 (Zero.toOfNat0.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instZeroZsqrtd (Nat.cast.{0} Int instNatCastInt d)))) b) -> (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) (OfNat.ofNat.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) 0 (Zero.toOfNat0.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instZeroZsqrtd (Nat.cast.{0} Int instNatCastInt d)))) (HMul.hMul.{0, 0, 0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (instHMul.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instMulZsqrtd (Nat.cast.{0} Int instNatCastInt d))) a b))
Case conversion may be inaccurate. Consider using '#align zsqrtd.mul_nonneg Zsqrtd.mul_nonnegₓ'. -/
protected theorem mul_nonneg (a b : ℤ√d) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
  repeat' rw [← nonneg_iff_zero_le] <;> exact nonneg_mul
#align zsqrtd.mul_nonneg Zsqrtd.mul_nonneg

#print Zsqrtd.not_sqLe_succ /-
theorem not_sqLe_succ (c d y) (h : 0 < c) : ¬SqLe (y + 1) c 0 d :=
  not_le_of_gt <| mul_pos (mul_pos h <| Nat.succ_pos _) <| Nat.succ_pos _
#align zsqrtd.not_sq_le_succ Zsqrtd.not_sqLe_succ
-/

#print Zsqrtd.Nonsquare /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`ns] [] -/
/-- A nonsquare is a natural number that is not equal to the square of an
  integer. This is implemented as a typeclass because it's a necessary condition
  for much of the Pell equation theory. -/
class Nonsquare (x : ℕ) : Prop where
  ns : ∀ n : ℕ, x ≠ n * n
#align zsqrtd.nonsquare Zsqrtd.Nonsquare
-/

parameter [dnsq : Nonsquare d]

include dnsq

#print Zsqrtd.d_pos /-
theorem d_pos : 0 < d :=
  lt_of_le_of_ne (Nat.zero_le _) <| Ne.symm <| Nonsquare.ns d 0
#align zsqrtd.d_pos Zsqrtd.d_pos
-/

#print Zsqrtd.divides_sq_eq_zero /-
theorem divides_sq_eq_zero {x y} (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
  let g := x.gcd y
  Or.elim g.eq_zero_or_pos
    (fun H => ⟨Nat.eq_zero_of_gcd_eq_zero_left H, Nat.eq_zero_of_gcd_eq_zero_right H⟩) fun gpos =>
    False.elim <|
      by
      let ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := Nat.exists_coprime gpos
      rw [hx, hy] at h
      have : m * m = d * (n * n) :=
        mul_left_cancel₀ (mul_pos gpos gpos).ne' (by simpa [mul_comm, mul_left_comm] using h)
      have co2 :=
        let co1 := co.mul_right co
        co1.mul co1
      exact
        nonsquare.ns d m
          (Nat.dvd_antisymm (by rw [this] <;> apply dvd_mul_right) <|
            co2.dvd_of_dvd_mul_right <| by simp [this])
#align zsqrtd.divides_sq_eq_zero Zsqrtd.divides_sq_eq_zero
-/

#print Zsqrtd.divides_sq_eq_zero_z /-
theorem divides_sq_eq_zero_z {x y : ℤ} (h : x * x = d * y * y) : x = 0 ∧ y = 0 := by
  rw [mul_assoc, ← Int.natAbs_mul_self, ← Int.natAbs_mul_self, ← Int.ofNat_mul, ← mul_assoc] at
      h <;>
    exact
      let ⟨h1, h2⟩ := divides_sq_eq_zero (Int.ofNat.inj h)
      ⟨Int.eq_zero_of_natAbs_eq_zero h1, Int.eq_zero_of_natAbs_eq_zero h2⟩
#align zsqrtd.divides_sq_eq_zero_z Zsqrtd.divides_sq_eq_zero_z
-/

#print Zsqrtd.not_divides_sq /-
theorem not_divides_sq (x y) : (x + 1) * (x + 1) ≠ d * (y + 1) * (y + 1) := fun e => by
  have t := (divides_sq_eq_zero e).left <;> contradiction
#align zsqrtd.not_divides_sq Zsqrtd.not_divides_sq
-/

#print Zsqrtd.nonneg_antisymm /-
theorem nonneg_antisymm : ∀ {a : ℤ√d}, nonneg a → nonneg (-a) → a = 0
  | ⟨0, 0⟩, xy, yx => rfl
  | ⟨-[x+1], -[y+1]⟩, xy, yx => False.elim xy
  | ⟨(x + 1 : Nat), (y + 1 : Nat)⟩, xy, yx => False.elim yx
  | ⟨-[x+1], 0⟩, xy, yx => absurd xy (not_sqLe_succ _ _ _ (by decide))
  | ⟨(x + 1 : Nat), 0⟩, xy, yx => absurd yx (not_sqLe_succ _ _ _ (by decide))
  | ⟨0, -[y+1]⟩, xy, yx => absurd xy (not_sqLe_succ _ _ _ d_pos)
  | ⟨0, (y + 1 : Nat)⟩, _, yx => absurd yx (not_sqLe_succ _ _ _ d_pos)
  | ⟨(x + 1 : Nat), -[y+1]⟩, (xy : sq_le _ _ _ _), (yx : sq_le _ _ _ _) =>
    by
    let t := le_antisymm yx xy
    rw [one_mul] at t <;> exact absurd t (not_divides_sq _ _)
  | ⟨-[x+1], (y + 1 : Nat)⟩, (xy : sq_le _ _ _ _), (yx : sq_le _ _ _ _) =>
    by
    let t := le_antisymm xy yx
    rw [one_mul] at t <;> exact absurd t (not_divides_sq _ _)
#align zsqrtd.nonneg_antisymm Zsqrtd.nonneg_antisymm
-/

/- warning: zsqrtd.le_antisymm -> Zsqrtd.le_antisymm is a dubious translation:
lean 3 declaration is
  forall {d : Nat} [dnsq : Zsqrtd.Nonsquare d] {a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)} {b : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)}, (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) a b) -> (LE.le.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLe d) b a) -> (Eq.{1} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) a b)
but is expected to have type
  forall {d : Nat} [dnsq : Zsqrtd.Nonsquare d] {a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)} {b : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)}, (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) a b) -> (LE.le.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLEZsqrtdCastIntInstNatCastInt d) b a) -> (Eq.{1} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) a b)
Case conversion may be inaccurate. Consider using '#align zsqrtd.le_antisymm Zsqrtd.le_antisymmₓ'. -/
theorem le_antisymm {a b : ℤ√d} (ab : a ≤ b) (ba : b ≤ a) : a = b :=
  eq_of_sub_eq_zero <| nonneg_antisymm ba (by rw [neg_sub] <;> exact ab)
#align zsqrtd.le_antisymm Zsqrtd.le_antisymm

instance : LinearOrder (ℤ√d) :=
  { Zsqrtd.preorder with
    le_antisymm := @Zsqrtd.le_antisymm
    le_total := Zsqrtd.le_total
    decidableLe := Zsqrtd.decidableLE }

#print Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero /-
protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : ℤ√d}, a * b = 0 → a = 0 ∨ b = 0
  | ⟨x, y⟩, ⟨z, w⟩, h => by
    injection h with h1 h2 <;>
      exact
        have h1 : x * z = -(d * y * w) := eq_neg_of_add_eq_zero_left h1
        have h2 : x * w = -(y * z) := eq_neg_of_add_eq_zero_left h2
        have fin : x * x = d * y * y → (⟨x, y⟩ : ℤ√d) = 0 := fun e =>
          match x, y, divides_sq_eq_zero_z e with
          | _, _, ⟨rfl, rfl⟩ => rfl
        if z0 : z = 0 then
          if w0 : w = 0 then
            Or.inr
              (match z, w, z0, w0 with
              | _, _, rfl, rfl => rfl)
          else
            Or.inl <|
              Fin <|
                mul_right_cancel₀ w0 <|
                  calc
                    x * x * w = -y * (x * z) := by simp [h2, mul_assoc, mul_left_comm]
                    _ = d * y * y * w := by simp [h1, mul_assoc, mul_left_comm]
                    
        else
          Or.inl <|
            Fin <|
              mul_right_cancel₀ z0 <|
                calc
                  x * x * z = d * -y * (x * w) := by simp [h1, mul_assoc, mul_left_comm]
                  _ = d * y * y * z := by simp [h2, mul_assoc, mul_left_comm]
                  
#align zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero
-/

instance : NoZeroDivisors (ℤ√d)
    where eq_zero_or_eq_zero_of_mul_eq_zero := @Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero

instance : IsDomain (ℤ√d) :=
  NoZeroDivisors.to_isDomain _

/- warning: zsqrtd.mul_pos -> Zsqrtd.mul_pos is a dubious translation:
lean 3 declaration is
  forall {d : Nat} [dnsq : Zsqrtd.Nonsquare d] (a : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (b : Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)), (LT.lt.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLt d) (OfNat.ofNat.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (OfNat.mk.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (Zero.zero.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasZero ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))))) a) -> (LT.lt.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLt d) (OfNat.ofNat.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (OfNat.mk.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (Zero.zero.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasZero ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))))) b) -> (LT.lt.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasLt d) (OfNat.ofNat.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (OfNat.mk.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) 0 (Zero.zero.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasZero ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))))) (HMul.hMul.{0, 0, 0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (instHMul.{0} (Zsqrtd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (Zsqrtd.hasMul ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))) a b))
but is expected to have type
  forall {d : Nat} [dnsq : Zsqrtd.Nonsquare d] (a : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (b : Zsqrtd (Nat.cast.{0} Int instNatCastInt d)), (LT.lt.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLTZsqrtdCastIntInstNatCastInt d) (OfNat.ofNat.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) 0 (Zero.toOfNat0.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instZeroZsqrtd (Nat.cast.{0} Int instNatCastInt d)))) a) -> (LT.lt.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLTZsqrtdCastIntInstNatCastInt d) (OfNat.ofNat.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) 0 (Zero.toOfNat0.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instZeroZsqrtd (Nat.cast.{0} Int instNatCastInt d)))) b) -> (LT.lt.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instLTZsqrtdCastIntInstNatCastInt d) (OfNat.ofNat.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) 0 (Zero.toOfNat0.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instZeroZsqrtd (Nat.cast.{0} Int instNatCastInt d)))) (HMul.hMul.{0, 0, 0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (instHMul.{0} (Zsqrtd (Nat.cast.{0} Int instNatCastInt d)) (Zsqrtd.instMulZsqrtd (Nat.cast.{0} Int instNatCastInt d))) a b))
Case conversion may be inaccurate. Consider using '#align zsqrtd.mul_pos Zsqrtd.mul_posₓ'. -/
protected theorem mul_pos (a b : ℤ√d) (a0 : 0 < a) (b0 : 0 < b) : 0 < a * b := fun ab =>
  Or.elim
    (eq_zero_or_eq_zero_of_mul_eq_zero
      (le_antisymm ab (mul_nonneg _ _ (le_of_lt a0) (le_of_lt b0))))
    (fun e => ne_of_gt a0 e) fun e => ne_of_gt b0 e
#align zsqrtd.mul_pos Zsqrtd.mul_pos

instance : LinearOrderedCommRing (ℤ√d) :=
  { Zsqrtd.commRing, Zsqrtd.linearOrder,
    Zsqrtd.nontrivial with
    add_le_add_left := @Zsqrtd.add_le_add_left
    mul_pos := @Zsqrtd.mul_pos
    zero_le_one := by decide }

instance : LinearOrderedRing (ℤ√d) := by infer_instance

instance : OrderedRing (ℤ√d) := by infer_instance

end

#print Zsqrtd.norm_eq_zero /-
theorem norm_eq_zero {d : ℤ} (h_nonsquare : ∀ n : ℤ, d ≠ n * n) (a : ℤ√d) : norm a = 0 ↔ a = 0 :=
  by
  refine' ⟨fun ha => ext.mpr _, fun h => by rw [h, norm_zero]⟩
  delta norm at ha
  rw [sub_eq_zero] at ha
  by_cases h : 0 ≤ d
  · obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le h
    haveI : nonsquare d' := ⟨fun n h => h_nonsquare n <| by exact_mod_cast h⟩
    exact divides_sq_eq_zero_z ha
  · push_neg  at h
    suffices a.re * a.re = 0 by
      rw [eq_zero_of_mul_self_eq_zero this] at ha⊢
      simpa only [true_and_iff, or_self_right, zero_re, zero_im, eq_self_iff_true, zero_eq_mul,
        MulZeroClass.mul_zero, mul_eq_zero, h.ne, false_or_iff, or_self_iff] using ha
    apply _root_.le_antisymm _ (mul_self_nonneg _)
    rw [ha, mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg h.le (mul_self_nonneg _)
#align zsqrtd.norm_eq_zero Zsqrtd.norm_eq_zero
-/

variable {R : Type}

/- warning: zsqrtd.hom_ext -> Zsqrtd.hom_ext is a dubious translation:
lean 3 declaration is
  forall {R : Type} [_inst_1 : Ring.{0} R] {d : Int} (f : RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (g : RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))), (Eq.{1} R (coeFn.{1, 1} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (fun (_x : RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) => (Zsqrtd d) -> R) (RingHom.hasCoeToFun.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) f (Zsqrtd.sqrtd d)) (coeFn.{1, 1} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (fun (_x : RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) => (Zsqrtd d) -> R) (RingHom.hasCoeToFun.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) g (Zsqrtd.sqrtd d))) -> (Eq.{1} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) f g)
but is expected to have type
  forall {R : Type} [_inst_1 : Ring.{0} R] {d : Int} (f : RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (g : RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))), (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Zsqrtd d) => R) (Zsqrtd.sqrtd d)) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (Zsqrtd d) (fun (_x : Zsqrtd d) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Zsqrtd d) => R) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (Zsqrtd d) R (NonUnitalNonAssocSemiring.toMul.{0} (Zsqrtd d) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))))) (NonUnitalNonAssocSemiring.toMul.{0} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} R (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (Zsqrtd d) R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} R (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1)) (RingHom.instRingHomClassRingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1)))))) f (Zsqrtd.sqrtd d)) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (Zsqrtd d) (fun (_x : Zsqrtd d) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Zsqrtd d) => R) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (Zsqrtd d) R (NonUnitalNonAssocSemiring.toMul.{0} (Zsqrtd d) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))))) (NonUnitalNonAssocSemiring.toMul.{0} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} R (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (Zsqrtd d) R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} R (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1)) (RingHom.instRingHomClassRingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1)))))) g (Zsqrtd.sqrtd d))) -> (Eq.{1} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R _inst_1))) f g)
Case conversion may be inaccurate. Consider using '#align zsqrtd.hom_ext Zsqrtd.hom_extₓ'. -/
@[ext]
theorem hom_ext [Ring R] {d : ℤ} (f g : ℤ√d →+* R) (h : f sqrtd = g sqrtd) : f = g :=
  by
  ext ⟨x_re, x_im⟩
  simp [decompose, h]
#align zsqrtd.hom_ext Zsqrtd.hom_ext

variable [CommRing R]

/- warning: zsqrtd.lift -> Zsqrtd.lift is a dubious translation:
lean 3 declaration is
  forall {R : Type} [_inst_1 : CommRing.{0} R] {d : Int}, Equiv.{1, 1} (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (Distrib.toHasMul.{0} R (Ring.toDistrib.{0} R (CommRing.toRing.{0} R _inst_1)))) r r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int R (HasLiftT.mk.{1, 1} Int R (CoeTCₓ.coe.{1, 1} Int R (Int.castCoe.{0} R (AddGroupWithOne.toHasIntCast.{0} R (AddCommGroupWithOne.toAddGroupWithOne.{0} R (Ring.toAddCommGroupWithOne.{0} R (CommRing.toRing.{0} R _inst_1))))))) d))) (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))
but is expected to have type
  forall {R : Type} [_inst_1 : CommRing.{0} R] {d : Int}, Equiv.{1, 1} (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align zsqrtd.lift Zsqrtd.liftₓ'. -/
/-- The unique `ring_hom` from `ℤ√d` to a ring `R`, constructed by replacing `√d` with the provided
root. Conversely, this associates to every mapping `ℤ√d →+* R` a value of `√d` in `R`. -/
@[simps]
def lift {d : ℤ} : { r : R // r * r = ↑d } ≃ (ℤ√d →+* R)
    where
  toFun r :=
    { toFun := fun a => a.1 + a.2 * (r : R)
      map_zero' := by simp
      map_add' := fun a b => by
        simp
        ring
      map_one' := by simp
      map_mul' := fun a b =>
        by
        have :
          (a.re + a.im * r : R) * (b.re + b.im * r) =
            a.re * b.re + (a.re * b.im + a.im * b.re) * r + a.im * b.im * (r * r) :=
          by ring
        simp [this, r.prop]
        ring }
  invFun f := ⟨f sqrtd, by rw [← f.map_mul, dmuld, map_intCast]⟩
  left_inv r := by
    ext
    simp
  right_inv f := by
    ext
    simp
#align zsqrtd.lift Zsqrtd.lift

/- warning: zsqrtd.lift_injective -> Zsqrtd.lift_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type} [_inst_1 : CommRing.{0} R] [_inst_2 : CharZero.{0} R (AddGroupWithOne.toAddMonoidWithOne.{0} R (AddCommGroupWithOne.toAddGroupWithOne.{0} R (Ring.toAddCommGroupWithOne.{0} R (CommRing.toRing.{0} R _inst_1))))] {d : Int} (r : Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (Distrib.toHasMul.{0} R (Ring.toDistrib.{0} R (CommRing.toRing.{0} R _inst_1)))) r r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int R (HasLiftT.mk.{1, 1} Int R (CoeTCₓ.coe.{1, 1} Int R (Int.castCoe.{0} R (AddGroupWithOne.toHasIntCast.{0} R (AddCommGroupWithOne.toAddGroupWithOne.{0} R (Ring.toAddCommGroupWithOne.{0} R (CommRing.toRing.{0} R _inst_1))))))) d))), (forall (n : Int), Ne.{1} Int d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) n n)) -> (Function.Injective.{1, 1} (Zsqrtd d) R (coeFn.{1, 1} (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) (fun (_x : RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) => (Zsqrtd d) -> R) (RingHom.hasCoeToFun.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) (coeFn.{1, 1} (Equiv.{1, 1} (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (Distrib.toHasMul.{0} R (Ring.toDistrib.{0} R (CommRing.toRing.{0} R _inst_1)))) r r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int R (HasLiftT.mk.{1, 1} Int R (CoeTCₓ.coe.{1, 1} Int R (Int.castCoe.{0} R (AddGroupWithOne.toHasIntCast.{0} R (AddCommGroupWithOne.toAddGroupWithOne.{0} R (Ring.toAddCommGroupWithOne.{0} R (CommRing.toRing.{0} R _inst_1))))))) d))) (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) (fun (_x : Equiv.{1, 1} (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (Distrib.toHasMul.{0} R (Ring.toDistrib.{0} R (CommRing.toRing.{0} R _inst_1)))) r r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int R (HasLiftT.mk.{1, 1} Int R (CoeTCₓ.coe.{1, 1} Int R (Int.castCoe.{0} R (AddGroupWithOne.toHasIntCast.{0} R (AddCommGroupWithOne.toAddGroupWithOne.{0} R (Ring.toAddCommGroupWithOne.{0} R (CommRing.toRing.{0} R _inst_1))))))) d))) (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) => (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (Distrib.toHasMul.{0} R (Ring.toDistrib.{0} R (CommRing.toRing.{0} R _inst_1)))) r r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int R (HasLiftT.mk.{1, 1} Int R (CoeTCₓ.coe.{1, 1} Int R (Int.castCoe.{0} R (AddGroupWithOne.toHasIntCast.{0} R (AddCommGroupWithOne.toAddGroupWithOne.{0} R (Ring.toAddCommGroupWithOne.{0} R (CommRing.toRing.{0} R _inst_1))))))) d))) -> (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) (Equiv.hasCoeToFun.{1, 1} (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (Distrib.toHasMul.{0} R (Ring.toDistrib.{0} R (CommRing.toRing.{0} R _inst_1)))) r r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int R (HasLiftT.mk.{1, 1} Int R (CoeTCₓ.coe.{1, 1} Int R (Int.castCoe.{0} R (AddGroupWithOne.toHasIntCast.{0} R (AddCommGroupWithOne.toAddGroupWithOne.{0} R (Ring.toAddCommGroupWithOne.{0} R (CommRing.toRing.{0} R _inst_1))))))) d))) (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) (Zsqrtd.lift R _inst_1 d) r)))
but is expected to have type
  forall {R : Type} [_inst_1 : CommRing.{0} R] [_inst_2 : CharZero.{0} R (AddGroupWithOne.toAddMonoidWithOne.{0} R (Ring.toAddGroupWithOne.{0} R (CommRing.toRing.{0} R _inst_1)))] {d : Int} (r : Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))), (forall (n : Int), Ne.{1} Int d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) n n)) -> (Function.Injective.{1, 1} (Zsqrtd d) R (FunLike.coe.{1, 1, 1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) => RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) r) (Zsqrtd d) (fun (_x : Zsqrtd d) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Zsqrtd d) => R) _x) (MulHomClass.toFunLike.{0, 0, 0} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) => RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) r) (Zsqrtd d) R (NonUnitalNonAssocSemiring.toMul.{0} (Zsqrtd d) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))))) (NonUnitalNonAssocSemiring.toMul.{0} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} R (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) => RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) r) (Zsqrtd d) R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} R (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) => RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) r) (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))) (RingHom.instRingHomClassRingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))))) (FunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) (fun (_x : Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) => RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1)))) _x) (Equiv.instFunLikeEquiv.{1, 1} (Subtype.{1} R (fun (r : R) => Eq.{1} R (HMul.hMul.{0, 0, 0} R R R (instHMul.{0} R (NonUnitalNonAssocRing.toMul.{0} R (NonAssocRing.toNonUnitalNonAssocRing.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) r r) (Int.cast.{0} R (Ring.toIntCast.{0} R (CommRing.toRing.{0} R _inst_1)) d))) (RingHom.{0, 0} (Zsqrtd d) R (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))) (NonAssocRing.toNonAssocSemiring.{0} R (Ring.toNonAssocRing.{0} R (CommRing.toRing.{0} R _inst_1))))) (Zsqrtd.lift R _inst_1 d) r)))
Case conversion may be inaccurate. Consider using '#align zsqrtd.lift_injective Zsqrtd.lift_injectiveₓ'. -/
/-- `lift r` is injective if `d` is non-square, and R has characteristic zero (that is, the map from
`ℤ` into `R` is injective). -/
theorem lift_injective [CharZero R] {d : ℤ} (r : { r : R // r * r = ↑d })
    (hd : ∀ n : ℤ, d ≠ n * n) : Function.Injective (lift r) :=
  (injective_iff_map_eq_zero (lift r)).mpr fun a ha =>
    by
    have h_inj : Function.Injective (coe : ℤ → R) := Int.cast_injective
    suffices lift r a.norm = 0
      by
      simp only [coe_int_re, add_zero, lift_apply_apply, coe_int_im, Int.cast_zero,
        MulZeroClass.zero_mul] at this
      rwa [← Int.cast_zero, h_inj.eq_iff, norm_eq_zero hd] at this
    rw [norm_eq_mul_conj, RingHom.map_mul, ha, MulZeroClass.zero_mul]
#align zsqrtd.lift_injective Zsqrtd.lift_injective

/- warning: zsqrtd.norm_eq_one_iff_mem_unitary -> Zsqrtd.norm_eq_one_iff_mem_unitary is a dubious translation:
lean 3 declaration is
  forall {d : Int} {a : Zsqrtd d}, Iff (Eq.{1} Int (Zsqrtd.norm d a) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (Membership.Mem.{0, 0} (Zsqrtd d) (Submonoid.{0} (Zsqrtd d) (Monoid.toMulOneClass.{0} (Zsqrtd d) (Zsqrtd.monoid d))) (SetLike.hasMem.{0, 0} (Submonoid.{0} (Zsqrtd d) (Monoid.toMulOneClass.{0} (Zsqrtd d) (Zsqrtd.monoid d))) (Zsqrtd d) (Submonoid.setLike.{0} (Zsqrtd d) (Monoid.toMulOneClass.{0} (Zsqrtd d) (Zsqrtd.monoid d)))) a (unitary.{0} (Zsqrtd d) (Zsqrtd.monoid d) (StarRing.toStarSemigroup.{0} (Zsqrtd d) (NonUnitalRing.toNonUnitalSemiring.{0} (Zsqrtd d) (NonUnitalCommRing.toNonUnitalRing.{0} (Zsqrtd d) (CommRing.toNonUnitalCommRing.{0} (Zsqrtd d) (Zsqrtd.commRing d)))) (Zsqrtd.starRing d))))
but is expected to have type
  forall {d : Int} {a : Zsqrtd d}, Iff (Eq.{1} Int (Zsqrtd.norm d a) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Membership.mem.{0, 0} (Zsqrtd d) (Submonoid.{0} (Zsqrtd d) (Monoid.toMulOneClass.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d))) (SetLike.instMembership.{0, 0} (Submonoid.{0} (Zsqrtd d) (Monoid.toMulOneClass.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d))) (Zsqrtd d) (Submonoid.instSetLikeSubmonoid.{0} (Zsqrtd d) (Monoid.toMulOneClass.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d)))) a (unitary.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d) (StarRing.toStarSemigroup.{0} (Zsqrtd d) (NonUnitalRing.toNonUnitalSemiring.{0} (Zsqrtd d) (NonUnitalCommRing.toNonUnitalRing.{0} (Zsqrtd d) (CommRing.toNonUnitalCommRing.{0} (Zsqrtd d) (Zsqrtd.commRing d)))) (Zsqrtd.instStarRingZsqrtdToNonUnitalSemiringToNonUnitalRingToNonUnitalCommRingCommRing d))))
Case conversion may be inaccurate. Consider using '#align zsqrtd.norm_eq_one_iff_mem_unitary Zsqrtd.norm_eq_one_iff_mem_unitaryₓ'. -/
/-- An element of `ℤ√d` has norm equal to `1` if and only if it is contained in the submonoid
of unitary elements. -/
theorem norm_eq_one_iff_mem_unitary {d : ℤ} {a : ℤ√d} : a.norm = 1 ↔ a ∈ unitary (ℤ√d) :=
  by
  rw [unitary.mem_iff_self_mul_star, ← norm_eq_mul_conj]
  norm_cast
#align zsqrtd.norm_eq_one_iff_mem_unitary Zsqrtd.norm_eq_one_iff_mem_unitary

/- warning: zsqrtd.mker_norm_eq_unitary -> Zsqrtd.mker_norm_eq_unitary is a dubious translation:
lean 3 declaration is
  forall {d : Int}, Eq.{1} (Submonoid.{0} (Zsqrtd d) (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d)))))) (MonoidHom.mker.{0, 0, 0} (Zsqrtd d) Int (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (MonoidHom.{0, 0} (Zsqrtd d) Int (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))))) (MonoidHom.monoidHomClass.{0, 0} (Zsqrtd d) Int (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.ring d))))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))))) (Zsqrtd.normMonoidHom d)) (unitary.{0} (Zsqrtd d) (Zsqrtd.monoid d) (StarRing.toStarSemigroup.{0} (Zsqrtd d) (NonUnitalRing.toNonUnitalSemiring.{0} (Zsqrtd d) (NonUnitalCommRing.toNonUnitalRing.{0} (Zsqrtd d) (CommRing.toNonUnitalCommRing.{0} (Zsqrtd d) (Zsqrtd.commRing d)))) (Zsqrtd.starRing d)))
but is expected to have type
  forall {d : Int}, Eq.{1} (Submonoid.{0} (Zsqrtd d) (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d)))))) (MonoidHom.mker.{0, 0, 0} (Zsqrtd d) Int (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (MonoidHom.{0, 0} (Zsqrtd d) Int (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MonoidHom.monoidHomClass.{0, 0} (Zsqrtd d) Int (MulZeroOneClass.toMulOneClass.{0} (Zsqrtd d) (NonAssocSemiring.toMulZeroOneClass.{0} (Zsqrtd d) (NonAssocRing.toNonAssocSemiring.{0} (Zsqrtd d) (Ring.toNonAssocRing.{0} (Zsqrtd d) (Zsqrtd.instRingZsqrtd d))))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (Zsqrtd.normMonoidHom d)) (unitary.{0} (Zsqrtd d) (Zsqrtd.instMonoidZsqrtd d) (StarRing.toStarSemigroup.{0} (Zsqrtd d) (NonUnitalRing.toNonUnitalSemiring.{0} (Zsqrtd d) (NonUnitalCommRing.toNonUnitalRing.{0} (Zsqrtd d) (CommRing.toNonUnitalCommRing.{0} (Zsqrtd d) (Zsqrtd.commRing d)))) (Zsqrtd.instStarRingZsqrtdToNonUnitalSemiringToNonUnitalRingToNonUnitalCommRingCommRing d)))
Case conversion may be inaccurate. Consider using '#align zsqrtd.mker_norm_eq_unitary Zsqrtd.mker_norm_eq_unitaryₓ'. -/
/-- The kernel of the norm map on `ℤ√d` equals the submonoid of unitary elements. -/
theorem mker_norm_eq_unitary {d : ℤ} : (@normMonoidHom d).mker = unitary (ℤ√d) :=
  Submonoid.ext fun x => norm_eq_one_iff_mem_unitary
#align zsqrtd.mker_norm_eq_unitary Zsqrtd.mker_norm_eq_unitary

end Zsqrtd

