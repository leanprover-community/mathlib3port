/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich
-/
import Data.Vector.Basic
import Data.Nat.Pow

#align_import data.bitvec.core from "leanprover-community/mathlib"@"a11f9106a169dd302a285019e5165f8ab32ff433"

/-!
# Basic operations on bitvectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This is a work-in-progress, and contains additions to other theories.

This file was moved to mathlib from core Lean in the switch to Lean 3.20.0c.
It is not fully in compliance with mathlib style standards.
-/


#print Std.BitVec /-
/-- `bitvec n` is a `vector` of `bool` with length `n`. -/
@[reducible]
def Std.BitVec (n : ℕ) :=
  Vector Bool n
#align bitvec Std.BitVec
-/

namespace Std.BitVec

open Nat

open Vector

local infixl:65 "++ₜ" => Vector.append

#print Std.BitVec.zero /-
/-- Create a zero bitvector -/
@[reducible]
protected def Std.BitVec.zero (n : ℕ) : Std.BitVec n :=
  replicate n false
#align bitvec.zero Std.BitVec.zero
-/

#print Std.BitVec.one /-
/-- Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/
@[reducible]
protected def Std.BitVec.one : ∀ n : ℕ, Std.BitVec n
  | 0 => nil
  | succ n => replicate n false++ₜtrue ::ᵥ nil
#align bitvec.one Std.BitVec.one
-/

#print Std.BitVec.cast /-
/-- Create a bitvector from another with a provably equal length. -/
protected def Std.BitVec.cast {a b : ℕ} (h : a = b) : Std.BitVec a → Std.BitVec b
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩
#align bitvec.cong Std.BitVec.cast
-/

#print Std.BitVec.append /-
/-- `bitvec` specific version of `vector.append` -/
def Std.BitVec.append {m n} : Std.BitVec m → Std.BitVec n → Std.BitVec (m + n) :=
  Vector.append
#align bitvec.append Std.BitVec.append
-/

/-! ### Shift operations -/


section Shift

variable {n : ℕ}

#print Std.BitVec.shiftLeft /-
/-- `shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `ff`.
If `x.length < i` then this will return the all-`ff`s bitvector. -/
def Std.BitVec.shiftLeft (x : Std.BitVec n) (i : ℕ) : Std.BitVec n :=
  Std.BitVec.cast (by simp) <| drop i x++ₜreplicate (min n i) false
#align bitvec.shl Std.BitVec.shiftLeft
-/

/-- `fill_shr x i fill` is the bitvector obtained by right-shifting `x` `i` times and then
padding with `fill : bool`. If `x.length < i` then this will return the constant `fill`
bitvector. -/
def Std.BitVec.fillShr (x : Std.BitVec n) (i : ℕ) (fill : Bool) : Std.BitVec n :=
  Std.BitVec.cast
      (by
        by_cases i ≤ n
        · have h₁ := Nat.sub_le n i
          rw [min_eq_right h]
          rw [min_eq_left h₁, ← add_tsub_assoc_of_le h, Nat.add_comm, add_tsub_cancel_right]
        · have h₁ := le_of_not_ge h
          rw [min_eq_left h₁, tsub_eq_zero_iff_le.mpr h₁, zero_min, Nat.add_zero]) <|
    replicate (min n i) fill++ₜtake (n - i) x
#align bitvec.fill_shr Std.BitVec.fillShr

#print Std.BitVec.ushiftRight /-
/-- unsigned shift right -/
def Std.BitVec.ushiftRight (x : Std.BitVec n) (i : ℕ) : Std.BitVec n :=
  Std.BitVec.fillShr x i false
#align bitvec.ushr Std.BitVec.ushiftRight
-/

#print Std.BitVec.sshiftRight /-
/-- signed shift right -/
def Std.BitVec.sshiftRight : ∀ {m : ℕ}, Std.BitVec m → ℕ → Std.BitVec m
  | 0, _, _ => nil
  | succ m, x, i => head x ::ᵥ Std.BitVec.fillShr (tail x) i (head x)
#align bitvec.sshr Std.BitVec.sshiftRight
-/

end Shift

/-! ### Bitwise operations -/


section Bitwise

variable {n : ℕ}

#print Std.BitVec.not /-
/-- bitwise not -/
def Std.BitVec.not : Std.BitVec n → Std.BitVec n :=
  map not
#align bitvec.not Std.BitVec.not
-/

#print Std.BitVec.and /-
/-- bitwise and -/
def Std.BitVec.and : Std.BitVec n → Std.BitVec n → Std.BitVec n :=
  map₂ and
#align bitvec.and Std.BitVec.and
-/

#print Std.BitVec.or /-
/-- bitwise or -/
def Std.BitVec.or : Std.BitVec n → Std.BitVec n → Std.BitVec n :=
  map₂ or
#align bitvec.or Std.BitVec.or
-/

#print Std.BitVec.xor /-
/-- bitwise xor -/
def Std.BitVec.xor : Std.BitVec n → Std.BitVec n → Std.BitVec n :=
  map₂ xor
#align bitvec.xor Std.BitVec.xor
-/

end Bitwise

/-! ### Arithmetic operators -/


section Arith

variable {n : ℕ}

#print Bool.xor3 /-
/-- `xor3 x y c` is `((x XOR y) XOR c)`. -/
protected def xor3 (x y c : Bool) :=
  xor (xor x y) c
#align bitvec.xor3 Bool.xor3
-/

#print Bool.carry /-
/-- `carry x y c` is `x && y || x && c || y && c`. -/
protected def carry (x y c : Bool) :=
  x && y || x && c || y && c
#align bitvec.carry Bool.carry
-/

#print Std.BitVec.neg /-
/-- `neg x` is the two's complement of `x`. -/
protected def Std.BitVec.neg (x : Std.BitVec n) : Std.BitVec n :=
  let f y c := (y || c, xor y c)
  Prod.snd (mapAccumr f x false)
#align bitvec.neg Std.BitVec.neg
-/

#print Std.BitVec.adc /-
/-- Add with carry (no overflow) -/
def Std.BitVec.adc (x y : Std.BitVec n) (c : Bool) : Std.BitVec (n + 1) :=
  let f x y c := (Bool.carry x y c, Bool.xor3 x y c)
  let ⟨c, z⟩ := Vector.mapAccumr₂ f x y c
  c ::ᵥ z
#align bitvec.adc Std.BitVec.adc
-/

#print Std.BitVec.add /-
/-- The sum of two bitvectors -/
protected def Std.BitVec.add (x y : Std.BitVec n) : Std.BitVec n :=
  tail (Std.BitVec.adc x y false)
#align bitvec.add Std.BitVec.add
-/

#print Std.BitVec.sbb /-
/-- Subtract with borrow -/
def Std.BitVec.sbb (x y : Std.BitVec n) (b : Bool) : Bool × Std.BitVec n :=
  let f x y c := (Bool.carry (not x) y c, Bool.xor3 x y c)
  Vector.mapAccumr₂ f x y b
#align bitvec.sbb Std.BitVec.sbb
-/

#print Std.BitVec.sub /-
/-- The difference of two bitvectors -/
protected def Std.BitVec.sub (x y : Std.BitVec n) : Std.BitVec n :=
  Prod.snd (Std.BitVec.sbb x y false)
#align bitvec.sub Std.BitVec.sub
-/

instance : Zero (Std.BitVec n) :=
  ⟨Std.BitVec.zero n⟩

instance : One (Std.BitVec n) :=
  ⟨Std.BitVec.one n⟩

instance : Add (Std.BitVec n) :=
  ⟨Std.BitVec.add⟩

instance : Sub (Std.BitVec n) :=
  ⟨Std.BitVec.sub⟩

instance : Neg (Std.BitVec n) :=
  ⟨Std.BitVec.neg⟩

#print Std.BitVec.mul /-
/-- The product of two bitvectors -/
protected def Std.BitVec.mul (x y : Std.BitVec n) : Std.BitVec n :=
  let f r b := cond b (r + r + y) (r + r)
  (toList x).foldl f 0
#align bitvec.mul Std.BitVec.mul
-/

instance : Mul (Std.BitVec n) :=
  ⟨Std.BitVec.mul⟩

end Arith

/-! ### Comparison operators -/


section Comparison

variable {n : ℕ}

#print Std.BitVec.ult /-
/-- `uborrow x y` returns `tt` iff the "subtract with borrow" operation on `x`, `y` and `ff`
required a borrow. -/
def Std.BitVec.ult (x y : Std.BitVec n) : Bool :=
  Prod.fst (Std.BitVec.sbb x y false)
#align bitvec.uborrow Std.BitVec.ult
-/

/- warning: bitvec.ult clashes with bitvec.uborrow -> Std.BitVec.ult
Case conversion may be inaccurate. Consider using '#align bitvec.ult Std.BitVec.ultₓ'. -/
#print Std.BitVec.ult /-
/-- unsigned less-than proposition -/
def Std.BitVec.ult (x y : Std.BitVec n) : Prop :=
  Std.BitVec.ult x y
#align bitvec.ult Std.BitVec.ult
-/

#print Std.BitVec.ugt /-
/-- unsigned greater-than proposition -/
def Std.BitVec.ugt (x y : Std.BitVec n) : Prop :=
  Std.BitVec.ult y x
#align bitvec.ugt Std.BitVec.ugt
-/

#print Std.BitVec.ule /-
/-- unsigned less-than-or-equal-to proposition -/
def Std.BitVec.ule (x y : Std.BitVec n) : Prop :=
  ¬Std.BitVec.ult y x
#align bitvec.ule Std.BitVec.ule
-/

#print Std.BitVec.uge /-
/-- unsigned greater-than-or-equal-to proposition -/
def Std.BitVec.uge (x y : Std.BitVec n) : Prop :=
  Std.BitVec.ule y x
#align bitvec.uge Std.BitVec.uge
-/

#print Std.BitVec.slt /-
/-- `sborrow x y` returns `tt` iff `x < y` as two's complement integers -/
def Std.BitVec.slt : ∀ {n : ℕ}, Std.BitVec n → Std.BitVec n → Bool
  | 0, _, _ => false
  | succ n, x, y =>
    match (head x, head y) with
    | (tt, ff) => true
    | (ff, tt) => false
    | _ => Std.BitVec.ult (tail x) (tail y)
#align bitvec.sborrow Std.BitVec.slt
-/

/- warning: bitvec.slt clashes with bitvec.sborrow -> Std.BitVec.slt
Case conversion may be inaccurate. Consider using '#align bitvec.slt Std.BitVec.sltₓ'. -/
#print Std.BitVec.slt /-
/-- signed less-than proposition -/
def Std.BitVec.slt (x y : Std.BitVec n) : Prop :=
  Std.BitVec.slt x y
#align bitvec.slt Std.BitVec.slt
-/

#print Std.BitVec.sgt /-
/-- signed greater-than proposition -/
def Std.BitVec.sgt (x y : Std.BitVec n) : Prop :=
  Std.BitVec.slt y x
#align bitvec.sgt Std.BitVec.sgt
-/

#print Std.BitVec.sle /-
/-- signed less-than-or-equal-to proposition -/
def Std.BitVec.sle (x y : Std.BitVec n) : Prop :=
  ¬Std.BitVec.slt y x
#align bitvec.sle Std.BitVec.sle
-/

#print Std.BitVec.sge /-
/-- signed greater-than-or-equal-to proposition -/
def Std.BitVec.sge (x y : Std.BitVec n) : Prop :=
  Std.BitVec.sle y x
#align bitvec.sge Std.BitVec.sge
-/

end Comparison

/-! ### Conversion to `nat` and `int` -/


section Conversion

variable {α : Type}

#print Std.BitVec.ofNat /-
/-- Create a bitvector from a `nat` -/
protected def Std.BitVec.ofNat : ∀ n : ℕ, Nat → Std.BitVec n
  | 0, x => nil
  | succ n, x => of_nat n (x / 2)++ₜdecide (x % 2 = 1) ::ᵥ nil
#align bitvec.of_nat Std.BitVec.ofNat
-/

#print Std.BitVec.ofInt /-
/-- Create a bitvector in the two's complement representation from an `int` -/
protected def Std.BitVec.ofInt : ∀ n : ℕ, Int → Std.BitVec (succ n)
  | n, Int.ofNat m => false ::ᵥ Std.BitVec.ofNat n m
  | n, Int.negSucc m => true ::ᵥ Std.BitVec.not (Std.BitVec.ofNat n m)
#align bitvec.of_int Std.BitVec.ofInt
-/

#print Std.BitVec.addLsb /-
/-- `add_lsb r b` is `r + r + 1` if `b` is `tt` and `r + r` otherwise. -/
def Std.BitVec.addLsb (r : ℕ) (b : Bool) :=
  r + r + cond b 1 0
#align bitvec.add_lsb Std.BitVec.addLsb
-/

/-- Given a `list` of `bool`s, return the `nat` they represent as a list of binary digits. -/
def Std.BitVec.bitsToNat (v : List Bool) : Nat :=
  v.foldl Std.BitVec.addLsb 0
#align bitvec.bits_to_nat Std.BitVec.bitsToNat

#print Std.BitVec.toNat /-
/-- Return the natural number encoded by the input bitvector -/
protected def Std.BitVec.toNat {n : Nat} (v : Std.BitVec n) : Nat :=
  Std.BitVec.bitsToNat (toList v)
#align bitvec.to_nat Std.BitVec.toNat
-/

theorem Std.BitVec.bitsToNat_toList {n : ℕ} (x : Std.BitVec n) :
    Std.BitVec.toNat x = Std.BitVec.bitsToNat (Vector.toList x) :=
  rfl
#align bitvec.bits_to_nat_to_list Std.BitVec.bitsToNat_toList

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

attribute [local simp] Nat.zero_add Nat.add_zero Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero

#print Std.BitVec.toNat_append /-
-- mul_left_comm
theorem Std.BitVec.toNat_append {m : ℕ} (xs : Std.BitVec m) (b : Bool) :
    Std.BitVec.toNat (xs++ₜb ::ᵥ nil) = Std.BitVec.toNat xs * 2 + Std.BitVec.toNat (b ::ᵥ nil) :=
  by
  cases' xs with xs P
  simp [bits_to_nat_to_list]; clear P
  unfold bits_to_nat List.foldl
  -- generalize the accumulator of foldl
  generalize h : 0 = x;
  conv in add_lsb x b => rw [← h]; clear h
  simp
  induction' xs with x xs generalizing x
  · simp; unfold List.foldl add_lsb; simp [Nat.mul_succ]
  · simp; apply xs_ih
#align bitvec.to_nat_append Std.BitVec.toNat_append
-/

theorem Std.BitVec.bits_toNat_decide (n : ℕ) :
    Std.BitVec.toNat (decide (n % 2 = 1) ::ᵥ nil) = n % 2 :=
  by
  simp [bits_to_nat_to_list]
  unfold bits_to_nat add_lsb List.foldl cond
  simp [cond_to_bool_mod_two]
#align bitvec.bits_to_nat_to_bool Std.BitVec.bits_toNat_decide

theorem Std.BitVec.ofNat_succ {k n : ℕ} :
    Std.BitVec.ofNat (succ k) n = Std.BitVec.ofNat k (n / 2)++ₜdecide (n % 2 = 1) ::ᵥ nil :=
  rfl
#align bitvec.of_nat_succ Std.BitVec.ofNat_succ

#print Std.BitVec.toNat_ofNat /-
theorem Std.BitVec.toNat_ofNat {k n : ℕ} : Std.BitVec.toNat (Std.BitVec.ofNat k n) = n % 2 ^ k :=
  by
  induction' k with k ih generalizing n
  · simp [Nat.mod_one]; rfl
  · rw [of_nat_succ, to_nat_append, ih, bits_to_nat_to_bool, mod_pow_succ, Nat.mul_comm]
#align bitvec.to_nat_of_nat Std.BitVec.toNat_ofNat
-/

#print Std.BitVec.toInt /-
/-- Return the integer encoded by the input bitvector -/
protected def Std.BitVec.toInt : ∀ {n : Nat}, Std.BitVec n → Int
  | 0, _ => 0
  | succ n, v =>
    cond (head v) (Int.negSucc <| Std.BitVec.toNat <| Std.BitVec.not <| tail v)
      (Int.ofNat <| Std.BitVec.toNat <| tail v)
#align bitvec.to_int Std.BitVec.toInt
-/

end Conversion

/-! ### Miscellaneous instances -/


private def repr {n : Nat} : Std.BitVec n → String
  | ⟨bs, p⟩ => "0b" ++ (bs.map fun b : Bool => if b then '1' else '0').asString

instance (n : Nat) : Repr (Std.BitVec n) :=
  ⟨repr⟩

end Std.BitVec

instance {n} {x y : Std.BitVec n} : Decidable (Std.BitVec.ult x y) :=
  Bool.decidableEq _ _

instance {n} {x y : Std.BitVec n} : Decidable (Std.BitVec.ugt x y) :=
  Bool.decidableEq _ _

