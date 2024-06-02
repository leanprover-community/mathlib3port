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


#print BitVec /-
/-- `bitvec n` is a `vector` of `bool` with length `n`. -/
@[reducible]
def BitVec (n : ℕ) :=
  Vector Bool n
#align bitvec BitVec
-/

namespace BitVec

open Nat

open Vector

local infixl:65 "++ₜ" => Vector.append

#print BitVec.zero /-
/-- Create a zero bitvector -/
@[reducible]
protected def zero (n : ℕ) : BitVec n :=
  replicate n false
#align bitvec.zero BitVec.zero
-/

/-- Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/
@[reducible]
protected def one : ∀ n : ℕ, BitVec n
  | 0 => nil
  | succ n => replicate n false++ₜtrue ::ᵥ nil
#align bitvec.one BitVec.one

#print BitVec.cast /-
/-- Create a bitvector from another with a provably equal length. -/
protected def cast {a b : ℕ} (h : a = b) : BitVec a → BitVec b
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩
#align bitvec.cong BitVec.cast
-/

#print BitVec.append /-
/-- `bitvec` specific version of `vector.append` -/
def append {m n} : BitVec m → BitVec n → BitVec (m + n) :=
  Vector.append
#align bitvec.append BitVec.append
-/

/-! ### Shift operations -/


section Shift

variable {n : ℕ}

#print BitVec.shiftLeft /-
/-- `shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `ff`.
If `x.length < i` then this will return the all-`ff`s bitvector. -/
def shiftLeft (x : BitVec n) (i : ℕ) : BitVec n :=
  BitVec.cast (by simp) <| drop i x++ₜreplicate (min n i) false
#align bitvec.shl BitVec.shiftLeft
-/

/-- `fill_shr x i fill` is the bitvector obtained by right-shifting `x` `i` times and then
padding with `fill : bool`. If `x.length < i` then this will return the constant `fill`
bitvector. -/
def fillShr (x : BitVec n) (i : ℕ) (fill : Bool) : BitVec n :=
  BitVec.cast
      (by
        by_cases i ≤ n
        · have h₁ := Nat.sub_le n i
          rw [min_eq_right h]
          rw [min_eq_left h₁, ← add_tsub_assoc_of_le h, Nat.add_comm, add_tsub_cancel_right]
        · have h₁ := le_of_not_ge h
          rw [min_eq_left h₁, tsub_eq_zero_iff_le.mpr h₁, zero_min, Nat.add_zero]) <|
    replicate (min n i) fill++ₜtake (n - i) x
#align bitvec.fill_shr BitVec.fillShr

#print BitVec.ushiftRight /-
/-- unsigned shift right -/
def ushiftRight (x : BitVec n) (i : ℕ) : BitVec n :=
  fillShr x i false
#align bitvec.ushr BitVec.ushiftRight
-/

#print BitVec.sshiftRight /-
/-- signed shift right -/
def sshiftRight : ∀ {m : ℕ}, BitVec m → ℕ → BitVec m
  | 0, _, _ => nil
  | succ m, x, i => head x ::ᵥ fillShr (tail x) i (head x)
#align bitvec.sshr BitVec.sshiftRight
-/

end Shift

/-! ### Bitwise operations -/


section Bitwise

variable {n : ℕ}

#print BitVec.not /-
/-- bitwise not -/
def not : BitVec n → BitVec n :=
  map not
#align bitvec.not BitVec.not
-/

#print BitVec.and /-
/-- bitwise and -/
def and : BitVec n → BitVec n → BitVec n :=
  map₂ and
#align bitvec.and BitVec.and
-/

#print BitVec.or /-
/-- bitwise or -/
def or : BitVec n → BitVec n → BitVec n :=
  map₂ or
#align bitvec.or BitVec.or
-/

#print BitVec.xor /-
/-- bitwise xor -/
def xor : BitVec n → BitVec n → BitVec n :=
  map₂ xor
#align bitvec.xor BitVec.xor
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

#print BitVec.neg /-
/-- `neg x` is the two's complement of `x`. -/
protected def neg (x : BitVec n) : BitVec n :=
  let f y c := (y || c, xor y c)
  Prod.snd (mapAccumr f x false)
#align bitvec.neg BitVec.neg
-/

#print BitVec.adc /-
/-- Add with carry (no overflow) -/
def adc (x y : BitVec n) (c : Bool) : BitVec (n + 1) :=
  let f x y c := (Bool.carry x y c, Bool.xor3 x y c)
  let ⟨c, z⟩ := Vector.mapAccumr₂ f x y c
  c ::ᵥ z
#align bitvec.adc BitVec.adc
-/

#print BitVec.add /-
/-- The sum of two bitvectors -/
protected def add (x y : BitVec n) : BitVec n :=
  tail (adc x y false)
#align bitvec.add BitVec.add
-/

/-- Subtract with borrow -/
def sbb (x y : BitVec n) (b : Bool) : Bool × BitVec n :=
  let f x y c := (Bool.carry (not x) y c, Bool.xor3 x y c)
  Vector.mapAccumr₂ f x y b
#align bitvec.sbb BitVec.sbb

#print BitVec.sub /-
/-- The difference of two bitvectors -/
protected def sub (x y : BitVec n) : BitVec n :=
  Prod.snd (sbb x y false)
#align bitvec.sub BitVec.sub
-/

instance : Zero (BitVec n) :=
  ⟨BitVec.zero n⟩

instance : One (BitVec n) :=
  ⟨BitVec.one n⟩

instance : Add (BitVec n) :=
  ⟨BitVec.add⟩

instance : Sub (BitVec n) :=
  ⟨BitVec.sub⟩

instance : Neg (BitVec n) :=
  ⟨BitVec.neg⟩

#print BitVec.mul /-
/-- The product of two bitvectors -/
protected def mul (x y : BitVec n) : BitVec n :=
  let f r b := cond b (r + r + y) (r + r)
  (toList x).foldl f 0
#align bitvec.mul BitVec.mul
-/

instance : Mul (BitVec n) :=
  ⟨BitVec.mul⟩

end Arith

/-! ### Comparison operators -/


section Comparison

variable {n : ℕ}

#print BitVec.ult /-
/-- `uborrow x y` returns `tt` iff the "subtract with borrow" operation on `x`, `y` and `ff`
required a borrow. -/
def ult (x y : BitVec n) : Bool :=
  Prod.fst (sbb x y false)
#align bitvec.uborrow BitVec.ult
-/

/- warning: bitvec.ult clashes with bitvec.uborrow -> BitVec.ult
Case conversion may be inaccurate. Consider using '#align bitvec.ult BitVec.ultₓ'. -/
#print BitVec.ult /-
/-- unsigned less-than proposition -/
def ult (x y : BitVec n) : Prop :=
  ult x y
#align bitvec.ult BitVec.ult
-/

/-- unsigned greater-than proposition -/
def Ugt (x y : BitVec n) : Prop :=
  ult y x
#align bitvec.ugt BitVec.Ugt

#print BitVec.ule /-
/-- unsigned less-than-or-equal-to proposition -/
def ule (x y : BitVec n) : Prop :=
  ¬ult y x
#align bitvec.ule BitVec.ule
-/

/-- unsigned greater-than-or-equal-to proposition -/
def Uge (x y : BitVec n) : Prop :=
  ule y x
#align bitvec.uge BitVec.Uge

#print BitVec.slt /-
/-- `sborrow x y` returns `tt` iff `x < y` as two's complement integers -/
def slt : ∀ {n : ℕ}, BitVec n → BitVec n → Bool
  | 0, _, _ => false
  | succ n, x, y =>
    match (head x, head y) with
    | (tt, ff) => true
    | (ff, tt) => false
    | _ => ult (tail x) (tail y)
#align bitvec.sborrow BitVec.slt
-/

/- warning: bitvec.slt clashes with bitvec.sborrow -> BitVec.slt
Case conversion may be inaccurate. Consider using '#align bitvec.slt BitVec.sltₓ'. -/
#print BitVec.slt /-
/-- signed less-than proposition -/
def slt (x y : BitVec n) : Prop :=
  slt x y
#align bitvec.slt BitVec.slt
-/

/-- signed greater-than proposition -/
def Sgt (x y : BitVec n) : Prop :=
  slt y x
#align bitvec.sgt BitVec.Sgt

#print BitVec.sle /-
/-- signed less-than-or-equal-to proposition -/
def sle (x y : BitVec n) : Prop :=
  ¬slt y x
#align bitvec.sle BitVec.sle
-/

/-- signed greater-than-or-equal-to proposition -/
def Sge (x y : BitVec n) : Prop :=
  sle y x
#align bitvec.sge BitVec.Sge

end Comparison

/-! ### Conversion to `nat` and `int` -/


section Conversion

variable {α : Type}

#print BitVec.ofNat /-
/-- Create a bitvector from a `nat` -/
protected def ofNat : ∀ n : ℕ, Nat → BitVec n
  | 0, x => nil
  | succ n, x => of_nat n (x / 2)++ₜdecide (x % 2 = 1) ::ᵥ nil
#align bitvec.of_nat BitVec.ofNat
-/

#print BitVec.ofInt /-
/-- Create a bitvector in the two's complement representation from an `int` -/
protected def ofInt : ∀ n : ℕ, Int → BitVec (succ n)
  | n, Int.ofNat m => false ::ᵥ BitVec.ofNat n m
  | n, Int.negSucc m => true ::ᵥ not (BitVec.ofNat n m)
#align bitvec.of_int BitVec.ofInt
-/

/-- `add_lsb r b` is `r + r + 1` if `b` is `tt` and `r + r` otherwise. -/
def addLsb (r : ℕ) (b : Bool) :=
  r + r + cond b 1 0
#align bitvec.add_lsb BitVec.addLsb

/-- Given a `list` of `bool`s, return the `nat` they represent as a list of binary digits. -/
def bitsToNat (v : List Bool) : Nat :=
  v.foldl addLsb 0
#align bitvec.bits_to_nat BitVec.bitsToNat

#print BitVec.toNat /-
/-- Return the natural number encoded by the input bitvector -/
protected def toNat {n : Nat} (v : BitVec n) : Nat :=
  bitsToNat (toList v)
#align bitvec.to_nat BitVec.toNat
-/

theorem bitsToNat_toList {n : ℕ} (x : BitVec n) : BitVec.toNat x = bitsToNat (Vector.toList x) :=
  rfl
#align bitvec.bits_to_nat_to_list BitVec.bitsToNat_toList

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

attribute [local simp] Nat.zero_add Nat.add_zero Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero

#print BitVec.toNat_append /-
-- mul_left_comm
theorem toNat_append {m : ℕ} (xs : BitVec m) (b : Bool) :
    BitVec.toNat (xs++ₜb ::ᵥ nil) = BitVec.toNat xs * 2 + BitVec.toNat (b ::ᵥ nil) :=
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
#align bitvec.to_nat_append BitVec.toNat_append
-/

theorem bits_toNat_decide (n : ℕ) : BitVec.toNat (decide (n % 2 = 1) ::ᵥ nil) = n % 2 :=
  by
  simp [bits_to_nat_to_list]
  unfold bits_to_nat add_lsb List.foldl cond
  simp [cond_to_bool_mod_two]
#align bitvec.bits_to_nat_to_bool BitVec.bits_toNat_decide

theorem ofNat_succ {k n : ℕ} :
    BitVec.ofNat (succ k) n = BitVec.ofNat k (n / 2)++ₜdecide (n % 2 = 1) ::ᵥ nil :=
  rfl
#align bitvec.of_nat_succ BitVec.ofNat_succ

#print BitVec.toNat_ofNat /-
theorem toNat_ofNat {k n : ℕ} : BitVec.toNat (BitVec.ofNat k n) = n % 2 ^ k :=
  by
  induction' k with k ih generalizing n
  · simp [Nat.mod_one]; rfl
  · rw [of_nat_succ, to_nat_append, ih, bits_to_nat_to_bool, mod_pow_succ, Nat.mul_comm]
#align bitvec.to_nat_of_nat BitVec.toNat_ofNat
-/

#print BitVec.toInt /-
/-- Return the integer encoded by the input bitvector -/
protected def toInt : ∀ {n : Nat}, BitVec n → Int
  | 0, _ => 0
  | succ n, v =>
    cond (head v) (Int.negSucc <| BitVec.toNat <| not <| tail v)
      (Int.ofNat <| BitVec.toNat <| tail v)
#align bitvec.to_int BitVec.toInt
-/

end Conversion

/-! ### Miscellaneous instances -/


private def repr {n : Nat} : BitVec n → String
  | ⟨bs, p⟩ => "0b" ++ (bs.map fun b : Bool => if b then '1' else '0').asString

instance (n : Nat) : Repr (BitVec n) :=
  ⟨repr⟩

end BitVec

instance {n} {x y : BitVec n} : Decidable (BitVec.ult x y) :=
  Bool.decidableEq _ _

instance {n} {x y : BitVec n} : Decidable (BitVec.Ugt x y) :=
  Bool.decidableEq _ _

