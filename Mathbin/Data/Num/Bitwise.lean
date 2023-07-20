/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Num.Basic
import Mathbin.Data.Bitvec.Core

#align_import data.num.bitwise from "leanprover-community/mathlib"@"68d1483e8a718ec63219f0e227ca3f0140361086"

/-!
# Bitwise operations using binary representation of integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Definitions

* bitwise operations for `pos_num` and `num`,
* `snum`, a type that represents integers as a bit string with a sign bit at the end,
* arithmetic operations for `snum`.
-/


namespace PosNum

#print PosNum.lor /-
/-- Bitwise "or" for `pos_num`. -/
def lor : PosNum → PosNum → PosNum
  | 1, bit0 q => bit1 q
  | 1, q => q
  | bit0 p, 1 => bit1 p
  | p, 1 => p
  | bit0 p, bit0 q => bit0 (lor p q)
  | bit0 p, bit1 q => bit1 (lor p q)
  | bit1 p, bit0 q => bit1 (lor p q)
  | bit1 p, bit1 q => bit1 (lor p q)
#align pos_num.lor PosNum.lor
-/

#print PosNum.land /-
/-- Bitwise "and" for `pos_num`. -/
def land : PosNum → PosNum → Num
  | 1, bit0 q => 0
  | 1, _ => 1
  | bit0 p, 1 => 0
  | _, 1 => 1
  | bit0 p, bit0 q => Num.bit0 (land p q)
  | bit0 p, bit1 q => Num.bit0 (land p q)
  | bit1 p, bit0 q => Num.bit0 (land p q)
  | bit1 p, bit1 q => Num.bit1 (land p q)
#align pos_num.land PosNum.land
-/

#print PosNum.ldiff /-
/-- Bitwise `λ a b, a && !b` for `pos_num`. For example, `ldiff 5 9 = 4`:

     101
    1001
    ----
     100

  -/
def ldiff : PosNum → PosNum → Num
  | 1, bit0 q => 1
  | 1, _ => 0
  | bit0 p, 1 => Num.pos (bit0 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (ldiff p q)
  | bit0 p, bit1 q => Num.bit0 (ldiff p q)
  | bit1 p, bit0 q => Num.bit1 (ldiff p q)
  | bit1 p, bit1 q => Num.bit0 (ldiff p q)
#align pos_num.ldiff PosNum.ldiff
-/

#print PosNum.lxor /-
/-- Bitwise "xor" for `pos_num`. -/
def lxor : PosNum → PosNum → Num
  | 1, 1 => 0
  | 1, bit0 q => Num.pos (bit1 q)
  | 1, bit1 q => Num.pos (bit0 q)
  | bit0 p, 1 => Num.pos (bit1 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (lxor p q)
  | bit0 p, bit1 q => Num.bit1 (lxor p q)
  | bit1 p, bit0 q => Num.bit1 (lxor p q)
  | bit1 p, bit1 q => Num.bit0 (lxor p q)
#align pos_num.lxor PosNum.lxor
-/

#print PosNum.testBit /-
/-- `a.test_bit n` is `tt` iff the `n`-th bit (starting from the LSB) in the binary representation
      of `a` is active. If the size of `a` is less than `n`, this evaluates to `ff`. -/
def testBit : PosNum → Nat → Bool
  | 1, 0 => true
  | 1, n + 1 => false
  | bit0 p, 0 => false
  | bit0 p, n + 1 => test_bit p n
  | bit1 p, 0 => true
  | bit1 p, n + 1 => test_bit p n
#align pos_num.test_bit PosNum.testBit
-/

#print PosNum.oneBits /-
/-- `n.one_bits 0` is the list of indices of active bits in the binary representation of `n`. -/
def oneBits : PosNum → Nat → List Nat
  | 1, d => [d]
  | bit0 p, d => one_bits p (d + 1)
  | bit1 p, d => d :: one_bits p (d + 1)
#align pos_num.one_bits PosNum.oneBits
-/

#print PosNum.shiftl /-
/-- Left-shift the binary representation of a `pos_num`. -/
def shiftl (p : PosNum) : Nat → PosNum
  | 0 => p
  | n + 1 => bit0 (shiftl n)
#align pos_num.shiftl PosNum.shiftl
-/

#print PosNum.shiftr /-
/-- Right-shift the binary representation of a `pos_num`. -/
def shiftr : PosNum → Nat → Num
  | p, 0 => Num.pos p
  | 1, n + 1 => 0
  | bit0 p, n + 1 => shiftr p n
  | bit1 p, n + 1 => shiftr p n
#align pos_num.shiftr PosNum.shiftr
-/

end PosNum

namespace Num

#print Num.lor /-
/-- Bitwise "or" for `num`. -/
def lor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | Pos p, Pos q => pos (p.lor' q)
#align num.lor Num.lor
-/

#print Num.land /-
/-- Bitwise "and" for `num`. -/
def land : Num → Num → Num
  | 0, q => 0
  | p, 0 => 0
  | Pos p, Pos q => p.land' q
#align num.land Num.land
-/

#print Num.ldiff /-
/-- Bitwise `λ a b, a && !b` for `num`. For example, `ldiff 5 9 = 4`:

     101
    1001
    ----
     100

  -/
def ldiff : Num → Num → Num
  | 0, q => 0
  | p, 0 => p
  | Pos p, Pos q => p.ldiff' q
#align num.ldiff Num.ldiff
-/

#print Num.lxor /-
/-- Bitwise "xor" for `num`. -/
def lxor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | Pos p, Pos q => p.lxor' q
#align num.lxor Num.lxor
-/

#print Num.shiftl /-
/-- Left-shift the binary representation of a `num`. -/
def shiftl : Num → Nat → Num
  | 0, n => 0
  | Pos p, n => pos (p.shiftl n)
#align num.shiftl Num.shiftl
-/

#print Num.shiftr /-
/-- Right-shift the binary representation of a `pos_num`. -/
def shiftr : Num → Nat → Num
  | 0, n => 0
  | Pos p, n => p.shiftr n
#align num.shiftr Num.shiftr
-/

#print Num.testBit /-
/-- `a.test_bit n` is `tt` iff the `n`-th bit (starting from the LSB) in the binary representation
      of `a` is active. If the size of `a` is less than `n`, this evaluates to `ff`. -/
def testBit : Num → Nat → Bool
  | 0, n => false
  | Pos p, n => p.testBit n
#align num.test_bit Num.testBit
-/

#print Num.oneBits /-
/-- `n.one_bits` is the list of indices of active bits in the binary representation of `n`. -/
def oneBits : Num → List Nat
  | 0 => []
  | Pos p => p.oneBits 0
#align num.one_bits Num.oneBits
-/

end Num

#print NzsNum /-
/-- This is a nonzero (and "non minus one") version of `snum`.
    See the documentation of `snum` for more details. -/
inductive NzsNum : Type
  | msb : Bool → NzsNum
  | bit : Bool → NzsNum → NzsNum
  deriving has_reflect, DecidableEq
#align nzsnum NzsNum
-/

#print SNum /-
/-- Alternative representation of integers using a sign bit at the end.
  The convention on sign here is to have the argument to `msb` denote
  the sign of the MSB itself, with all higher bits set to the negation
  of this sign. The result is interpreted in two's complement.

     13  = ..0001101(base 2) = nz (bit1 (bit0 (bit1 (msb tt))))
     -13 = ..1110011(base 2) = nz (bit1 (bit1 (bit0 (msb ff))))

  As with `num`, a special case must be added for zero, which has no msb,
  but by two's complement symmetry there is a second special case for -1.
  Here the `bool` field indicates the sign of the number.

     0  = ..0000000(base 2) = zero ff
     -1 = ..1111111(base 2) = zero tt -/
inductive SNum : Type
  | zero : Bool → SNum
  | nz : NzsNum → SNum
  deriving has_reflect, DecidableEq
#align snum SNum
-/

instance : Coe NzsNum SNum :=
  ⟨SNum.nz⟩

instance : Zero SNum :=
  ⟨SNum.zero false⟩

instance : One NzsNum :=
  ⟨NzsNum.msb true⟩

instance : One SNum :=
  ⟨SNum.nz 1⟩

instance : Inhabited NzsNum :=
  ⟨1⟩

instance : Inhabited SNum :=
  ⟨0⟩

/-!
The `snum` representation uses a bit string, essentially a list of 0 (`ff`) and 1 (`tt`) bits,
and the negation of the MSB is sign-extended to all higher bits.
-/


namespace NzsNum

notation a "::" b => bit a b

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print NzsNum.sign /-
/-- Sign of a `nzsnum`. -/
def sign : NzsNum → Bool
  | msb b => not b
  | b::p => SignType.sign p
#align nzsnum.sign NzsNum.sign
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print NzsNum.not /-
/-- Bitwise `not` for `nzsnum`. -/
@[match_pattern]
def not : NzsNum → NzsNum
  | msb b => msb (not b)
  | b::p => not b::Not p
#align nzsnum.not NzsNum.not
-/

prefix:100 "~" => not

#print NzsNum.bit0 /-
/-- Add an inactive bit at the end of a `nzsnum`. This mimics `pos_num.bit0`. -/
def bit0 : NzsNum → NzsNum :=
  bit false
#align nzsnum.bit0 NzsNum.bit0
-/

#print NzsNum.bit1 /-
/-- Add an active bit at the end of a `nzsnum`. This mimics `pos_num.bit1`. -/
def bit1 : NzsNum → NzsNum :=
  bit true
#align nzsnum.bit1 NzsNum.bit1
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print NzsNum.head /-
/-- The `head` of a `nzsnum` is the boolean value of its LSB. -/
def head : NzsNum → Bool
  | msb b => b
  | b::p => b
#align nzsnum.head NzsNum.head
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print NzsNum.tail /-
/-- The `tail` of a `nzsnum` is the `snum` obtained by removing the LSB.
      Edge cases: `tail 1 = 0` and `tail (-2) = -1`. -/
def tail : NzsNum → SNum
  | msb b => SNum.zero (not b)
  | b::p => p
#align nzsnum.tail NzsNum.tail
-/

end NzsNum

namespace SNum

open NzsNum

#print SNum.sign /-
/-- Sign of a `snum`. -/
def sign : SNum → Bool
  | zero z => z
  | nz p => p.sign
#align snum.sign SNum.sign
-/

#print SNum.not /-
/-- Bitwise `not` for `snum`. -/
@[match_pattern]
def not : SNum → SNum
  | zero z => zero (not z)
  | nz p => ~p
#align snum.not SNum.not
-/

prefix:0 "~" => not

#print SNum.bit /-
/-- Add a bit at the end of a `snum`. This mimics `nzsnum.bit`. -/
@[match_pattern]
def bit : Bool → SNum → SNum
  | b, zero z => if b = z then zero b else msb b
  | b, nz p => p.bit b
#align snum.bit SNum.bit
-/

notation a "::" b => bit a b

#print SNum.bit0 /-
/-- Add an inactive bit at the end of a `snum`. This mimics `znum.bit0`. -/
def bit0 : SNum → SNum :=
  bit false
#align snum.bit0 SNum.bit0
-/

#print SNum.bit1 /-
/-- Add an active bit at the end of a `snum`. This mimics `znum.bit1`. -/
def bit1 : SNum → SNum :=
  bit true
#align snum.bit1 SNum.bit1
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SNum.bit_zero /-
theorem bit_zero (b) : (b::zero b) = zero b := by cases b <;> rfl
#align snum.bit_zero SNum.bit_zero
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SNum.bit_one /-
theorem bit_one (b) : (b::zero (not b)) = msb b := by cases b <;> rfl
#align snum.bit_one SNum.bit_one
-/

end SNum

namespace NzsNum

open SNum

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print NzsNum.drec' /-
/-- A dependent induction principle for `nzsnum`, with base cases
      `0 : snum` and `(-1) : snum`. -/
def drec' {C : SNum → Sort _} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b::p)) :
    ∀ p : NzsNum, C p
  | msb b => by rw [← bit_one] <;> exact s b (SNum.zero (not b)) (z (not b))
  | bit b p => s b p (drec' p)
#align nzsnum.drec' NzsNum.drec'
-/

end NzsNum

namespace SNum

open NzsNum

#print SNum.head /-
/-- The `head` of a `snum` is the boolean value of its LSB. -/
def head : SNum → Bool
  | zero z => z
  | nz p => p.headI
#align snum.head SNum.head
-/

#print SNum.tail /-
/-- The `tail` of a `snum` is obtained by removing the LSB.
      Edge cases: `tail 1 = 0`, `tail (-2) = -1`, `tail 0 = 0` and `tail (-1) = -1`. -/
def tail : SNum → SNum
  | zero z => zero z
  | nz p => p.tail
#align snum.tail SNum.tail
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SNum.drec' /-
/-- A dependent induction principle for `snum` which avoids relying on `nzsnum`. -/
def drec' {C : SNum → Sort _} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b::p)) : ∀ p, C p
  | zero b => z b
  | nz p => p.drec' z s
#align snum.drec' SNum.drec'
-/

#print SNum.rec' /-
/-- An induction principle for `snum` which avoids relying on `nzsnum`. -/
def rec' {α} (z : Bool → α) (s : Bool → SNum → α → α) : SNum → α :=
  drec' z s
#align snum.rec' SNum.rec'
-/

#print SNum.testBit /-
/-- `snum.test_bit n a` is `tt` iff the `n`-th bit (starting from the LSB) of `a` is active.
      If the size of `a` is less than `n`, this evaluates to `ff`. -/
def testBit : Nat → SNum → Bool
  | 0, p => head p
  | n + 1, p => test_bit n (tail p)
#align snum.test_bit SNum.testBit
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SNum.succ /-
/-- The successor of a `snum` (i.e. the operation adding one). -/
def succ : SNum → SNum :=
  rec' (fun b => cond b 0 1) fun b p succp => cond b (false::succp) (true::p)
#align snum.succ SNum.succ
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SNum.pred /-
/-- The predecessor of a `snum` (i.e. the operation of removing one). -/
def pred : SNum → SNum :=
  rec' (fun b => cond b (~1) (~0)) fun b p predp => cond b (false::p) (true::predp)
#align snum.pred SNum.pred
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SNum.neg /-
/-- The opposite of a `snum`. -/
protected def neg (n : SNum) : SNum :=
  succ (~n)
#align snum.neg SNum.neg
-/

instance : Neg SNum :=
  ⟨SNum.neg⟩

#print SNum.czAdd /-
/-- `snum.czadd a b n` is `n + a - b` (where `a` and `b` should be read as either 0 or 1).
      This is useful to implement the carry system in `cadd`. -/
def czAdd : Bool → Bool → SNum → SNum
  | ff, ff, p => p
  | ff, tt, p => pred p
  | tt, ff, p => succ p
  | tt, tt, p => p
#align snum.czadd SNum.czAdd
-/

end SNum

namespace SNum

#print SNum.bits /-
/-- `a.bits n` is the vector of the `n` first bits of `a` (starting from the LSB). -/
def bits : SNum → ∀ n, Vector Bool n
  | p, 0 => Vector.nil
  | p, n + 1 => head p ::ᵥ bits (tail p) n
#align snum.bits SNum.bits
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SNum.cAdd /-
def cAdd : SNum → SNum → Bool → SNum :=
  rec' (fun a p c => czAdd c a p) fun a p IH =>
    rec' (fun b c => czAdd c b (a::p)) fun b q _ c => Bool.xor3 a b c::IH q (Bool.carry a b c)
#align snum.cadd SNum.cAdd
-/

#print SNum.add /-
/-- Add two `snum`s. -/
protected def add (a b : SNum) : SNum :=
  cAdd a b false
#align snum.add SNum.add
-/

instance : Add SNum :=
  ⟨SNum.add⟩

#print SNum.sub /-
/-- subtract two `snum`s. -/
protected def sub (a b : SNum) : SNum :=
  a + -b
#align snum.sub SNum.sub
-/

instance : Sub SNum :=
  ⟨SNum.sub⟩

#print SNum.mul /-
/-- Multiply two `snum`s. -/
protected def mul (a : SNum) : SNum → SNum :=
  rec' (fun b => cond b (-a) 0) fun b q IH => cond b (bit0 IH + a) (bit0 IH)
#align snum.mul SNum.mul
-/

instance : Mul SNum :=
  ⟨SNum.mul⟩

end SNum

