/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fp.basic
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Semiquot
import Mathbin.Data.Rat.Floor

/-!
# Implementation of floating-point numbers (experimental).

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


#print Int.shift2 /-
def Int.shift2 (a b : ℕ) : ℤ → ℕ × ℕ
  | Int.ofNat e => (a.shiftl e, b)
  | -[e+1] => (a, b.shiftl e.succ)
#align int.shift2 Int.shift2
-/

namespace Fp

#print FP.RMode /-
inductive RMode
  | NE
  deriving Inhabited
#align fp.rmode FP.RMode
-/

#print FP.FloatCfg /-
-- round to nearest even
class FloatCfg where
  (prec emax : ℕ)
  prec_pos : 0 < prec
  prec_max : prec ≤ emax
#align fp.float_cfg FP.FloatCfg
-/

variable [C : FloatCfg]

include C

#print FP.prec /-
def prec :=
  C.prec
#align fp.prec FP.prec
-/

#print FP.emax /-
def emax :=
  C.emax
#align fp.emax FP.emax
-/

#print FP.emin /-
def emin : ℤ :=
  1 - C.emax
#align fp.emin FP.emin
-/

#print FP.ValidFinite /-
def ValidFinite (e : ℤ) (m : ℕ) : Prop :=
  emin ≤ e + prec - 1 ∧ e + prec - 1 ≤ emax ∧ e = max (e + m.size - prec) emin
#align fp.valid_finite FP.ValidFinite
-/

#print FP.decValidFinite /-
instance decValidFinite (e m) : Decidable (ValidFinite e m) := by
  unfold valid_finite <;> infer_instance
#align fp.dec_valid_finite FP.decValidFinite
-/

#print FP.Float /-
inductive Float
  | inf : Bool → float
  | nan : float
  | Finite : Bool → ∀ e m, ValidFinite e m → float
#align fp.float FP.Float
-/

#print FP.Float.isFinite /-
def Float.isFinite : Float → Bool
  | float.finite s e m f => true
  | _ => false
#align fp.float.is_finite FP.Float.isFinite
-/

#print FP.toRat /-
def toRat : ∀ f : Float, f.isFinite → ℚ
  | float.finite s e m f, _ =>
    let (n, d) := Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r
#align fp.to_rat FP.toRat
-/

#print FP.Float.Zero.valid /-
theorem Float.Zero.valid : ValidFinite emin 0 :=
  ⟨by
    rw [add_sub_assoc]
    apply le_add_of_nonneg_right
    apply sub_nonneg_of_le
    apply Int.ofNat_le_ofNat_of_le
    exact C.prec_pos,
    suffices prec ≤ 2 * emax by
      rw [← Int.ofNat_le] at this
      rw [← sub_nonneg] at *
      simp only [emin, emax] at *
      ring_nf
      assumption
    le_trans C.prec_max (Nat.le_mul_of_pos_left (by decide)),
    by rw [max_eq_right] <;> simp [sub_eq_add_neg]⟩
#align fp.float.zero.valid FP.Float.Zero.valid
-/

#print FP.Float.zero /-
def Float.zero (s : Bool) : Float :=
  Float.finite s emin 0 Float.Zero.valid
#align fp.float.zero FP.Float.zero
-/

instance : Inhabited Float :=
  ⟨Float.zero true⟩

protected def Float.sign' : Float → Semiquot Bool
  | float.inf s => pure s
  | float.nan => ⊤
  | float.finite s e m f => pure s
#align fp.float.sign' FP.Float.sign'

#print FP.Float.sign /-
protected def Float.sign : Float → Bool
  | float.inf s => s
  | float.nan => false
  | float.finite s e m f => s
#align fp.float.sign FP.Float.sign
-/

#print FP.Float.isZero /-
protected def Float.isZero : Float → Bool
  | float.finite s e 0 f => true
  | _ => false
#align fp.float.is_zero FP.Float.isZero
-/

#print FP.Float.neg /-
protected def Float.neg : Float → Float
  | float.inf s => Float.inf (not s)
  | float.nan => Float.nan
  | float.finite s e m f => Float.finite (not s) e m f
#align fp.float.neg FP.Float.neg
-/

def divNatLtTwoPow (n d : ℕ) : ℤ → Bool
  | Int.ofNat e => n < d.shiftl e
  | -[e+1] => n.shiftl e.succ < d
#align fp.div_nat_lt_two_pow FP.divNatLtTwoPowₓ

#print FP.ofPosRatDn /-
-- TODO(Mario): Prove these and drop 'meta'
unsafe def ofPosRatDn (n : ℕ+) (d : ℕ+) : Float × Bool :=
  by
  let e₁ : ℤ := n.1.size - d.1.size - prec
  cases' h₁ : Int.shift2 d.1 n.1 (e₁ + prec) with d₁ n₁
  let e₂ := if n₁ < d₁ then e₁ - 1 else e₁
  let e₃ := max e₂ emin
  cases' h₂ : Int.shift2 d.1 n.1 (e₃ + prec) with d₂ n₂
  let r := mkRat n₂ d₂
  let m := r.floor
  refine' (float.finite ff e₃ (Int.toNat m) _, r.denom = 1)
  · exact undefined
#align fp.of_pos_rat_dn FP.ofPosRatDn
-/

#print FP.nextUpPos /-
unsafe def nextUpPos (e m) (v : ValidFinite e m) : Float :=
  let m' := m.succ
  if ss : m'.size = m.size then
    Float.finite false e m' (by unfold valid_finite at * <;> rw [ss] <;> exact v)
  else if h : e = emax then Float.inf false else Float.finite false e.succ (Nat.div2 m') undefined
#align fp.next_up_pos FP.nextUpPos
-/

#print FP.nextDnPos /-
unsafe def nextDnPos (e m) (v : ValidFinite e m) : Float :=
  match m with
  | 0 => nextUpPos _ _ Float.Zero.valid
  | Nat.succ m' =>
    if ss : m'.size = m.size then
      Float.finite false e m' (by unfold valid_finite at * <;> rw [ss] <;> exact v)
    else
      if h : e = emin then Float.finite false emin m' undefined
      else Float.finite false e.pred (bit1 m') undefined
#align fp.next_dn_pos FP.nextDnPos
-/

#print FP.nextUp /-
unsafe def nextUp : Float → Float
  | float.finite ff e m f => nextUpPos e m f
  | float.finite tt e m f => Float.neg <| nextDnPos e m f
  | f => f
#align fp.next_up FP.nextUp
-/

#print FP.nextDn /-
unsafe def nextDn : Float → Float
  | float.finite ff e m f => nextDnPos e m f
  | float.finite tt e m f => Float.neg <| nextUpPos e m f
  | f => f
#align fp.next_dn FP.nextDn
-/

#print FP.ofRatUp /-
unsafe def ofRatUp : ℚ → Float
  | ⟨0, _, _, _⟩ => Float.zero false
  | ⟨Nat.succ n, d, h, _⟩ =>
    let (f, exact) := ofPosRatDn n.succPNat ⟨d, h⟩
    if exact then f else nextUp f
  | ⟨-[n+1], d, h, _⟩ => Float.neg (ofPosRatDn n.succPNat ⟨d, h⟩).1
#align fp.of_rat_up FP.ofRatUp
-/

#print FP.ofRatDn /-
unsafe def ofRatDn (r : ℚ) : Float :=
  Float.neg <| ofRatUp (-r)
#align fp.of_rat_dn FP.ofRatDn
-/

#print FP.ofRat /-
unsafe def ofRat : RMode → ℚ → Float
  | rmode.NE, r =>
    let low := ofRatDn r
    let high := ofRatUp r
    if hf : high.isFinite then
      if r = toRat _ hf then high
      else
        if lf : low.isFinite then
          if r - toRat _ lf > toRat _ hf - r then high
          else
            if r - toRat _ lf < toRat _ hf - r then low
            else
              match low, lf with
              | float.finite s e m f, _ => if 2 ∣ m then low else high
        else Float.inf true
    else Float.inf false
#align fp.of_rat FP.ofRat
-/

namespace Float

instance : Neg Float :=
  ⟨Float.neg⟩

#print FP.Float.add /-
unsafe def add (mode : RMode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf tt, inf ff => nan
  | inf ff, inf tt => nan
  | inf s₁, _ => inf s₁
  | _, inf s₂ => inf s₂
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    ofRat mode (toRat f₁ rfl + toRat f₂ rfl)
#align fp.float.add FP.Float.add
-/

unsafe instance : Add Float :=
  ⟨Float.add RMode.NE⟩

#print FP.Float.sub /-
unsafe def sub (mode : RMode) (f1 f2 : Float) : Float :=
  add mode f1 (-f2)
#align fp.float.sub FP.Float.sub
-/

unsafe instance : Sub Float :=
  ⟨Float.sub RMode.NE⟩

#print FP.Float.mul /-
unsafe def mul (mode : RMode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf s₁, f₂ => if f₂.isZero then nan else inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => if f₁.isZero then nan else inf (xor f₁.sign s₂)
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    ofRat mode (toRat f₁ rfl * toRat f₂ rfl)
#align fp.float.mul FP.Float.mul
-/

#print FP.Float.div /-
unsafe def div (mode : RMode) : Float → Float → Float
  | nan, _ => nan
  | _, nan => nan
  | inf s₁, inf s₂ => nan
  | inf s₁, f₂ => inf (xor s₁ f₂.sign)
  | f₁, inf s₂ => zero (xor f₁.sign s₂)
  | Finite s₁ e₁ m₁ v₁, Finite s₂ e₂ m₂ v₂ =>
    let f₁ := finite s₁ e₁ m₁ v₁
    let f₂ := finite s₂ e₂ m₂ v₂
    if f₂.isZero then inf (xor s₁ s₂) else ofRat mode (toRat f₁ rfl / toRat f₂ rfl)
#align fp.float.div FP.Float.div
-/

end Float

end Fp

