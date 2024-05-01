/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Algebra.Group.Nat
import Order.Monotone.Basic

#align_import data.int.basic from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"

/-!
# Basic instances on the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains:
* instances on `ℤ`. The stronger one is `int.comm_ring`.
  See `data/int/defs/order` for `int.linear_ordered_comm_ring`.
* basic lemmas about the integers, but which do not use the ordered algebra hierarchy.
-/


open Nat

namespace Int

instance : Inhabited ℤ :=
  ⟨Int.zero⟩

instance : Nontrivial ℤ :=
  ⟨⟨0, 1, Int.zero_ne_one⟩⟩

instance : CommRing ℤ where
  add := Int.add
  add_assoc := Int.add_assoc
  zero := Int.zero
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg := Int.neg
  add_left_neg := Int.add_left_neg
  add_comm := Int.add_comm
  mul := Int.mul
  mul_assoc := Int.hMul_assoc
  one := Int.one
  one_mul := Int.one_hMul
  mul_one := Int.hMul_one
  sub := Int.sub
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_comm := Int.hMul_comm
  natCast := Int.ofNat
  natCast_zero := rfl
  natCast_succ n := rfl
  intCast n := n
  intCast_ofNat n := rfl
  intCast_negSucc n := rfl
  zsmul := (· * ·)
  zsmul_zero' := Int.zero_hMul
  zsmul_succ' n x := by
    rw [Nat.succ_eq_add_one, Nat.add_comm, of_nat_add, Int.add_mul, of_nat_one, Int.one_hMul]
  zsmul_neg' n x := Int.neg_mul_eq_neg_mul_symm (n.succ : ℤ) x

/-! ### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `int.normed_comm_ring` being used to construct
these instances non-computably.
-/


-- instance : has_sub int            := by apply_instance -- This is in core
instance : AddCommMonoid ℤ := by infer_instance

instance : AddMonoid ℤ := by infer_instance

instance : Monoid ℤ := by infer_instance

instance : CommMonoid ℤ := by infer_instance

instance : CommSemigroup ℤ := by infer_instance

instance : Semigroup ℤ := by infer_instance

instance : AddCommGroup ℤ := by infer_instance

instance : AddGroup ℤ := by infer_instance

instance : AddCommSemigroup ℤ := by infer_instance

instance : AddSemigroup ℤ := by infer_instance

instance : CommSemiring ℤ := by infer_instance

instance : Semiring ℤ := by infer_instance

instance : Ring ℤ := by infer_instance

instance : Distrib ℤ := by infer_instance

end Int

namespace Int

#print Int.add_neg_one /-
@[simp]
theorem add_neg_one (i : ℤ) : i + -1 = i - 1 :=
  rfl
#align int.add_neg_one Int.add_neg_one
-/

#print Int.sign_natCast_add_one /-
@[simp]
theorem sign_natCast_add_one (n : ℕ) : Int.sign (n + 1) = 1 :=
  rfl
#align int.sign_coe_add_one Int.sign_natCast_add_one
-/

#print Int.sign_negSucc /-
@[simp]
theorem sign_negSucc (n : ℕ) : Int.sign -[n+1] = -1 :=
  rfl
#align int.sign_neg_succ_of_nat Int.sign_negSucc
-/

#print Int.default_eq_zero /-
@[simp]
theorem default_eq_zero : default = (0 : ℤ) :=
  rfl
#align int.default_eq_zero Int.default_eq_zero
-/

unsafe instance : has_to_format ℤ :=
  ⟨fun z => toString z⟩

section

-- Note that here we are disabling the "safety" of reflected, to allow us to reuse `int.mk_numeral`.
-- The usual way to provide the required `reflected` instance would be via rewriting to prove that
-- the expression we use here is equivalent.
attribute [local semireducible] reflected

unsafe instance reflect : has_reflect ℤ :=
  int.mk_numeral q(ℤ) q((by infer_instance : Zero ℤ)) q((by infer_instance : One ℤ))
    q((by infer_instance : Add ℤ)) q((by infer_instance : Neg ℤ))
#align int.reflect int.reflect

end

attribute [simp] Int.bodd

#print Int.add_def /-
@[simp]
theorem add_def {a b : ℤ} : Int.add a b = a + b :=
  rfl
#align int.add_def Int.add_def
-/

#print Int.mul_def /-
@[simp]
theorem mul_def {a b : ℤ} : Int.mul a b = a * b :=
  rfl
#align int.mul_def Int.mul_def
-/

#print Int.negSucc_not_nonneg /-
@[simp]
theorem negSucc_not_nonneg (n : ℕ) : 0 ≤ -[n+1] ↔ False := by simp only [not_le, iff_false_iff];
  exact Int.negSucc_lt_zero n
#align int.neg_succ_not_nonneg Int.negSucc_not_nonneg
-/

#print Int.negSucc_not_pos /-
@[simp]
theorem negSucc_not_pos (n : ℕ) : 0 < -[n+1] ↔ False := by simp only [not_lt, iff_false_iff]
#align int.neg_succ_not_pos Int.negSucc_not_pos
-/

#print Int.negSucc_sub_one /-
@[simp]
theorem negSucc_sub_one (n : ℕ) : -[n+1] - 1 = -[n + 1+1] :=
  rfl
#align int.neg_succ_sub_one Int.negSucc_sub_one
-/

#print Int.ofNat_mul_negSucc /-
@[simp]
theorem ofNat_mul_negSucc (m n : ℕ) : (m : ℤ) * -[n+1] = -(m * succ n) :=
  rfl
#align int.coe_nat_mul_neg_succ Int.ofNat_mul_negSucc
-/

#print Int.negSucc_mul_ofNat /-
@[simp]
theorem negSucc_mul_ofNat (m n : ℕ) : -[m+1] * n = -(succ m * n) :=
  rfl
#align int.neg_succ_mul_coe_nat Int.negSucc_mul_ofNat
-/

#print Int.negSucc_mul_negSucc /-
@[simp]
theorem negSucc_mul_negSucc (m n : ℕ) : -[m+1] * -[n+1] = succ m * succ n :=
  rfl
#align int.neg_succ_mul_neg_succ Int.negSucc_mul_negSucc
-/

/- warning: int.coe_nat_le clashes with int.coe_nat_le_coe_nat_iff -> Int.ofNat_le
Case conversion may be inaccurate. Consider using '#align int.coe_nat_le Int.ofNat_leₓ'. -/
#print Int.ofNat_le /-
theorem ofNat_le {m n : ℕ} : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
  ofNat_le m n
#align int.coe_nat_le Int.ofNat_le
-/

/- warning: int.coe_nat_lt clashes with int.coe_nat_lt_coe_nat_iff -> Int.ofNat_lt
Case conversion may be inaccurate. Consider using '#align int.coe_nat_lt Int.ofNat_ltₓ'. -/
#print Int.ofNat_lt /-
theorem ofNat_lt {m n : ℕ} : (↑m : ℤ) < ↑n ↔ m < n :=
  ofNat_lt m n
#align int.coe_nat_lt Int.ofNat_lt
-/

#print Int.natCast_inj /-
theorem natCast_inj {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n :=
  Int.ofNat_inj m n
#align int.coe_nat_inj' Int.natCast_inj
-/

#print Int.coe_nat_strictMono /-
theorem coe_nat_strictMono : StrictMono (coe : ℕ → ℤ) := fun _ _ => Int.ofNat_lt.2
#align int.coe_nat_strict_mono Int.coe_nat_strictMono
-/

#print Int.natCast_nonneg /-
theorem natCast_nonneg (n : ℕ) : 0 ≤ (n : ℤ) :=
  ofNat_le.2 (Nat.zero_le _)
#align int.coe_nat_nonneg Int.natCast_nonneg
-/

#print Int.negSucc_ne_zero /-
@[simp]
theorem negSucc_ne_zero (n : ℕ) : -[n+1] ≠ 0 := fun h => Int.noConfusion h
#align int.neg_of_nat_ne_zero Int.negSucc_ne_zero
-/

#print Int.zero_ne_negSucc /-
@[simp]
theorem zero_ne_negSucc (n : ℕ) : 0 ≠ -[n+1] := fun h => Int.noConfusion h
#align int.zero_ne_neg_of_nat Int.zero_ne_negSucc
-/

/-! ### succ and pred -/


#print Int.succ /-
/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) :=
  a + 1
#align int.succ Int.succ
-/

#print Int.pred /-
/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) :=
  a - 1
#align int.pred Int.pred
-/

#print Int.natCast_succ /-
theorem natCast_succ (n : ℕ) : (Nat.succ n : ℤ) = Int.succ n :=
  rfl
#align int.nat_succ_eq_int_succ Int.natCast_succ
-/

#print Int.pred_succ /-
theorem pred_succ (a : ℤ) : pred (succ a) = a :=
  add_sub_cancel_right _ _
#align int.pred_succ Int.pred_succ
-/

#print Int.succ_pred /-
theorem succ_pred (a : ℤ) : succ (pred a) = a :=
  sub_add_cancel _ _
#align int.succ_pred Int.succ_pred
-/

#print Int.neg_succ /-
theorem neg_succ (a : ℤ) : -succ a = pred (-a) :=
  neg_add _ _
#align int.neg_succ Int.neg_succ
-/

#print Int.succ_neg_succ /-
theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]
#align int.succ_neg_succ Int.succ_neg_succ
-/

#print Int.neg_pred /-
theorem neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [neg_eq_iff_eq_neg.mp (neg_succ (-a)), neg_neg]
#align int.neg_pred Int.neg_pred
-/

#print Int.pred_neg_pred /-
theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]
#align int.pred_neg_pred Int.pred_neg_pred
-/

#print Int.pred_nat_succ /-
theorem pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n :=
  pred_succ n
#align int.pred_nat_succ Int.pred_nat_succ
-/

#print Int.neg_nat_succ /-
theorem neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) :=
  neg_succ n
#align int.neg_nat_succ Int.neg_nat_succ
-/

#print Int.succ_neg_natCast_succ /-
theorem succ_neg_natCast_succ (n : ℕ) : succ (-Nat.succ n) = -n :=
  succ_neg_succ n
#align int.succ_neg_nat_succ Int.succ_neg_natCast_succ
-/

#print Int.add_one_le_iff /-
theorem add_one_le_iff {a b : ℤ} : a + 1 ≤ b ↔ a < b :=
  Iff.rfl
#align int.add_one_le_iff Int.add_one_le_iff
-/

#print Int.natCast_pred_of_pos /-
@[norm_cast]
theorem natCast_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by cases n;
  cases h; simp
#align int.coe_pred_of_pos Int.natCast_pred_of_pos
-/

#print Int.induction_on /-
@[elab_as_elim]
protected theorem induction_on {p : ℤ → Prop} (i : ℤ) (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1))
    (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i :=
  by
  induction i
  · induction i
    · exact hz
    · exact hp _ i_ih
  · have : ∀ n : ℕ, p (-n) := by
      intro n; induction n
      · simp [hz]
      · convert hn _ n_ih using 1; simp [sub_eq_neg_add]
    exact this (i + 1)
#align int.induction_on Int.induction_on
-/

/-! ### nat abs -/


variable {a b : ℤ} {n : ℕ}

attribute [simp] nat_abs_of_nat nat_abs_zero nat_abs_one

#print Int.natAbs_surjective /-
theorem natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_ofNat n⟩
#align int.nat_abs_surjective Int.natAbs_surjective
-/

#print Int.natAbs_add_le /-
theorem natAbs_add_le (a b : ℤ) : natAbs (a + b) ≤ natAbs a + natAbs b :=
  by
  have : ∀ a b : ℕ, nat_abs (sub_nat_nat a (Nat.succ b)) ≤ Nat.succ (a + b) :=
    by
    refine' fun a b : ℕ =>
      sub_nat_nat_elim a b.succ (fun m n i => n = b.succ → nat_abs i ≤ (m + b).succ) _
        (fun i n e => _) rfl
    · rintro i n rfl
      rw [add_comm _ i, add_assoc]
      exact Nat.le_add_right i (b.succ + b).succ
    · apply succ_le_succ
      rw [← succ.inj e, ← add_assoc, add_comm]
      apply Nat.le_add_right
  cases a <;> cases' b with b b <;> simp [nat_abs, Nat.succ_add] <;> try rfl <;> [skip;
      rw [add_comm a b]] <;>
    apply this
#align int.nat_abs_add_le Int.natAbs_add_le
-/

#print Int.natAbs_sub_le /-
theorem natAbs_sub_le (a b : ℤ) : natAbs (a - b) ≤ natAbs a + natAbs b := by
  rw [sub_eq_add_neg, ← Int.natAbs_neg b]; apply nat_abs_add_le
#align int.nat_abs_sub_le Int.natAbs_sub_le
-/

#print Int.natAbs_negOfNat /-
theorem natAbs_negOfNat (n : ℕ) : natAbs (negOfNat n) = n := by cases n <;> rfl
#align int.nat_abs_neg_of_nat Int.natAbs_negOfNat
-/

#print Int.natAbs_mul /-
theorem natAbs_mul (a b : ℤ) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;>
    simp only [← Int.mul_def, Int.mul, nat_abs_neg_of_nat, eq_self_iff_true, Int.natAbs]
#align int.nat_abs_mul Int.natAbs_mul
-/

#print Int.natAbs_mul_natAbs_eq /-
theorem natAbs_mul_natAbs_eq {a b : ℤ} {c : ℕ} (h : a * b = (c : ℤ)) : a.natAbs * b.natAbs = c := by
  rw [← nat_abs_mul, h, nat_abs_of_nat]
#align int.nat_abs_mul_nat_abs_eq Int.natAbs_mul_natAbs_eq
-/

#print Int.natAbs_mul_self' /-
theorem natAbs_mul_self' (a : ℤ) : (natAbs a * natAbs a : ℤ) = a * a := by
  rw [← Int.ofNat_mul, nat_abs_mul_self]
#align int.nat_abs_mul_self' Int.natAbs_mul_self'
-/

#print Int.negSucc_eq' /-
theorem negSucc_eq' (m : ℕ) : -[m+1] = -m - 1 := by simp [neg_succ_of_nat_eq, sub_eq_neg_add]
#align int.neg_succ_of_nat_eq' Int.negSucc_eq'
-/

#print Int.natAbs_ne_zero_of_ne_zero /-
theorem natAbs_ne_zero_of_ne_zero {z : ℤ} (hz : z ≠ 0) : z.natAbs ≠ 0 := fun h =>
  hz <| Int.natAbs_eq_zero h
#align int.nat_abs_ne_zero_of_ne_zero Int.natAbs_ne_zero_of_ne_zero
-/

/- warning: int.nat_abs_eq_zero clashes with int.eq_zero_of_nat_abs_eq_zero -> Int.natAbs_eq_zero
Case conversion may be inaccurate. Consider using '#align int.nat_abs_eq_zero Int.natAbs_eq_zeroₓ'. -/
#print Int.natAbs_eq_zero /-
@[simp]
theorem natAbs_eq_zero {a : ℤ} : a.natAbs = 0 ↔ a = 0 :=
  ⟨Int.natAbs_eq_zero, fun h => h.symm ▸ rfl⟩
#align int.nat_abs_eq_zero Int.natAbs_eq_zero
-/

#print Int.natAbs_ne_zero /-
theorem natAbs_ne_zero {a : ℤ} : a.natAbs ≠ 0 ↔ a ≠ 0 :=
  not_congr Int.natAbs_eq_zero
#align int.nat_abs_ne_zero Int.natAbs_ne_zero
-/

#print Int.natAbs_lt_natAbs_of_nonneg_of_lt /-
theorem natAbs_lt_natAbs_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) :
    a.natAbs < b.natAbs := by
  lift b to ℕ using le_trans w₁ (le_of_lt w₂)
  lift a to ℕ using w₁
  simpa [coe_nat_lt] using w₂
#align int.nat_abs_lt_nat_abs_of_nonneg_of_lt Int.natAbs_lt_natAbs_of_nonneg_of_lt
-/

#print Int.natAbs_eq_natAbs_iff /-
theorem natAbs_eq_natAbs_iff {a b : ℤ} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b :=
  by
  constructor <;> intro h
  ·
    cases' Int.natAbs_eq a with h₁ h₁ <;> cases' Int.natAbs_eq b with h₂ h₂ <;> rw [h₁, h₂] <;>
      simp [h]
  · cases h <;> rw [h]; rw [Int.natAbs_neg]
#align int.nat_abs_eq_nat_abs_iff Int.natAbs_eq_natAbs_iff
-/

#print Int.natAbs_eq_iff /-
theorem natAbs_eq_iff {a : ℤ} {n : ℕ} : a.natAbs = n ↔ a = n ∨ a = -n := by
  rw [← Int.natAbs_eq_natAbs_iff, Int.natAbs_ofNat]
#align int.nat_abs_eq_iff Int.natAbs_eq_iff
-/

/-! ### `/`  -/


#print Int.ofNat_div /-
@[simp]
theorem ofNat_div (m n : ℕ) : ofNat (m / n) = ofNat m / ofNat n :=
  rfl
#align int.of_nat_div Int.ofNat_div
-/

#print Int.natCast_div /-
@[simp, norm_cast]
theorem natCast_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n :=
  rfl
#align int.coe_nat_div Int.natCast_div
-/

#print Int.negSucc_ediv /-
theorem negSucc_ediv (m : ℕ) {b : ℤ} (H : 0 < b) : -[m+1] / b = -(m / b + 1) :=
  match b, eq_succ_of_zero_lt H with
  | _, ⟨n, rfl⟩ => rfl
#align int.neg_succ_of_nat_div Int.negSucc_ediv
-/

#print Int.zero_div /-
-- Will be generalized to Euclidean domains.
@[local simp]
protected theorem zero_div : ∀ b : ℤ, 0 / b = 0
  | (n : ℕ) => show ofNat _ = _ by simp
  | -[n+1] => show -ofNat _ = _ by simp
#align int.zero_div Int.zero_div
-/

#print Int.div_zero /-
-- Will be generalized to Euclidean domains.
@[local simp]
protected theorem div_zero : ∀ a : ℤ, a / 0 = 0
  | (n : ℕ) => show ofNat _ = _ by simp
  | -[n+1] => rfl
#align int.div_zero Int.div_zero
-/

@[simp]
protected theorem div_neg : ∀ a b : ℤ, a / -b = -(a / b)
  | (m : ℕ), 0 => show ofNat (m / 0) = -(m / 0 : ℕ) by rw [Nat.div_zero] <;> rfl
  | (m : ℕ), (n + 1 : ℕ) => rfl
  | (m : ℕ), -[n+1] => (neg_neg _).symm
  | -[m+1], 0 => rfl
  | -[m+1], (n + 1 : ℕ) => rfl
  | -[m+1], -[n+1] => rfl
#align int.div_neg Int.div_negₓ

#print Int.ediv_of_neg_of_pos /-
theorem ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    change (- -[m+1] : ℤ) with (m + 1 : ℤ) <;> rw [add_sub_cancel_right] <;> rfl
#align int.div_of_neg_of_pos Int.ediv_of_neg_of_pos
-/

protected theorem div_nonneg {a b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => ofNat_zero_le _
#align int.div_nonneg Int.div_nonnegₓ

#print Int.ediv_neg' /-
theorem ediv_neg' {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b < 0 :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => negSucc_lt_zero _
#align int.div_neg' Int.ediv_neg'
-/

@[simp]
protected theorem div_one : ∀ a : ℤ, a / 1 = a
  | (n : ℕ) => congr_arg ofNat (Nat.div_one _)
  | -[n+1] => congr_arg negSucc (Nat.div_one _)
#align int.div_one Int.div_oneₓ

theorem div_eq_zero_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (lt_of_le_of_lt H1 H2), H2 with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 => congr_arg ofNat <| Nat.div_eq_of_lt <| lt_of_ofNat_lt_ofNat H2
#align int.div_eq_zero_of_lt Int.div_eq_zero_of_ltₓ

/-! ### mod -/


#print Int.ofNat_mod_ofNat /-
theorem ofNat_mod_ofNat (m n : Nat) : (m % n : ℤ) = ofNat (m % n) :=
  rfl
#align int.of_nat_mod Int.ofNat_mod_ofNat
-/

#print Int.natCast_mod /-
@[simp, norm_cast]
theorem natCast_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n :=
  rfl
#align int.coe_nat_mod Int.natCast_mod
-/

#print Int.negSucc_emod /-
theorem negSucc_emod (m : ℕ) {b : ℤ} (bpos : 0 < b) : -[m+1] % b = b - 1 - m % b := by
  rw [sub_sub, add_comm] <;>
    exact
      match b, eq_succ_of_zero_lt bpos with
      | _, ⟨n, rfl⟩ => rfl
#align int.neg_succ_of_nat_mod Int.negSucc_emod
-/

@[simp]
theorem mod_neg : ∀ a b : ℤ, a % -b = a % b
  | (m : ℕ), n => @congr_arg ℕ ℤ _ _ (fun i => ↑(m % i)) (natAbs_neg _)
  | -[m+1], n => @congr_arg ℕ ℤ _ _ (fun i => subNatNat i (Nat.succ (m % i))) (natAbs_neg _)
#align int.mod_neg Int.mod_negₓ

-- Will be generalized to Euclidean domains.
@[local simp]
theorem zero_mod (b : ℤ) : 0 % b = 0 :=
  rfl
#align int.zero_mod Int.zero_modₓ

-- Will be generalized to Euclidean domains.
@[local simp]
theorem mod_zero : ∀ a : ℤ, a % 0 = a
  | (m : ℕ) => congr_arg ofNat <| Nat.mod_zero _
  | -[m+1] => congr_arg negSucc <| Nat.mod_zero _
#align int.mod_zero Int.mod_zeroₓ

-- Will be generalized to Euclidean domains.
@[local simp]
theorem mod_one : ∀ a : ℤ, a % 1 = 0
  | (m : ℕ) => congr_arg ofNat <| Nat.mod_one _
  | -[m+1] => show (1 - (m % 1).succ : ℤ) = 0 by rw [Nat.mod_one] <;> rfl
#align int.mod_one Int.mod_oneₓ

#print Int.emod_eq_of_lt /-
theorem emod_eq_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
  match a, b, eq_ofNat_of_zero_le H1, eq_ofNat_of_zero_le (le_trans H1 (le_of_lt H2)), H2 with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 => congr_arg ofNat <| Nat.mod_eq_of_lt (lt_of_ofNat_lt_ofNat H2)
#align int.mod_eq_of_lt Int.emod_eq_of_lt
-/

theorem mod_add_div_aux (m n : ℕ) : (n - (m % n + 1) - (n * (m / n) + n) : ℤ) = -[m+1] :=
  by
  rw [← sub_sub, neg_succ_of_nat_coe, sub_sub (n : ℤ), eq_comm, neg_eq_iff_eq_neg, neg_sub,
    sub_sub_self, add_right_comm]
  exact @congr_arg ℕ ℤ _ _ (fun i => (i + 1 : ℤ)) (Nat.mod_add_div _ _).symm
#align int.mod_add_div_aux Int.mod_add_div_aux

#print Int.emod_add_ediv /-
theorem emod_add_ediv : ∀ a b : ℤ, a % b + b * (a / b) = a
  | (m : ℕ), (n : ℕ) => congr_arg ofNat (Nat.mod_add_div _ _)
  | (m : ℕ), -[n+1] =>
    show (_ + -(n + 1) * -(m / (n + 1) : ℕ) : ℤ) = _ by
      rw [neg_mul_neg] <;> exact congr_arg of_nat (Nat.mod_add_div _ _)
  | -[m+1], 0 => by rw [mod_zero, Int.div_zero] <;> rfl
  | -[m+1], (n + 1 : ℕ) => mod_add_div_aux m n.succ
  | -[m+1], -[n+1] => mod_add_div_aux m n.succ
#align int.mod_add_div Int.emod_add_ediv
-/

theorem div_add_mod (a b : ℤ) : b * (a / b) + a % b = a :=
  (add_comm _ _).trans (emod_add_ediv _ _)
#align int.div_add_mod Int.div_add_modₓ

theorem mod_add_div' (m k : ℤ) : m % k + m / k * k = m := by rw [mul_comm]; exact mod_add_div _ _
#align int.mod_add_div' Int.mod_add_div'ₓ

theorem div_add_mod' (m k : ℤ) : m / k * k + m % k = m := by rw [mul_comm]; exact div_add_mod _ _
#align int.div_add_mod' Int.div_add_mod'ₓ

theorem mod_def (a b : ℤ) : a % b = a - b * (a / b) :=
  eq_sub_of_add_eq (emod_add_ediv _ _)
#align int.mod_def Int.mod_defₓ

/-! ### properties of `/` and `%` -/


#print Int.mul_ediv_mul_of_pos /-
@[simp]
theorem mul_ediv_mul_of_pos {a : ℤ} (b c : ℤ) (H : 0 < a) : a * b / (a * c) = b / c :=
  suffices ∀ (m k : ℕ) (b : ℤ), (m.succ * b / (m.succ * k) : ℤ) = b / k from
    match a, eq_succ_of_zero_lt H, c, eq_nat_or_neg c with
    | _, ⟨m, rfl⟩, _, ⟨k, Or.inl rfl⟩ => this _ _ _
    | _, ⟨m, rfl⟩, _, ⟨k, Or.inr rfl⟩ => by
      rw [mul_neg, Int.div_neg, Int.div_neg] <;> apply congr_arg Neg.neg <;> apply this
  fun m k b =>
  match b, k with
  | (n : ℕ), k => congr_arg ofNat (Nat.mul_div_mul_left _ _ m.succ_pos)
  | -[n+1], 0 => by rw [Int.ofNat_zero, MulZeroClass.mul_zero, Int.div_zero, Int.div_zero]
  | -[n+1], k + 1 =>
    congr_arg negSucc <|
      show (m.succ * n + m) / (m.succ * k.succ) = n / k.succ
        by
        apply Nat.div_eq_of_lt_le
        · refine' le_trans _ (Nat.le_add_right _ _)
          rw [← Nat.mul_div_mul_left _ _ m.succ_pos]
          apply Nat.div_mul_le_self
        · change m.succ * n.succ ≤ _
          rw [mul_left_comm]
          apply Nat.mul_le_mul_left
          apply (Nat.div_lt_iff_lt_mul k.succ_pos).1
          apply Nat.lt_succ_self
#align int.mul_div_mul_of_pos Int.mul_ediv_mul_of_pos
-/

#print Int.mul_ediv_mul_of_pos_left /-
@[simp]
theorem mul_ediv_mul_of_pos_left (a : ℤ) {b : ℤ} (H : 0 < b) (c : ℤ) : a * b / (c * b) = a / c := by
  rw [mul_comm, mul_comm c, mul_div_mul_of_pos _ _ H]
#align int.mul_div_mul_of_pos_left Int.mul_ediv_mul_of_pos_left
-/

#print Int.mul_emod_mul_of_pos /-
@[simp]
theorem mul_emod_mul_of_pos {a : ℤ} (H : 0 < a) (b c : ℤ) : a * b % (a * c) = a * (b % c) := by
  rw [mod_def, mod_def, mul_div_mul_of_pos _ _ H, mul_sub_left_distrib, mul_assoc]
#align int.mul_mod_mul_of_pos Int.mul_emod_mul_of_pos
-/

theorem mul_div_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : b * (a / b) = a := by
  have := mod_add_div a b <;> rwa [H, zero_add] at this
#align int.mul_div_cancel_of_mod_eq_zero Int.mul_div_cancel_of_mod_eq_zeroₓ

theorem div_mul_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : a / b * b = a := by
  rw [mul_comm, mul_div_cancel_of_mod_eq_zero H]
#align int.div_mul_cancel_of_mod_eq_zero Int.div_mul_cancel_of_mod_eq_zeroₓ

#print Int.natAbs_sign /-
theorem natAbs_sign (z : ℤ) : z.sign.natAbs = if z = 0 then 0 else 1 := by
  rcases z with ((_ | _) | _) <;> rfl
#align int.nat_abs_sign Int.natAbs_sign
-/

#print Int.natAbs_sign_of_nonzero /-
theorem natAbs_sign_of_nonzero {z : ℤ} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]
#align int.nat_abs_sign_of_nonzero Int.natAbs_sign_of_nonzero
-/

#print Int.sign_natCast_of_ne_zero /-
theorem sign_natCast_of_ne_zero {n : ℕ} (hn : n ≠ 0) : Int.sign n = 1 :=
  by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact Int.sign_of_succ n
#align int.sign_coe_nat_of_nonzero Int.sign_natCast_of_ne_zero
-/

#print Int.sign_neg /-
@[simp]
theorem sign_neg (z : ℤ) : Int.sign (-z) = -Int.sign z := by rcases z with ((_ | _) | _) <;> rfl
#align int.sign_neg Int.sign_neg
-/

#print Int.div_sign /-
theorem div_sign : ∀ a b, a / sign b = a * sign b
  | a, (n + 1 : ℕ) => by unfold SignType.sign <;> simp
  | a, 0 => by simp [SignType.sign]
  | a, -[n+1] => by simp [SignType.sign]
#align int.div_sign Int.div_sign
-/

#print Int.sign_mul /-
@[simp]
theorem sign_mul : ∀ a b, sign (a * b) = sign a * sign b
  | a, 0 => by simp
  | 0, b => by simp
  | (m + 1 : ℕ), (n + 1 : ℕ) => rfl
  | (m + 1 : ℕ), -[n+1] => rfl
  | -[m+1], (n + 1 : ℕ) => rfl
  | -[m+1], -[n+1] => rfl
#align int.sign_mul Int.sign_mul
-/

#print Int.mul_sign /-
theorem mul_sign : ∀ i : ℤ, i * sign i = natAbs i
  | (n + 1 : ℕ) => mul_one _
  | 0 => MulZeroClass.mul_zero _
  | -[n+1] => mul_neg_one _
#align int.mul_sign Int.mul_sign
-/

#print Int.ofNat_add_negSucc_of_lt /-
theorem ofNat_add_negSucc_of_lt {m n : ℕ} (h : m < n.succ) : ofNat m + -[n+1] = -[n - m+1] :=
  by
  change sub_nat_nat _ _ = _
  have h' : n.succ - m = (n - m).succ
  apply succ_sub
  apply le_of_lt_succ h
  simp [*, sub_nat_nat]
#align int.of_nat_add_neg_succ_of_nat_of_lt Int.ofNat_add_negSucc_of_lt
-/

/- warning: int.neg_add_neg clashes with int.neg_succ_of_nat_add_neg_succ_of_nat -> Int.negSucc_add_negSucc
Case conversion may be inaccurate. Consider using '#align int.neg_add_neg Int.negSucc_add_negSuccₓ'. -/
#print Int.negSucc_add_negSucc /-
@[simp]
theorem negSucc_add_negSucc (m n : ℕ) : -[m+1] + -[n+1] = -[Nat.succ (m + n)+1] :=
  rfl
#align int.neg_add_neg Int.negSucc_add_negSucc
-/

/-! ### to_nat -/


#print Int.toNat_eq_max /-
theorem toNat_eq_max : ∀ a : ℤ, (toNat a : ℤ) = max a 0
  | (n : ℕ) => (max_eq_left (ofNat_zero_le n)).symm
  | -[n+1] => (max_eq_right (le_of_lt (negSucc_lt_zero n))).symm
#align int.to_nat_eq_max Int.toNat_eq_max
-/

#print Int.toNat_zero /-
@[simp]
theorem toNat_zero : (0 : ℤ).toNat = 0 :=
  rfl
#align int.to_nat_zero Int.toNat_zero
-/

#print Int.toNat_one /-
@[simp]
theorem toNat_one : (1 : ℤ).toNat = 1 :=
  rfl
#align int.to_nat_one Int.toNat_one
-/

#print Int.toNat_of_nonneg /-
@[simp]
theorem toNat_of_nonneg {a : ℤ} (h : 0 ≤ a) : (toNat a : ℤ) = a := by
  rw [to_nat_eq_max, max_eq_left h]
#align int.to_nat_of_nonneg Int.toNat_of_nonneg
-/

#print Int.toNat_natCast /-
@[simp]
theorem toNat_natCast (n : ℕ) : toNat ↑n = n :=
  rfl
#align int.to_nat_coe_nat Int.toNat_natCast
-/

#print Int.toNat_natCast_add_one /-
@[simp]
theorem toNat_natCast_add_one {n : ℕ} : ((n : ℤ) + 1).toNat = n + 1 :=
  rfl
#align int.to_nat_coe_nat_add_one Int.toNat_natCast_add_one
-/

#print Int.self_le_toNat /-
theorem self_le_toNat (a : ℤ) : a ≤ toNat a := by rw [to_nat_eq_max] <;> apply le_max_left
#align int.le_to_nat Int.self_le_toNat
-/

#print Int.le_toNat /-
@[simp]
theorem le_toNat {n : ℕ} {z : ℤ} (h : 0 ≤ z) : n ≤ z.toNat ↔ (n : ℤ) ≤ z := by
  rw [← Int.ofNat_le, Int.toNat_of_nonneg h]
#align int.le_to_nat_iff Int.le_toNat
-/

#print Int.toNat_add /-
theorem toNat_add {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b).toNat = a.toNat + b.toNat :=
  by
  lift a to ℕ using ha
  lift b to ℕ using hb
  norm_cast
#align int.to_nat_add Int.toNat_add
-/

#print Int.toNat_add_nat /-
theorem toNat_add_nat {a : ℤ} (ha : 0 ≤ a) (n : ℕ) : (a + n).toNat = a.toNat + n :=
  by
  lift a to ℕ using ha
  norm_cast
#align int.to_nat_add_nat Int.toNat_add_nat
-/

#print Int.pred_toNat /-
@[simp]
theorem pred_toNat : ∀ i : ℤ, (i - 1).toNat = i.toNat - 1
  | (0 : ℕ) => rfl
  | (n + 1 : ℕ) => by simp
  | -[n+1] => rfl
#align int.pred_to_nat Int.pred_toNat
-/

#print Int.toNat_sub_toNat_neg /-
@[simp]
theorem toNat_sub_toNat_neg : ∀ n : ℤ, ↑n.toNat - ↑(-n).toNat = n
  | (0 : ℕ) => rfl
  | (n + 1 : ℕ) => show ↑(n + 1) - (0 : ℤ) = n + 1 from sub_zero _
  | -[n+1] => show 0 - (n + 1 : ℤ) = _ from zero_sub _
#align int.to_nat_sub_to_nat_neg Int.toNat_sub_toNat_neg
-/

#print Int.toNat_add_toNat_neg_eq_natAbs /-
@[simp]
theorem toNat_add_toNat_neg_eq_natAbs : ∀ n : ℤ, n.toNat + (-n).toNat = n.natAbs
  | (0 : ℕ) => rfl
  | (n + 1 : ℕ) => show n + 1 + 0 = n + 1 from add_zero _
  | -[n+1] => show 0 + (n + 1) = n + 1 from zero_add _
#align int.to_nat_add_to_nat_neg_eq_nat_abs Int.toNat_add_toNat_neg_eq_natAbs
-/

#print Int.toNat' /-
/-- If `n : ℕ`, then `int.to_nat' n = some n`, if `n : ℤ` is negative, then `int.to_nat' n = none`.
-/
def toNat' : ℤ → Option ℕ
  | (n : ℕ) => some n
  | -[n+1] => none
#align int.to_nat' Int.toNat'
-/

#print Int.mem_toNat' /-
theorem mem_toNat' : ∀ (a : ℤ) (n : ℕ), n ∈ toNat' a ↔ a = n
  | (m : ℕ), n => Option.some_inj.trans natCast_inj.symm
  | -[m+1], n => by constructor <;> intro h <;> cases h
#align int.mem_to_nat' Int.mem_toNat'
-/

#print Int.toNat_neg_nat /-
@[simp]
theorem toNat_neg_nat : ∀ n : ℕ, (-(n : ℤ)).toNat = 0
  | 0 => rfl
  | n + 1 => rfl
#align int.to_nat_neg_nat Int.toNat_neg_nat
-/

end Int

