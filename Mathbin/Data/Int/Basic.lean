/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathbin.Data.Nat.Basic

/-!
# Basic instances on the integers

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
  mul_assoc := Int.mul_assoc
  one := Int.one
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  sub := Int.sub
  left_distrib := Int.distrib_left
  right_distrib := Int.distrib_right
  mul_comm := Int.mul_comm
  natCast := Int.ofNat
  nat_cast_zero := rfl
  nat_cast_succ n := rfl
  intCast n := n
  int_cast_of_nat n := rfl
  int_cast_neg_succ_of_nat n := rfl
  zsmul := (· * ·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' n x := by rw [Nat.succ_eq_add_one, Nat.add_comm, of_nat_add, Int.distrib_right, of_nat_one, Int.one_mul]
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
-/

#print Int.default_eq_zero /-
@[simp]
theorem default_eq_zero : default = (0 : ℤ) :=
  rfl
-/

unsafe instance : has_to_format ℤ :=
  ⟨fun z => toString z⟩

section

-- Note that here we are disabling the "safety" of reflected, to allow us to reuse `int.mk_numeral`.
-- The usual way to provide the required `reflected` instance would be via rewriting to prove that
-- the expression we use here is equivalent.
attribute [local semireducible] reflected

unsafe instance reflect : has_reflect ℤ :=
  int.mk_numeral (quote.1 ℤ) (quote.1 (by infer_instance : Zero ℤ)) (quote.1 (by infer_instance : One ℤ))
    (quote.1 (by infer_instance : Add ℤ)) (quote.1 (by infer_instance : Neg ℤ))

end

attribute [simp] Int.bodd

#print Int.add_def /-
@[simp]
theorem add_def {a b : ℤ} : Int.add a b = a + b :=
  rfl
-/

#print Int.mul_def /-
@[simp]
theorem mul_def {a b : ℤ} : Int.mul a b = a * b :=
  rfl
-/

@[simp]
theorem neg_succ_not_nonneg (n : ℕ) : 0 ≤ -[n+1] ↔ False := by
  simp only [not_le, iff_false_iff]
  exact Int.neg_succ_lt_zero n

@[simp]
theorem neg_succ_not_pos (n : ℕ) : 0 < -[n+1] ↔ False := by simp only [not_lt, iff_false_iff]

@[simp]
theorem neg_succ_sub_one (n : ℕ) : -[n+1] - 1 = -[n + 1+1] :=
  rfl

@[simp]
theorem coe_nat_mul_neg_succ (m n : ℕ) : (m : ℤ) * -[n+1] = -(m * succ n) :=
  rfl

@[simp]
theorem neg_succ_mul_coe_nat (m n : ℕ) : -[m+1] * n = -(succ m * n) :=
  rfl

@[simp]
theorem neg_succ_mul_neg_succ (m n : ℕ) : -[m+1] * -[n+1] = succ m * succ n :=
  rfl

#print Int.coe_nat_le /-
theorem coe_nat_le {m n : ℕ} : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
  coe_nat_le_coe_nat_iff m n
-/

#print Int.coe_nat_lt /-
theorem coe_nat_lt {m n : ℕ} : (↑m : ℤ) < ↑n ↔ m < n :=
  coe_nat_lt_coe_nat_iff m n
-/

theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n :=
  Int.coe_nat_eq_coe_nat_iff m n

theorem coe_nat_strict_mono : StrictMono (coe : ℕ → ℤ) := fun _ _ => Int.coe_nat_lt.2

theorem coe_nat_nonneg (n : ℕ) : 0 ≤ (n : ℤ) :=
  coe_nat_le.2 (Nat.zero_le _)

@[simp]
theorem neg_of_nat_ne_zero (n : ℕ) : -[n+1] ≠ 0 := fun h => Int.noConfusion h

@[simp]
theorem zero_ne_neg_of_nat (n : ℕ) : 0 ≠ -[n+1] := fun h => Int.noConfusion h

/-! ### succ and pred -/


/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) :=
  a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) :=
  a - 1

theorem nat_succ_eq_int_succ (n : ℕ) : (Nat.succ n : ℤ) = Int.succ n :=
  rfl

theorem pred_succ (a : ℤ) : pred (succ a) = a :=
  add_sub_cancel _ _

theorem succ_pred (a : ℤ) : succ (pred a) = a :=
  sub_add_cancel _ _

theorem neg_succ (a : ℤ) : -succ a = pred (-a) :=
  neg_add _ _

theorem succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]

theorem neg_pred (a : ℤ) : -pred a = succ (-a) := by rw [eq_neg_of_eq_neg (neg_succ (-a)).symm, neg_neg]

theorem pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]

theorem pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n :=
  pred_succ n

theorem neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) :=
  neg_succ n

theorem succ_neg_nat_succ (n : ℕ) : succ (-Nat.succ n) = -n :=
  succ_neg_succ n

#print Int.add_one_le_iff /-
theorem add_one_le_iff {a b : ℤ} : a + 1 ≤ b ↔ a < b :=
  Iff.rfl
-/

@[norm_cast]
theorem coe_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  cases n
  cases h
  simp

@[elab_as_elim]
protected theorem induction_on {p : ℤ → Prop} (i : ℤ) (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1))
    (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i := by
  induction i
  · induction i
    · exact hz
      
    · exact hp _ i_ih
      
    
  · have : ∀ n : ℕ, p (-n) := by
      intro n
      induction n
      · simp [hz]
        
      · convert hn _ n_ih using 1
        simp [sub_eq_neg_add]
        
    exact this (i + 1)
    

/-! ### nat abs -/


variable {a b : ℤ} {n : ℕ}

attribute [simp] nat_abs nat_abs_of_nat nat_abs_zero nat_abs_one

theorem nat_abs_add_le (a b : ℤ) : natAbs (a + b) ≤ natAbs a + natAbs b := by
  have : ∀ a b : ℕ, nat_abs (sub_nat_nat a (Nat.succ b)) ≤ Nat.succ (a + b) := by
    refine' fun a b : ℕ =>
      sub_nat_nat_elim a b.succ (fun m n i => n = b.succ → nat_abs i ≤ (m + b).succ) _ (fun i n e => _) rfl
    · rintro i n rfl
      rw [add_comm _ i, add_assoc]
      exact Nat.le_add_right i (b.succ + b).succ
      
    · apply succ_le_succ
      rw [← succ.inj e, ← add_assoc, add_comm]
      apply Nat.le_add_right
      
  cases a <;>
    cases' b with b b <;> simp [nat_abs, Nat.succ_add] <;> try rfl <;> [skip, rw [add_comm a b]] <;> apply this

theorem nat_abs_sub_le (a b : ℤ) : natAbs (a - b) ≤ natAbs a + natAbs b := by
  rw [sub_eq_add_neg, ← Int.nat_abs_neg b]
  apply nat_abs_add_le

theorem nat_abs_neg_of_nat (n : ℕ) : natAbs (negOfNat n) = n := by cases n <;> rfl

theorem nat_abs_mul (a b : ℤ) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;> simp only [← Int.mul_def, Int.mul, nat_abs_neg_of_nat, eq_self_iff_true, Int.natAbs]

theorem nat_abs_mul_nat_abs_eq {a b : ℤ} {c : ℕ} (h : a * b = (c : ℤ)) : a.natAbs * b.natAbs = c := by
  rw [← nat_abs_mul, h, nat_abs_of_nat]

@[simp]
theorem nat_abs_mul_self' (a : ℤ) : (natAbs a * natAbs a : ℤ) = a * a := by rw [← Int.coe_nat_mul, nat_abs_mul_self]

theorem neg_succ_of_nat_eq' (m : ℕ) : -[m+1] = -m - 1 := by simp [neg_succ_of_nat_eq, sub_eq_neg_add]

theorem nat_abs_ne_zero_of_ne_zero {z : ℤ} (hz : z ≠ 0) : z.natAbs ≠ 0 := fun h =>
  hz <| Int.eq_zero_of_nat_abs_eq_zero h

@[simp]
theorem nat_abs_eq_zero {a : ℤ} : a.natAbs = 0 ↔ a = 0 :=
  ⟨Int.eq_zero_of_nat_abs_eq_zero, fun h => h.symm ▸ rfl⟩

theorem nat_abs_ne_zero {a : ℤ} : a.natAbs ≠ 0 ↔ a ≠ 0 :=
  not_congr Int.nat_abs_eq_zero

theorem nat_abs_lt_nat_abs_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) : a.natAbs < b.natAbs := by
  lift b to ℕ using le_trans w₁ (le_of_lt w₂)
  lift a to ℕ using w₁
  simpa [coe_nat_lt] using w₂

theorem nat_abs_eq_nat_abs_iff {a b : ℤ} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b := by
  constructor <;> intro h
  · cases' Int.nat_abs_eq a with h₁ h₁ <;> cases' Int.nat_abs_eq b with h₂ h₂ <;> rw [h₁, h₂] <;> simp [h]
    
  · cases h <;> rw [h]
    rw [Int.nat_abs_neg]
    

theorem nat_abs_eq_iff {a : ℤ} {n : ℕ} : a.natAbs = n ↔ a = n ∨ a = -n := by
  rw [← Int.nat_abs_eq_nat_abs_iff, Int.nat_abs_of_nat]

/-! ### `/`  -/


@[simp]
theorem of_nat_div (m n : ℕ) : ofNat (m / n) = ofNat m / ofNat n :=
  rfl

@[simp, norm_cast]
theorem coe_nat_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n :=
  rfl

theorem neg_succ_of_nat_div (m : ℕ) {b : ℤ} (H : 0 < b) : -[m+1] / b = -(m / b + 1) :=
  match b, eq_succ_of_zero_lt H with
  | _, ⟨n, rfl⟩ => rfl

#print Int.zero_div /-
-- Will be generalized to Euclidean domains.
@[local simp]
protected theorem zero_div : ∀ b : ℤ, 0 / b = 0
  | (n : ℕ) => show ofNat _ = _ by simp
  | -[n+1] => show -ofNat _ = _ by simp
-/

#print Int.div_zero /-
-- Will be generalized to Euclidean domains.
@[local simp]
protected theorem div_zero : ∀ a : ℤ, a / 0 = 0
  | (n : ℕ) => show ofNat _ = _ by simp
  | -[n+1] => rfl
-/

#print Int.div_neg /-
@[simp]
protected theorem div_neg : ∀ a b : ℤ, a / -b = -(a / b)
  | (m : ℕ), 0 => show ofNat (m / 0) = -(m / 0 : ℕ) by rw [Nat.div_zero] <;> rfl
  | (m : ℕ), (n + 1 : ℕ) => rfl
  | (m : ℕ), -[n+1] => (neg_neg _).symm
  | -[m+1], 0 => rfl
  | -[m+1], (n + 1 : ℕ) => rfl
  | -[m+1], -[n+1] => rfl
-/

theorem div_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b = -((-a - 1) / b + 1) :=
  match a, b, eq_neg_succ_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by change (- -[m+1] : ℤ) with (m + 1 : ℤ) <;> rw [add_sub_cancel] <;> rfl

#print Int.div_nonneg /-
protected theorem div_nonneg {a b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b :=
  match a, b, eq_coe_of_zero_le Ha, eq_coe_of_zero_le Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => coe_zero_le _
-/

theorem div_neg' {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : a / b < 0 :=
  match a, b, eq_neg_succ_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => neg_succ_lt_zero _

#print Int.div_one /-
@[simp]
protected theorem div_one : ∀ a : ℤ, a / 1 = a
  | (n : ℕ) => congr_arg ofNat (Nat.div_one _)
  | -[n+1] => congr_arg negSucc (Nat.div_one _)
-/

#print Int.div_eq_zero_of_lt /-
theorem div_eq_zero_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
  match a, b, eq_coe_of_zero_le H1, eq_succ_of_zero_lt (lt_of_le_of_lt H1 H2), H2 with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 => congr_arg ofNat <| Nat.div_eq_of_lt <| lt_of_coe_nat_lt_coe_nat H2
-/

/-! ### mod -/


theorem of_nat_mod (m n : Nat) : (m % n : ℤ) = ofNat (m % n) :=
  rfl

@[simp, norm_cast]
theorem coe_nat_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n :=
  rfl

theorem neg_succ_of_nat_mod (m : ℕ) {b : ℤ} (bpos : 0 < b) : -[m+1] % b = b - 1 - m % b := by
  rw [sub_sub, add_comm] <;>
    exact
      match b, eq_succ_of_zero_lt bpos with
      | _, ⟨n, rfl⟩ => rfl

#print Int.mod_neg /-
@[simp]
theorem mod_neg : ∀ a b : ℤ, a % -b = a % b
  | (m : ℕ), n => @congr_arg ℕ ℤ _ _ (fun i => ↑(m % i)) (nat_abs_neg _)
  | -[m+1], n => @congr_arg ℕ ℤ _ _ (fun i => subNatNat i (Nat.succ (m % i))) (nat_abs_neg _)
-/

#print Int.zero_mod /-
-- Will be generalized to Euclidean domains.
@[local simp]
theorem zero_mod (b : ℤ) : 0 % b = 0 :=
  rfl
-/

#print Int.mod_zero /-
-- Will be generalized to Euclidean domains.
@[local simp]
theorem mod_zero : ∀ a : ℤ, a % 0 = a
  | (m : ℕ) => congr_arg ofNat <| Nat.mod_zero _
  | -[m+1] => congr_arg negSucc <| Nat.mod_zero _
-/

#print Int.mod_one /-
-- Will be generalized to Euclidean domains.
@[local simp]
theorem mod_one : ∀ a : ℤ, a % 1 = 0
  | (m : ℕ) => congr_arg ofNat <| Nat.mod_one _
  | -[m+1] => show (1 - (m % 1).succ : ℤ) = 0 by rw [Nat.mod_one] <;> rfl
-/

#print Int.mod_eq_of_lt /-
theorem mod_eq_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
  match a, b, eq_coe_of_zero_le H1, eq_coe_of_zero_le (le_trans H1 (le_of_lt H2)), H2 with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩, H2 => congr_arg ofNat <| Nat.mod_eq_of_lt (lt_of_coe_nat_lt_coe_nat H2)
-/

theorem mod_add_div_aux (m n : ℕ) : (n - (m % n + 1) - (n * (m / n) + n) : ℤ) = -[m+1] := by
  rw [← sub_sub, neg_succ_of_nat_coe, sub_sub (n : ℤ)]
  apply eq_neg_of_eq_neg
  rw [neg_sub, sub_sub_self, add_right_comm]
  exact @congr_arg ℕ ℤ _ _ (fun i => (i + 1 : ℤ)) (Nat.mod_add_div _ _).symm

#print Int.mod_add_div /-
theorem mod_add_div : ∀ a b : ℤ, a % b + b * (a / b) = a
  | (m : ℕ), (n : ℕ) => congr_arg ofNat (Nat.mod_add_div _ _)
  | (m : ℕ), -[n+1] =>
    show (_ + -(n + 1) * -(m / (n + 1) : ℕ) : ℤ) = _ by
      rw [neg_mul_neg] <;> exact congr_arg of_nat (Nat.mod_add_div _ _)
  | -[m+1], 0 => by rw [mod_zero, Int.div_zero] <;> rfl
  | -[m+1], (n + 1 : ℕ) => mod_add_div_aux m n.succ
  | -[m+1], -[n+1] => mod_add_div_aux m n.succ
-/

#print Int.div_add_mod /-
theorem div_add_mod (a b : ℤ) : b * (a / b) + a % b = a :=
  (add_comm _ _).trans (mod_add_div _ _)
-/

#print Int.mod_add_div' /-
theorem mod_add_div' (m k : ℤ) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _
-/

#print Int.div_add_mod' /-
theorem div_add_mod' (m k : ℤ) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _
-/

#print Int.mod_def /-
theorem mod_def (a b : ℤ) : a % b = a - b * (a / b) :=
  eq_sub_of_add_eq (mod_add_div _ _)
-/

/-! ### properties of `/` and `%` -/


@[simp]
theorem mul_div_mul_of_pos {a : ℤ} (b c : ℤ) (H : 0 < a) : a * b / (a * c) = b / c :=
  suffices ∀ (m k : ℕ) (b : ℤ), (m.succ * b / (m.succ * k) : ℤ) = b / k from
    match a, eq_succ_of_zero_lt H, c, eq_coe_or_neg c with
    | _, ⟨m, rfl⟩, _, ⟨k, Or.inl rfl⟩ => this _ _ _
    | _, ⟨m, rfl⟩, _, ⟨k, Or.inr rfl⟩ => by
      rw [mul_neg, Int.div_neg, Int.div_neg] <;> apply congr_arg Neg.neg <;> apply this
  fun m k b =>
  match b, k with
  | (n : ℕ), k => congr_arg ofNat (Nat.mul_div_mul _ _ m.succ_pos)
  | -[n+1], 0 => by rw [Int.coe_nat_zero, mul_zero, Int.div_zero, Int.div_zero]
  | -[n+1], k + 1 =>
    congr_arg negSucc <|
      show (m.succ * n + m) / (m.succ * k.succ) = n / k.succ by
        apply Nat.div_eq_of_lt_le
        · refine' le_trans _ (Nat.le_add_right _ _)
          rw [← Nat.mul_div_mul _ _ m.succ_pos]
          apply Nat.div_mul_le_self
          
        · change m.succ * n.succ ≤ _
          rw [mul_left_comm]
          apply Nat.mul_le_mul_left
          apply (Nat.div_lt_iff_lt_mul k.succ_pos).1
          apply Nat.lt_succ_self
          

@[simp]
theorem mul_div_mul_of_pos_left (a : ℤ) {b : ℤ} (H : 0 < b) (c : ℤ) : a * b / (c * b) = a / c := by
  rw [mul_comm, mul_comm c, mul_div_mul_of_pos _ _ H]

@[simp]
theorem mul_mod_mul_of_pos {a : ℤ} (H : 0 < a) (b c : ℤ) : a * b % (a * c) = a * (b % c) := by
  rw [mod_def, mod_def, mul_div_mul_of_pos _ _ H, mul_sub_left_distrib, mul_assoc]

#print Int.mul_div_cancel_of_mod_eq_zero /-
theorem mul_div_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : b * (a / b) = a := by
  have := mod_add_div a b <;> rwa [H, zero_add] at this
-/

#print Int.div_mul_cancel_of_mod_eq_zero /-
theorem div_mul_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : a / b * b = a := by
  rw [mul_comm, mul_div_cancel_of_mod_eq_zero H]
-/

theorem nat_abs_sign (z : ℤ) : z.sign.natAbs = if z = 0 then 0 else 1 := by rcases z with ((_ | _) | _) <;> rfl

theorem nat_abs_sign_of_nonzero {z : ℤ} (hz : z ≠ 0) : z.sign.natAbs = 1 := by rw [Int.nat_abs_sign, if_neg hz]

theorem sign_coe_nat_of_nonzero {n : ℕ} (hn : n ≠ 0) : Int.sign n = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact Int.sign_of_succ n

#print Int.sign_neg /-
@[simp]
theorem sign_neg (z : ℤ) : Int.sign (-z) = -Int.sign z := by rcases z with ((_ | _) | _) <;> rfl
-/

#print Int.div_sign /-
theorem div_sign : ∀ a b, a / sign b = a * sign b
  | a, (n + 1 : ℕ) => by unfold sign <;> simp
  | a, 0 => by simp [sign]
  | a, -[n+1] => by simp [sign]
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
-/

#print Int.mul_sign /-
theorem mul_sign : ∀ i : ℤ, i * sign i = natAbs i
  | (n + 1 : ℕ) => mul_one _
  | 0 => mul_zero _
  | -[n+1] => mul_neg_one _
-/

theorem of_nat_add_neg_succ_of_nat_of_lt {m n : ℕ} (h : m < n.succ) : ofNat m + -[n+1] = -[n - m+1] := by
  change sub_nat_nat _ _ = _
  have h' : n.succ - m = (n - m).succ
  apply succ_sub
  apply le_of_lt_succ h
  simp [*, sub_nat_nat]

@[simp]
theorem neg_add_neg (m n : ℕ) : -[m+1] + -[n+1] = -[Nat.succ (m + n)+1] :=
  rfl

/-! ### to_nat -/


theorem to_nat_eq_max : ∀ a : ℤ, (toNat a : ℤ) = max a 0
  | (n : ℕ) => (max_eq_left (coe_zero_le n)).symm
  | -[n+1] => (max_eq_right (le_of_lt (neg_succ_lt_zero n))).symm

@[simp]
theorem to_nat_zero : (0 : ℤ).toNat = 0 :=
  rfl

@[simp]
theorem to_nat_one : (1 : ℤ).toNat = 1 :=
  rfl

@[simp]
theorem to_nat_of_nonneg {a : ℤ} (h : 0 ≤ a) : (toNat a : ℤ) = a := by rw [to_nat_eq_max, max_eq_left h]

@[simp]
theorem to_nat_coe_nat (n : ℕ) : toNat ↑n = n :=
  rfl

@[simp]
theorem to_nat_coe_nat_add_one {n : ℕ} : ((n : ℤ) + 1).toNat = n + 1 :=
  rfl

theorem le_to_nat (a : ℤ) : a ≤ toNat a := by rw [to_nat_eq_max] <;> apply le_max_left

@[simp]
theorem le_to_nat_iff {n : ℕ} {z : ℤ} (h : 0 ≤ z) : n ≤ z.toNat ↔ (n : ℤ) ≤ z := by
  rw [← Int.coe_nat_le_coe_nat_iff, Int.to_nat_of_nonneg h]

theorem to_nat_add {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b).toNat = a.toNat + b.toNat := by
  lift a to ℕ using ha
  lift b to ℕ using hb
  norm_cast

theorem to_nat_add_nat {a : ℤ} (ha : 0 ≤ a) (n : ℕ) : (a + n).toNat = a.toNat + n := by
  lift a to ℕ using ha
  norm_cast

@[simp]
theorem pred_to_nat : ∀ i : ℤ, (i - 1).toNat = i.toNat - 1
  | (0 : ℕ) => rfl
  | (n + 1 : ℕ) => by simp
  | -[n+1] => rfl

@[simp]
theorem to_nat_sub_to_nat_neg : ∀ n : ℤ, ↑n.toNat - ↑(-n).toNat = n
  | (0 : ℕ) => rfl
  | (n + 1 : ℕ) => show ↑(n + 1) - (0 : ℤ) = n + 1 from sub_zero _
  | -[n+1] => show 0 - (n + 1 : ℤ) = _ from zero_sub _

@[simp]
theorem to_nat_add_to_nat_neg_eq_nat_abs : ∀ n : ℤ, n.toNat + (-n).toNat = n.natAbs
  | (0 : ℕ) => rfl
  | (n + 1 : ℕ) => show n + 1 + 0 = n + 1 from add_zero _
  | -[n+1] => show 0 + (n + 1) = n + 1 from zero_add _

/-- If `n : ℕ`, then `int.to_nat' n = some n`, if `n : ℤ` is negative, then `int.to_nat' n = none`.
-/
def toNat' : ℤ → Option ℕ
  | (n : ℕ) => some n
  | -[n+1] => none

theorem mem_to_nat' : ∀ (a : ℤ) (n : ℕ), n ∈ toNat' a ↔ a = n
  | (m : ℕ), n => Option.some_inj.trans coe_nat_inj'.symm
  | -[m+1], n => by constructor <;> intro h <;> cases h

@[simp]
theorem to_nat_neg_nat : ∀ n : ℕ, (-(n : ℤ)).toNat = 0
  | 0 => rfl
  | n + 1 => rfl

/-! ### units -/


@[simp]
theorem units_nat_abs (u : ℤˣ) : natAbs u = 1 :=
  Units.ext_iff.1 <|
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← nat_abs_mul, Units.mul_inv] <;> rfl, by
        rw [← nat_abs_mul, Units.inv_mul] <;> rfl⟩

theorem units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by simpa only [Units.ext_iff, units_nat_abs] using nat_abs_eq u

theorem is_unit_eq_one_or {a : ℤ} : IsUnit a → a = 1 ∨ a = -1
  | ⟨x, hx⟩ => hx ▸ (units_eq_one_or _).imp (congr_arg coe) (congr_arg coe)

theorem is_unit_iff {a : ℤ} : IsUnit a ↔ a = 1 ∨ a = -1 := by
  refine' ⟨fun h => is_unit_eq_one_or h, fun h => _⟩
  rcases h with (rfl | rfl)
  · exact is_unit_one
    
  · exact is_unit_one.neg
    

theorem is_unit_eq_or_eq_neg {a b : ℤ} (ha : IsUnit a) (hb : IsUnit b) : a = b ∨ a = -b := by
  rcases is_unit_eq_one_or hb with (rfl | rfl)
  · exact is_unit_eq_one_or ha
    
  · rwa [or_comm', neg_neg, ← is_unit_iff]
    

theorem eq_one_or_neg_one_of_mul_eq_one {z w : ℤ} (h : z * w = 1) : z = 1 ∨ z = -1 :=
  is_unit_iff.mp (is_unit_of_mul_eq_one z w h)

theorem eq_one_or_neg_one_of_mul_eq_one' {z w : ℤ} (h : z * w = 1) : z = 1 ∧ w = 1 ∨ z = -1 ∧ w = -1 := by
  have h' : w * z = 1 := mul_comm z w ▸ h
  rcases eq_one_or_neg_one_of_mul_eq_one h with (rfl | rfl) <;>
    rcases eq_one_or_neg_one_of_mul_eq_one h' with (rfl | rfl) <;> tauto

theorem is_unit_iff_nat_abs_eq {n : ℤ} : IsUnit n ↔ n.natAbs = 1 := by simp [nat_abs_eq_iff, is_unit_iff]

alias is_unit_iff_nat_abs_eq ↔ is_unit.nat_abs_eq _

@[norm_cast]
theorem of_nat_is_unit {n : ℕ} : IsUnit (n : ℤ) ↔ IsUnit n := by
  rw [Nat.is_unit_iff, is_unit_iff_nat_abs_eq, nat_abs_of_nat]

theorem is_unit_mul_self {a : ℤ} (ha : IsUnit a) : a * a = 1 :=
  (is_unit_eq_one_or ha).elim (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl

theorem is_unit_add_is_unit_eq_is_unit_add_is_unit {a b c d : ℤ} (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c)
    (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [is_unit_iff] at ha hb hc hd
  cases ha <;> cases hb <;> cases hc <;> cases hd <;> subst ha <;> subst hb <;> subst hc <;> subst hd <;> tidy

end Int

