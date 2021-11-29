import Mathbin.Data.Num.Bitwise 
import Mathbin.Data.Int.CharZero 
import Mathbin.Data.Nat.Gcd 
import Mathbin.Data.Nat.Psub

/-!
# Properties of the binary representation of integers
-/


attribute [local simp] add_assocₓ

namespace PosNum

variable{α : Type _}

@[simp, normCast]
theorem cast_one [HasOne α] [Add α] : ((1 : PosNum) : α) = 1 :=
  rfl

@[simp]
theorem cast_one' [HasOne α] [Add α] : (PosNum.one : α) = 1 :=
  rfl

@[simp, normCast]
theorem cast_bit0 [HasOne α] [Add α] (n : PosNum) : (n.bit0 : α) = _root_.bit0 n :=
  rfl

@[simp, normCast]
theorem cast_bit1 [HasOne α] [Add α] (n : PosNum) : (n.bit1 : α) = _root_.bit1 n :=
  rfl

@[simp, normCast]
theorem cast_to_nat [AddMonoidₓ α] [HasOne α] : ∀ (n : PosNum), ((n : ℕ) : α) = n
| 1 => Nat.cast_one
| bit0 p => (Nat.cast_bit0 _).trans$ congr_argₓ _root_.bit0 p.cast_to_nat
| bit1 p => (Nat.cast_bit1 _).trans$ congr_argₓ _root_.bit1 p.cast_to_nat

@[simp, normCast]
theorem to_nat_to_int (n : PosNum) : ((n : ℕ) : ℤ) = n :=
  by 
    rw [←Int.nat_cast_eq_coe_nat, cast_to_nat]

@[simp, normCast]
theorem cast_to_int [AddGroupₓ α] [HasOne α] (n : PosNum) : ((n : ℤ) : α) = n :=
  by 
    rw [←to_nat_to_int, Int.cast_coe_nat, cast_to_nat]

theorem succ_to_nat : ∀ n, (succ n : ℕ) = n+1
| 1 => rfl
| bit0 p => rfl
| bit1 p =>
  (congr_argₓ _root_.bit0 (succ_to_nat p)).trans$
    show (((«expr↑ » p+1)+«expr↑ » p)+1) = ((«expr↑ » p+«expr↑ » p)+1)+1by 
      simp [add_left_commₓ]

theorem one_add (n : PosNum) : (1+n) = succ n :=
  by 
    cases n <;> rfl

theorem add_one (n : PosNum) : (n+1) = succ n :=
  by 
    cases n <;> rfl

@[normCast]
theorem add_to_nat : ∀ m n, ((m+n : PosNum) : ℕ) = m+n
| 1, b =>
  by 
    rw [one_add b, succ_to_nat, add_commₓ] <;> rfl
| a, 1 =>
  by 
    rw [add_one a, succ_to_nat] <;> rfl
| bit0 a, bit0 b =>
  (congr_argₓ _root_.bit0 (add_to_nat a b)).trans$
    show ((a+b)+a+b : ℕ) = (a+a)+b+b by 
      simp [add_left_commₓ]
| bit0 a, bit1 b =>
  (congr_argₓ _root_.bit1 (add_to_nat a b)).trans$
    show (((a+b)+a+b)+1 : ℕ) = (a+a)+(b+b)+1by 
      simp [add_left_commₓ]
| bit1 a, bit0 b =>
  (congr_argₓ _root_.bit1 (add_to_nat a b)).trans$
    show (((a+b)+a+b)+1 : ℕ) = ((a+a)+1)+b+b by 
      simp [add_commₓ, add_left_commₓ]
| bit1 a, bit1 b =>
  show (succ (a+b)+succ (a+b) : ℕ) = ((a+a)+1)+(b+b)+1by 
    rw [succ_to_nat, add_to_nat] <;> simp [add_left_commₓ]

theorem add_succ : ∀ (m n : PosNum), (m+succ n) = succ (m+n)
| 1, b =>
  by 
    simp [one_add]
| bit0 a, 1 => congr_argₓ bit0 (add_one a)
| bit1 a, 1 => congr_argₓ bit1 (add_one a)
| bit0 a, bit0 b => rfl
| bit0 a, bit1 b => congr_argₓ bit0 (add_succ a b)
| bit1 a, bit0 b => rfl
| bit1 a, bit1 b => congr_argₓ bit1 (add_succ a b)

theorem bit0_of_bit0 : ∀ n, _root_.bit0 n = bit0 n
| 1 => rfl
| bit0 p => congr_argₓ bit0 (bit0_of_bit0 p)
| bit1 p =>
  show bit0 (succ (_root_.bit0 p)) = _ by 
    rw [bit0_of_bit0] <;> rfl

theorem bit1_of_bit1 (n : PosNum) : _root_.bit1 n = bit1 n :=
  show (_root_.bit0 n+1) = bit1 n by 
    rw [add_one, bit0_of_bit0] <;> rfl

@[normCast]
theorem mul_to_nat m : ∀ n, ((m*n : PosNum) : ℕ) = m*n
| 1 => (mul_oneₓ _).symm
| bit0 p =>
  show («expr↑ » (m*p)+«expr↑ » (m*p) : ℕ) = «expr↑ » m*p+p by 
    rw [mul_to_nat, left_distrib]
| bit1 p =>
  (add_to_nat (bit0 (m*p)) m).trans$
    show ((«expr↑ » (m*p)+«expr↑ » (m*p))+«expr↑ » m : ℕ) = («expr↑ » m*p+p)+m by 
      rw [mul_to_nat, left_distrib]

theorem to_nat_pos : ∀ (n : PosNum), 0 < (n : ℕ)
| 1 => zero_lt_one
| bit0 p =>
  let h := to_nat_pos p 
  add_pos h h
| bit1 p => Nat.succ_posₓ _

theorem cmp_to_nat_lemma {m n : PosNum} : (m : ℕ) < n → (bit1 m : ℕ) < bit0 n :=
  show (m : ℕ) < n → (((m+m)+1)+1 : ℕ) ≤ n+n by 
    intro h <;> rw [Nat.add_right_comm m m 1, add_assocₓ] <;> exact add_le_add h h

theorem cmp_swap m : ∀ n, (cmp m n).swap = cmp n m :=
  by 
    induction' m with m IH m IH <;>
      intro n <;>
        cases' n with n n <;>
          try 
              unfold cmp <;>
            try 
                rfl <;>
              rw [←IH] <;> cases cmp m n <;> rfl

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cmp_to_nat : ∀
m n, (ordering.cases_on (cmp m n) «expr < »((m : exprℕ()), n) «expr = »(m, n) «expr < »((n : exprℕ()), m) : exprProp())
| 1, 1 := rfl
| bit0 a, 1 := let h : «expr ≤ »((1 : exprℕ()), a) := to_nat_pos a in
add_le_add h h
| bit1 a, 1 := «expr $ »(nat.succ_lt_succ, «expr $ »(to_nat_pos, bit0 a))
| 1, bit0 b := let h : «expr ≤ »((1 : exprℕ()), b) := to_nat_pos b in
add_le_add h h
| 1, bit1 b := «expr $ »(nat.succ_lt_succ, «expr $ »(to_nat_pos, bit0 b))
| bit0 a, bit0 b := begin
  have [] [] [":=", expr cmp_to_nat a b],
  revert [ident this],
  cases [expr cmp a b] []; dsimp [] [] [] []; intro [],
  { exact [expr add_lt_add this this] },
  { rw [expr this] [] },
  { exact [expr add_lt_add this this] }
end
| bit0 a, bit1 b := begin
  dsimp [] ["[", expr cmp, "]"] [] [],
  have [] [] [":=", expr cmp_to_nat a b],
  revert [ident this],
  cases [expr cmp a b] []; dsimp [] [] [] []; intro [],
  { exact [expr nat.le_succ_of_le (add_lt_add this this)] },
  { rw [expr this] [],
    apply [expr nat.lt_succ_self] },
  { exact [expr cmp_to_nat_lemma this] }
end
| bit1 a, bit0 b := begin
  dsimp [] ["[", expr cmp, "]"] [] [],
  have [] [] [":=", expr cmp_to_nat a b],
  revert [ident this],
  cases [expr cmp a b] []; dsimp [] [] [] []; intro [],
  { exact [expr cmp_to_nat_lemma this] },
  { rw [expr this] [],
    apply [expr nat.lt_succ_self] },
  { exact [expr nat.le_succ_of_le (add_lt_add this this)] }
end
| bit1 a, bit1 b := begin
  have [] [] [":=", expr cmp_to_nat a b],
  revert [ident this],
  cases [expr cmp a b] []; dsimp [] [] [] []; intro [],
  { exact [expr nat.succ_lt_succ (add_lt_add this this)] },
  { rw [expr this] [] },
  { exact [expr nat.succ_lt_succ (add_lt_add this this)] }
end

@[normCast]
theorem lt_to_nat {m n : PosNum} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with 
    | Ordering.lt, h =>
      by 
        simp  at h <;> simp [h]
    | Ordering.eq, h =>
      by 
        simp  at h <;>
          simp [h, lt_irreflₓ] <;>
            exact
              by 
                decide
    | Ordering.gt, h =>
      by 
        simp [not_lt_of_gtₓ h] <;>
          exact
            by 
              decide

@[normCast]
theorem le_to_nat {m n : PosNum} : (m : ℕ) ≤ n ↔ m ≤ n :=
  by 
    rw [←not_ltₓ] <;> exact not_congr lt_to_nat

end PosNum

namespace Num

variable{α : Type _}

open PosNum

theorem add_zeroₓ (n : Num) : (n+0) = n :=
  by 
    cases n <;> rfl

theorem zero_addₓ (n : Num) : (0+n) = n :=
  by 
    cases n <;> rfl

theorem add_one : ∀ (n : Num), (n+1) = succ n
| 0 => rfl
| Pos p =>
  by 
    cases p <;> rfl

theorem add_succ : ∀ (m n : Num), (m+succ n) = succ (m+n)
| 0, n =>
  by 
    simp [zero_addₓ]
| Pos p, 0 =>
  show Pos (p+1) = succ (Pos p+0)by 
    rw [PosNum.add_one, add_zeroₓ] <;> rfl
| Pos p, Pos q => congr_argₓ Pos (PosNum.add_succ _ _)

@[simp, normCast]
theorem add_of_nat m : ∀ n, ((m+n : ℕ) : Num) = m+n
| 0 => (add_zeroₓ _).symm
| n+1 =>
  show ((m+n : ℕ)+1 : Num) = m+«expr↑ » n+1by 
    rw [add_one, add_one, add_succ, add_of_nat]

theorem bit0_of_bit0 : ∀ (n : Num), bit0 n = n.bit0
| 0 => rfl
| Pos p => congr_argₓ Pos p.bit0_of_bit0

theorem bit1_of_bit1 : ∀ (n : Num), bit1 n = n.bit1
| 0 => rfl
| Pos p => congr_argₓ Pos p.bit1_of_bit1

@[simp, normCast]
theorem cast_zero [HasZero α] [HasOne α] [Add α] : ((0 : Num) : α) = 0 :=
  rfl

@[simp]
theorem cast_zero' [HasZero α] [HasOne α] [Add α] : (Num.zero : α) = 0 :=
  rfl

@[simp, normCast]
theorem cast_one [HasZero α] [HasOne α] [Add α] : ((1 : Num) : α) = 1 :=
  rfl

@[simp]
theorem cast_pos [HasZero α] [HasOne α] [Add α] (n : PosNum) : (Num.pos n : α) = n :=
  rfl

theorem succ'_to_nat : ∀ n, (succ' n : ℕ) = n+1
| 0 => (_root_.zero_add _).symm
| Pos p => PosNum.succ_to_nat _

theorem succ_to_nat n : (succ n : ℕ) = n+1 :=
  succ'_to_nat n

@[simp, normCast]
theorem cast_to_nat [AddMonoidₓ α] [HasOne α] : ∀ (n : Num), ((n : ℕ) : α) = n
| 0 => Nat.cast_zero
| Pos p => p.cast_to_nat

@[simp, normCast]
theorem to_nat_to_int (n : Num) : ((n : ℕ) : ℤ) = n :=
  by 
    rw [←Int.nat_cast_eq_coe_nat, cast_to_nat]

@[simp, normCast]
theorem cast_to_int [AddGroupₓ α] [HasOne α] (n : Num) : ((n : ℤ) : α) = n :=
  by 
    rw [←to_nat_to_int, Int.cast_coe_nat, cast_to_nat]

@[normCast]
theorem to_of_nat : ∀ (n : ℕ), ((n : Num) : ℕ) = n
| 0 => rfl
| n+1 =>
  by 
    rw [Nat.cast_add_one, add_one, succ_to_nat, to_of_nat]

@[simp, normCast]
theorem of_nat_cast [AddMonoidₓ α] [HasOne α] (n : ℕ) : ((n : Num) : α) = n :=
  by 
    rw [←cast_to_nat, to_of_nat]

@[normCast]
theorem of_nat_inj {m n : ℕ} : (m : Num) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective to_of_nat h, congr_argₓ _⟩

@[normCast]
theorem add_to_nat : ∀ m n, ((m+n : Num) : ℕ) = m+n
| 0, 0 => rfl
| 0, Pos q => (_root_.zero_add _).symm
| Pos p, 0 => rfl
| Pos p, Pos q => PosNum.add_to_nat _ _

@[normCast]
theorem mul_to_nat : ∀ m n, ((m*n : Num) : ℕ) = m*n
| 0, 0 => rfl
| 0, Pos q => (zero_mul _).symm
| Pos p, 0 => rfl
| Pos p, Pos q => PosNum.mul_to_nat _ _

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cmp_to_nat : ∀
m n, (ordering.cases_on (cmp m n) «expr < »((m : exprℕ()), n) «expr = »(m, n) «expr < »((n : exprℕ()), m) : exprProp())
| 0, 0 := rfl
| 0, pos b := to_nat_pos _
| pos a, 0 := to_nat_pos _
| pos a, pos b := by { have [] [] [":=", expr pos_num.cmp_to_nat a b]; revert [ident this]; dsimp [] ["[", expr cmp, "]"] [] []; cases [expr pos_num.cmp a b] [],
  exacts ["[", expr id, ",", expr congr_arg pos, ",", expr id, "]"] }

@[normCast]
theorem lt_to_nat {m n : Num} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with 
    | Ordering.lt, h =>
      by 
        simp  at h <;> simp [h]
    | Ordering.eq, h =>
      by 
        simp  at h <;>
          simp [h, lt_irreflₓ] <;>
            exact
              by 
                decide
    | Ordering.gt, h =>
      by 
        simp [not_lt_of_gtₓ h] <;>
          exact
            by 
              decide

@[normCast]
theorem le_to_nat {m n : Num} : (m : ℕ) ≤ n ↔ m ≤ n :=
  by 
    rw [←not_ltₓ] <;> exact not_congr lt_to_nat

end Num

namespace PosNum

@[simp]
theorem of_to_nat : ∀ (n : PosNum), ((n : ℕ) : Num) = Num.pos n
| 1 => rfl
| bit0 p =>
  show «expr↑ » (p+p : ℕ) = Num.pos p.bit0 by 
    rw [Num.add_of_nat, of_to_nat] <;> exact congr_argₓ Num.pos p.bit0_of_bit0
| bit1 p =>
  show (((p+p : ℕ) : Num)+1) = Num.pos p.bit1 by 
    rw [Num.add_of_nat, of_to_nat] <;> exact congr_argₓ Num.pos p.bit1_of_bit1

end PosNum

namespace Num

@[simp, normCast]
theorem of_to_nat : ∀ (n : Num), ((n : ℕ) : Num) = n
| 0 => rfl
| Pos p => p.of_to_nat

@[normCast]
theorem to_nat_inj {m n : Num} : (m : ℕ) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_nat h, congr_argₓ _⟩

/--
This tactic tries to turn an (in)equality about `num`s to one about `nat`s by rewriting.
```lean
example (n : num) (m : num) : n ≤ n + m :=
begin
  num.transfer_rw,
  exact nat.le_add_right _ _
end
```
-/
unsafe def transfer_rw : tactic Unit :=
  sorry

/--
This tactic tries to prove (in)equalities about `num`s by transfering them to the `nat` world and
then trying to call `simp`.
```lean
example (n : num) (m : num) : n ≤ n + m := by num.transfer
```
-/
unsafe def transfer : tactic Unit :=
  sorry

instance  : CommSemiringₓ Num :=
  by 
    refineStruct
        { add := ·+·, zero := 0, zero_add, add_zero, mul := ·*·, one := 1, nsmul := @nsmulRec Num ⟨0⟩ ⟨·+·⟩,
          npow := @npowRec Num ⟨1⟩ ⟨·*·⟩ } <;>
      try 
          intros 
          rfl <;>
        try 
            runTac 
              transfer <;>
          simp [mul_addₓ, mul_left_commₓ, mul_commₓ, add_commₓ]

instance  : OrderedCancelAddCommMonoid Num :=
  { Num.commSemiring with
    add_left_cancel :=
      by 
        intro a b c 
        runTac 
          transfer_rw 
        apply add_left_cancelₓ,
    lt := · < ·,
    lt_iff_le_not_le :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply lt_iff_le_not_leₓ,
    le := · ≤ ·,
    le_refl :=
      by 
        runTac 
          transfer,
    le_trans :=
      by 
        intro a b c 
        runTac 
          transfer_rw 
        apply le_transₓ,
    le_antisymm :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply le_antisymmₓ,
    add_le_add_left :=
      by 
        intro a b h c 
        revert h 
        runTac 
          transfer_rw 
        exact fun h => add_le_add_left h c,
    le_of_add_le_add_left :=
      by 
        intro a b c 
        runTac 
          transfer_rw 
        apply le_of_add_le_add_left }

instance  : LinearOrderedSemiring Num :=
  { Num.commSemiring, Num.orderedCancelAddCommMonoid with
    le_total :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply le_totalₓ,
    zero_le_one :=
      by 
        decide,
    mul_lt_mul_of_pos_left :=
      by 
        intro a b c 
        runTac 
          transfer_rw 
        apply mul_lt_mul_of_pos_left,
    mul_lt_mul_of_pos_right :=
      by 
        intro a b c 
        runTac 
          transfer_rw 
        apply mul_lt_mul_of_pos_right,
    decidableLt := Num.decidableLt, decidableLe := Num.decidableLe, DecidableEq := Num.decidableEq,
    exists_pair_ne :=
      ⟨0, 1,
        by 
          decide⟩ }

@[normCast]
theorem dvd_to_nat (m n : Num) : (m : ℕ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ =>
      ⟨k,
        by 
          rw [←of_to_nat n, e] <;> simp ⟩,
    fun ⟨k, e⟩ =>
      ⟨k,
        by 
          simp [e, mul_to_nat]⟩⟩

end Num

namespace PosNum

variable{α : Type _}

open Num

@[normCast]
theorem to_nat_inj {m n : PosNum} : (m : ℕ) = n ↔ m = n :=
  ⟨fun h =>
      Num.pos.inj$
        by 
          rw [←PosNum.of_to_nat, ←PosNum.of_to_nat, h],
    congr_argₓ _⟩

theorem pred'_to_nat : ∀ n, (pred' n : ℕ) = Nat.pred n
| 1 => rfl
| bit0 n =>
  have  : Nat.succ («expr↑ » (pred' n)) = «expr↑ » n :=
    by 
      rw [pred'_to_nat n, Nat.succ_pred_eq_of_posₓ (to_nat_pos n)]
  match pred' n, this with 
  | 0, (h : ((1 : Num) : ℕ) = n) =>
    by 
      rw [←to_nat_inj.1 h] <;> rfl
  | Num.pos p, (h : Nat.succ («expr↑ » p) = n) =>
    by 
      rw [←h] <;> exact (Nat.succ_add p p).symm
| bit1 n => rfl

@[simp]
theorem pred'_succ' n : pred' (succ' n) = n :=
  Num.to_nat_inj.1$
    by 
      rw [pred'_to_nat, succ'_to_nat, Nat.add_one, Nat.pred_succ]

@[simp]
theorem succ'_pred' n : succ' (pred' n) = n :=
  to_nat_inj.1$
    by 
      rw [succ'_to_nat, pred'_to_nat, Nat.add_one, Nat.succ_pred_eq_of_posₓ (to_nat_pos _)]

instance  : HasDvd PosNum :=
  ⟨fun m n => Pos m ∣ Pos n⟩

@[normCast]
theorem dvd_to_nat {m n : PosNum} : (m : ℕ) ∣ n ↔ m ∣ n :=
  Num.dvd_to_nat (Pos m) (Pos n)

theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
| 1 => Nat.size_one.symm
| bit0 n =>
  by 
    rw [size, succ_to_nat, size_to_nat, cast_bit0, Nat.size_bit0$ ne_of_gtₓ$ to_nat_pos n]
| bit1 n =>
  by 
    rw [size, succ_to_nat, size_to_nat, cast_bit1, Nat.size_bit1]

theorem size_eq_nat_size : ∀ n, (size n : ℕ) = nat_size n
| 1 => rfl
| bit0 n =>
  by 
    rw [size, succ_to_nat, nat_size, size_eq_nat_size]
| bit1 n =>
  by 
    rw [size, succ_to_nat, nat_size, size_eq_nat_size]

theorem nat_size_to_nat n : nat_size n = Nat.size n :=
  by 
    rw [←size_eq_nat_size, size_to_nat]

theorem nat_size_pos n : 0 < nat_size n :=
  by 
    cases n <;> apply Nat.succ_posₓ

/--
This tactic tries to turn an (in)equality about `pos_num`s to one about `nat`s by rewriting.
```lean
example (n : pos_num) (m : pos_num) : n ≤ n + m :=
begin
  pos_num.transfer_rw,
  exact nat.le_add_right _ _
end
```
-/
unsafe def transfer_rw : tactic Unit :=
  sorry

/--
This tactic tries to prove (in)equalities about `pos_num`s by transferring them to the `nat` world
and then trying to call `simp`.
```lean
example (n : pos_num) (m : pos_num) : n ≤ n + m := by pos_num.transfer
```
-/
unsafe def transfer : tactic Unit :=
  sorry

instance  : AddCommSemigroupₓ PosNum :=
  by 
    refine' { add := ·+·, .. } <;>
      runTac 
        transfer

instance  : CommMonoidₓ PosNum :=
  by 
    refineStruct { mul := ·*·, one := (1 : PosNum), npow := @npowRec PosNum ⟨1⟩ ⟨·*·⟩ } <;>
      try 
          intros 
          rfl <;>
        runTac 
          transfer

instance  : Distrib PosNum :=
  by 
    refine' { add := ·+·, mul := ·*·, .. } <;>
      ·
        runTac 
          transfer 
        simp [mul_addₓ, mul_commₓ]

instance  : LinearOrderₓ PosNum :=
  { lt := · < ·,
    lt_iff_le_not_le :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply lt_iff_le_not_leₓ,
    le := · ≤ ·,
    le_refl :=
      by 
        runTac 
          transfer,
    le_trans :=
      by 
        intro a b c 
        runTac 
          transfer_rw 
        apply le_transₓ,
    le_antisymm :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply le_antisymmₓ,
    le_total :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply le_totalₓ,
    decidableLt :=
      by 
        infer_instance,
    decidableLe :=
      by 
        infer_instance,
    DecidableEq :=
      by 
        infer_instance }

@[simp]
theorem cast_to_num (n : PosNum) : «expr↑ » n = Num.pos n :=
  by 
    rw [←cast_to_nat, ←of_to_nat n]

@[simp, normCast]
theorem bit_to_nat b n : (bit b n : ℕ) = Nat.bit b n :=
  by 
    cases b <;> rfl

@[simp, normCast]
theorem cast_add [AddMonoidₓ α] [HasOne α] m n : ((m+n : PosNum) : α) = m+n :=
  by 
    rw [←cast_to_nat, add_to_nat, Nat.cast_add, cast_to_nat, cast_to_nat]

@[simp, normCast]
theorem cast_succ [AddMonoidₓ α] [HasOne α] (n : PosNum) : (succ n : α) = n+1 :=
  by 
    rw [←add_one, cast_add, cast_one]

@[simp, normCast]
theorem cast_inj [AddMonoidₓ α] [HasOne α] [CharZero α] {m n : PosNum} : (m : α) = n ↔ m = n :=
  by 
    rw [←cast_to_nat m, ←cast_to_nat n, Nat.cast_inj, to_nat_inj]

@[simp]
theorem one_le_cast [LinearOrderedSemiring α] (n : PosNum) : (1 : α) ≤ n :=
  by 
    rw [←cast_to_nat, ←Nat.cast_one, Nat.cast_le] <;> apply to_nat_pos

@[simp]
theorem cast_pos [LinearOrderedSemiring α] (n : PosNum) : 0 < (n : α) :=
  lt_of_lt_of_leₓ zero_lt_one (one_le_cast n)

@[simp, normCast]
theorem cast_mul [Semiringₓ α] m n : ((m*n : PosNum) : α) = m*n :=
  by 
    rw [←cast_to_nat, mul_to_nat, Nat.cast_mul, cast_to_nat, cast_to_nat]

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem cmp_eq (m n) : «expr ↔ »(«expr = »(cmp m n, ordering.eq), «expr = »(m, n)) :=
begin
  have [] [] [":=", expr cmp_to_nat m n],
  cases [expr cmp m n] []; simp [] [] [] [] [] ["at", ident this, "⊢"]; try { exact [expr this] }; { simp [] [] [] ["[", expr show «expr ≠ »(m, n), from λ
     e, by rw [expr e] ["at", ident this]; exact [expr lt_irrefl _ this], "]"] [] [] }
end

@[simp, normCast]
theorem cast_lt [LinearOrderedSemiring α] {m n : PosNum} : (m : α) < n ↔ m < n :=
  by 
    rw [←cast_to_nat m, ←cast_to_nat n, Nat.cast_lt, lt_to_nat]

@[simp, normCast]
theorem cast_le [LinearOrderedSemiring α] {m n : PosNum} : (m : α) ≤ n ↔ m ≤ n :=
  by 
    rw [←not_ltₓ] <;> exact not_congr cast_lt

end PosNum

namespace Num

variable{α : Type _}

open PosNum

theorem bit_to_nat b n : (bit b n : ℕ) = Nat.bit b n :=
  by 
    cases b <;> cases n <;> rfl

theorem cast_succ' [AddMonoidₓ α] [HasOne α] n : (succ' n : α) = n+1 :=
  by 
    rw [←PosNum.cast_to_nat, succ'_to_nat, Nat.cast_add_one, cast_to_nat]

theorem cast_succ [AddMonoidₓ α] [HasOne α] n : (succ n : α) = n+1 :=
  cast_succ' n

@[simp, normCast]
theorem cast_add [Semiringₓ α] m n : ((m+n : Num) : α) = m+n :=
  by 
    rw [←cast_to_nat, add_to_nat, Nat.cast_add, cast_to_nat, cast_to_nat]

@[simp, normCast]
theorem cast_bit0 [Semiringₓ α] (n : Num) : (n.bit0 : α) = _root_.bit0 n :=
  by 
    rw [←bit0_of_bit0, _root_.bit0, cast_add] <;> rfl

@[simp, normCast]
theorem cast_bit1 [Semiringₓ α] (n : Num) : (n.bit1 : α) = _root_.bit1 n :=
  by 
    rw [←bit1_of_bit1, _root_.bit1, bit0_of_bit0, cast_add, cast_bit0] <;> rfl

@[simp, normCast]
theorem cast_mul [Semiringₓ α] : ∀ m n, ((m*n : Num) : α) = m*n
| 0, 0 => (zero_mul _).symm
| 0, Pos q => (zero_mul _).symm
| Pos p, 0 => (mul_zero _).symm
| Pos p, Pos q => PosNum.cast_mul _ _

theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
| 0 => Nat.size_zero.symm
| Pos p => p.size_to_nat

theorem size_eq_nat_size : ∀ n, (size n : ℕ) = nat_size n
| 0 => rfl
| Pos p => p.size_eq_nat_size

theorem nat_size_to_nat n : nat_size n = Nat.size n :=
  by 
    rw [←size_eq_nat_size, size_to_nat]

@[simp]
theorem of_nat'_zero : Num.ofNat' 0 = 0 :=
  by 
    simp [Num.ofNat']

@[simp]
theorem of_nat'_eq : ∀ n, Num.ofNat' n = n :=
  Nat.binaryRec
      (by 
        simp )$
    fun b n IH =>
      by 
        rw [of_nat'] at IH⊢
        rw [Nat.binary_rec_eq, IH]
        ·
          cases b <;> simp [Nat.bit, bit0_of_bit0, bit1_of_bit1]
        ·
          rfl

theorem zneg_to_znum (n : Num) : -n.to_znum = n.to_znum_neg :=
  by 
    cases n <;> rfl

theorem zneg_to_znum_neg (n : Num) : -n.to_znum_neg = n.to_znum :=
  by 
    cases n <;> rfl

theorem to_znum_inj {m n : Num} : m.to_znum = n.to_znum ↔ m = n :=
  ⟨fun h =>
      by 
        cases m <;> cases n <;> cases h <;> rfl,
    congr_argₓ _⟩

@[simp, normCast squash]
theorem cast_to_znum [HasZero α] [HasOne α] [Add α] [Neg α] : ∀ (n : Num), (n.to_znum : α) = n
| 0 => rfl
| Num.pos p => rfl

@[simp]
theorem cast_to_znum_neg [AddGroupₓ α] [HasOne α] : ∀ (n : Num), (n.to_znum_neg : α) = -n
| 0 => neg_zero.symm
| Num.pos p => rfl

@[simp]
theorem add_to_znum (m n : Num) : Num.toZnum (m+n) = m.to_znum+n.to_znum :=
  by 
    cases m <;> cases n <;> rfl

end Num

namespace PosNum

open Num

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pred_to_nat {n : pos_num} (h : «expr < »(1, n)) : «expr = »((pred n : exprℕ()), nat.pred n) :=
begin
  unfold [ident pred] [],
  have [] [] [":=", expr pred'_to_nat n],
  cases [expr e, ":", expr pred' n] [],
  { have [] [":", expr «expr ≤ »((1 : exprℕ()), nat.pred n)] [":=", expr nat.pred_le_pred ((@cast_lt exprℕ() _ _ _).2 h)],
    rw ["[", "<-", expr pred'_to_nat, ",", expr e, "]"] ["at", ident this],
    exact [expr absurd this exprdec_trivial()] },
  { rw ["[", "<-", expr pred'_to_nat, ",", expr e, "]"] [],
    refl }
end

theorem sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZnum :=
  by 
    cases a <;> rfl

theorem one_sub' (a : PosNum) : sub' 1 a = (pred' a).toZnumNeg :=
  by 
    cases a <;> rfl

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr$
    lt_iff_cmp.trans$
      by 
        rw [←cmp_swap] <;>
          cases cmp m n <;>
            exact
              by 
                decide

end PosNum

namespace Num

variable{α : Type _}

open PosNum

theorem pred_to_nat : ∀ (n : Num), (pred n : ℕ) = Nat.pred n
| 0 => rfl
| Pos p =>
  by 
    rw [pred, PosNum.pred'_to_nat] <;> rfl

theorem ppred_to_nat : ∀ (n : Num), coeₓ <$> ppred n = Nat.ppred n
| 0 => rfl
| Pos p =>
  by 
    rw [ppred, Option.map_some, Nat.ppred_eq_some.2] <;>
      rw [PosNum.pred'_to_nat, Nat.succ_pred_eq_of_posₓ (PosNum.to_nat_pos _)] <;> rfl

theorem cmp_swap m n : (cmp m n).swap = cmp n m :=
  by 
    cases m <;>
      cases n <;>
        try 
            unfold cmp <;>
          try 
              rfl <;>
            apply PosNum.cmp_swap

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cmp_eq (m n) : «expr ↔ »(«expr = »(cmp m n, ordering.eq), «expr = »(m, n)) :=
begin
  have [] [] [":=", expr cmp_to_nat m n],
  cases [expr cmp m n] []; simp [] [] [] [] [] ["at", ident this, "⊢"]; try { exact [expr this] }; { simp [] [] [] ["[", expr show «expr ≠ »(m, n), from λ
     e, by rw [expr e] ["at", ident this]; exact [expr lt_irrefl _ this], "]"] [] [] }
end

@[simp, normCast]
theorem cast_lt [LinearOrderedSemiring α] {m n : Num} : (m : α) < n ↔ m < n :=
  by 
    rw [←cast_to_nat m, ←cast_to_nat n, Nat.cast_lt, lt_to_nat]

@[simp, normCast]
theorem cast_le [LinearOrderedSemiring α] {m n : Num} : (m : α) ≤ n ↔ m ≤ n :=
  by 
    rw [←not_ltₓ] <;> exact not_congr cast_lt

@[simp, normCast]
theorem cast_inj [LinearOrderedSemiring α] {m n : Num} : (m : α) = n ↔ m = n :=
  by 
    rw [←cast_to_nat m, ←cast_to_nat n, Nat.cast_inj, to_nat_inj]

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr$
    lt_iff_cmp.trans$
      by 
        rw [←cmp_swap] <;>
          cases cmp m n <;>
            exact
              by 
                decide

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bitwise_to_nat
{f : num → num → num}
{g : bool → bool → bool}
(p : pos_num → pos_num → num)
(gff : «expr = »(g ff ff, ff))
(f00 : «expr = »(f 0 0, 0))
(f0n : ∀ n, «expr = »(f 0 (pos n), cond (g ff tt) (pos n) 0))
(fn0 : ∀ n, «expr = »(f (pos n) 0, cond (g tt ff) (pos n) 0))
(fnn : ∀ m n, «expr = »(f (pos m) (pos n), p m n))
(p11 : «expr = »(p 1 1, cond (g tt tt) 1 0))
(p1b : ∀ b n, «expr = »(p 1 (pos_num.bit b n), bit (g tt b) (cond (g ff tt) (pos n) 0)))
(pb1 : ∀ a m, «expr = »(p (pos_num.bit a m) 1, bit (g a tt) (cond (g tt ff) (pos m) 0)))
(pbb : ∀
 a
 b
 m
 n, «expr = »(p (pos_num.bit a m) (pos_num.bit b n), bit (g a b) (p m n))) : ∀
m n : num, «expr = »((f m n : exprℕ()), nat.bitwise g m n) :=
begin
  intros [],
  cases [expr m] ["with", ident m]; cases [expr n] ["with", ident n]; try { change [expr zero] ["with", expr 0] [] }; try { change [expr ((0 : num) : exprℕ())] ["with", expr 0] [] },
  { rw ["[", expr f00, ",", expr nat.bitwise_zero, "]"] []; refl },
  { unfold [ident nat.bitwise] [],
    rw ["[", expr f0n, ",", expr nat.binary_rec_zero, "]"] [],
    cases [expr g ff tt] []; refl },
  { unfold [ident nat.bitwise] [],
    generalize [ident h] [":"] [expr «expr = »((pos m : exprℕ()), m')],
    revert [ident h],
    apply [expr nat.bit_cases_on m' _],
    intros [ident b, ident m', ident h],
    rw ["[", expr fn0, ",", expr nat.binary_rec_eq, ",", expr nat.binary_rec_zero, ",", "<-", expr h, "]"] [],
    cases [expr g tt ff] []; refl,
    apply [expr nat.bitwise_bit_aux gff] },
  { rw [expr fnn] [],
    have [] [":", expr ∀
     (b)
     (n : pos_num), «expr = »((cond b «expr↑ »(n) 0 : exprℕ()), «expr↑ »((cond b (pos n) 0 : num)))] [":=", expr by intros []; cases [expr b] []; refl],
    induction [expr m] [] ["with", ident m, ident IH, ident m, ident IH] ["generalizing", ident n]; cases [expr n] ["with", ident n, ident n],
    any_goals { change [expr one] ["with", expr 1] [] },
    any_goals { change [expr pos 1] ["with", expr 1] [] },
    any_goals { change [expr pos_num.bit0] ["with", expr pos_num.bit ff] [] },
    any_goals { change [expr pos_num.bit1] ["with", expr pos_num.bit tt] [] },
    any_goals { change [expr ((1 : num) : exprℕ())] ["with", expr nat.bit tt 0] [] },
    all_goals { repeat { rw [expr show ∀
         b
         n, «expr = »((pos (pos_num.bit b n) : exprℕ()), nat.bit b «expr↑ »(n)), by intros []; cases [expr b] []; refl] [] },
      rw [expr nat.bitwise_bit] [] },
    any_goals { assumption },
    any_goals { rw ["[", expr nat.bitwise_zero, ",", expr p11, "]"] [],
      cases [expr g tt tt] []; refl },
    any_goals { rw ["[", expr nat.bitwise_zero_left, ",", expr this, ",", "<-", expr bit_to_nat, ",", expr p1b, "]"] [] },
    any_goals { rw ["[", expr nat.bitwise_zero_right _ gff, ",", expr this, ",", "<-", expr bit_to_nat, ",", expr pb1, "]"] [] },
    all_goals { rw ["[", "<-", expr show ∀
       n, «expr = »(«expr↑ »(p m n), nat.bitwise g «expr↑ »(m) «expr↑ »(n)), from IH, "]"] [],
      rw ["[", "<-", expr bit_to_nat, ",", expr pbb, "]"] [] } }
end

@[simp, normCast]
theorem lor_to_nat : ∀ m n, (lor m n : ℕ) = Nat.lorₓ m n :=
  by 
    apply bitwise_to_nat fun x y => Pos (PosNum.lor x y) <;>
      intros  <;>
        try 
            cases a <;>
          try 
              cases b <;>
            rfl

@[simp, normCast]
theorem land_to_nat : ∀ m n, (land m n : ℕ) = Nat.landₓ m n :=
  by 
    apply bitwise_to_nat PosNum.land <;>
      intros  <;>
        try 
            cases a <;>
          try 
              cases b <;>
            rfl

@[simp, normCast]
theorem ldiff_to_nat : ∀ m n, (ldiff m n : ℕ) = Nat.ldiff m n :=
  by 
    apply bitwise_to_nat PosNum.ldiff <;>
      intros  <;>
        try 
            cases a <;>
          try 
              cases b <;>
            rfl

@[simp, normCast]
theorem lxor_to_nat : ∀ m n, (lxor m n : ℕ) = Nat.lxor m n :=
  by 
    apply bitwise_to_nat PosNum.lxor <;>
      intros  <;>
        try 
            cases a <;>
          try 
              cases b <;>
            rfl

@[simp, normCast]
theorem shiftl_to_nat m n : (shiftl m n : ℕ) = Nat.shiftl m n :=
  by 
    cases m <;> dunfold shiftl
    ·
      symm 
      apply Nat.zero_shiftl 
    simp 
    induction' n with n IH
    ·
      rfl 
    simp [PosNum.shiftl, Nat.shiftl_succ]
    rw [←IH]

@[simp, normCast]
theorem shiftr_to_nat m n : (shiftr m n : ℕ) = Nat.shiftr m n :=
  by 
    cases' m with m <;> dunfold shiftr
    ·
      symm 
      apply Nat.zero_shiftr 
    induction' n with n IH generalizing m
    ·
      cases m <;> rfl 
    cases' m with m m <;> dunfold PosNum.shiftr
    ·
      rw [Nat.shiftr_eq_div_pow]
      symm 
      apply Nat.div_eq_of_ltₓ 
      exact
        @Nat.pow_lt_pow_of_lt_right 2
          (by 
            decide)
          0 (n+1) (Nat.succ_posₓ _)
    ·
      trans 
      apply IH 
      change Nat.shiftr m n = Nat.shiftr (bit1 m) (n+1)
      rw [add_commₓ n 1, Nat.shiftr_add]
      apply congr_argₓ fun x => Nat.shiftr x n 
      unfold Nat.shiftr 
      change (bit1 («expr↑ » m) : ℕ) with Nat.bit tt m 
      rw [Nat.div2_bit]
    ·
      trans 
      apply IH 
      change Nat.shiftr m n = Nat.shiftr (bit0 m) (n+1)
      rw [add_commₓ n 1, Nat.shiftr_add]
      apply congr_argₓ fun x => Nat.shiftr x n 
      unfold Nat.shiftr 
      change (bit0 («expr↑ » m) : ℕ) with Nat.bit ff m 
      rw [Nat.div2_bit]

@[simp]
theorem test_bit_to_nat m n : test_bit m n = Nat.testBit m n :=
  by 
    cases' m with m <;> unfold test_bit Nat.testBit
    ·
      change (zero : Nat) with 0
      rw [Nat.zero_shiftr]
      rfl 
    induction' n with n IH generalizing m <;> cases m <;> dunfold PosNum.testBit
    ·
      rfl
    ·
      exact (Nat.bodd_bit _ _).symm
    ·
      exact (Nat.bodd_bit _ _).symm
    ·
      change ff = Nat.bodd (Nat.shiftr 1 (n+1))
      rw [add_commₓ, Nat.shiftr_add]
      change Nat.shiftr 1 1 with 0
      rw [Nat.zero_shiftr] <;> rfl
    ·
      change PosNum.testBit m n = Nat.bodd (Nat.shiftr (Nat.bit tt m) (n+1))
      rw [add_commₓ, Nat.shiftr_add]
      unfold Nat.shiftr 
      rw [Nat.div2_bit]
      apply IH
    ·
      change PosNum.testBit m n = Nat.bodd (Nat.shiftr (Nat.bit ff m) (n+1))
      rw [add_commₓ, Nat.shiftr_add]
      unfold Nat.shiftr 
      rw [Nat.div2_bit]
      apply IH

end Num

namespace Znum

variable{α : Type _}

open PosNum

@[simp, normCast]
theorem cast_zero [HasZero α] [HasOne α] [Add α] [Neg α] : ((0 : Znum) : α) = 0 :=
  rfl

@[simp]
theorem cast_zero' [HasZero α] [HasOne α] [Add α] [Neg α] : (Znum.zero : α) = 0 :=
  rfl

@[simp, normCast]
theorem cast_one [HasZero α] [HasOne α] [Add α] [Neg α] : ((1 : Znum) : α) = 1 :=
  rfl

@[simp]
theorem cast_pos [HasZero α] [HasOne α] [Add α] [Neg α] (n : PosNum) : (Pos n : α) = n :=
  rfl

@[simp]
theorem cast_neg [HasZero α] [HasOne α] [Add α] [Neg α] (n : PosNum) : (neg n : α) = -n :=
  rfl

@[simp, normCast]
theorem cast_zneg [AddGroupₓ α] [HasOne α] : ∀ n, ((-n : Znum) : α) = -n
| 0 => neg_zero.symm
| Pos p => rfl
| neg p => (neg_negₓ _).symm

theorem neg_zero : (-0 : Znum) = 0 :=
  rfl

theorem zneg_pos (n : PosNum) : -Pos n = neg n :=
  rfl

theorem zneg_neg (n : PosNum) : -neg n = Pos n :=
  rfl

theorem zneg_zneg (n : Znum) : - -n = n :=
  by 
    cases n <;> rfl

theorem zneg_bit1 (n : Znum) : -n.bit1 = (-n).bitm1 :=
  by 
    cases n <;> rfl

theorem zneg_bitm1 (n : Znum) : -n.bitm1 = (-n).bit1 :=
  by 
    cases n <;> rfl

theorem zneg_succ (n : Znum) : -n.succ = (-n).pred :=
  by 
    cases n <;>
      try 
          rfl <;>
        rw [succ, Num.zneg_to_znum_neg] <;> rfl

theorem zneg_pred (n : Znum) : -n.pred = (-n).succ :=
  by 
    rw [←zneg_zneg (succ (-n)), zneg_succ, zneg_zneg]

@[simp, normCast]
theorem neg_of_int : ∀ n, ((-n : ℤ) : Znum) = -n
| (n+1 : ℕ) => rfl
| 0 => rfl
| -[1+ n] => (zneg_zneg _).symm

@[simp]
theorem abs_to_nat : ∀ n, (abs n : ℕ) = Int.natAbs n
| 0 => rfl
| Pos p => congr_argₓ Int.natAbs p.to_nat_to_int
| neg p =>
  show Int.natAbs ((p : ℕ) : ℤ) = Int.natAbs (-p)by 
    rw [p.to_nat_to_int, Int.nat_abs_neg]

@[simp]
theorem abs_to_znum : ∀ (n : Num), abs n.to_znum = n
| 0 => rfl
| Num.pos p => rfl

@[simp, normCast]
theorem cast_to_int [AddGroupₓ α] [HasOne α] : ∀ (n : Znum), ((n : ℤ) : α) = n
| 0 => rfl
| Pos p =>
  by 
    rw [cast_pos, cast_pos, PosNum.cast_to_int]
| neg p =>
  by 
    rw [cast_neg, cast_neg, Int.cast_neg, PosNum.cast_to_int]

theorem bit0_of_bit0 : ∀ (n : Znum), _root_.bit0 n = n.bit0
| 0 => rfl
| Pos a => congr_argₓ Pos a.bit0_of_bit0
| neg a => congr_argₓ neg a.bit0_of_bit0

theorem bit1_of_bit1 : ∀ (n : Znum), _root_.bit1 n = n.bit1
| 0 => rfl
| Pos a => congr_argₓ Pos a.bit1_of_bit1
| neg a =>
  show PosNum.sub' 1 (_root_.bit0 a) = _ by 
    rw [PosNum.one_sub', a.bit0_of_bit0] <;> rfl

@[simp, normCast]
theorem cast_bit0 [AddGroupₓ α] [HasOne α] : ∀ (n : Znum), (n.bit0 : α) = bit0 n
| 0 => (add_zeroₓ _).symm
| Pos p =>
  by 
    rw [Znum.bit0, cast_pos, cast_pos] <;> rfl
| neg p =>
  by 
    rw [Znum.bit0, cast_neg, cast_neg, PosNum.cast_bit0, _root_.bit0, _root_.bit0, neg_add_rev]

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp, norm_cast #[]] theorem cast_bit1 [add_group α] [has_one α] : ∀ n : znum, «expr = »((n.bit1 : α), bit1 n)
| 0 := by simp [] [] [] ["[", expr znum.bit1, ",", expr _root_.bit1, ",", expr _root_.bit0, "]"] [] []
| pos p := by rw ["[", expr znum.bit1, ",", expr cast_pos, ",", expr cast_pos, "]"] []; refl
| neg p := begin
  rw ["[", expr znum.bit1, ",", expr cast_neg, ",", expr cast_neg, "]"] [],
  cases [expr e, ":", expr pred' p] ["with", ident a]; have [] [":", expr «expr = »(p, _)] [":=", expr (succ'_pred' p).symm.trans (congr_arg num.succ' e)],
  { change [expr «expr = »(p, 1)] [] ["at", ident this],
    subst [expr p],
    simp [] [] [] ["[", expr _root_.bit1, ",", expr _root_.bit0, "]"] [] [] },
  { rw ["[", expr num.succ', "]"] ["at", ident this],
    subst [expr p],
    have [] [":", expr «expr = »((«expr↑ »((«expr- »(«expr↑ »(a)) : exprℤ())) : α), «expr + »(«expr- »(1), «expr↑ »((«expr + »(«expr- »(«expr↑ »(a)), 1) : exprℤ()))))] [],
    { simp [] [] [] ["[", expr add_comm, "]"] [] [] },
    simpa [] [] [] ["[", expr _root_.bit1, ",", expr _root_.bit0, ",", "-", ident add_comm, "]"] [] [] }
end

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem cast_bitm1 [add_group α] [has_one α] (n : znum) : «expr = »((n.bitm1 : α), «expr - »(bit0 n, 1)) :=
begin
  conv [] [] { to_lhs,
    rw ["<-", expr zneg_zneg n] },
  rw ["[", "<-", expr zneg_bit1, ",", expr cast_zneg, ",", expr cast_bit1, "]"] [],
  have [] [":", expr «expr = »(((«expr + »(«expr + »(«expr- »(1), n), n) : exprℤ()) : α), («expr + »(«expr + »(n, n), «expr- »(1)) : exprℤ()))] [],
  { simp [] [] [] ["[", expr add_comm, ",", expr add_left_comm, "]"] [] [] },
  simpa [] [] [] ["[", expr _root_.bit1, ",", expr _root_.bit0, ",", expr sub_eq_add_neg, ",", "-", ident int.add_neg_one, "]"] [] []
end

theorem add_zeroₓ (n : Znum) : (n+0) = n :=
  by 
    cases n <;> rfl

theorem zero_addₓ (n : Znum) : (0+n) = n :=
  by 
    cases n <;> rfl

theorem add_one : ∀ (n : Znum), (n+1) = succ n
| 0 => rfl
| Pos p => congr_argₓ Pos p.add_one
| neg p =>
  by 
    cases p <;> rfl

end Znum

namespace PosNum

variable{α : Type _}

theorem cast_to_znum : ∀ (n : PosNum), (n : Znum) = Znum.pos n
| 1 => rfl
| bit0 p => (Znum.bit0_of_bit0 p).trans$ congr_argₓ _ (cast_to_znum p)
| bit1 p => (Znum.bit1_of_bit1 p).trans$ congr_argₓ _ (cast_to_znum p)

attribute [-simp] Int.add_neg_one

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cast_sub' [add_group α] [has_one α] : ∀ m n : pos_num, «expr = »((sub' m n : α), «expr - »(m, n))
| a, 1 := by rw ["[", expr sub'_one, ",", expr num.cast_to_znum, ",", "<-", expr num.cast_to_nat, ",", expr pred'_to_nat, ",", "<-", expr nat.sub_one, "]"] []; simp [] [] [] ["[", expr pos_num.cast_pos, "]"] [] []
| 1, b := by rw ["[", expr one_sub', ",", expr num.cast_to_znum_neg, ",", "<-", expr neg_sub, ",", expr neg_inj, ",", "<-", expr num.cast_to_nat, ",", expr pred'_to_nat, ",", "<-", expr nat.sub_one, "]"] []; simp [] [] [] ["[", expr pos_num.cast_pos, "]"] [] []
| bit0 a, bit0 b := begin
  rw ["[", expr sub', ",", expr znum.cast_bit0, ",", expr cast_sub', "]"] [],
  have [] [":", expr «expr = »(((«expr + »(«expr + »(a, «expr- »(b)), «expr + »(a, «expr- »(b))) : exprℤ()) : α), «expr + »(«expr + »(a, a), «expr + »(«expr- »(b), «expr- »(b))))] [],
  { simp [] [] [] ["[", expr add_left_comm, "]"] [] [] },
  simpa [] [] [] ["[", expr _root_.bit0, ",", expr sub_eq_add_neg, "]"] [] []
end
| bit0 a, bit1 b := begin
  rw ["[", expr sub', ",", expr znum.cast_bitm1, ",", expr cast_sub', "]"] [],
  have [] [":", expr «expr = »(((«expr + »(«expr- »(b), «expr + »(a, «expr + »(«expr- »(b), «expr- »(1)))) : exprℤ()) : α), («expr + »(«expr + »(a, «expr- »(1)), «expr + »(«expr- »(b), «expr- »(b))) : exprℤ()))] [],
  { simp [] [] [] ["[", expr add_comm, ",", expr add_left_comm, "]"] [] [] },
  simpa [] [] [] ["[", expr _root_.bit1, ",", expr _root_.bit0, ",", expr sub_eq_add_neg, "]"] [] []
end
| bit1 a, bit0 b := begin
  rw ["[", expr sub', ",", expr znum.cast_bit1, ",", expr cast_sub', "]"] [],
  have [] [":", expr «expr = »(((«expr + »(«expr- »(b), «expr + »(a, «expr + »(«expr- »(b), 1))) : exprℤ()) : α), («expr + »(«expr + »(a, 1), «expr + »(«expr- »(b), «expr- »(b))) : exprℤ()))] [],
  { simp [] [] [] ["[", expr add_comm, ",", expr add_left_comm, "]"] [] [] },
  simpa [] [] [] ["[", expr _root_.bit1, ",", expr _root_.bit0, ",", expr sub_eq_add_neg, "]"] [] []
end
| bit1 a, bit1 b := begin
  rw ["[", expr sub', ",", expr znum.cast_bit0, ",", expr cast_sub', "]"] [],
  have [] [":", expr «expr = »(((«expr + »(«expr- »(b), «expr + »(a, «expr- »(b))) : exprℤ()) : α), «expr + »(a, «expr + »(«expr- »(b), «expr- »(b))))] [],
  { simp [] [] [] ["[", expr add_left_comm, "]"] [] [] },
  simpa [] [] [] ["[", expr _root_.bit1, ",", expr _root_.bit0, ",", expr sub_eq_add_neg, "]"] [] []
end

theorem to_nat_eq_succ_pred (n : PosNum) : (n : ℕ) = n.pred'+1 :=
  by 
    rw [←Num.succ'_to_nat, n.succ'_pred']

theorem to_int_eq_succ_pred (n : PosNum) : (n : ℤ) = (n.pred' : ℕ)+1 :=
  by 
    rw [←n.to_nat_to_int, to_nat_eq_succ_pred] <;> rfl

end PosNum

namespace Num

variable{α : Type _}

@[simp]
theorem cast_sub' [AddGroupₓ α] [HasOne α] : ∀ (m n : Num), (sub' m n : α) = m - n
| 0, 0 => (sub_zero _).symm
| Pos a, 0 => (sub_zero _).symm
| 0, Pos b => (zero_sub _).symm
| Pos a, Pos b => PosNum.cast_sub' _ _

@[simp]
theorem of_nat_to_znum : ∀ (n : ℕ), to_znum n = n
| 0 => rfl
| n+1 =>
  by 
    rw [Nat.cast_add_one, Nat.cast_add_one, Znum.add_one, add_one, ←of_nat_to_znum] <;> cases (n : Num) <;> rfl

@[simp]
theorem of_nat_to_znum_neg (n : ℕ) : to_znum_neg n = -n :=
  by 
    rw [←of_nat_to_znum, zneg_to_znum]

theorem mem_of_znum' : ∀ {m : Num} {n : Znum}, m ∈ of_znum' n ↔ n = to_znum m
| 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
| Pos m, 0 =>
  ⟨fun h =>
      by 
        cases h,
    fun h =>
      by 
        cases h⟩
| m, Znum.pos p =>
  Option.some_inj.trans$
    by 
      cases m <;>
        split  <;>
          intro h <;>
            try 
                cases h <;>
              rfl
| m, Znum.neg p =>
  ⟨fun h =>
      by 
        cases h,
    fun h =>
      by 
        cases m <;> cases h⟩

theorem of_znum'_to_nat : ∀ (n : Znum), coeₓ <$> of_znum' n = Int.toNat' n
| 0 => rfl
| Znum.pos p =>
  show _ = Int.toNat' p by 
    rw [←PosNum.to_nat_to_int p] <;> rfl
| Znum.neg p =>
  (congr_argₓ fun x => Int.toNat' (-x))$
    show ((p.pred'+1 : ℕ) : ℤ) = p by 
      rw [←succ'_to_nat] <;> simp 

@[simp]
theorem of_znum_to_nat : ∀ (n : Znum), (of_znum n : ℕ) = Int.toNat n
| 0 => rfl
| Znum.pos p =>
  show _ = Int.toNat p by 
    rw [←PosNum.to_nat_to_int p] <;> rfl
| Znum.neg p =>
  (congr_argₓ fun x => Int.toNat (-x))$
    show ((p.pred'+1 : ℕ) : ℤ) = p by 
      rw [←succ'_to_nat] <;> simp 

@[simp]
theorem cast_of_znum [AddGroupₓ α] [HasOne α] (n : Znum) : (of_znum n : α) = Int.toNat n :=
  by 
    rw [←cast_to_nat, of_znum_to_nat]

@[simp, normCast]
theorem sub_to_nat m n : ((m - n : Num) : ℕ) = m - n :=
  show (of_znum _ : ℕ) = _ by 
    rw [of_znum_to_nat, cast_sub', ←to_nat_to_int, ←to_nat_to_int, Int.to_nat_sub]

end Num

namespace Znum

variable{α : Type _}

@[simp, normCast]
theorem cast_add [AddGroupₓ α] [HasOne α] : ∀ m n, ((m+n : Znum) : α) = m+n
| 0, a =>
  by 
    cases a <;> exact (_root_.zero_add _).symm
| b, 0 =>
  by 
    cases b <;> exact (_root_.add_zero _).symm
| Pos a, Pos b => PosNum.cast_add _ _
| Pos a, neg b =>
  by 
    simpa only [sub_eq_add_neg] using PosNum.cast_sub' _ _
| neg a, Pos b =>
  have  : («expr↑ » b+-«expr↑ » a : α) = (-«expr↑ » a)+«expr↑ » b :=
    by 
      rw [←PosNum.cast_to_int a, ←PosNum.cast_to_int b, ←Int.cast_neg, ←Int.cast_add (-a)] <;> simp [add_commₓ]
  (PosNum.cast_sub' _ _).trans$ (sub_eq_add_neg _ _).trans this
| neg a, neg b =>
  show -(«expr↑ » (a+b) : α) = (-a)+-b by 
    rw [PosNum.cast_add, neg_eq_iff_neg_eq, neg_add_rev, neg_negₓ, neg_negₓ, ←PosNum.cast_to_int a,
        ←PosNum.cast_to_int b, ←Int.cast_add] <;>
      simp [add_commₓ]

@[simp]
theorem cast_succ [AddGroupₓ α] [HasOne α] n : ((succ n : Znum) : α) = n+1 :=
  by 
    rw [←add_one, cast_add, cast_one]

@[simp, normCast]
theorem mul_to_int : ∀ m n, ((m*n : Znum) : ℤ) = m*n
| 0, a =>
  by 
    cases a <;> exact (_root_.zero_mul _).symm
| b, 0 =>
  by 
    cases b <;> exact (_root_.mul_zero _).symm
| Pos a, Pos b => PosNum.cast_mul a b
| Pos a, neg b =>
  show -«expr↑ » (a*b) = «expr↑ » a*-«expr↑ » b by 
    rw [PosNum.cast_mul, neg_mul_eq_mul_neg]
| neg a, Pos b =>
  show -«expr↑ » (a*b) = (-«expr↑ » a)*«expr↑ » b by 
    rw [PosNum.cast_mul, neg_mul_eq_neg_mul]
| neg a, neg b =>
  show «expr↑ » (a*b) = (-«expr↑ » a)*-«expr↑ » b by 
    rw [PosNum.cast_mul, neg_mul_neg]

theorem cast_mul [Ringₓ α] m n : ((m*n : Znum) : α) = m*n :=
  by 
    rw [←cast_to_int, mul_to_int, Int.cast_mul, cast_to_int, cast_to_int]

@[simp, normCast]
theorem of_to_int : ∀ (n : Znum), ((n : ℤ) : Znum) = n
| 0 => rfl
| Pos a =>
  by 
    rw [cast_pos, ←PosNum.cast_to_nat, Int.cast_coe_nat', ←Num.of_nat_to_znum, PosNum.of_to_nat] <;> rfl
| neg a =>
  by 
    rw [cast_neg, neg_of_int, ←PosNum.cast_to_nat, Int.cast_coe_nat', ←Num.of_nat_to_znum_neg, PosNum.of_to_nat] <;> rfl

@[normCast]
theorem to_of_int : ∀ (n : ℤ), ((n : Znum) : ℤ) = n
| (n : ℕ) =>
  by 
    rw [Int.cast_coe_nat, ←Num.of_nat_to_znum, Num.cast_to_znum, ←Num.cast_to_nat, Int.nat_cast_eq_coe_nat,
      Num.to_of_nat]
| -[1+ n] =>
  by 
    rw [Int.cast_neg_succ_of_nat, cast_zneg, add_one, cast_succ, Int.neg_succ_of_nat_eq, ←Num.of_nat_to_znum,
      Num.cast_to_znum, ←Num.cast_to_nat, Int.nat_cast_eq_coe_nat, Num.to_of_nat]

theorem to_int_inj {m n : Znum} : (m : ℤ) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_int h, congr_argₓ _⟩

@[simp, normCast]
theorem of_int_cast [AddGroupₓ α] [HasOne α] (n : ℤ) : ((n : Znum) : α) = n :=
  by 
    rw [←cast_to_int, to_of_int]

@[simp, normCast]
theorem of_nat_cast [AddGroupₓ α] [HasOne α] (n : ℕ) : ((n : Znum) : α) = n :=
  of_int_cast n

@[simp]
theorem of_int'_eq : ∀ n, Znum.ofInt' n = n
| (n : ℕ) =>
  to_int_inj.1$
    by 
      simp [Znum.ofInt']
| -[1+ n] =>
  to_int_inj.1$
    by 
      simp [Znum.ofInt']

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cmp_to_int : ∀
m n, (ordering.cases_on (cmp m n) «expr < »((m : exprℤ()), n) «expr = »(m, n) «expr < »((n : exprℤ()), m) : exprProp())
| 0, 0 := rfl
| pos a, pos b := begin
  have [] [] [":=", expr pos_num.cmp_to_nat a b]; revert [ident this]; dsimp [] ["[", expr cmp, "]"] [] []; cases [expr pos_num.cmp a b] []; dsimp [] [] [] []; [simp [] [] [] [] [] [], exact [expr congr_arg pos], simp [] [] [] ["[", expr gt, "]"] [] []]
end
| neg a, neg b := begin
  have [] [] [":=", expr pos_num.cmp_to_nat b a]; revert [ident this]; dsimp [] ["[", expr cmp, "]"] [] []; cases [expr pos_num.cmp b a] []; dsimp [] [] [] []; [simp [] [] [] [] [] [], simp [] [] [] [] [] [] { contextual := tt }, simp [] [] [] ["[", expr gt, "]"] [] []]
end
| pos a, 0 := pos_num.cast_pos _
| pos a, neg b := lt_trans «expr $ »(neg_lt_zero.2, pos_num.cast_pos _) (pos_num.cast_pos _)
| 0, neg b := «expr $ »(neg_lt_zero.2, pos_num.cast_pos _)
| neg a, 0 := «expr $ »(neg_lt_zero.2, pos_num.cast_pos _)
| neg a, pos b := lt_trans «expr $ »(neg_lt_zero.2, pos_num.cast_pos _) (pos_num.cast_pos _)
| 0, pos b := pos_num.cast_pos _

@[normCast]
theorem lt_to_int {m n : Znum} : (m : ℤ) < n ↔ m < n :=
  show (m : ℤ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_int m n with 
    | Ordering.lt, h =>
      by 
        simp  at h <;> simp [h]
    | Ordering.eq, h =>
      by 
        simp  at h <;>
          simp [h, lt_irreflₓ] <;>
            exact
              by 
                decide
    | Ordering.gt, h =>
      by 
        simp [not_lt_of_gtₓ h] <;>
          exact
            by 
              decide

theorem le_to_int {m n : Znum} : (m : ℤ) ≤ n ↔ m ≤ n :=
  by 
    rw [←not_ltₓ] <;> exact not_congr lt_to_int

@[simp, normCast]
theorem cast_lt [LinearOrderedRing α] {m n : Znum} : (m : α) < n ↔ m < n :=
  by 
    rw [←cast_to_int m, ←cast_to_int n, Int.cast_lt, lt_to_int]

@[simp, normCast]
theorem cast_le [LinearOrderedRing α] {m n : Znum} : (m : α) ≤ n ↔ m ≤ n :=
  by 
    rw [←not_ltₓ] <;> exact not_congr cast_lt

@[simp, normCast]
theorem cast_inj [LinearOrderedRing α] {m n : Znum} : (m : α) = n ↔ m = n :=
  by 
    rw [←cast_to_int m, ←cast_to_int n, Int.cast_inj, to_int_inj]

/--
This tactic tries to turn an (in)equality about `znum`s to one about `int`s by rewriting.
```lean
example (n : znum) (m : znum) : n ≤ n + m * m :=
begin
  znum.transfer_rw,
  exact le_add_of_nonneg_right (mul_self_nonneg _)
end
```
-/
unsafe def transfer_rw : tactic Unit :=
  sorry

/--
This tactic tries to prove (in)equalities about `znum`s by transfering them to the `int` world and
then trying to call `simp`.
```lean
example (n : znum) (m : znum) : n ≤ n + m * m :=
begin
  znum.transfer,
  exact mul_self_nonneg _
end
```
-/
unsafe def transfer : tactic Unit :=
  sorry

instance  : LinearOrderₓ Znum :=
  { lt := · < ·,
    lt_iff_le_not_le :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply lt_iff_le_not_leₓ,
    le := · ≤ ·,
    le_refl :=
      by 
        runTac 
          transfer,
    le_trans :=
      by 
        intro a b c 
        runTac 
          transfer_rw 
        apply le_transₓ,
    le_antisymm :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply le_antisymmₓ,
    le_total :=
      by 
        intro a b 
        runTac 
          transfer_rw 
        apply le_totalₓ,
    DecidableEq := Znum.decidableEq, decidableLe := Znum.decidableLe, decidableLt := Znum.decidableLt }

instance  : AddCommGroupₓ Znum :=
  { add := ·+·,
    add_assoc :=
      by 
        runTac 
          transfer,
    zero := 0, zero_add := zero_addₓ, add_zero := add_zeroₓ,
    add_comm :=
      by 
        runTac 
          transfer,
    neg := Neg.neg,
    add_left_neg :=
      by 
        runTac 
          transfer }

instance  : LinearOrderedCommRing Znum :=
  { Znum.linearOrder, Znum.addCommGroup with mul := ·*·,
    mul_assoc :=
      by 
        runTac 
          transfer,
    one := 1,
    one_mul :=
      by 
        runTac 
          transfer,
    mul_one :=
      by 
        runTac 
          transfer,
    left_distrib :=
      by 
        runTac 
          transfer 
        simp [mul_addₓ],
    right_distrib :=
      by 
        runTac 
          transfer 
        simp [mul_addₓ, mul_commₓ],
    mul_comm :=
      by 
        runTac 
          transfer,
    exists_pair_ne :=
      ⟨0, 1,
        by 
          decide⟩,
    add_le_add_left :=
      by 
        intro a b h c 
        revert h 
        runTac 
          transfer_rw 
        exact fun h => add_le_add_left h c,
    mul_pos :=
      fun a b =>
        show 0 < a → 0 < b → 0 < a*b by 
          runTac 
            transfer_rw 
          apply mul_pos,
    zero_le_one :=
      by 
        decide }

@[simp, normCast]
theorem dvd_to_int (m n : Znum) : (m : ℤ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ =>
      ⟨k,
        by 
          rw [←of_to_int n, e] <;> simp ⟩,
    fun ⟨k, e⟩ =>
      ⟨k,
        by 
          simp [e]⟩⟩

end Znum

namespace PosNum

-- error in Data.Num.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem divmod_to_nat_aux
{n d : pos_num}
{q r : num}
(h₁ : «expr = »(«expr + »((r : exprℕ()), «expr * »(d, _root_.bit0 q)), n))
(h₂ : «expr < »((r : exprℕ()), «expr * »(2, d))) : «expr ∧ »(«expr = »((«expr + »((divmod_aux d q r).2, «expr * »(d, (divmod_aux d q r).1)) : exprℕ()), «expr↑ »(n)), «expr < »(((divmod_aux d q r).2 : exprℕ()), d)) :=
begin
  unfold [ident divmod_aux] [],
  have [] [":", expr ∀
   {r₂}, «expr ↔ »(«expr = »(num.of_znum' (num.sub' r (num.pos d)), some r₂), «expr = »((r : exprℕ()), «expr + »(r₂, d)))] [],
  { intro [ident r₂],
    apply [expr num.mem_of_znum'.trans],
    rw ["[", "<-", expr znum.to_int_inj, ",", expr num.cast_to_znum, ",", expr num.cast_sub', ",", expr sub_eq_iff_eq_add, ",", "<-", expr int.coe_nat_inj', "]"] [],
    simp [] [] [] [] [] [] },
  cases [expr e, ":", expr num.of_znum' (num.sub' r (num.pos d))] ["with", ident r₂]; simp [] [] [] ["[", expr divmod_aux, "]"] [] [],
  { refine [expr ⟨h₁, lt_of_not_ge (λ h, _)⟩],
    cases [expr nat.le.dest h] ["with", ident r₂, ident e'],
    rw ["[", "<-", expr num.to_of_nat r₂, ",", expr add_comm, "]"] ["at", ident e'],
    cases [expr e.symm.trans (this.2 e'.symm)] [] },
  { have [] [] [":=", expr this.1 e],
    split,
    { rwa ["[", expr _root_.bit1, ",", expr add_comm _ 1, ",", expr mul_add, ",", expr mul_one, ",", "<-", expr add_assoc, ",", "<-", expr this, "]"] [] },
    { rwa ["[", expr this, ",", expr two_mul, ",", expr add_lt_add_iff_right, "]"] ["at", ident h₂] } }
end

theorem divmod_to_nat (d n : PosNum) : (n / d : ℕ) = (divmod d n).1 ∧ (n % d : ℕ) = (divmod d n).2 :=
  by 
    rw [Nat.div_mod_unique (PosNum.cast_pos _)]
    induction' n with n IH n IH
    ·
      exact
        divmod_to_nat_aux
          (by 
            simp  <;> rfl)
          (Nat.mul_le_mul_leftₓ 2 (PosNum.cast_pos d : (0 : ℕ) < d))
    ·
      unfold divmod 
      cases' divmod d n with q r 
      simp only [divmod] at IH⊢
      apply divmod_to_nat_aux <;> simp 
      ·
        rw [_root_.bit1, _root_.bit1, add_right_commₓ, bit0_eq_two_mul («expr↑ » n), ←IH.1, mul_addₓ, ←bit0_eq_two_mul,
          mul_left_commₓ, ←bit0_eq_two_mul]
      ·
        rw [←bit0_eq_two_mul]
        exact Nat.bit1_lt_bit0 IH.2
    ·
      unfold divmod 
      cases' divmod d n with q r 
      simp only [divmod] at IH⊢
      apply divmod_to_nat_aux <;> simp 
      ·
        rw [bit0_eq_two_mul («expr↑ » n), ←IH.1, mul_addₓ, ←bit0_eq_two_mul, mul_left_commₓ, ←bit0_eq_two_mul]
      ·
        rw [←bit0_eq_two_mul]
        exact Nat.bit0_lt IH.2

@[simp]
theorem div'_to_nat n d : (div' n d : ℕ) = n / d :=
  (divmod_to_nat _ _).1.symm

@[simp]
theorem mod'_to_nat n d : (mod' n d : ℕ) = n % d :=
  (divmod_to_nat _ _).2.symm

end PosNum

namespace Num

@[simp]
protected theorem div_zero (n : Num) : n / 0 = 0 :=
  show n.div 0 = 0 by 
    cases n 
    rfl 
    simp [Num.div]

@[simp, normCast]
theorem div_to_nat : ∀ n d, ((n / d : Num) : ℕ) = n / d
| 0, 0 =>
  by 
    simp 
| 0, Pos d => (Nat.zero_divₓ _).symm
| Pos n, 0 => (Nat.div_zeroₓ _).symm
| Pos n, Pos d => PosNum.div'_to_nat _ _

@[simp]
protected theorem mod_zero (n : Num) : n % 0 = n :=
  show n.mod 0 = n by 
    cases n 
    rfl 
    simp [Num.mod]

@[simp, normCast]
theorem mod_to_nat : ∀ n d, ((n % d : Num) : ℕ) = n % d
| 0, 0 =>
  by 
    simp 
| 0, Pos d => (Nat.zero_modₓ _).symm
| Pos n, 0 => (Nat.mod_zeroₓ _).symm
| Pos n, Pos d => PosNum.mod'_to_nat _ _

theorem gcd_to_nat_aux : ∀ {n} {a b : Num}, a ≤ b → (a*b).natSize ≤ n → (gcd_aux n a b : ℕ) = Nat.gcdₓ a b
| 0, 0, b, ab, h => (Nat.gcd_zero_leftₓ _).symm
| 0, Pos a, 0, ab, h => (not_lt_of_geₓ ab).elim rfl
| 0, Pos a, Pos b, ab, h => (not_lt_of_le h).elim$ PosNum.nat_size_pos _
| Nat.succ n, 0, b, ab, h => (Nat.gcd_zero_leftₓ _).symm
| Nat.succ n, Pos a, b, ab, h =>
  by 
    simp [gcd_aux]
    rw [Nat.gcd_recₓ, gcd_to_nat_aux, mod_to_nat]
    ·
      rfl
    ·
      rw [←le_to_nat, mod_to_nat]
      exact le_of_ltₓ (Nat.mod_ltₓ _ (PosNum.cast_pos _))
    rw [nat_size_to_nat, mul_to_nat, Nat.size_le] at h⊢
    rw [mod_to_nat, mul_commₓ]
    rw [pow_succ'ₓ, ←Nat.mod_add_divₓ b (Pos a)] at h 
    refine' lt_of_mul_lt_mul_right (lt_of_le_of_ltₓ _ h) (Nat.zero_leₓ 2)
    rw [mul_two, mul_addₓ]
    refine' add_le_add_left (Nat.mul_le_mul_leftₓ _ (le_transₓ (le_of_ltₓ (Nat.mod_ltₓ _ (PosNum.cast_pos _))) _)) _ 
    suffices  : 1 ≤ _ 
    simpa using Nat.mul_le_mul_leftₓ (Pos a) this 
    rw [Nat.le_div_iff_mul_leₓ _ _ a.cast_pos, one_mulₓ]
    exact le_to_nat.2 ab

@[simp]
theorem gcd_to_nat : ∀ a b, (gcd a b : ℕ) = Nat.gcdₓ a b :=
  have  : ∀ (a b : Num), (a*b).natSize ≤ a.nat_size+b.nat_size :=
    by 
      intros 
      simp [nat_size_to_nat]
      rw [Nat.size_le, pow_addₓ]
      exact mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _) (Nat.zero_leₓ _) (Nat.zero_leₓ _)
  by 
    intros 
    unfold gcd 
    splitIfs
    ·
      exact gcd_to_nat_aux h (this _ _)
    ·
      rw [Nat.gcd_commₓ]
      exact gcd_to_nat_aux (le_of_not_leₓ h) (this _ _)

theorem dvd_iff_mod_eq_zero {m n : Num} : m ∣ n ↔ n % m = 0 :=
  by 
    rw [←dvd_to_nat, Nat.dvd_iff_mod_eq_zeroₓ, ←to_nat_inj, mod_to_nat] <;> rfl

instance decidable_dvd : DecidableRel (· ∣ · : Num → Num → Prop)
| a, b => decidableOfIff' _ dvd_iff_mod_eq_zero

end Num

instance PosNum.decidableDvd : DecidableRel (· ∣ · : PosNum → PosNum → Prop)
| a, b => Num.decidableDvd _ _

namespace Znum

@[simp]
protected theorem div_zero (n : Znum) : n / 0 = 0 :=
  show n.div 0 = 0 by 
    cases n <;>
      first |
        rfl|
        simp [Znum.div]

@[simp, normCast]
theorem div_to_int : ∀ n d, ((n / d : Znum) : ℤ) = n / d
| 0, 0 =>
  by 
    simp [Int.div_zero]
| 0, Pos d => (Int.zero_div _).symm
| 0, neg d => (Int.zero_div _).symm
| Pos n, 0 => (Int.div_zero _).symm
| neg n, 0 => (Int.div_zero _).symm
| Pos n, Pos d =>
  (Num.cast_to_znum _).trans$
    by 
      rw [←Num.to_nat_to_int] <;> simp 
| Pos n, neg d =>
  (Num.cast_to_znum_neg _).trans$
    by 
      rw [←Num.to_nat_to_int] <;> simp 
| neg n, Pos d =>
  show -_ = -_ / «expr↑ » d by 
    rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ←PosNum.to_nat_to_int, Num.succ'_to_nat, Num.div_to_nat]
    change -[1+ n.pred' / «expr↑ » d] = -[1+ n.pred' / d.pred'+1]
    rw [d.to_nat_eq_succ_pred]
| neg n, neg d =>
  show «expr↑ » (PosNum.pred' n / Num.pos d).succ' = -_ / -«expr↑ » d by 
    rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ←PosNum.to_nat_to_int, Num.succ'_to_nat, Num.div_to_nat]
    change (Nat.succ (_ / d) : ℤ) = Nat.succ (n.pred' / d.pred'+1)
    rw [d.to_nat_eq_succ_pred]

@[simp, normCast]
theorem mod_to_int : ∀ n d, ((n % d : Znum) : ℤ) = n % d
| 0, d => (Int.zero_mod _).symm
| Pos n, d =>
  (Num.cast_to_znum _).trans$
    by 
      rw [←Num.to_nat_to_int, cast_pos, Num.mod_to_nat, ←PosNum.to_nat_to_int, abs_to_nat] <;> rfl
| neg n, d =>
  (Num.cast_sub' _ _).trans$
    by 
      rw [←Num.to_nat_to_int, cast_neg, ←Num.to_nat_to_int, Num.succ_to_nat, Num.mod_to_nat, abs_to_nat,
          ←Int.sub_nat_nat_eq_coe, n.to_int_eq_succ_pred] <;>
        rfl

@[simp]
theorem gcd_to_nat a b : (gcd a b : ℕ) = Int.gcdₓ a b :=
  (Num.gcd_to_nat _ _).trans$
    by 
      simpa

theorem dvd_iff_mod_eq_zero {m n : Znum} : m ∣ n ↔ n % m = 0 :=
  by 
    rw [←dvd_to_int, Int.dvd_iff_mod_eq_zero, ←to_int_inj, mod_to_int] <;> rfl

instance  : DecidableRel (· ∣ · : Znum → Znum → Prop)
| a, b => decidableOfIff' _ dvd_iff_mod_eq_zero

end Znum

namespace Int

/-- Cast a `snum` to the corresponding integer. -/
def of_snum : Snum → ℤ :=
  Snum.rec' (fun a => cond a (-1) 0) fun a p IH => cond a (bit1 IH) (bit0 IH)

instance snum_coe : Coe Snum ℤ :=
  ⟨of_snum⟩

end Int

instance  : LT Snum :=
  ⟨fun a b => (a : ℤ) < b⟩

instance  : LE Snum :=
  ⟨fun a b => (a : ℤ) ≤ b⟩

