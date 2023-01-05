/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module algebra.big_operators.intervals
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.Nat.Interval
import Mathbin.Tactic.Linarith.Default

/-!
# Results about big operators over intervals

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/


universe u v w

open BigOperators Nat

namespace Finset

section Generic

variable {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : Finset α} {a : α} {g f : α → β}

variable [CommMonoid β]

@[to_additive]
theorem prod_Ico_add' [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in ico a b, f (x + c)) = ∏ x in ico (a + c) (b + c), f x :=
  by
  rw [← map_add_right_Ico, Prod_map]
  rfl
#align finset.prod_Ico_add' Finset.prod_Ico_add'

@[to_additive]
theorem prod_Ico_add [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in ico a b, f (c + x)) = ∏ x in ico (a + c) (b + c), f x :=
  by
  convert prod_Ico_add' f a b c
  simp_rw [add_comm]
#align finset.prod_Ico_add Finset.prod_Ico_add

theorem sum_Ico_succ_top {δ : Type _} [AddCommMonoid δ] {a b : ℕ} (hab : a ≤ b) (f : ℕ → δ) :
    (∑ k in ico a (b + 1), f k) = (∑ k in ico a b, f k) + f b := by
  rw [Nat.Ico_succ_right_eq_insert_Ico hab, sum_insert right_not_mem_Ico, add_comm]
#align finset.sum_Ico_succ_top Finset.sum_Ico_succ_top

@[to_additive]
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in ico a (b + 1), f k) = (∏ k in ico a b, f k) * f b :=
  @sum_Ico_succ_top (Additive β) _ _ _ hab _
#align finset.prod_Ico_succ_top Finset.prod_Ico_succ_top

theorem sum_eq_sum_Ico_succ_bot {δ : Type _} [AddCommMonoid δ] {a b : ℕ} (hab : a < b) (f : ℕ → δ) :
    (∑ k in ico a b, f k) = f a + ∑ k in ico (a + 1) b, f k :=
  by
  have ha : a ∉ ico (a + 1) b := by simp
  rw [← sum_insert ha, Nat.Ico_insert_succ_left hab]
#align finset.sum_eq_sum_Ico_succ_bot Finset.sum_eq_sum_Ico_succ_bot

@[to_additive]
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
    (∏ k in ico a b, f k) = f a * ∏ k in ico (a + 1) b, f k :=
  @sum_eq_sum_Ico_succ_bot (Additive β) _ _ _ hab _
#align finset.prod_eq_prod_Ico_succ_bot Finset.prod_eq_prod_Ico_succ_bot

@[to_additive]
theorem prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in ico m n, f i) * ∏ i in ico n k, f i) = ∏ i in ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm <| prod_union <| Ico_disjoint_Ico_consecutive m n k
#align finset.prod_Ico_consecutive Finset.prod_Ico_consecutive

@[to_additive]
theorem prod_Ioc_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in ioc m n, f i) * ∏ i in ioc n k, f i) = ∏ i in ioc m k, f i :=
  by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)
#align finset.prod_Ioc_consecutive Finset.prod_Ioc_consecutive

@[to_additive]
theorem prod_Ioc_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in ioc a (b + 1), f k) = (∏ k in ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b), Nat.Ioc_succ_singleton, prod_singleton]
#align finset.prod_Ioc_succ_top Finset.prod_Ioc_succ_top

@[to_additive]
theorem prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
    ((∏ k in range m, f k) * ∏ k in ico m n, f k) = ∏ k in range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h
#align finset.prod_range_mul_prod_Ico Finset.prod_range_mul_prod_Ico

@[to_additive]
theorem prod_Ico_eq_mul_inv {δ : Type _} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    (∏ k in ico m n, f k) = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by rw [mul_comm] <;> exact prod_range_mul_prod_Ico f h
#align finset.prod_Ico_eq_mul_inv Finset.prod_Ico_eq_mul_inv

@[to_additive]
theorem prod_Ico_eq_div {δ : Type _} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    (∏ k in ico m n, f k) = (∏ k in range n, f k) / ∏ k in range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h
#align finset.prod_Ico_eq_div Finset.prod_Ico_eq_div

@[to_additive]
theorem prod_range_sub_prod_range {α : Type _} [CommGroup α] {f : ℕ → α} {n m : ℕ} (hnm : n ≤ m) :
    ((∏ k in range m, f k) / ∏ k in range n, f k) = ∏ k in (range m).filter fun k => n ≤ k, f k :=
  by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto
#align finset.prod_range_sub_prod_range Finset.prod_range_sub_prod_range

/-- The two ways of summing over `(i,j)` in the range `a<=i<=j<b` are equal. -/
theorem sum_Ico_Ico_comm {M : Type _} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i in Finset.ico a b, ∑ j in Finset.ico i b, f i j) =
      ∑ j in Finset.ico a b, ∑ i in Finset.ico a (j + 1), f i j :=
  by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine'
            Finset.sum_bij' (fun (x : Σi : ℕ, ℕ) _ => (⟨x.2, x.1⟩ : Σi : ℕ, ℕ)) _ (fun _ _ => rfl)
              (fun (x : Σi : ℕ, ℕ) _ => (⟨x.2, x.1⟩ : Σi : ℕ, ℕ)) _ (by rintro ⟨⟩ _ <;> rfl)
              (by rintro ⟨⟩ _ <;> rfl) <;>
          simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
        rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
      refine' ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;>
    linarith
#align finset.sum_Ico_Ico_comm Finset.sum_Ico_Ico_comm

@[to_additive]
theorem prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
    (∏ k in ico m n, f k) = ∏ k in range (n - m), f (m + k) :=
  by
  by_cases h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h : n ≤ m := le_of_not_ge h
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]
#align finset.prod_Ico_eq_prod_range Finset.prod_Ico_eq_prod_range

theorem prod_Ico_reflect (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j in ico k m, f (n - j)) = ∏ j in ico (n + 1 - m) (n + 1 - k), f j :=
  by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  cases' lt_or_le k m with hkm hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine' (prod_image _).symm
    simp only [mem_Ico]
    rintro i ⟨ki, im⟩ j ⟨kj, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
  · simp [Ico_eq_empty_of_le, tsub_le_tsub_left, hkm]
#align finset.prod_Ico_reflect Finset.prod_Ico_reflect

theorem sum_Ico_reflect {δ : Type _} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ n + 1) : (∑ j in ico k m, f (n - j)) = ∑ j in ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h
#align finset.sum_Ico_reflect Finset.sum_Ico_reflect

theorem prod_range_reflect (f : ℕ → β) (n : ℕ) :
    (∏ j in range n, f (n - 1 - j)) = ∏ j in range n, f j :=
  by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp
#align finset.prod_range_reflect Finset.prod_range_reflect

theorem sum_range_reflect {δ : Type _} [AddCommMonoid δ] (f : ℕ → δ) (n : ℕ) :
    (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n
#align finset.sum_range_reflect Finset.sum_range_reflect

@[simp]
theorem prod_Ico_id_eq_factorial : ∀ n : ℕ, (∏ x in ico 1 (n + 1), x) = n !
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ico_succ_top <| Nat.succ_le_succ <| zero_le n, Nat.factorial_succ,
      prod_Ico_id_eq_factorial n, Nat.succ_eq_add_one, mul_comm]
#align finset.prod_Ico_id_eq_factorial Finset.prod_Ico_id_eq_factorial

@[simp]
theorem prod_range_add_one_eq_factorial : ∀ n : ℕ, (∏ x in range n, x + 1) = n !
  | 0 => rfl
  | n + 1 => by simp [Finset.range_succ, prod_range_add_one_eq_factorial n]
#align finset.prod_range_add_one_eq_factorial Finset.prod_range_add_one_eq_factorial

section GaussSum

/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : (∑ i in range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, n - 1 - i := by
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i in range n, i + (n - 1 - i) := sum_add_distrib.symm
    _ = ∑ i in range n, n - 1 :=
      (sum_congr rfl) fun i hi => add_tsub_cancel_of_le <| Nat.le_pred_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]
    
#align finset.sum_range_id_mul_two Finset.sum_range_id_mul_two

/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : (∑ i in range n, i) = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n, Nat.mul_div_cancel] <;> exact by decide
#align finset.sum_range_id Finset.sum_range_id

end GaussSum

end Generic

section Nat

variable {β : Type _}

variable (f g : ℕ → β) {m n : ℕ}

section Group

variable [CommGroup β]

@[to_additive]
theorem prod_range_succ_div_prod : ((∏ i in range (n + 1), f i) / ∏ i in range n, f i) = f n :=
  div_eq_iff_eq_mul'.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_prod Finset.prod_range_succ_div_prod

@[to_additive]
theorem prod_range_succ_div_top : (∏ i in range (n + 1), f i) / f n = ∏ i in range n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_top Finset.prod_range_succ_div_top

@[to_additive]
theorem prod_Ico_div_bot (hmn : m < n) : (∏ i in ico m n, f i) / f m = ∏ i in ico (m + 1) n, f i :=
  div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _
#align finset.prod_Ico_div_bot Finset.prod_Ico_div_bot

@[to_additive]
theorem prod_Ico_succ_div_top (hmn : m ≤ n) :
    (∏ i in ico m (n + 1), f i) / f n = ∏ i in ico m n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_Ico_succ_top hmn _
#align finset.prod_Ico_succ_div_top Finset.prod_Ico_succ_div_top

end Group

end Nat

section Module

variable {R M : Type _} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}

open Finset

-- mathport name: «exprG »
-- The partial sum of `g`, starting from zero
local notation "G " n:80 => ∑ i in range n, g i

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "**Summation by parts**, also known as **Abel's lemma** or an **Abel transformation** -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `sum_Ico_by_parts [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hmn] [":" («term_<_» `m "<" `n)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          " in "
          (Term.app `ico [`m `n])
          ", "
          (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.app `g [`i])))
         "="
         («term_-_»
          («term_-_»
           (Algebra.Group.Defs.«term_•_»
            (Term.app `f [(«term_-_» `n "-" (num "1"))])
            " • "
            (Finset.Algebra.BigOperators.Intervals.termG_ "G " `n))
           "-"
           (Algebra.Group.Defs.«term_•_»
            (Term.app `f [`m])
            " • "
            (Finset.Algebra.BigOperators.Intervals.termG_ "G " `m)))
          "-"
          (BigOperators.Algebra.BigOperators.Basic.finset.sum
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           " in "
           (Term.app `ico [`m («term_-_» `n "-" (num "1"))])
           ", "
           (Algebra.Group.Defs.«term_•_»
            («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
            " • "
            (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₁ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  " in "
                  (Term.app `Ico [(«term_+_» `m "+" (num "1")) `n])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (Term.app `f [`i])
                   " • "
                   (Finset.Algebra.BigOperators.Intervals.termG_ "G " `i)))
                 "="
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  " in "
                  (Term.app `Ico [`m («term_-_» `n "-" (num "1"))])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (Term.app `f [(«term_+_» `i "+" (num "1"))])
                   " • "
                   (Finset.Algebra.BigOperators.Intervals.termG_
                    "G "
                    («term_+_» `i "+" (num "1")))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.Conv.conv
                   "conv"
                   []
                   ["in" [] `n]
                   "=>"
                   (Tactic.Conv.convSeq
                    (Tactic.Conv.convSeq1Indented
                     [(Tactic.Conv.convRw__
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          [(patternIgnore (token.«← » "←"))]
                          (Term.app `Nat.sub_add_cancel [(Term.app `Nat.one_le_of_lt [`hmn])]))]
                        "]"))])))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sum_Ico_add')]
                    "]")
                   [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₂ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  " in "
                  (Term.app `Ico [(«term_+_» `m "+" (num "1")) `n])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (Term.app `f [`i])
                   " • "
                   (Finset.Algebra.BigOperators.Intervals.termG_
                    "G "
                    («term_+_» `i "+" (num "1")))))
                 "="
                 («term_-_»
                  («term_+_»
                   (BigOperators.Algebra.BigOperators.Basic.finset.sum
                    "∑"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    " in "
                    (Term.app `Ico [`m («term_-_» `n "-" (num "1"))])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (Term.app `f [`i])
                     " • "
                     (Finset.Algebra.BigOperators.Intervals.termG_
                      "G "
                      («term_+_» `i "+" (num "1")))))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (Term.app `f [(«term_-_» `n "-" (num "1"))])
                    " • "
                    (Finset.Algebra.BigOperators.Intervals.termG_ "G " `n)))
                  "-"
                  (Algebra.Group.Defs.«term_•_»
                   (Term.app `f [`m])
                   " • "
                   (Finset.Algebra.BigOperators.Intervals.termG_
                    "G "
                    («term_+_» `m "+" (num "1")))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `sum_Ico_sub_bot [(Term.hole "_") `hmn]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `sum_Ico_succ_sub_top
                       [(Term.hole "_") (Term.app `Nat.le_pred_of_lt [`hmn])]))
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app `Nat.sub_add_cancel [(Term.app `pos_of_gt [`hmn])]))
                     ","
                     (Tactic.rwRule [] `sub_add_cancel)]
                    "]")
                   [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `sum_eq_sum_Ico_succ_bot [`hmn]))]
             "]")
            [])
           []
           (Tactic.Conv.conv
            "conv"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(Tactic.Conv.«conv_<;>_»
                (Tactic.Conv.pattern
                 "pattern"
                 [(Tactic.Conv.occs "(" "occs" ":=" (Tactic.Conv.occsIndexed [(num "2")]) ")")]
                 (Algebra.Group.Defs.«term_•_»
                  (Term.app `f [(Term.hole "_")])
                  " • "
                  (Term.app `g [(Term.hole "_")])))
                "<;>"
                (Tactic.Conv.paren
                 "("
                 (Tactic.Conv.convSeq
                  (Tactic.Conv.convSeq1Indented
                   [(Tactic.Conv.convRw__
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app `sum_range_succ_sub_sum [`g]))]
                      "]"))]))
                 ")"))])))
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `smul_sub)
              ","
              (Tactic.rwRule [] `sum_sub_distrib)
              ","
              (Tactic.rwRule [] `h₂)
              ","
              (Tactic.rwRule [] `h₁)]
             "]")
            [])
           []
           (Mathlib.Tactic.Conv.convLHS
            "conv_lhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(Tactic.Conv.congr "congr")
               []
               (Tactic.Conv.skip "skip")
               []
               (Tactic.Conv.convRw__
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_sub)
                  ","
                  (Tactic.rwRule [] `add_comm)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_sub)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sum_sub_distrib)]
                 "]"))])))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`i]
                 []
                 ","
                 («term_=_»
                  («term_-_»
                   (Algebra.Group.Defs.«term_•_»
                    (Term.app `f [`i])
                    " • "
                    (Finset.Algebra.BigOperators.Intervals.termG_
                     "G "
                     («term_+_» `i "+" (num "1"))))
                   "-"
                   (Algebra.Group.Defs.«term_•_»
                    (Term.app `f [(«term_+_» `i "+" (num "1"))])
                    " • "
                    (Finset.Algebra.BigOperators.Intervals.termG_
                     "G "
                     («term_+_» `i "+" (num "1")))))
                  "="
                  («term-_»
                   "-"
                   (Algebra.Group.Defs.«term_•_»
                    («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
                    " • "
                    (Finset.Algebra.BigOperators.Intervals.termG_
                     "G "
                     («term_+_» `i "+" (num "1"))))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`i])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_smul)] "]")
                   [])
                  []
                  (Tactic.abel "abel" [] [])]))))))
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `this)
              ","
              (Tactic.rwRule [] `sum_neg_distrib)
              ","
              (Tactic.rwRule [] `sum_range_succ)
              ","
              (Tactic.rwRule [] `smul_add)]
             "]")
            [])
           []
           (Tactic.abel "abel" [] [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₁ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 " in "
                 (Term.app `Ico [(«term_+_» `m "+" (num "1")) `n])
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  (Term.app `f [`i])
                  " • "
                  (Finset.Algebra.BigOperators.Intervals.termG_ "G " `i)))
                "="
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 " in "
                 (Term.app `Ico [`m («term_-_» `n "-" (num "1"))])
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  (Term.app `f [(«term_+_» `i "+" (num "1"))])
                  " • "
                  (Finset.Algebra.BigOperators.Intervals.termG_
                   "G "
                   («term_+_» `i "+" (num "1")))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.Conv.conv
                  "conv"
                  []
                  ["in" [] `n]
                  "=>"
                  (Tactic.Conv.convSeq
                   (Tactic.Conv.convSeq1Indented
                    [(Tactic.Conv.convRw__
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         [(patternIgnore (token.«← » "←"))]
                         (Term.app `Nat.sub_add_cancel [(Term.app `Nat.one_le_of_lt [`hmn])]))]
                       "]"))])))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sum_Ico_add')]
                   "]")
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 " in "
                 (Term.app `Ico [(«term_+_» `m "+" (num "1")) `n])
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  (Term.app `f [`i])
                  " • "
                  (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))
                "="
                («term_-_»
                 («term_+_»
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                   " in "
                   (Term.app `Ico [`m («term_-_» `n "-" (num "1"))])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (Term.app `f [`i])
                    " • "
                    (Finset.Algebra.BigOperators.Intervals.termG_
                     "G "
                     («term_+_» `i "+" (num "1")))))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (Term.app `f [(«term_-_» `n "-" (num "1"))])
                   " • "
                   (Finset.Algebra.BigOperators.Intervals.termG_ "G " `n)))
                 "-"
                 (Algebra.Group.Defs.«term_•_»
                  (Term.app `f [`m])
                  " • "
                  (Finset.Algebra.BigOperators.Intervals.termG_
                   "G "
                   («term_+_» `m "+" (num "1")))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `sum_Ico_sub_bot [(Term.hole "_") `hmn]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `sum_Ico_succ_sub_top
                      [(Term.hole "_") (Term.app `Nat.le_pred_of_lt [`hmn])]))
                    ","
                    (Tactic.rwRule [] (Term.app `Nat.sub_add_cancel [(Term.app `pos_of_gt [`hmn])]))
                    ","
                    (Tactic.rwRule [] `sub_add_cancel)]
                   "]")
                  [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `sum_eq_sum_Ico_succ_bot [`hmn]))]
            "]")
           [])
          []
          (Tactic.Conv.conv
           "conv"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.«conv_<;>_»
               (Tactic.Conv.pattern
                "pattern"
                [(Tactic.Conv.occs "(" "occs" ":=" (Tactic.Conv.occsIndexed [(num "2")]) ")")]
                (Algebra.Group.Defs.«term_•_»
                 (Term.app `f [(Term.hole "_")])
                 " • "
                 (Term.app `g [(Term.hole "_")])))
               "<;>"
               (Tactic.Conv.paren
                "("
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `sum_range_succ_sub_sum [`g]))]
                     "]"))]))
                ")"))])))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `smul_sub)
             ","
             (Tactic.rwRule [] `sum_sub_distrib)
             ","
             (Tactic.rwRule [] `h₂)
             ","
             (Tactic.rwRule [] `h₁)]
            "]")
           [])
          []
          (Mathlib.Tactic.Conv.convLHS
           "conv_lhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.congr "congr")
              []
              (Tactic.Conv.skip "skip")
              []
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_sub)
                 ","
                 (Tactic.rwRule [] `add_comm)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_sub)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sum_sub_distrib)]
                "]"))])))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`i]
                []
                ","
                («term_=_»
                 («term_-_»
                  (Algebra.Group.Defs.«term_•_»
                   (Term.app `f [`i])
                   " • "
                   (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1"))))
                  "-"
                  (Algebra.Group.Defs.«term_•_»
                   (Term.app `f [(«term_+_» `i "+" (num "1"))])
                   " • "
                   (Finset.Algebra.BigOperators.Intervals.termG_
                    "G "
                    («term_+_» `i "+" (num "1")))))
                 "="
                 («term-_»
                  "-"
                  (Algebra.Group.Defs.«term_•_»
                   («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
                   " • "
                   (Finset.Algebra.BigOperators.Intervals.termG_
                    "G "
                    («term_+_» `i "+" (num "1"))))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`i])
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_smul)] "]") [])
                 []
                 (Tactic.abel "abel" [] [])]))))))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `this)
             ","
             (Tactic.rwRule [] `sum_neg_distrib)
             ","
             (Tactic.rwRule [] `sum_range_succ)
             ","
             (Tactic.rwRule [] `smul_add)]
            "]")
           [])
          []
          (Tactic.abel "abel" [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abel "abel" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [] `sum_neg_distrib)
         ","
         (Tactic.rwRule [] `sum_range_succ)
         ","
         (Tactic.rwRule [] `smul_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sum_range_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sum_neg_distrib
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`i]
            []
            ","
            («term_=_»
             («term_-_»
              (Algebra.Group.Defs.«term_•_»
               (Term.app `f [`i])
               " • "
               (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1"))))
              "-"
              (Algebra.Group.Defs.«term_•_»
               (Term.app `f [(«term_+_» `i "+" (num "1"))])
               " • "
               (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))
             "="
             («term-_»
              "-"
              (Algebra.Group.Defs.«term_•_»
               («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
               " • "
               (Finset.Algebra.BigOperators.Intervals.termG_
                "G "
                («term_+_» `i "+" (num "1"))))))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`i])
             []
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_smul)] "]") [])
             []
             (Tactic.abel "abel" [] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`i])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_smul)] "]") [])
          []
          (Tactic.abel "abel" [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abel "abel" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_smul)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i]
       []
       ","
       («term_=_»
        («term_-_»
         (Algebra.Group.Defs.«term_•_»
          (Term.app `f [`i])
          " • "
          (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1"))))
         "-"
         (Algebra.Group.Defs.«term_•_»
          (Term.app `f [(«term_+_» `i "+" (num "1"))])
          " • "
          (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))
        "="
        («term-_»
         "-"
         (Algebra.Group.Defs.«term_•_»
          («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
          " • "
          (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_-_»
        (Algebra.Group.Defs.«term_•_»
         (Term.app `f [`i])
         " • "
         (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1"))))
        "-"
        (Algebra.Group.Defs.«term_•_»
         (Term.app `f [(«term_+_» `i "+" (num "1"))])
         " • "
         (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))
       "="
       («term-_»
        "-"
        (Algebra.Group.Defs.«term_•_»
         («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
         " • "
         (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (Algebra.Group.Defs.«term_•_»
        («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
        " • "
        (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
       " • "
       (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Algebra.BigOperators.Intervals.termG_', expected 'Finset.Algebra.BigOperators.Intervals.termG_._@.Algebra.BigOperators.Intervals._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- **Summation by parts**, also known as **Abel's lemma** or an **Abel transformation** -/
  theorem
    sum_Ico_by_parts
    ( hmn : m < n )
      :
        ∑ i in ico m n , f i • g i
          =
          f n - 1 • G n - f m • G m - ∑ i in ico m n - 1 , f i + 1 - f i • G i + 1
    :=
      by
        have
            h₁
              : ∑ i in Ico m + 1 n , f i • G i = ∑ i in Ico m n - 1 , f i + 1 • G i + 1
              :=
              by conv in n => rw [ ← Nat.sub_add_cancel Nat.one_le_of_lt hmn ] rw [ ← sum_Ico_add' ]
          have
            h₂
              :
                ∑ i in Ico m + 1 n , f i • G i + 1
                  =
                  ∑ i in Ico m n - 1 , f i • G i + 1 + f n - 1 • G n - f m • G m + 1
              :=
              by
                rw
                  [
                    ← sum_Ico_sub_bot _ hmn
                      ,
                      ← sum_Ico_succ_sub_top _ Nat.le_pred_of_lt hmn
                      ,
                      Nat.sub_add_cancel pos_of_gt hmn
                      ,
                      sub_add_cancel
                    ]
          rw [ sum_eq_sum_Ico_succ_bot hmn ]
          conv => pattern ( occs := 2 ) f _ • g _ <;> ( rw [ ← sum_range_succ_sub_sum g ] )
          simp_rw [ smul_sub , sum_sub_distrib , h₂ , h₁ ]
          conv_lhs => congr skip rw [ ← add_sub , add_comm , ← add_sub , ← sum_sub_distrib ]
          have
            : ∀ i , f i • G i + 1 - f i + 1 • G i + 1 = - f i + 1 - f i • G i + 1
              :=
              by intro i rw [ sub_smul ] abel
          simp_rw [ this , sum_neg_distrib , sum_range_succ , smul_add ]
          abel
#align finset.sum_Ico_by_parts Finset.sum_Ico_by_parts

variable (n)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "**Summation by parts** for ranges -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `sum_range_by_parts [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          " in "
          (Term.app `range [`n])
          ", "
          (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.app `g [`i])))
         "="
         («term_-_»
          (Algebra.Group.Defs.«term_•_»
           (Term.app `f [(«term_-_» `n "-" (num "1"))])
           " • "
           (Finset.Algebra.BigOperators.Intervals.termG_ "G " `n))
          "-"
          (BigOperators.Algebra.BigOperators.Basic.finset.sum
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           " in "
           (Term.app `range [(«term_-_» `n "-" (num "1"))])
           ", "
           (Algebra.Group.Defs.«term_•_»
            («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
            " • "
            (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Classical.«tacticBy_cases_:_» "by_cases" [`hn ":"] («term_=_» `n "=" (num "0")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `range_eq_Ico)
                ","
                (Tactic.rwRule
                 []
                 (Term.app `sum_Ico_by_parts [`f `g (Term.app `Nat.pos_of_ne_zero [`hn])]))
                ","
                (Tactic.rwRule [] `sum_range_zero)
                ","
                (Tactic.rwRule [] `smul_zero)
                ","
                (Tactic.rwRule [] `sub_zero)
                ","
                (Tactic.rwRule [] `range_eq_Ico)]
               "]")
              [])])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Classical.«tacticBy_cases_:_» "by_cases" [`hn ":"] («term_=_» `n "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `range_eq_Ico)
               ","
               (Tactic.rwRule
                []
                (Term.app `sum_Ico_by_parts [`f `g (Term.app `Nat.pos_of_ne_zero [`hn])]))
               ","
               (Tactic.rwRule [] `sum_range_zero)
               ","
               (Tactic.rwRule [] `smul_zero)
               ","
               (Tactic.rwRule [] `sub_zero)
               ","
               (Tactic.rwRule [] `range_eq_Ico)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `range_eq_Ico)
           ","
           (Tactic.rwRule
            []
            (Term.app `sum_Ico_by_parts [`f `g (Term.app `Nat.pos_of_ne_zero [`hn])]))
           ","
           (Tactic.rwRule [] `sum_range_zero)
           ","
           (Tactic.rwRule [] `smul_zero)
           ","
           (Tactic.rwRule [] `sub_zero)
           ","
           (Tactic.rwRule [] `range_eq_Ico)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `range_eq_Ico)
         ","
         (Tactic.rwRule
          []
          (Term.app `sum_Ico_by_parts [`f `g (Term.app `Nat.pos_of_ne_zero [`hn])]))
         ","
         (Tactic.rwRule [] `sum_range_zero)
         ","
         (Tactic.rwRule [] `smul_zero)
         ","
         (Tactic.rwRule [] `sub_zero)
         ","
         (Tactic.rwRule [] `range_eq_Ico)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_eq_Ico
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sum_range_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sum_Ico_by_parts [`f `g (Term.app `Nat.pos_of_ne_zero [`hn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.pos_of_ne_zero [`hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.pos_of_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Nat.pos_of_ne_zero [`hn])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_Ico_by_parts
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_eq_Ico
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`hn ":"] («term_=_» `n "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `n "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        (Term.app `range [`n])
        ", "
        (Algebra.Group.Defs.«term_•_» (Term.app `f [`i]) " • " (Term.app `g [`i])))
       "="
       («term_-_»
        (Algebra.Group.Defs.«term_•_»
         (Term.app `f [(«term_-_» `n "-" (num "1"))])
         " • "
         (Finset.Algebra.BigOperators.Intervals.termG_ "G " `n))
        "-"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         " in "
         (Term.app `range [(«term_-_» `n "-" (num "1"))])
         ", "
         (Algebra.Group.Defs.«term_•_»
          («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
          " • "
          (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Algebra.Group.Defs.«term_•_»
        (Term.app `f [(«term_-_» `n "-" (num "1"))])
        " • "
        (Finset.Algebra.BigOperators.Intervals.termG_ "G " `n))
       "-"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        " in "
        (Term.app `range [(«term_-_» `n "-" (num "1"))])
        ", "
        (Algebra.Group.Defs.«term_•_»
         («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
         " • "
         (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       " in "
       (Term.app `range [(«term_-_» `n "-" (num "1"))])
       ", "
       (Algebra.Group.Defs.«term_•_»
        («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
        " • "
        (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       («term_-_» (Term.app `f [(«term_+_» `i "+" (num "1"))]) "-" (Term.app `f [`i]))
       " • "
       (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Finset.Algebra.BigOperators.Intervals.termG_ "G " («term_+_» `i "+" (num "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Algebra.BigOperators.Intervals.termG_', expected 'Finset.Algebra.BigOperators.Intervals.termG_._@.Algebra.BigOperators.Intervals._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- **Summation by parts** for ranges -/
  theorem
    sum_range_by_parts
    : ∑ i in range n , f i • g i = f n - 1 • G n - ∑ i in range n - 1 , f i + 1 - f i • G i + 1
    :=
      by
        by_cases hn : n = 0
          · simp [ hn ]
          ·
            rw
              [
                range_eq_Ico
                  ,
                  sum_Ico_by_parts f g Nat.pos_of_ne_zero hn
                  ,
                  sum_range_zero
                  ,
                  smul_zero
                  ,
                  sub_zero
                  ,
                  range_eq_Ico
                ]
#align finset.sum_range_by_parts Finset.sum_range_by_parts

end Module

end Finset

