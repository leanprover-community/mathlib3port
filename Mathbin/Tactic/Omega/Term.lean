/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.term
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.Coeffs

/-
Normalized linear integer arithmetic terms.
-/
namespace Omega

/-- Shadow syntax of normalized terms. The first element
    represents the constant term and the list represents
    the coefficients. -/
def Term : Type :=
  Int × List Int deriving Inhabited
#align omega.term Omega.Term

unsafe instance : has_reflect Term :=
  prod.has_reflect _ _

namespace Term

/-- Evaluate a term using the valuation v. -/
@[simp]
def val (v : Nat → Int) : Term → Int
  | (b, as) => b + Coeffs.val v as
#align omega.term.val Omega.Term.val

@[simp]
def neg : Term → Term
  | (b, as) => (-b, List.Func.neg as)
#align omega.term.neg Omega.Term.neg

@[simp]
def add : Term → Term → Term
  | (c1, cfs1), (c2, cfs2) => (c1 + c2, List.Func.add cfs1 cfs2)
#align omega.term.add Omega.Term.add

@[simp]
def sub : Term → Term → Term
  | (c1, cfs1), (c2, cfs2) => (c1 - c2, List.Func.sub cfs1 cfs2)
#align omega.term.sub Omega.Term.sub

@[simp]
def mul (i : Int) : Term → Term
  | (b, as) => (i * b, as.map ((· * ·) i))
#align omega.term.mul Omega.Term.mul

@[simp]
def div (i : Int) : Term → Term
  | (b, as) => (b / i, as.map fun x => x / i)
#align omega.term.div Omega.Term.div

theorem val_neg {v : Nat → Int} {t : Term} : (neg t).val v = -t.val v :=
  by
  cases' t with b as
  simp only [val, neg_add, neg, val, coeffs.val_neg]
#align omega.term.val_neg Omega.Term.val_neg

@[simp]
theorem val_sub {v : Nat → Int} {t1 t2 : Term} : (sub t1 t2).val v = t1.val v - t2.val v :=
  by
  cases t1; cases t2
  simp only [add_assoc, coeffs.val_sub, neg_add_rev, val, sub, add_comm, add_left_comm,
    sub_eq_add_neg]
#align omega.term.val_sub Omega.Term.val_sub

@[simp]
theorem val_add {v : Nat → Int} {t1 t2 : Term} : (add t1 t2).val v = t1.val v + t2.val v :=
  by
  cases t1; cases t2
  simp only [coeffs.val_add, add, val, add_comm, add_left_comm]
#align omega.term.val_add Omega.Term.val_add

@[simp]
theorem val_mul {v : Nat → Int} {i : Int} {t : Term} : val v (mul i t) = i * val v t :=
  by
  cases t
  simp only [mul, mul_add, add_mul, List.length_map, coeffs.val, coeffs.val_between_map_mul, val,
    List.map]
#align omega.term.val_mul Omega.Term.val_mul

theorem val_div {v : Nat → Int} {i b : Int} {as : List Int} :
    i ∣ b → (∀ x ∈ as, i ∣ x) → (div i (b, as)).val v = val v (b, as) / i :=
  by
  intro h1 h2; simp only [val, div, List.map]
  rw [Int.add_ediv_of_dvd_left h1]
  apply fun_mono_2 rfl
  rw [← coeffs.val_map_div h2]
#align omega.term.val_div Omega.Term.val_div

/-- Fresh de Brujin index not used by any variable ocurring in the term -/
def freshIndex (t : Term) : Nat :=
  t.snd.length
#align omega.term.fresh_index Omega.Term.freshIndex

def toString (t : Term) : String :=
  t.2.enum.foldr (fun ⟨i, n⟩ r => toString n ++ " * x" ++ toString i ++ " + " ++ r) (toString t.1)
#align omega.term.to_string Omega.Term.toString

instance : ToString Term :=
  ⟨toString⟩

end Term

/-- Fresh de Brujin index not used by any variable ocurring in the list of terms -/
def Terms.freshIndex : List Term → Nat
  | [] => 0
  | t :: ts => max t.freshIndex (terms.fresh_index ts)
#align omega.terms.fresh_index Omega.Terms.freshIndex

end Omega

