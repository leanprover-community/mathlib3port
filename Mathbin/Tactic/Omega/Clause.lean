/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.clause
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic
import Mathbin.Tactic.Omega.Term

/-
Definition of linear constrain clauses.
-/
namespace Omega

/-- (([t₁,...tₘ],[s₁,...,sₙ]) : clause) encodes the constraints
0 = ⟦t₁⟧ ∧ ... ∧ 0 = ⟦tₘ⟧ ∧ 0 ≤ ⟦s₁⟧ ∧ ... ∧ 0 ≤ ⟦sₙ⟧, where
⟦t⟧ is the value of (t : term). -/
@[reducible]
def Clause :=
  List Term × List Term
#align omega.clause Omega.Clause

namespace Clause

/-- holds v c := clause c holds under valuation v -/
def Holds (v : Nat → Int) : Clause → Prop
  | (eqs, les) => (∀ t : Term, t ∈ eqs → 0 = Term.val v t) ∧ ∀ t : Term, t ∈ les → 0 ≤ Term.val v t
#align omega.clause.holds Omega.Clause.Holds

/-- sat c := there exists a valuation v under which c holds -/
def Sat (c : Clause) : Prop :=
  ∃ v : Nat → Int, Holds v c
#align omega.clause.sat Omega.Clause.Sat

/-- unsat c := there is no valuation v under which c holds -/
def Unsat (c : Clause) : Prop :=
  ¬c.Sat
#align omega.clause.unsat Omega.Clause.Unsat

/-- append two clauses by elementwise appending -/
def append (c1 c2 : Clause) : Clause :=
  (c1.fst ++ c2.fst, c1.snd ++ c2.snd)
#align omega.clause.append Omega.Clause.append

theorem holds_append {v : Nat → Int} {c1 c2 : Clause} :
    Holds v c1 → Holds v c2 → Holds v (append c1 c2) :=
  by
  intro h1 h2
  cases' c1 with eqs1 les1
  cases' c2 with eqs2 les2
  cases h1; cases h2
  constructor <;> rw [List.forall_mem_append] <;> constructor <;> assumption
#align omega.clause.holds_append Omega.Clause.holds_append

end Clause

/-- There exists a satisfiable clause c in argument -/
def Clauses.Sat (cs : List Clause) : Prop :=
  ∃ c ∈ cs, Clause.Sat c
#align omega.clauses.sat Omega.Clauses.Sat

/-- There is no satisfiable clause c in argument -/
def Clauses.Unsat (cs : List Clause) : Prop :=
  ¬Clauses.Sat cs
#align omega.clauses.unsat Omega.Clauses.Unsat

theorem Clauses.unsat_nil : Clauses.Unsat [] := by intro h1; rcases h1 with ⟨c, h1, h2⟩; cases h1
#align omega.clauses.unsat_nil Omega.Clauses.unsat_nil

theorem Clauses.unsat_cons (c : Clause) (cs : List Clause) :
    Clause.Unsat c → Clauses.Unsat cs → Clauses.Unsat (c :: cs)
  | h1, h2, h3 => by
    unfold clauses.sat at h3
    rw [List.exists_mem_cons_iff] at h3
    cases h3 <;> contradiction
#align omega.clauses.unsat_cons Omega.Clauses.unsat_cons

end Omega

