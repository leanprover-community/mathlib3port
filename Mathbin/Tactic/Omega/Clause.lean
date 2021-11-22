import Mathbin.Tactic.Omega.Term

namespace Omega

/-- (([t₁,...tₘ],[s₁,...,sₙ]) : clause) encodes the constraints
0 = ⟦t₁⟧ ∧ ... ∧ 0 = ⟦tₘ⟧ ∧ 0 ≤ ⟦s₁⟧ ∧ ... ∧ 0 ≤ ⟦sₙ⟧, where
⟦t⟧ is the value of (t : term). -/
@[reducible]
def clause :=
  List term × List term

namespace Clause

/-- holds v c := clause c holds under valuation v -/
def holds (v : Nat → Int) : clause → Prop
| (eqs, les) => (∀ t : term, t ∈ eqs → 0 = term.val v t) ∧ ∀ t : term, t ∈ les → 0 ≤ term.val v t

/-- sat c := there exists a valuation v under which c holds -/
def sat (c : clause) : Prop :=
  ∃ v : Nat → Int, holds v c

/-- unsat c := there is no valuation v under which c holds -/
def unsat (c : clause) : Prop :=
  ¬c.sat

/-- append two clauses by elementwise appending -/
def append (c1 c2 : clause) : clause :=
  (c1.fst ++ c2.fst, c1.snd ++ c2.snd)

theorem holds_append {v : Nat → Int} {c1 c2 : clause} : holds v c1 → holds v c2 → holds v (append c1 c2) :=
  by 
    intro h1 h2 
    cases' c1 with eqs1 les1 
    cases' c2 with eqs2 les2 
    cases h1 
    cases h2 
    constructor <;> rw [List.forall_mem_appendₓ] <;> constructor <;> assumption

end Clause

/-- There exists a satisfiable clause c in argument -/
def clauses.sat (cs : List clause) : Prop :=
  ∃ (c : _)(_ : c ∈ cs), clause.sat c

/-- There is no satisfiable clause c in argument -/
def clauses.unsat (cs : List clause) : Prop :=
  ¬clauses.sat cs

theorem clauses.unsat_nil : clauses.unsat [] :=
  by 
    intro h1 
    rcases h1 with ⟨c, h1, h2⟩
    cases h1

theorem clauses.unsat_cons (c : clause) (cs : List clause) : clause.unsat c → clauses.unsat cs → clauses.unsat (c :: cs)
| h1, h2, h3 =>
  by 
    unfold clauses.sat  at h3 
    rw [List.exists_mem_cons_iffₓ] at h3 
    cases h3 <;> contradiction

end Omega

