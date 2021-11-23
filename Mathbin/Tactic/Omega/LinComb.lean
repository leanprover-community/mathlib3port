import Mathbin.Tactic.Omega.Clause

namespace Omega

/-- Linear combination of constraints. The second
    argument is the list of constraints, and the first
    argument is the list of conefficients by which the
    constraints are multiplied -/
@[simp]
def lin_comb : List Nat → List term → term
| [], [] => ⟨0, []⟩
| [], _ :: _ => ⟨0, []⟩
| _ :: _, [] => ⟨0, []⟩
| n :: ns, t :: ts => term.add (t.mul («expr↑ » n)) (lin_comb ns ts)

-- error in Tactic.Omega.LinComb: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lin_comb_holds
{v : nat → int} : ∀ {ts} (ns), ∀ t «expr ∈ » ts, «expr ≤ »(0, term.val v t) → «expr ≤ »(0, (lin_comb ns ts).val v)
| «expr[ , ]»([]), «expr[ , ]»([]), h := by simp [] [] ["only"] ["[", expr add_zero, ",", expr term.val, ",", expr lin_comb, ",", expr coeffs.val_nil, "]"] [] []
| «expr[ , ]»([]), [«expr :: »/«expr :: »/«expr :: »](_, _), h := by simp [] [] ["only"] ["[", expr add_zero, ",", expr term.val, ",", expr lin_comb, ",", expr coeffs.val_nil, "]"] [] []
| [«expr :: »/«expr :: »/«expr :: »](_, _), «expr[ , ]»([]), h := by simp [] [] ["only"] ["[", expr add_zero, ",", expr term.val, ",", expr lin_comb, ",", expr coeffs.val_nil, "]"] [] []
| [«expr :: »/«expr :: »/«expr :: »](t, ts), [«expr :: »/«expr :: »/«expr :: »](n, ns), h := begin
  have [] [":", expr «expr ≤ »(0, «expr + »(«expr * »(«expr↑ »(n), term.val v t), term.val v (lin_comb ns ts)))] [],
  { apply [expr add_nonneg],
    { apply [expr mul_nonneg],
      apply [expr int.coe_nat_nonneg],
      apply [expr h _ (or.inl rfl)] },
    { apply [expr lin_comb_holds],
      apply [expr list.forall_mem_of_forall_mem_cons h] } },
  simpa [] [] ["only"] ["[", expr lin_comb, ",", expr term.val_mul, ",", expr term.val_add, "]"] [] []
end

/-- `unsat_lin_comb ns ts` asserts that the linear combination
    `lin_comb ns ts` is unsatisfiable  -/
def unsat_lin_comb (ns : List Nat) (ts : List term) : Prop :=
  (lin_comb ns ts).fst < 0 ∧ ∀ x _ : x ∈ (lin_comb ns ts).snd, x = (0 : Int)

theorem unsat_lin_comb_of (ns : List Nat) (ts : List term) :
  (lin_comb ns ts).fst < 0 → (∀ x _ : x ∈ (lin_comb ns ts).snd, x = (0 : Int)) → unsat_lin_comb ns ts :=
  by 
    intro h1 h2 
    exact ⟨h1, h2⟩

-- error in Tactic.Omega.LinComb: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem unsat_of_unsat_lin_comb
(ns : list nat)
(ts : list term) : unsat_lin_comb ns ts → clause.unsat («expr[ , ]»([]), ts) :=
begin
  intros [ident h1, ident h2],
  cases [expr h2] ["with", ident v, ident h2],
  have [ident h3] [] [":=", expr lin_comb_holds ns h2.right],
  cases [expr h1] ["with", ident hl, ident hr],
  cases [expr lin_comb ns ts] ["with", ident b, ident as],
  unfold [ident term.val] ["at", ident h3],
  rw ["[", expr coeffs.val_eq_zero hr, ",", expr add_zero, ",", "<-", expr not_lt, "]"] ["at", ident h3],
  apply [expr h3 hl]
end

end Omega

