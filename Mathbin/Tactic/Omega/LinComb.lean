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
| n :: ns, t :: ts => term.add (t.mul (↑n)) (lin_comb ns ts)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » ts)
theorem lin_comb_holds {v : Nat → Int} : ∀ {ts} ns, (∀ t _ : t ∈ ts, 0 ≤ term.val v t) → 0 ≤ (lin_comb ns ts).val v
| [], [], h =>
  by 
    simp only [add_zeroₓ, term.val, lin_comb, coeffs.val_nil]
| [], _ :: _, h =>
  by 
    simp only [add_zeroₓ, term.val, lin_comb, coeffs.val_nil]
| _ :: _, [], h =>
  by 
    simp only [add_zeroₓ, term.val, lin_comb, coeffs.val_nil]
| t :: ts, n :: ns, h =>
  by 
    have  : 0 ≤ ((↑n)*term.val v t)+term.val v (lin_comb ns ts)
    ·
      apply add_nonneg
      ·
        apply mul_nonneg 
        apply Int.coe_nat_nonneg 
        apply h _ (Or.inl rfl)
      ·
        apply lin_comb_holds 
        apply List.forall_mem_of_forall_mem_consₓ h 
    simpa only [lin_comb, term.val_mul, term.val_add]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » (lin_comb ns ts).snd)
/-- `unsat_lin_comb ns ts` asserts that the linear combination
    `lin_comb ns ts` is unsatisfiable  -/
def unsat_lin_comb (ns : List Nat) (ts : List term) : Prop :=
  (lin_comb ns ts).fst < 0 ∧ ∀ x _ : x ∈ (lin_comb ns ts).snd, x = (0 : Int)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » (lin_comb ns ts).snd)
theorem unsat_lin_comb_of (ns : List Nat) (ts : List term) :
  (lin_comb ns ts).fst < 0 → (∀ x _ : x ∈ (lin_comb ns ts).snd, x = (0 : Int)) → unsat_lin_comb ns ts :=
  by 
    intro h1 h2 
    exact ⟨h1, h2⟩

theorem unsat_of_unsat_lin_comb (ns : List Nat) (ts : List term) : unsat_lin_comb ns ts → clause.unsat ([], ts) :=
  by 
    intro h1 h2 
    cases' h2 with v h2 
    have h3 := lin_comb_holds ns h2.right 
    cases' h1 with hl hr 
    cases' lin_comb ns ts with b as 
    unfold term.val  at h3 
    rw [coeffs.val_eq_zero hr, add_zeroₓ, ←not_ltₓ] at h3 
    apply h3 hl

end Omega

