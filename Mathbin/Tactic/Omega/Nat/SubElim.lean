import Mathbin.Tactic.Omega.Nat.Form

namespace Omega

namespace Nat

open_locale Omega.Nat

namespace Preterm

/-- Find subtraction inside preterm and return its operands -/
def sub_terms : preterm → Option (preterm × preterm)
| &i => none
| i ** n => none
| t +* s => t.sub_terms <|> s.sub_terms
| t -* s => t.sub_terms <|> s.sub_terms <|> some (t, s)

/-- Find (t - s) inside a preterm and replace it with variable k -/
def sub_subst (t s : preterm) (k : Nat) : preterm → preterm
| t@(&m) => t
| t@(m ** n) => t
| x +* y => x.sub_subst +* y.sub_subst
| x -* y => if x = t ∧ y = s then 1 ** k else x.sub_subst -* y.sub_subst

-- error in Tactic.Omega.Nat.SubElim: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem val_sub_subst
{k : nat}
{x y : preterm}
{v : nat → nat} : ∀
{t : preterm}, «expr ≤ »(t.fresh_index, k) → «expr = »((sub_subst x y k t).val (update k «expr - »(x.val v, y.val v) v), t.val v)
| «expr& »(m), h1 := rfl
| «expr ** »(m, n), h1 := begin
  have [ident h2] [":", expr «expr ≠ »(n, k)] [":=", expr ne_of_lt h1],
  simp [] [] ["only"] ["[", expr sub_subst, ",", expr preterm.val, "]"] [] [],
  rw [expr update_eq_of_ne _ h2] []
end
| «expr +* »(t, s), h1 := begin
  simp [] [] ["only"] ["[", expr sub_subst, ",", expr val_add, "]"] [] [],
  apply [expr fun_mono_2]; apply [expr val_sub_subst (le_trans _ h1)],
  apply [expr le_max_left],
  apply [expr le_max_right]
end
| «expr -* »(t, s), h1 := begin
  simp [] [] ["only"] ["[", expr sub_subst, ",", expr val_sub, "]"] [] [],
  by_cases [expr h2, ":", expr «expr ∧ »(«expr = »(t, x), «expr = »(s, y))],
  { rw [expr if_pos h2] [],
    simp [] [] ["only"] ["[", expr val_var, ",", expr one_mul, "]"] [] [],
    rw ["[", expr update_eq, ",", expr h2.left, ",", expr h2.right, "]"] [] },
  { rw [expr if_neg h2] [],
    simp [] [] ["only"] ["[", expr val_sub, ",", expr sub_subst, "]"] [] [],
    apply [expr fun_mono_2]; apply [expr val_sub_subst (le_trans _ h1)],
    apply [expr le_max_left],
    apply [expr le_max_right] }
end

end Preterm

namespace Preform

/-- Find subtraction inside preform and return its operands -/
def sub_terms : preform → Option (preterm × preterm)
| t =* s => t.sub_terms <|> s.sub_terms
| t ≤* s => t.sub_terms <|> s.sub_terms
| ¬* p => p.sub_terms
| p ∨* q => p.sub_terms <|> q.sub_terms
| p ∧* q => p.sub_terms <|> q.sub_terms

/-- Find (t - s) inside a preform and replace it with variable k -/
@[simp]
def sub_subst (x y : preterm) (k : Nat) : preform → preform
| t =* s => preterm.sub_subst x y k t =* preterm.sub_subst x y k s
| t ≤* s => preterm.sub_subst x y k t ≤* preterm.sub_subst x y k s
| ¬* p => ¬* p.sub_subst
| p ∨* q => p.sub_subst ∨* q.sub_subst
| p ∧* q => p.sub_subst ∧* q.sub_subst

end Preform

/-- Preform which asserts that the value of variable k is
    the truncated difference between preterms t and s -/
def is_diff (t s : preterm) (k : Nat) : preform :=
  (t =* s +* 1 ** k) ∨* (t ≤* s) ∧* (1 ** k) =* &0

theorem holds_is_diff {t s : preterm} {k : Nat} {v : Nat → Nat} : v k = t.val v - s.val v → (is_diff t s k).Holds v :=
  by 
    intro h1 
    simp only [preform.holds, is_diff, if_pos (Eq.refl 1), preterm.val_add, preterm.val_var, preterm.val_const]
    cases' le_totalₓ (t.val v) (s.val v) with h2 h2
    ·
      right 
      refine' ⟨h2, _⟩
      rw [h1, one_mulₓ, tsub_eq_zero_iff_le]
      exact h2
    ·
      left 
      rw [h1, one_mulₓ, add_commₓ, tsub_add_cancel_of_le h2]

/-- Helper function for sub_elim -/
def sub_elim_core (t s : preterm) (k : Nat) (p : preform) : preform :=
  preform.sub_subst t s k p ∧* is_diff t s k

/-- Return de Brujin index of fresh variable that does not occur
    in any of the arguments -/
def sub_fresh_index (t s : preterm) (p : preform) : Nat :=
  max p.fresh_index (max t.fresh_index s.fresh_index)

/-- Return a new preform with all subtractions eliminated -/
def sub_elim (t s : preterm) (p : preform) : preform :=
  sub_elim_core t s (sub_fresh_index t s p) p

theorem sub_subst_equiv {k : Nat} {x y : preterm} {v : Nat → Nat} :
  ∀ p : preform, p.fresh_index ≤ k → ((preform.sub_subst x y k p).Holds (update k (x.val v - y.val v) v) ↔ p.holds v)
| t =* s, h1 =>
  by 
    simp only [preform.holds, preform.sub_subst]
    apply pred_mono_2 <;> apply preterm.val_sub_subst (le_transₓ _ h1)
    apply le_max_leftₓ 
    apply le_max_rightₓ
| t ≤* s, h1 =>
  by 
    simp only [preform.holds, preform.sub_subst]
    apply pred_mono_2 <;> apply preterm.val_sub_subst (le_transₓ _ h1)
    apply le_max_leftₓ 
    apply le_max_rightₓ
| ¬* p, h1 =>
  by 
    apply not_iff_not_of_iff 
    apply sub_subst_equiv p h1
| p ∨* q, h1 =>
  by 
    simp only [preform.holds, preform.sub_subst]
    apply pred_mono_2 <;> apply propext <;> apply sub_subst_equiv _ (le_transₓ _ h1)
    apply le_max_leftₓ 
    apply le_max_rightₓ
| p ∧* q, h1 =>
  by 
    simp only [preform.holds, preform.sub_subst]
    apply pred_mono_2 <;> apply propext <;> apply sub_subst_equiv _ (le_transₓ _ h1)
    apply le_max_leftₓ 
    apply le_max_rightₓ

theorem sat_sub_elim {t s : preterm} {p : preform} : p.sat → (sub_elim t s p).sat :=
  by 
    intro h1 
    simp only [sub_elim, sub_elim_core]
    cases' h1 with v h1 
    refine' ⟨update (sub_fresh_index t s p) (t.val v - s.val v) v, _⟩
    constructor
    ·
      apply (sub_subst_equiv p _).elim_right h1 
      apply le_max_leftₓ
    ·
      apply holds_is_diff 
      rw [update_eq]
      apply fun_mono_2 <;>
        apply preterm.val_constant <;>
          intro x h2 <;>
            rw [update_eq_of_ne _ (Ne.symm (ne_of_gtₓ _))] <;>
              apply lt_of_lt_of_leₓ h2 <;> apply le_transₓ _ (le_max_rightₓ _ _)
      apply le_max_leftₓ 
      apply le_max_rightₓ

theorem unsat_of_unsat_sub_elim (t s : preterm) (p : preform) : (sub_elim t s p).Unsat → p.unsat :=
  mt sat_sub_elim

end Nat

end Omega

