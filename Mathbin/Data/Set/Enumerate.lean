import Mathbin.Data.Set.Lattice 
import Mathbin.Tactic.Wlog

/-!
# Set enumeration

This file allows enumeration of sets given a choice function.

The definition does not assume `sel` actually is a choice function, i.e. `sel s ∈ s` and
`sel s = none ↔ s = ∅`. These assumptions are added to the lemmas needing them.
-/


noncomputable theory

open Function

namespace Set

section Enumerate

parameter {α : Type _}(sel : Set α → Option α)

/-- Given a choice function `sel`, enumerates the elements of a set in the order
`a 0 = sel s`, `a 1 = sel (s \ {a 0})`, `a 2 = sel (s \ {a 0, a 1})`, ... and stops when
`sel (s \ {a 0, ..., a n}) = none`. Note that we don't require `sel` to be a choice function. -/
def enumerate : Set α → ℕ → Option α
| s, 0 => sel s
| s, n+1 =>
  do 
    let a ← sel s 
    enumerate (s \ {a}) n

theorem enumerate_eq_none_of_sel {s : Set α} (h : sel s = none) : ∀ {n}, enumerate s n = none
| 0 =>
  by 
    simp [h, enumerate] <;> rfl
| n+1 =>
  by 
    simp [h, enumerate] <;> rfl

-- error in Data.Set.Enumerate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem enumerate_eq_none : ∀
{s n₁ n₂}, «expr = »(enumerate s n₁, none) → «expr ≤ »(n₁, n₂) → «expr = »(enumerate s n₂, none)
| s, 0, m := λ h _, enumerate_eq_none_of_sel h
| s, «expr + »(n, 1), m := λ h hm, begin
  cases [expr hs, ":", expr sel s] [],
  { exact [expr enumerate_eq_none_of_sel sel hs] },
  { cases [expr m] [],
    case [ident nat.zero] { have [] [":", expr «expr = »(«expr + »(n, 1), 0)] [],
      from [expr nat.eq_zero_of_le_zero hm],
      contradiction },
    case [ident nat.succ, ":", ident m'] { simp [] [] [] ["[", expr hs, ",", expr enumerate, "]"] [] ["at", ident h, "⊢"],
      have [ident hm] [":", expr «expr ≤ »(n, m')] [],
      from [expr nat.le_of_succ_le_succ hm],
      exact [expr enumerate_eq_none h hm] } }
end

theorem enumerate_mem (h_sel : ∀ s a, sel s = some a → a ∈ s) : ∀ {s n a}, enumerate s n = some a → a ∈ s
| s, 0, a => h_sel s a
| s, n+1, a =>
  by 
    cases h : sel s 
    case none => 
      simp [enumerate_eq_none_of_sel, h]
    case some a' => 
      simp [enumerate, h]
      exact
        fun h' : enumerate _ (s \ {a'}) n = some a =>
          have  : a ∈ s \ {a'} := enumerate_mem h' 
          this.left

-- error in Data.Set.Enumerate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem enumerate_inj
{n₁ n₂ : exprℕ()}
{a : α}
{s : set α}
(h_sel : ∀ s a, «expr = »(sel s, some a) → «expr ∈ »(a, s))
(h₁ : «expr = »(enumerate s n₁, some a))
(h₂ : «expr = »(enumerate s n₂, some a)) : «expr = »(n₁, n₂) :=
begin
  wlog [ident hn] [":", expr «expr ≤ »(n₁, n₂)] [] [],
  { rcases [expr nat.le.dest hn, "with", "⟨", ident m, ",", ident rfl, "⟩"],
    clear [ident hn],
    induction [expr n₁] [] [] ["generalizing", ident s],
    case [ident nat.zero] { cases [expr m] [],
      case [ident nat.zero] { refl },
      case [ident nat.succ, ":", ident m] { have [] [":", expr «expr = »(enumerate sel «expr \ »(s, {a}) m, some a)] [],
        { simp [] [] [] ["[", expr enumerate, ",", "*", "]"] [] ["at", "*"] },
        have [] [":", expr «expr ∈ »(a, «expr \ »(s, {a}))] [],
        from [expr enumerate_mem _ h_sel this],
        by simpa [] [] [] [] [] [] } },
    case [ident nat.succ] { cases [expr h, ":", expr sel s] []; simp [] [] [] ["[", expr enumerate, ",", expr nat.add_succ, ",", expr add_comm, ",", "*", "]"] [] ["at", "*"]; tauto [] } }
end

end Enumerate

end Set

