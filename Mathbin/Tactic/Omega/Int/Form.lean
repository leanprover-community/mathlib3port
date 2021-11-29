import Mathbin.Tactic.Omega.Int.Preterm

namespace Omega

namespace Int

/-- Intermediate shadow syntax for LNA formulas that includes unreified exprs -/
unsafe inductive exprform
  | Eq : exprterm → exprterm → exprform
  | le : exprterm → exprterm → exprform
  | Not : exprform → exprform
  | Or : exprform → exprform → exprform
  | And : exprform → exprform → exprform

-- error in Tactic.Omega.Int.Form: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler has_reflect
/-- Intermediate shadow syntax for LIA formulas that includes non-canonical terms -/
@[derive #[expr has_reflect], derive #[expr inhabited]]
inductive preform
| eq : preterm → preterm → preform
| le : preterm → preterm → preform
| not : preform → preform
| or : preform → preform → preform
| and : preform → preform → preform

localized [Omega.Int] notation x " =* " y => Omega.Int.Preform.eq x y

localized [Omega.Int] notation x " ≤* " y => Omega.Int.Preform.le x y

localized [Omega.Int] notation "¬* " p => Omega.Int.Preform.not p

localized [Omega.Int] notation p " ∨* " q => Omega.Int.Preform.or p q

localized [Omega.Int] notation p " ∧* " q => Omega.Int.Preform.and p q

namespace Preform

/-- Evaluate a preform into prop using the valuation v. -/
@[simp]
def holds (v : Nat → Int) : preform → Prop
| t =* s => t.val v = s.val v
| t ≤* s => t.val v ≤ s.val v
| ¬* p => ¬p.holds
| p ∨* q => p.holds ∨ q.holds
| p ∧* q => p.holds ∧ q.holds

end Preform

/-- univ_close p n := p closed by prepending n universal quantifiers -/
@[simp]
def univ_close (p : preform) : (Nat → Int) → Nat → Prop
| v, 0 => p.holds v
| v, k+1 => ∀ (i : Int), univ_close (update_zero i v) k

namespace Preform

/-- Fresh de Brujin index not used by any variable in argument -/
def fresh_index : preform → Nat
| t =* s => max t.fresh_index s.fresh_index
| t ≤* s => max t.fresh_index s.fresh_index
| ¬* p => p.fresh_index
| p ∨* q => max p.fresh_index q.fresh_index
| p ∧* q => max p.fresh_index q.fresh_index

/-- All valuations satisfy argument -/
def valid (p : preform) : Prop :=
  ∀ v, holds v p

/-- There exists some valuation that satisfies argument -/
def sat (p : preform) : Prop :=
  ∃ v, holds v p

/-- implies p q := under any valuation, q holds if p holds -/
def Implies (p q : preform) : Prop :=
  ∀ v, holds v p → holds v q

/-- equiv p q := under any valuation, p holds iff q holds -/
def Equiv (p q : preform) : Prop :=
  ∀ v, holds v p ↔ holds v q

theorem sat_of_implies_of_sat {p q : preform} : Implies p q → sat p → sat q :=
  by 
    intro h1 h2 
    apply exists_imp_exists h1 h2

theorem sat_or {p q : preform} : sat (p ∨* q) ↔ sat p ∨ sat q :=
  by 
    constructor <;> intro h1
    ·
      cases' h1 with v h1 
      cases' h1 with h1 h1 <;> [left, right] <;> refine' ⟨v, _⟩ <;> assumption
    ·
      cases' h1 with h1 h1 <;> cases' h1 with v h1 <;> refine' ⟨v, _⟩ <;> [left, right] <;> assumption

/-- There does not exist any valuation that satisfies argument -/
def unsat (p : preform) : Prop :=
  ¬sat p

def reprₓ : preform → Stringₓ
| t =* s => "(" ++ t.repr ++ " = " ++ s.repr ++ ")"
| t ≤* s => "(" ++ t.repr ++ " ≤ " ++ s.repr ++ ")"
| ¬* p => "¬" ++ p.repr
| p ∨* q => "(" ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
| p ∧* q => "(" ++ p.repr ++ " ∧ " ++ q.repr ++ ")"

instance HasRepr : HasRepr preform :=
  ⟨reprₓ⟩

unsafe instance has_to_format : has_to_format preform :=
  ⟨fun x => x.repr⟩

end Preform

theorem univ_close_of_valid {p : preform} : ∀ {m v}, p.valid → univ_close p v m
| 0, v, h1 => h1 _
| m+1, v, h1 => fun i => univ_close_of_valid h1

theorem valid_of_unsat_not {p : preform} : (¬* p).Unsat → p.valid :=
  by 
    simp only [preform.sat, preform.unsat, preform.valid, preform.holds]
    rw [not_exists_not]
    intro h 
    assumption

/-- Tactic for setting up proof by induction over preforms. -/
unsafe def preform.induce (t : tactic Unit := tactic.skip) : tactic Unit :=
  sorry

end Int

end Omega

