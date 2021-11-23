import Mathbin.Tactic.Rcases 
import Mathbin.Computability.Language

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

TODO
* Show that this regular expressions and DFA/NFA's are equivalent.
* `attribute [pattern] has_mul.mul` has been added into this file, it could be moved.
-/


universe u

variable{α : Type u}[dec : DecidableEq α]

/--
This is the definition of regular expressions. The names used here is to mirror the definition
of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression
  | epsilon : RegularExpression
  | Charₓ : α → RegularExpression
  | plus : RegularExpression → RegularExpression → RegularExpression
  | comp : RegularExpression → RegularExpression → RegularExpression
  | star : RegularExpression → RegularExpression

namespace RegularExpression

instance  : Inhabited (RegularExpression α) :=
  ⟨zero⟩

instance  : Add (RegularExpression α) :=
  ⟨plus⟩

instance  : Mul (RegularExpression α) :=
  ⟨comp⟩

instance  : HasOne (RegularExpression α) :=
  ⟨epsilon⟩

instance  : HasZero (RegularExpression α) :=
  ⟨zero⟩

attribute [matchPattern] Mul.mul

@[simp]
theorem zero_def : (zero : RegularExpression α) = 0 :=
  rfl

@[simp]
theorem one_def : (epsilon : RegularExpression α) = 1 :=
  rfl

@[simp]
theorem plus_def (P Q : RegularExpression α) : plus P Q = P+Q :=
  rfl

@[simp]
theorem comp_def (P Q : RegularExpression α) : comp P Q = P*Q :=
  rfl

/-- `matches P` provides a language which contains all strings that `P` matches -/
def matches : RegularExpression α → Language α
| 0 => 0
| 1 => 1
| Charₓ a => {[a]}
| P+Q => P.matches+Q.matches
| P*Q => P.matches*Q.matches
| star P => P.matches.star

@[simp]
theorem matches_zero_def : (0 : RegularExpression α).Matches = 0 :=
  rfl

@[simp]
theorem matches_epsilon_def : (1 : RegularExpression α).Matches = 1 :=
  rfl

@[simp]
theorem matches_add_def (P Q : RegularExpression α) : (P+Q).Matches = P.matches+Q.matches :=
  rfl

@[simp]
theorem matches_mul_def (P Q : RegularExpression α) : (P*Q).Matches = P.matches*Q.matches :=
  rfl

@[simp]
theorem matches_star_def (P : RegularExpression α) : P.star.matches = P.matches.star :=
  rfl

/-- `match_epsilon P` is true if and only if `P` matches the empty string -/
def match_epsilon : RegularExpression α → Bool
| 0 => ff
| 1 => tt
| Charₓ _ => ff
| P+Q => P.match_epsilon || Q.match_epsilon
| P*Q => P.match_epsilon && Q.match_epsilon
| star P => tt

include dec

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : RegularExpression α → α → RegularExpression α
| 0, _ => 0
| 1, _ => 0
| Charₓ a₁, a₂ => if a₁ = a₂ then 1 else 0
| P+Q, a => deriv P a+deriv Q a
| P*Q, a => if P.match_epsilon then (deriv P a*Q)+deriv Q a else deriv P a*Q
| star P, a => deriv P a*star P

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches`. -/
def rmatch : RegularExpression α → List α → Bool
| P, [] => match_epsilon P
| P, a :: as => rmatch (P.deriv a) as

@[simp]
theorem zero_rmatch (x : List α) : rmatch 0 x = ff :=
  by 
    induction x <;> simp [rmatch, match_epsilon, deriv]

theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] :=
  by 
    induction x <;> simp [rmatch, match_epsilon, deriv]

theorem char_rmatch_iff (a : α) (x : List α) : rmatch (Charₓ a) x ↔ x = [a] :=
  by 
    cases' x with _ x 
    decide 
    cases x 
    rw [rmatch, deriv]
    splitIfs <;> tauto 
    rw [rmatch, deriv]
    splitIfs 
    rw [one_rmatch_iff]
    tauto 
    rw [zero_rmatch]
    tauto

theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) : (P+Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x :=
  by 
    induction' x with _ _ ih generalizing P Q
    ·
      repeat' 
        rw [rmatch]
      rw [match_epsilon]
      finish
    ·
      repeat' 
        rw [rmatch]
      rw [deriv]
      exact ih _ _

theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
  (P*Q).rmatch x ↔ ∃ t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u :=
  by 
    induction' x with a x ih generalizing P Q
    ·
      rw [rmatch, match_epsilon]
      split 
      ·
        intro h 
        refine' ⟨[], [], rfl, _⟩
        rw [rmatch, rmatch]
        rwa [band_coe_iff] at h
      ·
        rintro ⟨t, u, h₁, h₂⟩
        cases' List.append_eq_nil.1 h₁.symm with ht hu 
        subst ht 
        subst hu 
        repeat' 
          rw [rmatch] at h₂ 
        finish
    ·
      rw [rmatch, deriv]
      splitIfs with hepsilon
      ·
        rw [add_rmatch_iff, ih]
        split 
        ·
          rintro (⟨t, u, _⟩ | h)
          ·
            exact
              ⟨a :: t, u,
                by 
                  tauto⟩
          ·
            exact ⟨[], a :: x, rfl, hepsilon, h⟩
        ·
          rintro ⟨t, u, h, hP, hQ⟩
          cases' t with b t
          ·
            right 
            rw [List.nil_append] at h 
            rw [←h] at hQ 
            exact hQ
          ·
            left 
            refine'
              ⟨t, u,
                by 
                  finish,
                _, hQ⟩
            rw [rmatch] at hP 
            convert hP 
            finish
      ·
        rw [ih]
        split  <;> rintro ⟨t, u, h, hP, hQ⟩
        ·
          exact
            ⟨a :: t, u,
              by 
                tauto⟩
        ·
          cases' t with b t
          ·
            contradiction
          ·
            refine'
              ⟨t, u,
                by 
                  finish,
                _, hQ⟩
            rw [rmatch] at hP 
            convert hP 
            finish

-- error in Computability.RegularExpressions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem star_rmatch_iff
(P : regular_expression α) : ∀
x : list α, «expr ↔ »((star P).rmatch x, «expr∃ , »((S : list (list α)), «expr ∧ »(«expr = »(x, S.join), ∀
   t «expr ∈ » S, «expr ∧ »(«expr ≠ »(t, «expr[ , ]»([])), P.rmatch t))))
| x := begin
  have [ident A] [":", expr ∀ m n : exprℕ(), «expr < »(n, «expr + »(«expr + »(m, n), 1))] [],
  { assume [binders (m n)],
    convert [] [expr add_lt_add_of_le_of_lt (add_le_add (zero_le m) (le_refl n)) zero_lt_one] [],
    simp [] [] [] [] [] [] },
  have [ident IH] [] [":=", expr λ (t) (h : «expr < »(list.length t, list.length x)), star_rmatch_iff t],
  clear [ident star_rmatch_iff],
  split,
  { cases [expr x] ["with", ident a, ident x],
    { intro [],
      fconstructor,
      exact [expr «expr[ , ]»([])],
      tauto [] },
    { rw ["[", expr rmatch, ",", expr deriv, ",", expr mul_rmatch_iff, "]"] [],
      rintro ["⟨", ident t, ",", ident u, ",", ident hs, ",", ident ht, ",", ident hu, "⟩"],
      have [ident hwf] [":", expr «expr < »(u.length, (list.cons a x).length)] [],
      { rw ["[", expr hs, ",", expr list.length_cons, ",", expr list.length_append, "]"] [],
        apply [expr A] },
      rw [expr IH _ hwf] ["at", ident hu],
      rcases [expr hu, "with", "⟨", ident S', ",", ident hsum, ",", ident helem, "⟩"],
      use [expr «expr :: »(«expr :: »(a, t), S')],
      split,
      { finish [] [] },
      { intros [ident t', ident ht'],
        cases [expr ht'] ["with", ident ht', ident ht'],
        { rw [expr ht'] [],
          exact [expr ⟨exprdec_trivial(), ht⟩] },
        { exact [expr helem _ ht'] } } } },
  { rintro ["⟨", ident S, ",", ident hsum, ",", ident helem, "⟩"],
    cases [expr x] ["with", ident a, ident x],
    { dec_trivial [] },
    { rw ["[", expr rmatch, ",", expr deriv, ",", expr mul_rmatch_iff, "]"] [],
      cases [expr S] ["with", ident t', ident U],
      { exact [expr ⟨«expr[ , ]»([]), «expr[ , ]»([]), by tauto []⟩] },
      { cases [expr t'] ["with", ident b, ident t],
        { finish [] [] },
        refine [expr ⟨t, U.join, by finish [] [], _, _⟩],
        { specialize [expr helem «expr :: »(b, t) _],
          { finish [] [] },
          rw [expr rmatch] ["at", ident helem],
          convert [] [expr helem.2] [],
          finish [] [] },
        { have [ident hwf] [":", expr «expr < »(U.join.length, (list.cons a x).length)] [],
          { rw [expr hsum] [],
            simp [] [] ["only"] ["[", expr list.join, ",", expr list.length_append, ",", expr list.cons_append, ",", expr list.length_join, ",", expr list.length, "]"] [] [],
            apply [expr A] },
          rw [expr IH _ hwf] [],
          refine [expr ⟨U, rfl, λ t h, helem t _⟩],
          right,
          assumption } } } }
end

@[simp]
theorem rmatch_iff_matches (P : RegularExpression α) : ∀ x : List α, P.rmatch x ↔ x ∈ P.matches :=
  by 
    intro x 
    induction P generalizing x 
    all_goals 
      try 
        rw [zero_def]
      try 
        rw [one_def]
      try 
        rw [plus_def]
      try 
        rw [comp_def]
      rw [matches]
    case zero => 
      rw [zero_rmatch]
      tauto 
    case epsilon => 
      rw [one_rmatch_iff]
      rfl 
    case char => 
      rw [char_rmatch_iff]
      rfl 
    case plus _ _ ih₁ ih₂ => 
      rw [add_rmatch_iff, ih₁, ih₂]
      rfl 
    case comp P Q ih₁ ih₂ => 
      simp only [mul_rmatch_iff, comp_def, Language.mul_def, exists_and_distrib_left, Set.mem_image2, Set.image_prod]
      split 
      ·
        rintro ⟨x, y, hsum, hmatch₁, hmatch₂⟩
        rw [ih₁] at hmatch₁ 
        rw [ih₂] at hmatch₂ 
        exact ⟨x, hmatch₁, y, hmatch₂, hsum.symm⟩
      ·
        rintro ⟨x, hmatch₁, y, hmatch₂, hsum⟩
        rw [←ih₁] at hmatch₁ 
        rw [←ih₂] at hmatch₂ 
        exact ⟨x, y, hsum.symm, hmatch₁, hmatch₂⟩
    case star _ ih => 
      rw [star_rmatch_iff, Language.star_def_nonempty]
      split 
      all_goals 
        rintro ⟨S, hx, hS⟩
        refine' ⟨S, hx, _⟩
        intro y 
        specialize hS y
      ·
        rw [←ih y]
        tauto
      ·
        rw [ih y]
        tauto

instance  (P : RegularExpression α) : DecidablePred P.matches :=
  by 
    intro x 
    change Decidable (x ∈ P.matches)
    rw [←rmatch_iff_matches]
    exact Eq.decidable _ _

end RegularExpression

