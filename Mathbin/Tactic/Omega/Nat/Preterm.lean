import Mathbin.Tactic.Omega.Term

open Tactic

namespace Omega

namespace Nat

/-- The shadow syntax for arithmetic terms. All constants are reified to `cst`
(e.g., `5` is reified to `cst 5`) and all other atomic terms are reified to
`exp` (e.g., `5 * (list.length l)` is reified to `exp 5 \`(list.length l)`).
`exp` accepts a coefficient of type `nat` as its first argument because
multiplication by constant is allowed by the omega test. -/
unsafe inductive exprterm : Type
  | cst : Nat → exprterm
  | exp : Nat → expr → exprterm
  | add : exprterm → exprterm → exprterm
  | sub : exprterm → exprterm → exprterm

-- error in Tactic.Omega.Nat.Preterm: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler has_reflect
/-- Similar to `exprterm`, except that all exprs are now replaced with
de Brujin indices of type `nat`. This is akin to generalizing over
the terms represented by the said exprs. -/
@[derive #[expr has_reflect], derive #[expr decidable_eq], derive #[expr inhabited]]
inductive preterm : Type
| cst : nat → preterm
| var : nat → nat → preterm
| add : preterm → preterm → preterm
| sub : preterm → preterm → preterm

localized [Omega.Nat] notation "&" k => Omega.Nat.Preterm.cst k

localized [Omega.Nat] infixl:300 " ** " => Omega.Nat.Preterm.var

localized [Omega.Nat] notation t " +* " s => Omega.Nat.Preterm.add t s

localized [Omega.Nat] notation t " -* " s => Omega.Nat.Preterm.sub t s

namespace Preterm

/-- Helper tactic for proof by induction over preterms -/
unsafe def induce (tac : tactic Unit := tactic.skip) : tactic Unit :=
  sorry

/-- Preterm evaluation -/
def val (v : Nat → Nat) : preterm → Nat
| &i => i
| i ** n => if i = 1 then v n else v n*i
| t1 +* t2 => t1.val+t2.val
| t1 -* t2 => t1.val - t2.val

@[simp]
theorem val_const {v : Nat → Nat} {m : Nat} : (&m).val v = m :=
  rfl

@[simp]
theorem val_var {v : Nat → Nat} {m n : Nat} : (m ** n).val v = m*v n :=
  by 
    simp only [val]
    byCases' h1 : m = 1
    rw [if_pos h1, h1, one_mulₓ]
    rw [if_neg h1, mul_commₓ]

@[simp]
theorem val_add {v : Nat → Nat} {t s : preterm} : (t +* s).val v = t.val v+s.val v :=
  rfl

@[simp]
theorem val_sub {v : Nat → Nat} {t s : preterm} : (t -* s).val v = t.val v - s.val v :=
  rfl

/-- Fresh de Brujin index not used by any variable in argument -/
def fresh_index : preterm → Nat
| &_ => 0
| i ** n => n+1
| t1 +* t2 => max t1.fresh_index t2.fresh_index
| t1 -* t2 => max t1.fresh_index t2.fresh_index

-- error in Tactic.Omega.Nat.Preterm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If variable assignments `v` and `w` agree on all variables that occur
in term `t`, the value of `t` under `v` and `w` are identical. -/
theorem val_constant
(v w : nat → nat) : ∀ t : preterm, ∀ x «expr < » t.fresh_index, «expr = »(v x, w x) → «expr = »(t.val v, t.val w)
| «expr& »(n), h1 := rfl
| «expr ** »(m, n), h1 := begin
  simp [] [] ["only"] ["[", expr val_var, "]"] [] [],
  apply [expr congr_arg (λ y, «expr * »(m, y))],
  apply [expr h1 _ (lt_add_one _)]
end
| «expr +* »(t, s), h1 := begin
  simp [] [] ["only"] ["[", expr val_add, "]"] [] [],
  have [ident ht] [] [":=", expr val_constant t (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_left _ _)))],
  have [ident hs] [] [":=", expr val_constant s (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_right _ _)))],
  rw ["[", expr ht, ",", expr hs, "]"] []
end
| «expr -* »(t, s), h1 := begin
  simp [] [] ["only"] ["[", expr val_sub, "]"] [] [],
  have [ident ht] [] [":=", expr val_constant t (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_left _ _)))],
  have [ident hs] [] [":=", expr val_constant s (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_right _ _)))],
  rw ["[", expr ht, ",", expr hs, "]"] []
end

def reprₓ : preterm → Stringₓ
| &i => i.repr
| i ** n => i.repr ++ "*x" ++ n.repr
| t1 +* t2 => "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"
| t1 -* t2 => "(" ++ t1.repr ++ " - " ++ t2.repr ++ ")"

@[simp]
def add_one (t : preterm) : preterm :=
  t +* &1

/-- Preterm is free of subtractions -/
def sub_free : preterm → Prop
| &m => True
| m ** n => True
| t +* s => t.sub_free ∧ s.sub_free
| _ -* _ => False

end Preterm

open_locale List.Func

/-- Return a term (which is in canonical form by definition)
    that is equivalent to the input preterm -/
@[simp]
def canonize : preterm → term
| &m => ⟨«expr↑ » m, []⟩
| m ** n => ⟨0, [] {n ↦ «expr↑ » m}⟩
| t +* s => term.add (canonize t) (canonize s)
| _ -* _ => ⟨0, []⟩

@[simp]
theorem val_canonize {v : Nat → Nat} :
  ∀ {t : preterm}, t.sub_free → ((canonize t).val fun x => «expr↑ » (v x)) = t.val v
| &i, h1 =>
  by 
    simp only [canonize, preterm.val_const, term.val, coeffs.val_nil, add_zeroₓ]
| i ** n, h1 =>
  by 
    simp only [preterm.val_var, coeffs.val_set, term.val, zero_addₓ, Int.coe_nat_mul, canonize]
| t +* s, h1 =>
  by 
    simp only [val_canonize h1.left, val_canonize h1.right, Int.coe_nat_add, canonize, term.val_add, preterm.val_add]

end Nat

end Omega

