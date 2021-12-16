import Mathbin.Tactic.Omega.Term

namespace Omega

namespace Int

/-- The shadow syntax for arithmetic terms. All constants are reified to `cst`
(e.g., `-5` is reified to `cst -5`) and all other atomic terms are reified to
`exp` (e.g., `-5 * (gcd 14 -7)` is reified to `exp -5 \`(gcd 14 -7)`).
`exp` accepts a coefficient of type `int` as its first argument because
multiplication by constant is allowed by the omega test. -/
unsafe inductive exprterm : Type
  | cst : Int → exprterm
  | exp : Int → expr → exprterm
  | add : exprterm → exprterm → exprterm

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler has_reflect
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler inhabited
/-- Similar to `exprterm`, except that all exprs are now replaced with
de Brujin indices of type `nat`. This is akin to generalizing over
the terms represented by the said exprs. -/
inductive preterm : Type
  | cst : Int → preterm
  | var : Int → Nat → preterm
  | add : preterm → preterm → preterm deriving [anonymous], [anonymous]

localized [Omega.Int] notation "&" k => Omega.Int.Preterm.cst k

localized [Omega.Int] infixl:300 " ** " => Omega.Int.Preterm.var

localized [Omega.Int] notation t "+*" s => Omega.Int.Preterm.add t s

namespace Preterm

/-- Preterm evaluation -/
@[simp]
def val (v : Nat → Int) : preterm → Int
| &i => i
| i ** n => if i = 1 then v n else if i = -1 then -v n else v n*i
| t1+*t2 => t1.val+t2.val

/-- Fresh de Brujin index not used by any variable in argument -/
def fresh_index : preterm → Nat
| &_ => 0
| i ** n => n+1
| t1+*t2 => max t1.fresh_index t2.fresh_index

@[simp]
def add_one (t : preterm) : preterm :=
  t+*&1

def reprₓ : preterm → Stringₓ
| &i => i.repr
| i ** n => i.repr ++ "*x" ++ n.repr
| t1+*t2 => "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"

end Preterm

open_locale List.Func

/-- Return a term (which is in canonical form by definition)
    that is equivalent to the input preterm -/
@[simp]
def canonize : preterm → term
| &i => ⟨i, []⟩
| i ** n => ⟨0, [] {n ↦ i}⟩
| t1+*t2 => term.add (canonize t1) (canonize t2)

@[simp]
theorem val_canonize {v : Nat → Int} : ∀ {t : preterm}, (canonize t).val v = t.val v
| &i =>
  by 
    simp only [preterm.val, add_zeroₓ, term.val, canonize, coeffs.val_nil]
| i ** n =>
  by 
    simp only [coeffs.val_set, canonize, preterm.val, zero_addₓ, term.val]
    splitIfs with h1 h2
    ·
      simp only [one_mulₓ, h1]
    ·
      simp only [neg_mul_eq_neg_mul_symm, one_mulₓ, h2]
    ·
      rw [mul_commₓ]
| t+*s =>
  by 
    simp only [canonize, val_canonize, term.val_add, preterm.val]

end Int

end Omega

