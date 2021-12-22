import Mathbin.Algebra.BigOperators.Basic
import Mathbin.RingTheory.Polynomial.Basic

/-!
# Lagrange interpolation

## Main definitions

* `lagrange.basis s x` where `s : finset F` and `x : F`: the Lagrange basis polynomial
  that evaluates to `1` at `x` and `0` at other elements of `s`.
* `lagrange.interpolate s f` where `s : finset F` and `f : s → F`: the Lagrange interpolant
  that evaluates to `f x` at `x` for `x ∈ s`.

-/


noncomputable section

open_locale BigOperators Classical

universe u

namespace Lagrange

variable {F : Type u} [DecidableEq F] [Field F] (s : Finset F)

variable {F' : Type u} [Field F'] (s' : Finset F')

open Polynomial

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Lagrange basis polynomials that evaluate to 1 at `x` and 0 at other elements of `s`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `basis [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`x] [":" `F] [] ")")]
   [(Term.typeSpec ":" (Term.app `Polynomial [`F]))])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
    " in "
    (Term.app `s.erase [`x])
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Term.app `C [(Init.Logic.«term_⁻¹» («term_-_» `x "-" `y) "⁻¹")])
     "*"
     («term_-_» `X "-" (Term.app `C [`y]))))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
   " in "
   (Term.app `s.erase [`x])
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app `C [(Init.Logic.«term_⁻¹» («term_-_» `x "-" `y) "⁻¹")])
    "*"
    («term_-_» `X "-" (Term.app `C [`y]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app `C [(Init.Logic.«term_⁻¹» («term_-_» `x "-" `y) "⁻¹")])
   "*"
   («term_-_» `X "-" (Term.app `C [`y])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `X "-" (Term.app `C [`y]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `C [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `X
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `C [(Init.Logic.«term_⁻¹» («term_-_» `x "-" `y) "⁻¹")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_⁻¹» («term_-_» `x "-" `y) "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_-_» `x "-" `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `x "-" `y) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_⁻¹» (Term.paren "(" [(«term_-_» `x "-" `y) []] ")") "⁻¹") []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `s.erase [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s.erase
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Lagrange basis polynomials that evaluate to 1 at `x` and 0 at other elements of `s`. -/
  def basis ( x : F ) : Polynomial F := ∏ y in s.erase x , C x - y ⁻¹ * X - C y

@[simp]
theorem basis_empty (x : F) : basis ∅ x = 1 :=
  rfl

@[simp]
theorem eval_basis_self (x : F) : (basis s x).eval x = 1 := by
  rw [basis, ← coe_eval_ring_hom, (eval_ring_hom x).map_prod, coe_eval_ring_hom, Finset.prod_eq_one]
  intro y hy
  simp_rw [eval_mul, eval_sub, eval_C, eval_X]
  exact inv_mul_cancel (sub_ne_zero_of_ne (Finset.ne_of_mem_erase hy).symm)

@[simp]
theorem eval_basis_ne (x y : F) (h1 : y ∈ s) (h2 : y ≠ x) : (basis s x).eval y = 0 := by
  rw [basis, ← coe_eval_ring_hom, (eval_ring_hom y).map_prod, coe_eval_ring_hom,
    Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h2, h1⟩)]
  simp_rw [eval_mul, eval_sub, eval_C, eval_X, sub_self, mul_zero]

theorem eval_basis (x y : F) (h : y ∈ s) : (basis s x).eval y = if y = x then 1 else 0 := by
  split_ifs with H
  ·
    subst H
    apply eval_basis_self
  ·
    exact eval_basis_ne s x y h H

@[simp]
theorem nat_degree_basis (x : F) (hx : x ∈ s) : (basis s x).natDegree = s.card - 1 := by
  unfold basis
  generalize hsx : s.erase x = sx
  have : x ∉ sx := hsx ▸ Finset.not_mem_erase x s
  rw [← Finset.insert_erase hx, hsx, Finset.card_insert_of_not_mem this, add_tsub_cancel_right]
  clear hx hsx s
  revert this
  apply sx.induction_on
  ·
    intro hx
    rw [Finset.prod_empty, nat_degree_one]
    rfl
  ·
    intro y s hys ih hx
    rw [Finset.mem_insert, not_or_distrib] at hx
    have h1 : C ((x - y)⁻¹) ≠ C 0 := fun h => hx.1 (eq_of_sub_eq_zero $ inv_eq_zero.1 $ C_inj.1 h)
    have h2 : (X^1) - C y ≠ 0 := by
      convert X_pow_sub_C_ne_zero zero_lt_one y
    rw [C_0] at h1
    rw [pow_oneₓ] at h2
    rw [Finset.prod_insert hys, nat_degree_mul (mul_ne_zero h1 h2), ih hx.2, Finset.card_insert_of_not_mem hys,
      nat_degree_mul h1 h2, nat_degree_C, zero_addₓ, nat_degree, degree_X_sub_C, add_commₓ]
    rfl
    rw [Ne, Finset.prod_eq_zero_iff]
    rintro ⟨z, hzs, hz⟩
    rw [mul_eq_zero] at hz
    cases' hz with hz hz
    ·
      rw [← C_0, C_inj, inv_eq_zero, sub_eq_zero] at hz
      exact hx.2 (hz.symm ▸ hzs)
    ·
      rw [← pow_oneₓ (X : Polynomial F)] at hz
      exact X_pow_sub_C_ne_zero zero_lt_one _ hz

variable (f : s → F)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Lagrange interpolation: given a finset `s` and a function `f : s → F`,\n`interpolate s f` is the unique polynomial of degree `< s.card`\nthat takes value `f x` on all `x` in `s`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `interpolate [])
  (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Polynomial [`F]))])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    " in "
    `s.attach
    ", "
    (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [(Term.app `f [`x])]) "*" (Term.app `basis [`s `x])))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   " in "
   `s.attach
   ", "
   (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [(Term.app `f [`x])]) "*" (Term.app `basis [`s `x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `C [(Term.app `f [`x])]) "*" (Term.app `basis [`s `x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `basis [`s `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `basis
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `C [(Term.app `f [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s.attach
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Lagrange interpolation: given a finset `s` and a function `f : s → F`,
    `interpolate s f` is the unique polynomial of degree `< s.card`
    that takes value `f x` on all `x` in `s`. -/
  def interpolate : Polynomial F := ∑ x in s.attach , C f x * basis s x

@[simp]
theorem interpolate_empty f : interpolate (∅ : Finset F) f = 0 :=
  rfl

@[simp]
theorem eval_interpolate x (H : x ∈ s) : eval x (interpolate s f) = f ⟨x, H⟩ := by
  rw [interpolate, ← coe_eval_ring_hom, (eval_ring_hom x).map_sum, coe_eval_ring_hom,
    Finset.sum_eq_single (⟨x, H⟩ : { x // x ∈ s })]
  ·
    rw [eval_mul, eval_C, Subtype.coe_mk, eval_basis_self, mul_oneₓ]
  ·
    rintro ⟨y, hy⟩ _ hyx
    rw [eval_mul, Subtype.coe_mk, eval_basis_ne s y x H, mul_zero]
    ·
      rintro rfl
      exact hyx rfl
  ·
    intro h
    exact absurd (Finset.mem_attach _ _) h

theorem degree_interpolate_lt : (interpolate s f).degree < s.card :=
  if H : s = ∅ then by
    subst H
    rw [interpolate_empty, degree_zero]
    exact WithBot.bot_lt_coe _
  else
    (degree_sum_le _ _).trans_lt $
      (Finset.sup_lt_iff $ WithBot.bot_lt_coe s.card).2 $ fun b _ =>
        calc (C (f b)*basis s b).degree ≤ (C (f b)).degree+(basis s b).degree := degree_mul_le _ _
          _ ≤ 0+(basis s b).degree := add_le_add_right degree_C_le _
          _ = (basis s b).degree := zero_addₓ _
          _ ≤ (basis s b).natDegree := degree_le_nat_degree
          _ = (s.card - 1 : ℕ) := by
          rw [nat_degree_basis s b b.2]
          _ < s.card := WithBot.coe_lt_coe.2 (Nat.pred_ltₓ $ mt Finset.card_eq_zero.1 H)
          

/--  Linear version of `interpolate`. -/
def linterpolate : (s → F) →ₗ[F] Polynomial F :=
  { toFun := interpolate s,
    map_add' := fun f g => by
      simp_rw [interpolate, ← Finset.sum_add_distrib, ← add_mulₓ, ← C_add]
      rfl,
    map_smul' := fun c f => by
      simp_rw [interpolate, Finset.smul_sum, C_mul', smul_smul]
      rfl }

@[simp]
theorem interpolate_add f g : interpolate s (f+g) = interpolate s f+interpolate s g :=
  (linterpolate s).map_add f g

@[simp]
theorem interpolate_zero : interpolate s 0 = 0 :=
  (linterpolate s).map_zero

@[simp]
theorem interpolate_neg f : interpolate s (-f) = -interpolate s f :=
  (linterpolate s).map_neg f

@[simp]
theorem interpolate_sub f g : interpolate s (f - g) = interpolate s f - interpolate s g :=
  (linterpolate s).map_sub f g

@[simp]
theorem interpolate_smul (c : F) f : interpolate s (c • f) = c • interpolate s f :=
  (linterpolate s).map_smul c f

theorem eq_zero_of_eval_eq_zero {f : Polynomial F'} (hf1 : f.degree < s'.card) (hf2 : ∀, ∀ x ∈ s', ∀, f.eval x = 0) :
    f = 0 :=
  by_contradiction $ fun hf3 =>
    not_le_of_lt hf1 $
      calc (s'.card : WithBot ℕ) ≤ f.roots.to_finset.card :=
        WithBot.coe_le_coe.2 $
          Finset.card_le_of_subset $ fun x hx => Multiset.mem_to_finset.mpr $ (mem_roots hf3).2 $ hf2 x hx
        _ ≤ f.roots.card := WithBot.coe_le_coe.2 $ f.roots.to_finset_card_le
        _ ≤ f.degree := card_roots hf3
        

theorem eq_of_eval_eq {f g : Polynomial F'} (hf : f.degree < s'.card) (hg : g.degree < s'.card)
    (hfg : ∀, ∀ x ∈ s', ∀, f.eval x = g.eval x) : f = g :=
  eq_of_sub_eq_zero $
    eq_zero_of_eval_eq_zero s' (lt_of_le_of_ltₓ (degree_sub_le f g) $ max_ltₓ hf hg) fun x hx => by
      rw [eval_sub, hfg x hx, sub_self]

theorem eq_interpolate (f : Polynomial F) (hf : f.degree < s.card) : (interpolate s fun x => f.eval x) = f :=
  eq_of_eval_eq s (degree_interpolate_lt s _) hf $ fun x hx => eval_interpolate s _ x hx

/--  Lagrange interpolation induces isomorphism between functions from `s` and polynomials
of degree less than `s.card`. -/
def fun_equiv_degree_lt : degree_lt F s.card ≃ₗ[F] s → F :=
  { toFun := fun f x => f.1.eval x, map_add' := fun f g => funext $ fun x => eval_add,
    map_smul' := fun c f =>
      funext $ fun x => by
        change eval (↑x) (c • f).val = (c • fun x : s => eval (↑x) f.val) x
        rw [Pi.smul_apply, smul_eq_mul, ← @eval_C F c _ x, ← eval_mul, eval_C, C_mul']
        rfl,
    invFun := fun f => ⟨interpolate s f, mem_degree_lt.2 $ degree_interpolate_lt s f⟩,
    left_inv := fun f => Subtype.eq $ eq_interpolate s f $ mem_degree_lt.1 f.2,
    right_inv := fun f => funext $ fun ⟨x, hx⟩ => eval_interpolate s f x hx }

end Lagrange

