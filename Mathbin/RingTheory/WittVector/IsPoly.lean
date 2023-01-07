/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis

! This file was ported from Lean 3 source module ring_theory.witt_vector.is_poly
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Ulift
import Mathbin.RingTheory.WittVector.Basic
import Mathbin.Data.MvPolynomial.Funext

/-!
# The `is_poly` predicate

`witt_vector.is_poly` is a (type-valued) predicate on functions `f : Π R, 𝕎 R → 𝕎 R`.
It asserts that there is a family of polynomials `φ : ℕ → mv_polynomial ℕ ℤ`,
such that the `n`th coefficient of `f x` is equal to `φ n` evaluated on the coefficients of `x`.
Many operations on Witt vectors satisfy this predicate (or an analogue for higher arity functions).
We say that such a function `f` is a *polynomial function*.

The power of satisfying this predicate comes from `is_poly.ext`.
It shows that if `φ` and `ψ` witness that `f` and `g` are polynomial functions,
then `f = g` not merely when `φ = ψ`, but in fact it suffices to prove
```
∀ n, bind₁ φ (witt_polynomial p _ n) = bind₁ ψ (witt_polynomial p _ n)
```
(in other words, when evaluating the Witt polynomials on `φ` and `ψ`, we get the same values)
which will then imply `φ = ψ` and hence `f = g`.

Even though this sufficient condition looks somewhat intimidating,
it is rather pleasant to check in practice;
more so than direct checking of `φ = ψ`.

In practice, we apply this technique to show that the composition of `witt_vector.frobenius`
and `witt_vector.verschiebung` is equal to multiplication by `p`.

## Main declarations

* `witt_vector.is_poly`, `witt_vector.is_poly₂`:
  two predicates that assert that a unary/binary function on Witt vectors
  is polynomial in the coefficients of the input values.
* `witt_vector.is_poly.ext`, `witt_vector.is_poly₂.ext`:
  two polynomial functions are equal if their families of polynomials are equal
  after evaluating the Witt polynomials on them.
* `witt_vector.is_poly.comp` (+ many variants) show that unary/binary compositions
  of polynomial functions are polynomial.
* `witt_vector.id_is_poly`, `witt_vector.neg_is_poly`,
  `witt_vector.add_is_poly₂`, `witt_vector.mul_is_poly₂`:
  several well-known operations are polynomial functions
  (for Verschiebung, Frobenius, and multiplication by `p`, see their respective files).

## On higher arity analogues

Ideally, there should be a predicate `is_polyₙ` for functions of higher arity,
together with `is_polyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary and binary variants so far.
Nullary functions (a.k.a. constants) are treated
as constant functions and fall under the unary case.

## Tactics

There are important metaprograms defined in this file:
the tactics `ghost_simp` and `ghost_calc` and the attributes `@[is_poly]` and `@[ghost_simps]`.
These are used in combination to discharge proofs of identities between polynomial functions.

Any atomic proof of `is_poly` or `is_poly₂` (i.e. not taking additional `is_poly` arguments)
should be tagged as `@[is_poly]`.

Any lemma doing "ring equation rewriting" with polynomial functions should be tagged
`@[ghost_simps]`, e.g.
```lean
@[ghost_simps]
lemma bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (witt_polynomial p ℤ n) = (witt_polynomial p ℤ (n+1))
```

Proofs of identities between polynomial functions will often follow the pattern
```lean
begin
  ghost_calc _,
  <minor preprocessing>,
  ghost_simp
end
```

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment "/--" "Simplification rules for ghost equations -/")]
     "register_simp_attr"
     `ghost_simps)-/-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simplification rules for ghost equations -/ register_simp_attr ghost_simps

namespace Tactic

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- A macro for a common simplification when rewriting with ghost component equations. -/
unsafe def ghost_simp (lems : parse simp_arg_list) : tactic Unit := do
  tactic.try tactic.intro1
  simp none none tt (lems ++ [simp_arg_type.symm_expr ``(sub_eq_add_neg)]) [`ghost_simps]
      (loc.ns [none])
#align tactic.interactive.ghost_simp tactic.interactive.ghost_simp

/-- `ghost_calc` is a tactic for proving identities between polynomial functions.
Typically, when faced with a goal like
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
you can
1. call `ghost_calc`
2. do a small amount of manual work -- maybe nothing, maybe `rintro`, etc
3. call `ghost_simp`

and this will close the goal.

`ghost_calc` cannot detect whether you are dealing with unary or binary polynomial functions.
You must give it arguments to determine this.
If you are proving a universally quantified goal like the above,
call `ghost_calc _ _`.
If the variables are introduced already, call `ghost_calc x y`.
In the unary case, use `ghost_calc _` or `ghost_calc x`.

`ghost_calc` is a light wrapper around type class inference.
All it does is apply the appropriate extensionality lemma and try to infer the resulting goals.
This is subtle and Lean's elaborator doesn't like it because of the HO unification involved,
so it is easier (and prettier) to put it in a tactic script.
-/
unsafe def ghost_calc (ids' : parse ident_*) : tactic Unit := do
  let ids ← ids'.mmap fun n => get_local n <|> tactic.intro n
  let q(@Eq (WittVector _ $(R)) _ _) ← target
  match ids with
    | [x] => refine `(is_poly.ext _ _ _ _ $(x))
    | [x, y] => refine `(is_poly₂.ext _ _ _ _ $(x) $(y))
    | _ => fail "ghost_calc takes one or two arguments"
  let nm ←
    match R with
      | expr.local_const _ nm _ _ => return nm
      | _ => get_unused_name `R
  iterate_exactly 2 apply_instance
  unfreezingI (tactic.clear' tt [R])
  introsI <| [nm, .str nm "_inst"] ++ ids'
  skip
#align tactic.interactive.ghost_calc tactic.interactive.ghost_calc

end Interactive

end Tactic

namespace WittVector

universe u

variable {p : ℕ} {R S : Type u} {σ idx : Type _} [hp : Fact p.Prime] [CommRing R] [CommRing S]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

-- type as `\bbW`
open MvPolynomial

open Function (uncurry)

include hp

variable (p)

noncomputable section

/-!
### The `is_poly` predicate
-/


theorem poly_eq_of_witt_polynomial_bind_eq' (f g : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g :=
  by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← Function.funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp, map_bind₁, map_witt_polynomial, ← bind₁_bind₁,
    bind₁_witt_polynomial_X_in_terms_of_W, bind₁_X_right] using h
#align
  witt_vector.poly_eq_of_witt_polynomial_bind_eq' WittVector.poly_eq_of_witt_polynomial_bind_eq'

theorem poly_eq_of_witt_polynomial_bind_eq (f g : ℕ → MvPolynomial ℕ ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g :=
  by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← Function.funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp, map_bind₁, map_witt_polynomial, ← bind₁_bind₁,
    bind₁_witt_polynomial_X_in_terms_of_W, bind₁_X_right] using h
#align witt_vector.poly_eq_of_witt_polynomial_bind_eq WittVector.poly_eq_of_witt_polynomial_bind_eq

omit hp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings\nis said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th\ncoefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.\n\nSee also `witt_vector.is_poly₂` for the binary variant.\n\nThe `ghost_calc` tactic treats `is_poly` as a type class,\nand the `@[is_poly]` attribute derives certain specialized composition instances\nfor declarations of type `is_poly f`.\nFor the most part, users are not expected to treat `is_poly` as a class.\n-/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `IsPoly [])
      [(Term.explicitBinder
        "("
        [`f]
        [":"
         (Term.forall
          "∀"
          [(Term.strictImplicitBinder "⦃" [`R] [] "⦄")
           (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")]
          []
          ","
          (Term.arrow
           (Term.app `WittVector [`p `R])
           "→"
           (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])))]
        []
        ")")]
      []
      [(Term.typeSpec ":" (Term.prop "Prop"))]
      ["where"
       [(Command.structCtor (Command.declModifiers [] [] [] [] [] []) `mk' "::")]
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `poly
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `φ)]
                [":"
                 (Term.arrow (termℕ "ℕ") "→" (Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")]))]))
              ","
              (Term.forall
               "∀"
               [(Term.strictImplicitBinder "⦃" [`R] [] "⦄")
                (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")
                (Term.explicitBinder
                 "("
                 [`x]
                 [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
                 []
                 ")")]
               []
               ","
               («term_=_»
                (Term.proj (Term.app `f [`x]) "." `coeff)
                "="
                (Term.fun
                 "fun"
                 (Term.basicFun [`n] [] "=>" (Term.app `aeval [`x.coeff (Term.app `φ [`n])])))))))])
          [])])]
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structExplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structInstBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `φ)]
         [":" (Term.arrow (termℕ "ℕ") "→" (Term.app `MvPolynomial [(termℕ "ℕ") (termℤ "ℤ")]))]))
       ","
       (Term.forall
        "∀"
        [(Term.strictImplicitBinder "⦃" [`R] [] "⦄")
         (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")
         (Term.explicitBinder
          "("
          [`x]
          [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
          []
          ")")]
        []
        ","
        («term_=_»
         (Term.proj (Term.app `f [`x]) "." `coeff)
         "="
         (Term.fun
          "fun"
          (Term.basicFun [`n] [] "=>" (Term.app `aeval [`x.coeff (Term.app `φ [`n])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.strictImplicitBinder "⦃" [`R] [] "⦄")
        (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")
        (Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
         []
         ")")]
       []
       ","
       («term_=_»
        (Term.proj (Term.app `f [`x]) "." `coeff)
        "="
        (Term.fun
         "fun"
         (Term.basicFun [`n] [] "=>" (Term.app `aeval [`x.coeff (Term.app `φ [`n])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.proj (Term.app `f [`x]) "." `coeff)
       "="
       (Term.fun
        "fun"
        (Term.basicFun [`n] [] "=>" (Term.app `aeval [`x.coeff (Term.app `φ [`n])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.app `aeval [`x.coeff (Term.app `φ [`n])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aeval [`x.coeff (Term.app `φ [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x.coeff
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.app `f [`x]) "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`x]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.IsPoly.term𝕎', expected 'WittVector.RingTheory.WittVector.IsPoly.term𝕎._@.RingTheory.WittVector.IsPoly._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
/--
    A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings
    is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
    coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.
    
    See also `witt_vector.is_poly₂` for the binary variant.
    
    The `ghost_calc` tactic treats `is_poly` as a type class,
    and the `@[is_poly]` attribute derives certain specialized composition instances
    for declarations of type `is_poly f`.
    For the most part, users are not expected to treat `is_poly` as a class.
    -/
  class
    IsPoly
    ( f : ∀ ⦃ R ⦄ [ CommRing R ] , WittVector p R → 𝕎 R )
    : Prop
    where
      mk' ::
      poly
        :
          ∃
            φ : ℕ → MvPolynomial ℕ ℤ
            ,
            ∀ ⦃ R ⦄ [ CommRing R ] ( x : 𝕎 R ) , f x . coeff = fun n => aeval x.coeff φ n
#align witt_vector.is_poly WittVector.IsPoly

/-- The identity function on Witt vectors is a polynomial function. -/
instance id_is_poly : IsPoly p fun _ _ => id :=
  ⟨⟨x, by
      intros
      simp only [aeval_X, id]⟩⟩
#align witt_vector.id_is_poly WittVector.id_is_poly

instance id_is_poly_i' : IsPoly p fun _ _ a => a :=
  WittVector.id_is_poly _
#align witt_vector.id_is_poly_i' WittVector.id_is_poly_i'

namespace IsPoly

instance : Inhabited (IsPoly p fun _ _ => id) :=
  ⟨WittVector.id_is_poly p⟩

variable {p}

include hp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ext [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `IsPoly [`p `f])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `IsPoly [`p `g])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`R] [":" (Term.type "Type" [`u])] [] ")")
            (Term.instBinder "[" [`_Rcr ":"] (Term.app `CommRing [`R]) "]")
            (Term.explicitBinder
             "("
             [`x]
             [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
             []
             ")")
            (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
           []
           ","
           («term_=_»
            (Term.app `ghost_component [`n (Term.app `f [`x])])
            "="
            (Term.app `ghost_component [`n (Term.app `g [`x])])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.explicitBinder "(" [`R] [":" (Term.type "Type" [`u])] [] ")")
          (Term.instBinder "[" [`_Rcr ":"] (Term.app `CommRing [`R]) "]")
          (Term.explicitBinder
           "("
           [`x]
           [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
           []
           ")")]
         []
         ","
         («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                  [])]
                "⟩")])]
            []
            [":=" [`hf]])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ψ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                  [])]
                "⟩")])]
            []
            [":=" [`hg]])
           []
           (Tactic.intros "intros" [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `hf)
              ","
              (Tactic.rwRule [] `hg)
              ","
              (Tactic.rwRule [] (Term.app `poly_eq_of_witt_polynomial_bind_eq [`p `φ `ψ]))]
             "]")
            [])
           []
           (Tactic.intro "intro" [`k])
           []
           (Tactic.apply "apply" `MvPolynomial.funext)
           []
           (Tactic.intro "intro" [`x])
           []
           (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `hom_bind₁)] "]"] [])
           []
           (Tactic.specialize
            "specialize"
            (Term.app
             `h
             [(Term.app `ULift [(termℤ "ℤ")])
              (Term.app
               (Term.app `mk [`p])
               [(Term.fun
                 "fun"
                 (Term.basicFun [`i] [] "=>" (Term.anonymousCtor "⟨" [(Term.app `x [`i])] "⟩")))])
              `k]))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `ghost_component_apply)
              ","
              (Tactic.simpLemma [] [] `aeval_eq_eval₂_hom)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Tactic.apply
            "apply"
            (Term.proj
             (Term.typeAscription
              "("
              `ulift.ring_equiv.symm
              ":"
              [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
              ")")
             "."
             `Injective))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingEquiv.coe_toRingHom)
              ","
              (Tactic.simpLemma [] [] `map_eval₂_hom)]
             "]"]
            [])
           []
           (convert "convert" [] `h ["using" (num "1")])
           []
           (Tactic.allGoals
            "all_goals"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(tacticFunext__ "funext" [`i])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `hf)
                  ","
                  (Tactic.simpLemma [] [] `hg)
                  ","
                  (Tactic.simpLemma [] [] `MvPolynomial.eval)
                  ","
                  (Tactic.simpLemma [] [] `map_eval₂_hom)]
                 "]"]
                [])
               []
               (Tactic.apply
                "apply"
                (Term.app
                 `eval₂_hom_congr
                 [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                  (Term.hole "_")
                  `rfl]))
               []
               (Std.Tactic.Ext.tacticExt1___ "ext1" [])
               []
               (Tactic.apply
                "apply"
                (Term.app
                 `eval₂_hom_congr
                 [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                  (Term.hole "_")
                  `rfl]))
               []
               (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `coeff_mk)] "]"] [])
               ";"
               (Tactic.tacticRfl "rfl")])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                 [])]
               "⟩")])]
           []
           [":=" [`hf]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ψ)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                 [])]
               "⟩")])]
           []
           [":=" [`hg]])
          []
          (Tactic.intros "intros" [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `hf)
             ","
             (Tactic.rwRule [] `hg)
             ","
             (Tactic.rwRule [] (Term.app `poly_eq_of_witt_polynomial_bind_eq [`p `φ `ψ]))]
            "]")
           [])
          []
          (Tactic.intro "intro" [`k])
          []
          (Tactic.apply "apply" `MvPolynomial.funext)
          []
          (Tactic.intro "intro" [`x])
          []
          (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `hom_bind₁)] "]"] [])
          []
          (Tactic.specialize
           "specialize"
           (Term.app
            `h
            [(Term.app `ULift [(termℤ "ℤ")])
             (Term.app
              (Term.app `mk [`p])
              [(Term.fun
                "fun"
                (Term.basicFun [`i] [] "=>" (Term.anonymousCtor "⟨" [(Term.app `x [`i])] "⟩")))])
             `k]))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `ghost_component_apply)
             ","
             (Tactic.simpLemma [] [] `aeval_eq_eval₂_hom)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.apply
           "apply"
           (Term.proj
            (Term.typeAscription
             "("
             `ulift.ring_equiv.symm
             ":"
             [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
             ")")
            "."
            `Injective))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingEquiv.coe_toRingHom)
             ","
             (Tactic.simpLemma [] [] `map_eval₂_hom)]
            "]"]
           [])
          []
          (convert "convert" [] `h ["using" (num "1")])
          []
          (Tactic.allGoals
           "all_goals"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(tacticFunext__ "funext" [`i])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `hf)
                 ","
                 (Tactic.simpLemma [] [] `hg)
                 ","
                 (Tactic.simpLemma [] [] `MvPolynomial.eval)
                 ","
                 (Tactic.simpLemma [] [] `map_eval₂_hom)]
                "]"]
               [])
              []
              (Tactic.apply
               "apply"
               (Term.app
                `eval₂_hom_congr
                [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                 (Term.hole "_")
                 `rfl]))
              []
              (Std.Tactic.Ext.tacticExt1___ "ext1" [])
              []
              (Tactic.apply
               "apply"
               (Term.app
                `eval₂_hom_congr
                [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                 (Term.hole "_")
                 `rfl]))
              []
              (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `coeff_mk)] "]"] [])
              ";"
              (Tactic.tacticRfl "rfl")])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.allGoals
       "all_goals"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(tacticFunext__ "funext" [`i])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `hf)
             ","
             (Tactic.simpLemma [] [] `hg)
             ","
             (Tactic.simpLemma [] [] `MvPolynomial.eval)
             ","
             (Tactic.simpLemma [] [] `map_eval₂_hom)]
            "]"]
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `eval₂_hom_congr
            [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
          []
          (Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `eval₂_hom_congr
            [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
          []
          (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `coeff_mk)] "]"] [])
          ";"
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `coeff_mk)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coeff_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `eval₂_hom_congr
        [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eval₂_hom_congr
       [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.ext_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `eval₂_hom_congr
        [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eval₂_hom_congr
       [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.ext_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hf)
         ","
         (Tactic.simpLemma [] [] `hg)
         ","
         (Tactic.simpLemma [] [] `MvPolynomial.eval)
         ","
         (Tactic.simpLemma [] [] `map_eval₂_hom)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_eval₂_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MvPolynomial.eval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticFunext__ "funext" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `h ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingEquiv.coe_toRingHom)
         ","
         (Tactic.simpLemma [] [] `map_eval₂_hom)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_eval₂_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingEquiv.coe_toRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj
        (Term.typeAscription
         "("
         `ulift.ring_equiv.symm
         ":"
         [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
         ")")
        "."
        `Injective))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        `ulift.ring_equiv.symm
        ":"
        [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
        ")")
       "."
       `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       `ulift.ring_equiv.symm
       ":"
       [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ulift.ring_equiv.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `ghost_component_apply)
         ","
         (Tactic.simpLemma [] [] `aeval_eq_eval₂_hom)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_eq_eval₂_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ghost_component_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.specialize
       "specialize"
       (Term.app
        `h
        [(Term.app `ULift [(termℤ "ℤ")])
         (Term.app
          (Term.app `mk [`p])
          [(Term.fun
            "fun"
            (Term.basicFun [`i] [] "=>" (Term.anonymousCtor "⟨" [(Term.app `x [`i])] "⟩")))])
         `k]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h
       [(Term.app `ULift [(termℤ "ℤ")])
        (Term.app
         (Term.app `mk [`p])
         [(Term.fun
           "fun"
           (Term.basicFun [`i] [] "=>" (Term.anonymousCtor "⟨" [(Term.app `x [`i])] "⟩")))])
        `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.app `mk [`p])
       [(Term.fun
         "fun"
         (Term.basicFun [`i] [] "=>" (Term.anonymousCtor "⟨" [(Term.app `x [`i])] "⟩")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`i] [] "=>" (Term.anonymousCtor "⟨" [(Term.app `x [`i])] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `x [`i])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `mk [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `mk [`p]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.paren "(" (Term.app `mk [`p]) ")")
      [(Term.fun
        "fun"
        (Term.basicFun [`i] [] "=>" (Term.anonymousCtor "⟨" [(Term.app `x [`i])] "⟩")))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ULift [(termℤ "ℤ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ULift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ULift [(termℤ "ℤ")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `hom_bind₁)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hom_bind₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `MvPolynomial.funext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MvPolynomial.funext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`k])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `hf)
         ","
         (Tactic.rwRule [] `hg)
         ","
         (Tactic.rwRule [] (Term.app `poly_eq_of_witt_polynomial_bind_eq [`p `φ `ψ]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `poly_eq_of_witt_polynomial_bind_eq [`p `φ `ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `poly_eq_of_witt_polynomial_bind_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ψ)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
             [])]
           "⟩")])]
       []
       [":=" [`hg]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
             [])]
           "⟩")])]
       []
       [":=" [`hf]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`R] [":" (Term.type "Type" [`u])] [] ")")
        (Term.instBinder "[" [`_Rcr ":"] (Term.app `CommRing [`R]) "]")
        (Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
         []
         ")")]
       []
       ","
       («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `f [`x]) "=" (Term.app `g [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.IsPoly.term𝕎', expected 'WittVector.RingTheory.WittVector.IsPoly.term𝕎._@.RingTheory.WittVector.IsPoly._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ext
  { f g }
      ( hf : IsPoly p f )
      ( hg : IsPoly p g )
      (
        h
        :
          ∀
            ( R : Type u ) [ _Rcr : CommRing R ] ( x : 𝕎 R ) ( n : ℕ )
            ,
            ghost_component n f x = ghost_component n g x
        )
    : ∀ ( R : Type u ) [ _Rcr : CommRing R ] ( x : 𝕎 R ) , f x = g x
  :=
    by
      obtain ⟨ φ , hf ⟩ := hf
        obtain ⟨ ψ , hg ⟩ := hg
        intros
        ext n
        rw [ hf , hg , poly_eq_of_witt_polynomial_bind_eq p φ ψ ]
        intro k
        apply MvPolynomial.funext
        intro x
        simp only [ hom_bind₁ ]
        specialize h ULift ℤ mk p fun i => ⟨ x i ⟩ k
        simp only [ ghost_component_apply , aeval_eq_eval₂_hom ] at h
        apply ( ulift.ring_equiv.symm : ℤ ≃+* _ ) . Injective
        simp only [ ← RingEquiv.coe_toRingHom , map_eval₂_hom ]
        convert h using 1
        all_goals
          funext i
            simp only [ hf , hg , MvPolynomial.eval , map_eval₂_hom ]
            apply eval₂_hom_congr RingHom.ext_int _ _ _ rfl
            ext1
            apply eval₂_hom_congr RingHom.ext_int _ _ _ rfl
            simp only [ coeff_mk ]
            ;
            rfl
#align witt_vector.is_poly.ext WittVector.IsPoly.ext

omit hp

/-- The composition of polynomial functions is polynomial. -/
theorem comp {g f} (hg : IsPoly p g) (hf : IsPoly p f) :
    IsPoly p fun R _Rcr => @g R _Rcr ∘ @f R _Rcr :=
  by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [aeval_bind₁, Function.comp, hg, hf]
#align witt_vector.is_poly.comp WittVector.IsPoly.comp

end IsPoly

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors\nis said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th\ncoefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.\n\nSee also `witt_vector.is_poly` for the unary variant.\n\nThe `ghost_calc` tactic treats `is_poly₂` as a type class,\nand the `@[is_poly]` attribute derives certain specialized composition instances\nfor declarations of type `is_poly₂ f`.\nFor the most part, users are not expected to treat `is_poly₂` as a class.\n-/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `IsPoly₂ [])
      [(Term.explicitBinder
        "("
        [`f]
        [":"
         (Term.forall
          "∀"
          [(Term.strictImplicitBinder "⦃" [`R] [] "⦄")
           (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")]
          []
          ","
          (Term.arrow
           (Term.app `WittVector [`p `R])
           "→"
           (Term.arrow
            (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
            "→"
            (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R]))))]
        []
        ")")]
      []
      [(Term.typeSpec ":" (Term.prop "Prop"))]
      ["where"
       [(Command.structCtor (Command.declModifiers [] [] [] [] [] []) `mk' "::")]
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `poly
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `φ)]
                [":"
                 (Term.arrow
                  (termℕ "ℕ")
                  "→"
                  (Term.app
                   `MvPolynomial
                   [(«term_×_» (Term.app `Fin [(num "2")]) "×" (termℕ "ℕ")) (termℤ "ℤ")]))]))
              ","
              (Term.forall
               "∀"
               [(Term.strictImplicitBinder "⦃" [`R] [] "⦄")
                (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")
                (Term.explicitBinder
                 "("
                 [`x `y]
                 [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
                 []
                 ")")]
               []
               ","
               («term_=_»
                (Term.proj (Term.app `f [`x `y]) "." `coeff)
                "="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`n]
                  []
                  "=>"
                  (Term.app
                   `peval
                   [(Term.app `φ [`n])
                    (Matrix.Data.Fin.VecNotation.«term![_,»
                     "!["
                     [`x.coeff "," `y.coeff]
                     "]")])))))))])
          [])])]
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structExplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structInstBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `φ)]
         [":"
          (Term.arrow
           (termℕ "ℕ")
           "→"
           (Term.app
            `MvPolynomial
            [(«term_×_» (Term.app `Fin [(num "2")]) "×" (termℕ "ℕ")) (termℤ "ℤ")]))]))
       ","
       (Term.forall
        "∀"
        [(Term.strictImplicitBinder "⦃" [`R] [] "⦄")
         (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")
         (Term.explicitBinder
          "("
          [`x `y]
          [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
          []
          ")")]
        []
        ","
        («term_=_»
         (Term.proj (Term.app `f [`x `y]) "." `coeff)
         "="
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.app
            `peval
            [(Term.app `φ [`n])
             (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x.coeff "," `y.coeff] "]")]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.strictImplicitBinder "⦃" [`R] [] "⦄")
        (Term.instBinder "[" [] (Term.app `CommRing [`R]) "]")
        (Term.explicitBinder
         "("
         [`x `y]
         [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
         []
         ")")]
       []
       ","
       («term_=_»
        (Term.proj (Term.app `f [`x `y]) "." `coeff)
        "="
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.app
           `peval
           [(Term.app `φ [`n])
            (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x.coeff "," `y.coeff] "]")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.proj (Term.app `f [`x `y]) "." `coeff)
       "="
       (Term.fun
        "fun"
        (Term.basicFun
         [`n]
         []
         "=>"
         (Term.app
          `peval
          [(Term.app `φ [`n])
           (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x.coeff "," `y.coeff] "]")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.app
         `peval
         [(Term.app `φ [`n])
          (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x.coeff "," `y.coeff] "]")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `peval
       [(Term.app `φ [`n])
        (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x.coeff "," `y.coeff] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.Data.Fin.VecNotation.«term![_,»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`x.coeff "," `y.coeff] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y.coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x.coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `φ [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`n]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `peval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.app `f [`x `y]) "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`x `y]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.IsPoly.term𝕎', expected 'WittVector.RingTheory.WittVector.IsPoly.term𝕎._@.RingTheory.WittVector.IsPoly._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
/--
    A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
    is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
    coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.
    
    See also `witt_vector.is_poly` for the unary variant.
    
    The `ghost_calc` tactic treats `is_poly₂` as a type class,
    and the `@[is_poly]` attribute derives certain specialized composition instances
    for declarations of type `is_poly₂ f`.
    For the most part, users are not expected to treat `is_poly₂` as a class.
    -/
  class
    IsPoly₂
    ( f : ∀ ⦃ R ⦄ [ CommRing R ] , WittVector p R → 𝕎 R → 𝕎 R )
    : Prop
    where
      mk' ::
      poly
        :
          ∃
            φ : ℕ → MvPolynomial Fin 2 × ℕ ℤ
            ,
            ∀
              ⦃ R ⦄ [ CommRing R ] ( x y : 𝕎 R )
              ,
              f x y . coeff = fun n => peval φ n ![ x.coeff , y.coeff ]
#align witt_vector.is_poly₂ WittVector.IsPoly₂

variable {p}

/-- The composition of polynomial functions is polynomial. -/
theorem IsPoly₂.comp {h f g} (hh : IsPoly₂ p h) (hf : IsPoly p f) (hg : IsPoly p g) :
    IsPoly₂ p fun R _Rcr x y => h (f x) (g y) :=
  by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  obtain ⟨χ, hh⟩ := hh
  refine'
    ⟨⟨fun n =>
        bind₁
          (uncurry <|
            ![fun k => rename (Prod.mk (0 : Fin 2)) (φ k), fun k =>
              rename (Prod.mk (1 : Fin 2)) (ψ k)])
          (χ n),
        _⟩⟩
  intros
  funext n
  simp only [peval, aeval_bind₁, Function.comp, hh, hf, hg, uncurry]
  apply eval₂_hom_congr rfl _ rfl
  ext ⟨i, n⟩
  fin_cases i <;>
    simp only [aeval_eq_eval₂_hom, eval₂_hom_rename, Function.comp, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
#align witt_vector.is_poly₂.comp WittVector.IsPoly₂.comp

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
theorem IsPoly.comp₂ {g f} (hg : IsPoly p g) (hf : IsPoly₂ p f) :
    IsPoly₂ p fun R _Rcr x y => g (f x y) :=
  by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [peval, aeval_bind₁, Function.comp, hg, hf]
#align witt_vector.is_poly.comp₂ WittVector.IsPoly.comp₂

/-- The diagonal `λ x, f x x` of a polynomial function `f` is polynomial. -/
theorem IsPoly₂.diag {f} (hf : IsPoly₂ p f) : IsPoly p fun R _Rcr x => f x x :=
  by
  obtain ⟨φ, hf⟩ := hf
  refine' ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), _⟩⟩
  intros ; funext n
  simp only [hf, peval, uncurry, aeval_bind₁]
  apply eval₂_hom_congr rfl _ rfl
  ext ⟨i, k⟩;
  fin_cases i <;> simp only [Matrix.head_cons, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
#align witt_vector.is_poly₂.diag WittVector.IsPoly₂.diag

open Tactic

namespace Tactic

/-!
### The `@[is_poly]` attribute

This attribute is used to derive specialized composition instances
for `is_poly` and `is_poly₂` declarations.
-/


/-- If `n` is the name of a lemma with opened type `∀ vars, is_poly p _`,
`mk_poly_comp_lemmas n vars p` adds composition instances to the environment
`n.comp_i` and `n.comp₂_i`.
-/
unsafe def mk_poly_comp_lemmas (n : Name) (vars : List expr) (p : expr) : tactic Unit := do
  let c ← mk_const n
  let appd := vars.foldl expr.app c
  let tgt_bod ←
    to_expr ``(fun f [hf : IsPoly $(p) f] => IsPoly.comp $(appd) hf) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod
  let nm := .str n "comp_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
  let tgt_bod ←
    to_expr ``(fun f [hf : IsPoly₂ $(p) f] => IsPoly.comp₂ $(appd) hf) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod
  let nm := .str n "comp₂_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
#align witt_vector.tactic.mk_poly_comp_lemmas witt_vector.tactic.mk_poly_comp_lemmas

/-- If `n` is the name of a lemma with opened type `∀ vars, is_poly₂ p _`,
`mk_poly₂_comp_lemmas n vars p` adds composition instances to the environment
`n.comp₂_i` and `n.comp_diag`.
-/
unsafe def mk_poly₂_comp_lemmas (n : Name) (vars : List expr) (p : expr) : tactic Unit := do
  let c ← mk_const n
  let appd := vars.foldl expr.app c
  let tgt_bod ←
    to_expr
          ``(fun {f g} [hf : IsPoly $(p) f] [hg : IsPoly $(p) g] => IsPoly₂.comp $(appd) hf hg) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod >>= simp_lemmas.mk.dsimplify
  let nm := .str n "comp₂_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
  let tgt_bod ←
    to_expr
          ``(fun {f g} [hf : IsPoly $(p) f] [hg : IsPoly $(p) g] =>
            (IsPoly₂.comp $(appd) hf hg).diag) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod >>= simp_lemmas.mk.dsimplify
  let nm := .str n "comp_diag"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
#align witt_vector.tactic.mk_poly₂_comp_lemmas witt_vector.tactic.mk_poly₂_comp_lemmas

/-- The `after_set` function for `@[is_poly]`. Calls `mk_poly(₂)_comp_lemmas`.
-/
unsafe def mk_comp_lemmas (n : Name) : tactic Unit := do
  let d ← get_decl n
  let (vars, tp) ← open_pis d.type
  match tp with
    | q(IsPoly $(p) _) => mk_poly_comp_lemmas n vars p
    | q(IsPoly₂ $(p) _) => mk_poly₂_comp_lemmas n vars p
    | _ => fail "@[is_poly] should only be applied to terms of type `is_poly _ _` or `is_poly₂ _ _`"
#align witt_vector.tactic.mk_comp_lemmas witt_vector.tactic.mk_comp_lemmas

/-- `@[is_poly]` is applied to lemmas of the form `is_poly f φ` or `is_poly₂ f φ`.
These lemmas should *not* be tagged as instances, and only atomic `is_poly` defs should be tagged:
composition lemmas should not. Roughly speaking, lemmas that take `is_poly` proofs as arguments
should not be tagged.

Type class inference struggles with function composition, and the higher order unification problems
involved in inferring `is_poly` proofs are complex. The standard style writing these proofs by hand
doesn't work very well. Instead, we construct the type class hierarchy "under the hood", with
limited forms of composition.

Applying `@[is_poly]` to a lemma creates a number of instances. Roughly, if the tagged lemma is a
proof of `is_poly f φ`, the instances added have the form
```lean
∀ g ψ, [is_poly g ψ] → is_poly (f ∘ g) _
```
Since `f` is fixed in this instance, it restricts the HO unification needed when the instance is
applied. Composition lemmas relating `is_poly` with `is_poly₂` are also added.
`id_is_poly` is an atomic instance.

The user-written lemmas are not instances. Users should be able to assemble `is_poly` proofs by hand
"as normal" if the tactic fails.
-/
@[user_attribute]
unsafe def is_poly_attr : user_attribute
    where
  Name := `is_poly
  descr := "Lemmas with this attribute describe the polynomial structure of functions"
  after_set := some fun n _ _ => mk_comp_lemmas n
#align witt_vector.tactic.is_poly_attr witt_vector.tactic.is_poly_attr

end Tactic

include hp

/-!
### `is_poly` instances

These are not declared as instances at the top level,
but the `@[is_poly]` attribute adds instances based on each one.
Users are expected to use the non-instance versions manually.
-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The additive negation is a polynomial function on Witt vectors. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `is_poly []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_is_poly [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `IsPoly
         [`p
          (Term.fun
           "fun"
           (Term.basicFun
            [`R (Term.hole "_")]
            []
            "=>"
            (Term.app
             (Term.explicit "@" `Neg.neg)
             [(Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
              (Term.hole "_")])))])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun [`n] [] "=>" (Term.app `rename [`Prod.snd (Term.app `wittNeg [`p `n])])))
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intros "intros" [])
               ";"
               (tacticFunext__ "funext" [`n])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `neg_coeff)
                  ","
                  (Tactic.rwRule [] `aeval_eq_eval₂_hom)
                  ","
                  (Tactic.rwRule [] `eval₂_hom_rename)]
                 "]")
                [])
               []
               (Tactic.apply "apply" (Term.app `eval₂_hom_congr [`rfl (Term.hole "_") `rfl]))
               []
               (Std.Tactic.Ext.«tacticExt___:_»
                "ext"
                [(Std.Tactic.RCases.rintroPat.one
                  (Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                     [])]
                   "⟩"))]
                [])
               ";"
               (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
               ";"
               (Tactic.tacticRfl "rfl")])))]
          "⟩")]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun [`n] [] "=>" (Term.app `rename [`Prod.snd (Term.app `wittNeg [`p `n])])))
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.intros "intros" [])
              ";"
              (tacticFunext__ "funext" [`n])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `neg_coeff)
                 ","
                 (Tactic.rwRule [] `aeval_eq_eval₂_hom)
                 ","
                 (Tactic.rwRule [] `eval₂_hom_rename)]
                "]")
               [])
              []
              (Tactic.apply "apply" (Term.app `eval₂_hom_congr [`rfl (Term.hole "_") `rfl]))
              []
              (Std.Tactic.Ext.«tacticExt___:_»
               "ext"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                    [])]
                  "⟩"))]
               [])
              ";"
              (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
              ";"
              (Tactic.tacticRfl "rfl")])))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun [`n] [] "=>" (Term.app `rename [`Prod.snd (Term.app `wittNeg [`p `n])])))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intros "intros" [])
            ";"
            (tacticFunext__ "funext" [`n])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `neg_coeff)
               ","
               (Tactic.rwRule [] `aeval_eq_eval₂_hom)
               ","
               (Tactic.rwRule [] `eval₂_hom_rename)]
              "]")
             [])
            []
            (Tactic.apply "apply" (Term.app `eval₂_hom_congr [`rfl (Term.hole "_") `rfl]))
            []
            (Std.Tactic.Ext.«tacticExt___:_»
             "ext"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                  [])]
                "⟩"))]
             [])
            ";"
            (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
            ";"
            (Tactic.tacticRfl "rfl")])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intros "intros" [])
          ";"
          (tacticFunext__ "funext" [`n])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `neg_coeff)
             ","
             (Tactic.rwRule [] `aeval_eq_eval₂_hom)
             ","
             (Tactic.rwRule [] `eval₂_hom_rename)]
            "]")
           [])
          []
          (Tactic.apply "apply" (Term.app `eval₂_hom_congr [`rfl (Term.hole "_") `rfl]))
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                [])]
              "⟩"))]
           [])
          ";"
          (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
          ";"
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `eval₂_hom_congr [`rfl (Term.hole "_") `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eval₂_hom_congr [`rfl (Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `neg_coeff)
         ","
         (Tactic.rwRule [] `aeval_eq_eval₂_hom)
         ","
         (Tactic.rwRule [] `eval₂_hom_rename)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval₂_hom_rename
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_eq_eval₂_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticFunext__ "funext" [`n])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`n] [] "=>" (Term.app `rename [`Prod.snd (Term.app `wittNeg [`p `n])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rename [`Prod.snd (Term.app `wittNeg [`p `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `wittNeg [`p `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wittNeg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `wittNeg [`p `n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Prod.snd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rename
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsPoly
       [`p
        (Term.fun
         "fun"
         (Term.basicFun
          [`R (Term.hole "_")]
          []
          "=>"
          (Term.app
           (Term.explicit "@" `Neg.neg)
           [(Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
            (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`R (Term.hole "_")]
        []
        "=>"
        (Term.app
         (Term.explicit "@" `Neg.neg)
         [(Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R]) (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Neg.neg)
       [(Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.IsPoly.term𝕎', expected 'WittVector.RingTheory.WittVector.IsPoly.term𝕎._@.RingTheory.WittVector.IsPoly._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The additive negation is a polynomial function on Witt vectors. -/ @[ is_poly ]
  theorem
    neg_is_poly
    : IsPoly p fun R _ => @ Neg.neg 𝕎 R _
    :=
      ⟨
        ⟨
          fun n => rename Prod.snd wittNeg p n
            ,
            by
              intros
                ;
                funext n
                rw [ neg_coeff , aeval_eq_eval₂_hom , eval₂_hom_rename ]
                apply eval₂_hom_congr rfl _ rfl
                ext ⟨ i , k ⟩
                ;
                fin_cases i
                ;
                rfl
          ⟩
        ⟩
#align witt_vector.neg_is_poly WittVector.neg_is_poly

section ZeroOne

/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/
/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
instance zero_is_poly : IsPoly p fun _ _ _ => 0 :=
  ⟨⟨0, by
      intros
      funext n
      simp only [Pi.zero_apply, AlgHom.map_zero, zero_coeff]⟩⟩
#align witt_vector.zero_is_poly WittVector.zero_is_poly

@[simp]
theorem bind₁_zero_witt_polynomial (n : ℕ) :
    bind₁ (0 : ℕ → MvPolynomial ℕ R) (wittPolynomial p R n) = 0 := by
  rw [← aeval_eq_bind₁, aeval_zero, constant_coeff_witt_polynomial, RingHom.map_zero]
#align witt_vector.bind₁_zero_witt_polynomial WittVector.bind₁_zero_witt_polynomial

omit hp

/-- The coefficients of `1 : 𝕎 R` as polynomials. -/
def onePoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 1 else 0
#align witt_vector.one_poly WittVector.onePoly

include hp

@[simp]
theorem bind₁_one_poly_witt_polynomial (n : ℕ) : bind₁ onePoly (wittPolynomial p ℤ n) = 1 :=
  by
  rw [witt_polynomial_eq_sum_C_mul_X_pow, AlgHom.map_sum, Finset.sum_eq_single 0]
  ·
    simp only [one_poly, one_pow, one_mul, AlgHom.map_pow, C_1, pow_zero, bind₁_X_right, if_true,
      eq_self_iff_true]
  · intro i hi hi0
    simp only [one_poly, if_neg hi0, zero_pow (pow_pos hp.1.Pos _), mul_zero, AlgHom.map_pow,
      bind₁_X_right, AlgHom.map_mul]
  · rw [Finset.mem_range]
    decide
#align witt_vector.bind₁_one_poly_witt_polynomial WittVector.bind₁_one_poly_witt_polynomial

/-- The function that is constantly one on Witt vectors is a polynomial function. -/
instance one_is_poly : IsPoly p fun _ _ _ => 1 :=
  ⟨⟨onePoly, by
      intros ; funext n; cases n
      · simp only [one_poly, if_true, eq_self_iff_true, one_coeff_zero, AlgHom.map_one]
      ·
        simp only [one_poly, Nat.succ_pos', one_coeff_eq_of_pos, if_neg n.succ_ne_zero,
          AlgHom.map_zero]⟩⟩
#align witt_vector.one_is_poly WittVector.one_is_poly

end ZeroOne

omit hp

/-- Addition of Witt vectors is a polynomial function. -/
@[is_poly]
theorem add_is_poly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· + ·) :=
  ⟨⟨wittAdd p, by
      intros
      dsimp only [WittVector.hasAdd]
      simp [eval]⟩⟩
#align witt_vector.add_is_poly₂ WittVector.add_is_poly₂

/-- Multiplication of Witt vectors is a polynomial function. -/
@[is_poly]
theorem mul_is_poly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· * ·) :=
  ⟨⟨wittMul p, by
      intros
      dsimp only [WittVector.hasMul]
      simp [eval]⟩⟩
#align witt_vector.mul_is_poly₂ WittVector.mul_is_poly₂

include hp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `IsPoly.map [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f] [] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `IsPoly [`p `f])] [] ")")
        (Term.explicitBinder "(" [`g] [":" (Algebra.Hom.Ring.«term_→+*_» `R " →+* " `S)] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `map [`g (Term.app `f [`x])])
         "="
         (Term.app `f [(Term.app `map [`g `x])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                  [])]
                "⟩")])]
            []
            [":=" [`hf]])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `map_coeff)
              ","
              (Tactic.simpLemma [] [] `hf)
              ","
              (Tactic.simpLemma [] [] `map_aeval)]
             "]"]
            [])
           []
           (Tactic.apply
            "apply"
            (Term.app
             `eval₂_hom_congr
             [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `map_coeff)] "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                 [])]
               "⟩")])]
           []
           [":=" [`hf]])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `map_coeff)
             ","
             (Tactic.simpLemma [] [] `hf)
             ","
             (Tactic.simpLemma [] [] `map_aeval)]
            "]"]
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `eval₂_hom_congr
            [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
          []
          (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `map_coeff)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `map_coeff)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `eval₂_hom_congr
        [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eval₂_hom_congr
       [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.ext_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `map_coeff)
         ","
         (Tactic.simpLemma [] [] `hf)
         ","
         (Tactic.simpLemma [] [] `map_aeval)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_aeval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
             [])]
           "⟩")])]
       []
       [":=" [`hf]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `map [`g (Term.app `f [`x])])
       "="
       (Term.app `f [(Term.app `map [`g `x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app `map [`g `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map [`g `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `map [`g `x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `map [`g (Term.app `f [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.IsPoly.term𝕎', expected 'WittVector.RingTheory.WittVector.IsPoly.term𝕎._@.RingTheory.WittVector.IsPoly._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  IsPoly.map
  { f } ( hf : IsPoly p f ) ( g : R →+* S ) ( x : 𝕎 R ) : map g f x = f map g x
  :=
    by
      obtain ⟨ φ , hf ⟩ := hf
        ext n
        simp only [ map_coeff , hf , map_aeval ]
        apply eval₂_hom_congr RingHom.ext_int _ _ _ rfl
        simp only [ map_coeff ]
#align witt_vector.is_poly.map WittVector.IsPoly.map

namespace IsPoly₂

omit hp

instance [Fact p.Prime] : Inhabited (IsPoly₂ p _) :=
  ⟨add_is_poly₂⟩

variable {p}

/-- The composition of a binary polynomial function
 with a unary polynomial function in the first argument is polynomial. -/
theorem comp_left {g f} (hg : IsPoly₂ p g) (hf : IsPoly p f) :
    IsPoly₂ p fun R _Rcr x y => g (f x) y :=
  hg.comp hf (WittVector.id_is_poly _)
#align witt_vector.is_poly₂.comp_left WittVector.IsPoly₂.comp_left

/-- The composition of a binary polynomial function
 with a unary polynomial function in the second argument is polynomial. -/
theorem comp_right {g f} (hg : IsPoly₂ p g) (hf : IsPoly p f) :
    IsPoly₂ p fun R _Rcr x y => g x (f y) :=
  hg.comp (WittVector.id_is_poly p) hf
#align witt_vector.is_poly₂.comp_right WittVector.IsPoly₂.comp_right

include hp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ext [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `IsPoly₂ [`p `f])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `IsPoly₂ [`p `g])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`R] [":" (Term.type "Type" [`u])] [] ")")
            (Term.instBinder "[" [`_Rcr ":"] (Term.app `CommRing [`R]) "]")
            (Term.explicitBinder
             "("
             [`x `y]
             [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
             []
             ")")
            (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
           []
           ","
           («term_=_»
            (Term.app `ghost_component [`n (Term.app `f [`x `y])])
            "="
            (Term.app `ghost_component [`n (Term.app `g [`x `y])])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.explicitBinder "(" [`R] [] [] ")")
          (Term.instBinder "[" [`_Rcr ":"] (Term.app `CommRing [`R]) "]")
          (Term.explicitBinder
           "("
           [`x `y]
           [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
           []
           ")")]
         []
         ","
         («term_=_» (Term.app `f [`x `y]) "=" (Term.app `g [`x `y])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                  [])]
                "⟩")])]
            []
            [":=" [`hf]])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ψ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                  [])]
                "⟩")])]
            []
            [":=" [`hg]])
           []
           (Tactic.intros "intros" [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `hf)
              ","
              (Tactic.rwRule [] `hg)
              ","
              (Tactic.rwRule [] (Term.app `poly_eq_of_witt_polynomial_bind_eq' [`p `φ `ψ]))]
             "]")
            [])
           []
           (Tactic.clear "clear" [`x `y])
           []
           (Tactic.intro "intro" [`k])
           []
           (Tactic.apply "apply" `MvPolynomial.funext)
           []
           (Tactic.intro "intro" [`x])
           []
           (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `hom_bind₁)] "]"] [])
           []
           (Tactic.specialize
            "specialize"
            (Term.app
             `h
             [(Term.app `ULift [(termℤ "ℤ")])
              (Term.app
               (Term.app `mk [`p])
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`i]
                  []
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])]
                   "⟩")))])
              (Term.app
               (Term.app `mk [`p])
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`i]
                  []
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])]
                   "⟩")))])
              `k]))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `ghost_component_apply)
              ","
              (Tactic.simpLemma [] [] `aeval_eq_eval₂_hom)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Tactic.apply
            "apply"
            (Term.proj
             (Term.typeAscription
              "("
              `ulift.ring_equiv.symm
              ":"
              [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
              ")")
             "."
             `Injective))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingEquiv.coe_toRingHom)
              ","
              (Tactic.simpLemma [] [] `map_eval₂_hom)]
             "]"]
            [])
           []
           (convert "convert" [] `h ["using" (num "1")])
           []
           (Tactic.allGoals
            "all_goals"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(tacticFunext__ "funext" [`i])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `hf)
                  ","
                  (Tactic.simpLemma [] [] `hg)
                  ","
                  (Tactic.simpLemma [] [] `MvPolynomial.eval)
                  ","
                  (Tactic.simpLemma [] [] `map_eval₂_hom)]
                 "]"]
                [])
               []
               (Tactic.apply
                "apply"
                (Term.app
                 `eval₂_hom_congr
                 [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                  (Term.hole "_")
                  `rfl]))
               []
               (Std.Tactic.Ext.tacticExt1___ "ext1" [])
               []
               (Tactic.apply
                "apply"
                (Term.app
                 `eval₂_hom_congr
                 [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                  (Term.hole "_")
                  `rfl]))
               []
               (Std.Tactic.Ext.«tacticExt___:_»
                "ext"
                [(Std.Tactic.RCases.rintroPat.one
                  (Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                     [])]
                   "⟩"))]
                [])
               []
               (Tactic.«tactic_<;>_»
                (Tactic.«tactic_<;>_»
                 (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
                 "<;>"
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `coeff_mk) "," (Tactic.simpLemma [] [] `uncurry)]
                   "]"]
                  []))
                "<;>"
                (Tactic.tacticRfl "rfl"))])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                 [])]
               "⟩")])]
           []
           [":=" [`hf]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ψ)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
                 [])]
               "⟩")])]
           []
           [":=" [`hg]])
          []
          (Tactic.intros "intros" [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `hf)
             ","
             (Tactic.rwRule [] `hg)
             ","
             (Tactic.rwRule [] (Term.app `poly_eq_of_witt_polynomial_bind_eq' [`p `φ `ψ]))]
            "]")
           [])
          []
          (Tactic.clear "clear" [`x `y])
          []
          (Tactic.intro "intro" [`k])
          []
          (Tactic.apply "apply" `MvPolynomial.funext)
          []
          (Tactic.intro "intro" [`x])
          []
          (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `hom_bind₁)] "]"] [])
          []
          (Tactic.specialize
           "specialize"
           (Term.app
            `h
            [(Term.app `ULift [(termℤ "ℤ")])
             (Term.app
              (Term.app `mk [`p])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i]
                 []
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])]
                  "⟩")))])
             (Term.app
              (Term.app `mk [`p])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i]
                 []
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])]
                  "⟩")))])
             `k]))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `ghost_component_apply)
             ","
             (Tactic.simpLemma [] [] `aeval_eq_eval₂_hom)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.apply
           "apply"
           (Term.proj
            (Term.typeAscription
             "("
             `ulift.ring_equiv.symm
             ":"
             [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
             ")")
            "."
            `Injective))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingEquiv.coe_toRingHom)
             ","
             (Tactic.simpLemma [] [] `map_eval₂_hom)]
            "]"]
           [])
          []
          (convert "convert" [] `h ["using" (num "1")])
          []
          (Tactic.allGoals
           "all_goals"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(tacticFunext__ "funext" [`i])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `hf)
                 ","
                 (Tactic.simpLemma [] [] `hg)
                 ","
                 (Tactic.simpLemma [] [] `MvPolynomial.eval)
                 ","
                 (Tactic.simpLemma [] [] `map_eval₂_hom)]
                "]"]
               [])
              []
              (Tactic.apply
               "apply"
               (Term.app
                `eval₂_hom_congr
                [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                 (Term.hole "_")
                 `rfl]))
              []
              (Std.Tactic.Ext.tacticExt1___ "ext1" [])
              []
              (Tactic.apply
               "apply"
               (Term.app
                `eval₂_hom_congr
                [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                 (Term.hole "_")
                 `rfl]))
              []
              (Std.Tactic.Ext.«tacticExt___:_»
               "ext"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                    [])]
                  "⟩"))]
               [])
              []
              (Tactic.«tactic_<;>_»
               (Tactic.«tactic_<;>_»
                (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
                "<;>"
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `coeff_mk) "," (Tactic.simpLemma [] [] `uncurry)]
                  "]"]
                 []))
               "<;>"
               (Tactic.tacticRfl "rfl"))])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.allGoals
       "all_goals"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(tacticFunext__ "funext" [`i])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `hf)
             ","
             (Tactic.simpLemma [] [] `hg)
             ","
             (Tactic.simpLemma [] [] `MvPolynomial.eval)
             ","
             (Tactic.simpLemma [] [] `map_eval₂_hom)]
            "]"]
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `eval₂_hom_congr
            [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
          []
          (Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `eval₂_hom_congr
            [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `coeff_mk) "," (Tactic.simpLemma [] [] `uncurry)] "]"]
             []))
           "<;>"
           (Tactic.tacticRfl "rfl"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
        "<;>"
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `coeff_mk) "," (Tactic.simpLemma [] [] `uncurry)] "]"]
         []))
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `coeff_mk) "," (Tactic.simpLemma [] [] `uncurry)] "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `coeff_mk) "," (Tactic.simpLemma [] [] `uncurry)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coeff_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `eval₂_hom_congr
        [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eval₂_hom_congr
       [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.ext_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `eval₂_hom_congr
        [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eval₂_hom_congr
       [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.ext_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hf)
         ","
         (Tactic.simpLemma [] [] `hg)
         ","
         (Tactic.simpLemma [] [] `MvPolynomial.eval)
         ","
         (Tactic.simpLemma [] [] `map_eval₂_hom)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_eval₂_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MvPolynomial.eval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticFunext__ "funext" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `h ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingEquiv.coe_toRingHom)
         ","
         (Tactic.simpLemma [] [] `map_eval₂_hom)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_eval₂_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingEquiv.coe_toRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj
        (Term.typeAscription
         "("
         `ulift.ring_equiv.symm
         ":"
         [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
         ")")
        "."
        `Injective))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        `ulift.ring_equiv.symm
        ":"
        [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
        ")")
       "."
       `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       `ulift.ring_equiv.symm
       ":"
       [(Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Ring.Equiv.«term_≃+*_» (termℤ "ℤ") " ≃+* " (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ulift.ring_equiv.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `ghost_component_apply)
         ","
         (Tactic.simpLemma [] [] `aeval_eq_eval₂_hom)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_eq_eval₂_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ghost_component_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.specialize
       "specialize"
       (Term.app
        `h
        [(Term.app `ULift [(termℤ "ℤ")])
         (Term.app
          (Term.app `mk [`p])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])]
              "⟩")))])
         (Term.app
          (Term.app `mk [`p])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])]
              "⟩")))])
         `k]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h
       [(Term.app `ULift [(termℤ "ℤ")])
        (Term.app
         (Term.app `mk [`p])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])]
             "⟩")))])
        (Term.app
         (Term.app `mk [`p])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])]
             "⟩")))])
        `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.app `mk [`p])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])]
           "⟩")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(num "1") "," [`i]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `mk [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `mk [`p]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.paren "(" (Term.app `mk [`p]) ")")
      [(Term.fun
        "fun"
        (Term.basicFun
         [`i]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `x [(Term.tuple "(" [(num "1") "," [`i]] ")")])]
          "⟩")))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.app `mk [`p])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])]
           "⟩")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(num "0") "," [`i]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `mk [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `mk [`p]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.paren "(" (Term.app `mk [`p]) ")")
      [(Term.fun
        "fun"
        (Term.basicFun
         [`i]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `x [(Term.tuple "(" [(num "0") "," [`i]] ")")])]
          "⟩")))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ULift [(termℤ "ℤ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ULift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ULift [(termℤ "ℤ")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `hom_bind₁)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hom_bind₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `MvPolynomial.funext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MvPolynomial.funext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`k])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.clear "clear" [`x `y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `hf)
         ","
         (Tactic.rwRule [] `hg)
         ","
         (Tactic.rwRule [] (Term.app `poly_eq_of_witt_polynomial_bind_eq' [`p `φ `ψ]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `poly_eq_of_witt_polynomial_bind_eq' [`p `φ `ψ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ψ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `poly_eq_of_witt_polynomial_bind_eq'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ψ)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hg)])
             [])]
           "⟩")])]
       []
       [":=" [`hg]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
             [])]
           "⟩")])]
       []
       [":=" [`hf]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`R] [] [] ")")
        (Term.instBinder "[" [`_Rcr ":"] (Term.app `CommRing [`R]) "]")
        (Term.explicitBinder
         "("
         [`x `y]
         [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
         []
         ")")]
       []
       ","
       («term_=_» (Term.app `f [`x `y]) "=" (Term.app `g [`x `y])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `f [`x `y]) "=" (Term.app `g [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.IsPoly.term𝕎', expected 'WittVector.RingTheory.WittVector.IsPoly.term𝕎._@.RingTheory.WittVector.IsPoly._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ext
  { f g }
      ( hf : IsPoly₂ p f )
      ( hg : IsPoly₂ p g )
      (
        h
        :
          ∀
            ( R : Type u ) [ _Rcr : CommRing R ] ( x y : 𝕎 R ) ( n : ℕ )
            ,
            ghost_component n f x y = ghost_component n g x y
        )
    : ∀ ( R ) [ _Rcr : CommRing R ] ( x y : 𝕎 R ) , f x y = g x y
  :=
    by
      obtain ⟨ φ , hf ⟩ := hf
        obtain ⟨ ψ , hg ⟩ := hg
        intros
        ext n
        rw [ hf , hg , poly_eq_of_witt_polynomial_bind_eq' p φ ψ ]
        clear x y
        intro k
        apply MvPolynomial.funext
        intro x
        simp only [ hom_bind₁ ]
        specialize h ULift ℤ mk p fun i => ⟨ x ( 0 , i ) ⟩ mk p fun i => ⟨ x ( 1 , i ) ⟩ k
        simp only [ ghost_component_apply , aeval_eq_eval₂_hom ] at h
        apply ( ulift.ring_equiv.symm : ℤ ≃+* _ ) . Injective
        simp only [ ← RingEquiv.coe_toRingHom , map_eval₂_hom ]
        convert h using 1
        all_goals
          funext i
            simp only [ hf , hg , MvPolynomial.eval , map_eval₂_hom ]
            apply eval₂_hom_congr RingHom.ext_int _ _ _ rfl
            ext1
            apply eval₂_hom_congr RingHom.ext_int _ _ _ rfl
            ext ⟨ b , _ ⟩
            fin_cases b <;> simp only [ coeff_mk , uncurry ] <;> rfl
#align witt_vector.is_poly₂.ext WittVector.IsPoly₂.ext

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f] [] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `IsPoly₂ [`p `f])] [] ")")
        (Term.explicitBinder "(" [`g] [":" (Algebra.Hom.Ring.«term_→+*_» `R " →+* " `S)] [] ")")
        (Term.explicitBinder
         "("
         [`x `y]
         [":" (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `map [`g (Term.app `f [`x `y])])
         "="
         (Term.app `f [(Term.app `map [`g `x]) (Term.app `map [`g `y])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                  [])]
                "⟩")])]
            []
            [":=" [`hf]])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `map_coeff)
              ","
              (Tactic.simpLemma [] [] `hf)
              ","
              (Tactic.simpLemma [] [] `map_aeval)
              ","
              (Tactic.simpLemma [] [] `peval)
              ","
              (Tactic.simpLemma [] [] `uncurry)]
             "]"]
            [])
           []
           (Tactic.apply
            "apply"
            (Term.app
             `eval₂_hom_congr
             [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
           []
           (Tactic.tacticTry_
            "try"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.«tacticExt___:_»
                "ext"
                [(Std.Tactic.RCases.rintroPat.one
                  (Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                     [])]
                   "⟩"))]
                [])
               ";"
               (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])])))
           []
           (Tactic.allGoals
            "all_goals"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `map_coeff)
                  ","
                  (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
                  ","
                  (Tactic.simpLemma [] [] `Matrix.head_cons)
                  ","
                  (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
                 "]"]
                [])])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
                 [])]
               "⟩")])]
           []
           [":=" [`hf]])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `map_coeff)
             ","
             (Tactic.simpLemma [] [] `hf)
             ","
             (Tactic.simpLemma [] [] `map_aeval)
             ","
             (Tactic.simpLemma [] [] `peval)
             ","
             (Tactic.simpLemma [] [] `uncurry)]
            "]"]
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `eval₂_hom_congr
            [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
          []
          (Tactic.tacticTry_
           "try"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Ext.«tacticExt___:_»
               "ext"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                    [])]
                  "⟩"))]
               [])
              ";"
              (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])])))
          []
          (Tactic.allGoals
           "all_goals"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `map_coeff)
                 ","
                 (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
                 ","
                 (Tactic.simpLemma [] [] `Matrix.head_cons)
                 ","
                 (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
                "]"]
               [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.allGoals
       "all_goals"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `map_coeff)
             ","
             (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
             ","
             (Tactic.simpLemma [] [] `Matrix.head_cons)
             ","
             (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `map_coeff)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
         ","
         (Tactic.simpLemma [] [] `Matrix.head_cons)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_one)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.head_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticTry_
       "try"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                [])]
              "⟩"))]
           [])
          ";"
          (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `eval₂_hom_congr
        [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eval₂_hom_congr
       [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.ext_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `map_coeff)
         ","
         (Tactic.simpLemma [] [] `hf)
         ","
         (Tactic.simpLemma [] [] `map_aeval)
         ","
         (Tactic.simpLemma [] [] `peval)
         ","
         (Tactic.simpLemma [] [] `uncurry)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `peval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_aeval
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `φ)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hf)])
             [])]
           "⟩")])]
       []
       [":=" [`hf]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `map [`g (Term.app `f [`x `y])])
       "="
       (Term.app `f [(Term.app `map [`g `x]) (Term.app `map [`g `y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app `map [`g `x]) (Term.app `map [`g `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map [`g `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `map [`g `y]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `map [`g `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `map [`g `x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `map [`g (Term.app `f [`x `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`x `y]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.IsPoly.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.IsPoly.term𝕎', expected 'WittVector.RingTheory.WittVector.IsPoly.term𝕎._@.RingTheory.WittVector.IsPoly._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  map
  { f } ( hf : IsPoly₂ p f ) ( g : R →+* S ) ( x y : 𝕎 R ) : map g f x y = f map g x map g y
  :=
    by
      obtain ⟨ φ , hf ⟩ := hf
        ext n
        simp only [ map_coeff , hf , map_aeval , peval , uncurry ]
        apply eval₂_hom_congr RingHom.ext_int _ _ _ rfl
        try ext ⟨ i , k ⟩ ; fin_cases i
        all_goals
          simp only [ map_coeff , Matrix.cons_val_zero , Matrix.head_cons , Matrix.cons_val_one ]
#align witt_vector.is_poly₂.map WittVector.IsPoly₂.map

end IsPoly₂

attribute [ghost_simps]
  AlgHom.map_zero AlgHom.map_one AlgHom.map_add AlgHom.map_mul AlgHom.map_sub AlgHom.map_neg AlgHom.id_apply map_nat_cast RingHom.map_zero RingHom.map_one RingHom.map_mul RingHom.map_add RingHom.map_sub RingHom.map_neg RingHom.id_apply mul_add add_mul add_zero zero_add mul_one one_mul mul_zero zero_mul Nat.succ_ne_zero add_tsub_cancel_right Nat.succ_eq_add_one if_true eq_self_iff_true if_false forall_true_iff forall₂_true_iff forall₃_true_iff

end WittVector

