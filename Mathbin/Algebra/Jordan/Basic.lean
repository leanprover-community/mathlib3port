/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module algebra.jordan.basic
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Lie.OfAssociative

/-!
# Jordan rings

Let `A` be a non-unital, non-associative ring. Then `A` is said to be a (commutative, linear) Jordan
ring if the multiplication is commutative and satisfies a weak associativity law known as the
Jordan Identity: for all `a` and `b` in `A`,
```
(a * b) * a^2 = a * (b * a^2)
```
i.e. the operators of multiplication by `a` and `a^2` commute.

A more general concept of a (non-commutative) Jordan ring can also be defined, as a
(non-commutative, non-associative) ring `A` where, for each `a` in `A`, the operators of left and
right multiplication by `a` and `a^2` commute.

Every associative algebra can be equipped with a symmetrized multiplication (characterized by
`sym_alg.sym_mul_sym`) making it into a commutative Jordan algebra (`sym_alg.is_comm_jordan`).
Jordan algebras arising this way are said to be special.

A real Jordan algebra `A` can be introduced by
```lean
variables {A : Type*} [non_unital_non_assoc_ring A] [module ℝ A] [smul_comm_class ℝ A A]
  [is_scalar_tower ℝ A A] [is_comm_jordan A]
```

## Main results

- `two_nsmul_lie_lmul_lmul_add_add_eq_zero` : Linearisation of the commutative Jordan axiom

## Implementation notes

We shall primarily be interested in linear Jordan algebras (i.e. over rings of characteristic not
two) leaving quadratic algebras to those better versed in that theory.

The conventional way to linearise the Jordan axiom is to equate coefficients (more formally, assume
that the axiom holds in all field extensions). For simplicity we use brute force algebraic expansion
and substitution instead.

## Motivation

Every Jordan algebra `A` has a triple product defined, for `a` `b` and `c` in `A` by
$$
{a\,b\,c} = (a * b) * c - (a * c) * b + a * (b * c).
$$
Via this triple product Jordan algebras are related to a number of other mathematical structures:
Jordan triples, partial Jordan triples, Jordan pairs and quadratic Jordan algebras. In addition to
their considerable algebraic interest ([mccrimmon2004]) these structures have been shown to have
deep connections to mathematical physics, functional analysis and differential geometry. For more
information about these connections the interested reader is referred to [alfsenshultz2003],
[chu2012], [friedmanscarr2005], [iordanescu2003] and [upmeier1987].

There are also exceptional Jordan algebras which can be shown not to be the symmetrization of any
associative algebra. The 3x3 matrices of octonions is the canonical example.

Non-commutative Jordan algebras have connections to the Vidav-Palmer theorem
[cabreragarciarodriguezpalacios2014].

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

-/


variable (A : Type _)

/-- A (non-commutative) Jordan multiplication. -/
class IsJordan [Mul A] where
  lmul_comm_rmul : ∀ a b : A, a * b * a = a * (b * a)
  lmul_lmul_comm_lmul : ∀ a b : A, a * a * (a * b) = a * (a * a * b)
  lmul_lmul_comm_rmul : ∀ a b : A, a * a * (b * a) = a * a * b * a
  lmul_comm_rmul_rmul : ∀ a b : A, a * b * (a * a) = a * (b * (a * a))
  rmul_comm_rmul_rmul : ∀ a b : A, b * a * (a * a) = b * (a * a) * a
#align is_jordan IsJordan

/-- A commutative Jordan multipication -/
class IsCommJordan [Mul A] where
  mul_comm : ∀ a b : A, a * b = b * a
  lmul_comm_rmul_rmul : ∀ a b : A, a * b * (a * a) = a * (b * (a * a))
#align is_comm_jordan IsCommJordan

-- see Note [lower instance priority]
/-- A (commutative) Jordan multiplication is also a Jordan multipication -/
instance (priority := 100) IsCommJordan.toIsJordan [Mul A] [IsCommJordan A] : IsJordan A
    where
  lmul_comm_rmul a b := by rw [IsCommJordan.mul_comm, IsCommJordan.mul_comm a b]
  lmul_lmul_comm_lmul a b := by
    rw [IsCommJordan.mul_comm (a * a) (a * b), IsCommJordan.lmul_comm_rmul_rmul,
      IsCommJordan.mul_comm b (a * a)]
  lmul_comm_rmul_rmul := IsCommJordan.lmul_comm_rmul_rmul
  lmul_lmul_comm_rmul a b := by
    rw [IsCommJordan.mul_comm (a * a) (b * a), IsCommJordan.mul_comm b a,
      IsCommJordan.lmul_comm_rmul_rmul, IsCommJordan.mul_comm, IsCommJordan.mul_comm b (a * a)]
  rmul_comm_rmul_rmul a b := by
    rw [IsCommJordan.mul_comm b a, IsCommJordan.lmul_comm_rmul_rmul, IsCommJordan.mul_comm]
#align is_comm_jordan.to_is_jordan IsCommJordan.toIsJordan

-- see Note [lower instance priority]
/-- Semigroup multiplication satisfies the (non-commutative) Jordan axioms-/
instance (priority := 100) Semigroup.isJordan [Semigroup A] : IsJordan A
    where
  lmul_comm_rmul a b := by rw [mul_assoc]
  lmul_lmul_comm_lmul a b := by rw [mul_assoc, mul_assoc]
  lmul_comm_rmul_rmul a b := by rw [mul_assoc]
  lmul_lmul_comm_rmul a b := by rw [← mul_assoc]
  rmul_comm_rmul_rmul a b := by rw [← mul_assoc, ← mul_assoc]
#align semigroup.is_jordan Semigroup.isJordan

-- see Note [lower instance priority]
instance (priority := 100) CommSemigroup.isCommJordan [CommSemigroup A] : IsCommJordan A
    where
  mul_comm := mul_comm
  lmul_comm_rmul_rmul a b := mul_assoc _ _ _
#align comm_semigroup.is_comm_jordan CommSemigroup.isCommJordan

-- mathport name: exprL
local notation "L" => AddMonoid.End.mulLeft

-- mathport name: exprR
local notation "R" => AddMonoid.End.mulRight

/-!
The Jordan axioms can be expressed in terms of commuting multiplication operators.
-/


section Commute

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `commute_lmul_rmul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Commute
         [(Term.app (Algebra.Jordan.Basic.termL "L") [`a])
          (Term.app (Algebra.Jordan.Basic.termR "R") [`a])])))
      (Command.declValSimple
       ":="
       (Term.app
        `AddMonoidHom.ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`b]
           []
           "=>"
           (Term.proj
            (Term.app `IsJordan.lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])
            "."
            `symm)))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `AddMonoidHom.ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`b]
          []
          "=>"
          (Term.proj
           (Term.app `IsJordan.lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])
           "."
           `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b]
        []
        "=>"
        (Term.proj
         (Term.app `IsJordan.lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])
         "."
         `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `IsJordan.lmul_comm_rmul [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsJordan.lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])
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
      `IsJordan.lmul_comm_rmul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsJordan.lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AddMonoidHom.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Commute
       [(Term.app (Algebra.Jordan.Basic.termL "L") [`a])
        (Term.app (Algebra.Jordan.Basic.termR "R") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Algebra.Jordan.Basic.termR "R") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Jordan.Basic.termR "R")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Jordan.Basic.termR', expected 'Algebra.Jordan.Basic.termR._@.Algebra.Jordan.Basic._hyg.328'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    commute_lmul_rmul
    ( a : A ) : Commute L a R a
    := AddMonoidHom.ext fun b => IsJordan.lmul_comm_rmul _ _ . symm
#align commute_lmul_rmul commute_lmul_rmul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `commute_lmul_lmul_sq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Commute
         [(Term.app (Algebra.Jordan.Basic.termL "L") [`a])
          (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])])))
      (Command.declValSimple
       ":="
       (Term.app
        `AddMonoidHom.ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`b]
           []
           "=>"
           (Term.proj
            (Term.app `IsJordan.lmul_lmul_comm_lmul [(Term.hole "_") (Term.hole "_")])
            "."
            `symm)))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `AddMonoidHom.ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`b]
          []
          "=>"
          (Term.proj
           (Term.app `IsJordan.lmul_lmul_comm_lmul [(Term.hole "_") (Term.hole "_")])
           "."
           `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b]
        []
        "=>"
        (Term.proj
         (Term.app `IsJordan.lmul_lmul_comm_lmul [(Term.hole "_") (Term.hole "_")])
         "."
         `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `IsJordan.lmul_lmul_comm_lmul [(Term.hole "_") (Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsJordan.lmul_lmul_comm_lmul [(Term.hole "_") (Term.hole "_")])
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
      `IsJordan.lmul_lmul_comm_lmul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsJordan.lmul_lmul_comm_lmul [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AddMonoidHom.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Commute
       [(Term.app (Algebra.Jordan.Basic.termL "L") [`a])
        (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `a "*" `a) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Jordan.Basic.termL "L")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Jordan.Basic.termL', expected 'Algebra.Jordan.Basic.termL._@.Algebra.Jordan.Basic._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    commute_lmul_lmul_sq
    ( a : A ) : Commute L a L a * a
    := AddMonoidHom.ext fun b => IsJordan.lmul_lmul_comm_lmul _ _ . symm
#align commute_lmul_lmul_sq commute_lmul_lmul_sq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `commute_lmul_rmul_sq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Commute
         [(Term.app (Algebra.Jordan.Basic.termL "L") [`a])
          (Term.app (Algebra.Jordan.Basic.termR "R") [(«term_*_» `a "*" `a)])])))
      (Command.declValSimple
       ":="
       (Term.app
        `AddMonoidHom.ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`b]
           []
           "=>"
           (Term.proj
            (Term.app `IsJordan.lmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
            "."
            `symm)))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `AddMonoidHom.ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`b]
          []
          "=>"
          (Term.proj
           (Term.app `IsJordan.lmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
           "."
           `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b]
        []
        "=>"
        (Term.proj
         (Term.app `IsJordan.lmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
         "."
         `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `IsJordan.lmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsJordan.lmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
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
      `IsJordan.lmul_comm_rmul_rmul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsJordan.lmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AddMonoidHom.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Commute
       [(Term.app (Algebra.Jordan.Basic.termL "L") [`a])
        (Term.app (Algebra.Jordan.Basic.termR "R") [(«term_*_» `a "*" `a)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Algebra.Jordan.Basic.termR "R") [(«term_*_» `a "*" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `a "*" `a) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Jordan.Basic.termR "R")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Jordan.Basic.termR', expected 'Algebra.Jordan.Basic.termR._@.Algebra.Jordan.Basic._hyg.328'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    commute_lmul_rmul_sq
    ( a : A ) : Commute L a R a * a
    := AddMonoidHom.ext fun b => IsJordan.lmul_comm_rmul_rmul _ _ . symm
#align commute_lmul_rmul_sq commute_lmul_rmul_sq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `commute_lmul_sq_rmul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Commute
         [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
          (Term.app (Algebra.Jordan.Basic.termR "R") [`a])])))
      (Command.declValSimple
       ":="
       (Term.app
        `AddMonoidHom.ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`b]
           []
           "=>"
           (Term.app `IsJordan.lmul_lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `AddMonoidHom.ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`b]
          []
          "=>"
          (Term.app `IsJordan.lmul_lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b]
        []
        "=>"
        (Term.app `IsJordan.lmul_lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsJordan.lmul_lmul_comm_rmul [(Term.hole "_") (Term.hole "_")])
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
      `IsJordan.lmul_lmul_comm_rmul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AddMonoidHom.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Commute
       [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
        (Term.app (Algebra.Jordan.Basic.termR "R") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Algebra.Jordan.Basic.termR "R") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Jordan.Basic.termR "R")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Jordan.Basic.termR', expected 'Algebra.Jordan.Basic.termR._@.Algebra.Jordan.Basic._hyg.328'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    commute_lmul_sq_rmul
    ( a : A ) : Commute L a * a R a
    := AddMonoidHom.ext fun b => IsJordan.lmul_lmul_comm_rmul _ _
#align commute_lmul_sq_rmul commute_lmul_sq_rmul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `commute_rmul_rmul_sq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Commute
         [(Term.app (Algebra.Jordan.Basic.termR "R") [`a])
          (Term.app (Algebra.Jordan.Basic.termR "R") [(«term_*_» `a "*" `a)])])))
      (Command.declValSimple
       ":="
       (Term.app
        `AddMonoidHom.ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`b]
           []
           "=>"
           (Term.proj
            (Term.app `IsJordan.rmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
            "."
            `symm)))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `AddMonoidHom.ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`b]
          []
          "=>"
          (Term.proj
           (Term.app `IsJordan.rmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
           "."
           `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b]
        []
        "=>"
        (Term.proj
         (Term.app `IsJordan.rmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
         "."
         `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `IsJordan.rmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsJordan.rmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
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
      `IsJordan.rmul_comm_rmul_rmul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsJordan.rmul_comm_rmul_rmul [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AddMonoidHom.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Commute
       [(Term.app (Algebra.Jordan.Basic.termR "R") [`a])
        (Term.app (Algebra.Jordan.Basic.termR "R") [(«term_*_» `a "*" `a)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Algebra.Jordan.Basic.termR "R") [(«term_*_» `a "*" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `a "*" `a) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Jordan.Basic.termR "R")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Jordan.Basic.termR', expected 'Algebra.Jordan.Basic.termR._@.Algebra.Jordan.Basic._hyg.328'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    commute_rmul_rmul_sq
    ( a : A ) : Commute R a R a * a
    := AddMonoidHom.ext fun b => IsJordan.rmul_comm_rmul_rmul _ _ . symm
#align commute_rmul_rmul_sq commute_rmul_rmul_sq

end Commute

variable {A} [NonUnitalNonAssocRing A] [IsCommJordan A]

/-!
The endomorphisms on an additive monoid `add_monoid.End` form a `ring`, and this may be equipped
with a Lie Bracket via `ring.has_bracket`.
-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_»
          (num "2")
          " • "
          («term_+_»
           (Data.Bracket.«term⁅_,_⁆»
            "⁅"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
            ", "
            (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
            "⁆")
           "+"
           (Data.Bracket.«term⁅_,_⁆»
            "⁅"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
            ", "
            (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
            "⁆")))
         "="
         («term_+_»
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
           ", "
           (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
           "⁆")
          "+"
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
           ", "
           (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
           "⁆")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             («term_=_»
              («term_+_»
               («term_+_»
                («term_+_»
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                   "⁆"))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
                   "⁆")))
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                 "⁆"))
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                "⁆"))
              "="
              (num "0"))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_sub)
                    ","
                    (Tactic.rwRule [] `sub_eq_add_neg)
                    ","
                    (Tactic.rwRule [] `sub_eq_add_neg)
                    ","
                    (Tactic.rwRule [] `lie_skew)
                    ","
                    (Tactic.rwRule [] `lie_skew)
                    ","
                    (Tactic.rwRule [] `nsmul_add)]
                   "]")
                  [])])))))
           []
           (convert
            "convert"
            []
            (Term.proj (Term.app `commute_lmul_lmul_sq [(«term_+_» `a "+" `b)]) "." `lie_eq)
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `add_mul)
              ","
              (Tactic.simpLemma [] [] `mul_add)
              ","
              (Tactic.simpLemma [] [] `map_add)
              ","
              (Tactic.simpLemma [] [] `lie_add)
              ","
              (Tactic.simpLemma [] [] `add_lie)
              ","
              (Tactic.simpLemma [] [] (Term.app `IsCommJordan.mul_comm [`b `a]))
              ","
              (Tactic.simpLemma [] [] (Term.proj (Term.app `commute_lmul_lmul_sq [`a]) "." `lie_eq))
              ","
              (Tactic.simpLemma
               []
               []
               (Term.proj (Term.app `commute_lmul_lmul_sq [`b]) "." `lie_eq))]
             "]"]
            [])
           []
           (Tactic.abel "abel" [] [])])))
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
         [(Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            («term_=_»
             («term_+_»
              («term_+_»
               («term_+_»
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                  "⁆"))
                "+"
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
                  "⁆")))
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                "⁆"))
              "+"
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
               ", "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
               "⁆"))
             "="
             (num "0"))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_sub)
                   ","
                   (Tactic.rwRule [] `sub_eq_add_neg)
                   ","
                   (Tactic.rwRule [] `sub_eq_add_neg)
                   ","
                   (Tactic.rwRule [] `lie_skew)
                   ","
                   (Tactic.rwRule [] `lie_skew)
                   ","
                   (Tactic.rwRule [] `nsmul_add)]
                  "]")
                 [])])))))
          []
          (convert
           "convert"
           []
           (Term.proj (Term.app `commute_lmul_lmul_sq [(«term_+_» `a "+" `b)]) "." `lie_eq)
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `add_mul)
             ","
             (Tactic.simpLemma [] [] `mul_add)
             ","
             (Tactic.simpLemma [] [] `map_add)
             ","
             (Tactic.simpLemma [] [] `lie_add)
             ","
             (Tactic.simpLemma [] [] `add_lie)
             ","
             (Tactic.simpLemma [] [] (Term.app `IsCommJordan.mul_comm [`b `a]))
             ","
             (Tactic.simpLemma [] [] (Term.proj (Term.app `commute_lmul_lmul_sq [`a]) "." `lie_eq))
             ","
             (Tactic.simpLemma [] [] (Term.proj (Term.app `commute_lmul_lmul_sq [`b]) "." `lie_eq))]
            "]"]
           [])
          []
          (Tactic.abel "abel" [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abel "abel" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `add_mul)
         ","
         (Tactic.simpLemma [] [] `mul_add)
         ","
         (Tactic.simpLemma [] [] `map_add)
         ","
         (Tactic.simpLemma [] [] `lie_add)
         ","
         (Tactic.simpLemma [] [] `add_lie)
         ","
         (Tactic.simpLemma [] [] (Term.app `IsCommJordan.mul_comm [`b `a]))
         ","
         (Tactic.simpLemma [] [] (Term.proj (Term.app `commute_lmul_lmul_sq [`a]) "." `lie_eq))
         ","
         (Tactic.simpLemma [] [] (Term.proj (Term.app `commute_lmul_lmul_sq [`b]) "." `lie_eq))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `commute_lmul_lmul_sq [`b]) "." `lie_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `commute_lmul_lmul_sq [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `commute_lmul_lmul_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `commute_lmul_lmul_sq [`b])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `commute_lmul_lmul_sq [`a]) "." `lie_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `commute_lmul_lmul_sq [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `commute_lmul_lmul_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `commute_lmul_lmul_sq [`a])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsCommJordan.mul_comm [`b `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCommJordan.mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_lie
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lie_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.proj (Term.app `commute_lmul_lmul_sq [(«term_+_» `a "+" `b)]) "." `lie_eq)
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `commute_lmul_lmul_sq [(«term_+_» `a "+" `b)]) "." `lie_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `commute_lmul_lmul_sq [(«term_+_» `a "+" `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `a "+" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `a "+" `b) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `commute_lmul_lmul_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `commute_lmul_lmul_sq [(Term.paren "(" («term_+_» `a "+" `b) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_=_»
         («term_+_»
          («term_+_»
           («term_+_»
            (Algebra.Group.Defs.«term_•_»
             (num "2")
             " • "
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
              ", "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
              "⁆"))
            "+"
            (Algebra.Group.Defs.«term_•_»
             (num "2")
             " • "
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
              ", "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
              "⁆")))
           "+"
           (Data.Bracket.«term⁅_,_⁆»
            "⁅"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
            ", "
            (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
            "⁆"))
          "+"
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
           ", "
           (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
           "⁆"))
         "="
         (num "0"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_sub)
               ","
               (Tactic.rwRule [] `sub_eq_add_neg)
               ","
               (Tactic.rwRule [] `sub_eq_add_neg)
               ","
               (Tactic.rwRule [] `lie_skew)
               ","
               (Tactic.rwRule [] `lie_skew)
               ","
               (Tactic.rwRule [] `nsmul_add)]
              "]")
             [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_sub)
         ","
         (Tactic.rwRule [] `sub_eq_add_neg)
         ","
         (Tactic.rwRule [] `sub_eq_add_neg)
         ","
         (Tactic.rwRule [] `lie_skew)
         ","
         (Tactic.rwRule [] `lie_skew)
         ","
         (Tactic.rwRule [] `nsmul_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nsmul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lie_skew
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lie_skew
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_add_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_add_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_+_»
        («term_+_»
         («term_+_»
          (Algebra.Group.Defs.«term_•_»
           (num "2")
           " • "
           (Data.Bracket.«term⁅_,_⁆»
            "⁅"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
            ", "
            (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
            "⁆"))
          "+"
          (Algebra.Group.Defs.«term_•_»
           (num "2")
           " • "
           (Data.Bracket.«term⁅_,_⁆»
            "⁅"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
            ", "
            (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
            "⁆")))
         "+"
         (Data.Bracket.«term⁅_,_⁆»
          "⁅"
          (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
          ", "
          (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
          "⁆"))
        "+"
        (Data.Bracket.«term⁅_,_⁆»
         "⁅"
         (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
         ", "
         (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
         "⁆"))
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       («term_+_»
        («term_+_»
         (Algebra.Group.Defs.«term_•_»
          (num "2")
          " • "
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
           ", "
           (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
           "⁆"))
         "+"
         (Algebra.Group.Defs.«term_•_»
          (num "2")
          " • "
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
           ", "
           (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
           "⁆")))
        "+"
        (Data.Bracket.«term⁅_,_⁆»
         "⁅"
         (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
         ", "
         (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
         "⁆"))
       "+"
       (Data.Bracket.«term⁅_,_⁆»
        "⁅"
        (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
        ", "
        (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
        "⁆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Bracket.«term⁅_,_⁆»
       "⁅"
       (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
       ", "
       (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
       "⁆")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `b "*" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `b "*" `b) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Jordan.Basic.termL "L")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Jordan.Basic.termL', expected 'Algebra.Jordan.Basic.termL._@.Algebra.Jordan.Basic._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add
  ( a b : A ) : 2 • ⁅ L a , L a * b ⁆ + ⁅ L b , L b * a ⁆ = ⁅ L a * a , L b ⁆ + ⁅ L b * b , L a ⁆
  :=
    by
      suffices
          2 • ⁅ L a , L a * b ⁆ + 2 • ⁅ L b , L b * a ⁆ + ⁅ L b , L a * a ⁆ + ⁅ L a , L b * b ⁆ = 0
            by
              rwa
                [
                  ← sub_eq_zero
                    ,
                    ← sub_sub
                    ,
                    sub_eq_add_neg
                    ,
                    sub_eq_add_neg
                    ,
                    lie_skew
                    ,
                    lie_skew
                    ,
                    nsmul_add
                  ]
        convert commute_lmul_lmul_sq a + b . lie_eq
        simp
          only
          [
            add_mul
              ,
              mul_add
              ,
              map_add
              ,
              lie_add
              ,
              add_lie
              ,
              IsCommJordan.mul_comm b a
              ,
              commute_lmul_lmul_sq a . lie_eq
              ,
              commute_lmul_lmul_sq b . lie_eq
            ]
        abel
#align
  two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `two_nsmul_lie_lmul_lmul_add_add_eq_zero [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b `c] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_»
          (num "2")
          " • "
          («term_+_»
           («term_+_»
            (Data.Bracket.«term⁅_,_⁆»
             "⁅"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
             ", "
             (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
             "⁆")
            "+"
            (Data.Bracket.«term⁅_,_⁆»
             "⁅"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
             ", "
             (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
             "⁆"))
           "+"
           (Data.Bracket.«term⁅_,_⁆»
            "⁅"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
            ", "
            (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
            "⁆")))
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSymm_ "symm" [])
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              (num "0")
              "="
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app
                (Algebra.Jordan.Basic.termL "L")
                [(«term_+_» («term_+_» `a "+" `b) "+" `c)])
               ", "
               (Term.app
                (Algebra.Jordan.Basic.termL "L")
                [(«term_*_»
                  («term_+_» («term_+_» `a "+" `b) "+" `c)
                  "*"
                  («term_+_» («term_+_» `a "+" `b) "+" `c))])
               "⁆"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.proj
                      (Term.app `commute_lmul_lmul_sq [(«term_+_» («term_+_» `a "+" `b) "+" `c)])
                      "."
                      `lie_eq))]
                   "]")
                  [])]))))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                («term_+_»
                 («term_+_»
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
                 "+"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
                ", "
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                    "+"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `c)]))
                  "+"
                  («term_+_»
                   («term_+_»
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
                    "+"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
                 "+"
                 («term_+_»
                  («term_+_»
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `b)]))
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])))
                "⁆"))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `add_mul)
                     ","
                     (Tactic.rwRule [] `add_mul)
                     ","
                     (Tactic.rwRule [] `mul_add)
                     ","
                     (Tactic.rwRule [] `mul_add)
                     ","
                     (Tactic.rwRule [] `mul_add)
                     ","
                     (Tactic.rwRule [] `mul_add)
                     ","
                     (Tactic.rwRule [] `mul_add)
                     ","
                     (Tactic.rwRule [] `mul_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)
                     ","
                     (Tactic.rwRule [] `map_add)]
                    "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                («term_+_»
                 («term_+_»
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
                 "+"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
                ", "
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                    "+"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                  "+"
                  («term_+_»
                   («term_+_»
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                    "+"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
                 "+"
                 («term_+_»
                  («term_+_»
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])))
                "⁆"))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`b `a]))
                     ","
                     (Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `a]))
                     ","
                     (Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `b]))]
                    "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                («term_+_»
                 («term_+_»
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
                 "+"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
                ", "
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                     "+"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
                    "+"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)]))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
                "⁆"))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `two_smul)
                     ","
                     (Tactic.rwRule [] `two_smul)
                     ","
                     (Tactic.rwRule [] `two_smul)]
                    "]")
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `lie_add)
                     ","
                     (Tactic.simpLemma [] [] `add_lie)
                     ","
                     (Tactic.simpLemma [] [] `commute_lmul_lmul_sq)
                     ","
                     (Tactic.simpLemma [] [] `zero_add)
                     ","
                     (Tactic.simpLemma [] [] `add_zero)]
                    "]"]
                   [])
                  []
                  (Tactic.abel "abel" [] [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     («term_+_»
                      (Data.Bracket.«term⁅_,_⁆»
                       "⁅"
                       (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                       ", "
                       (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                       "⁆")
                      "+"
                      (Data.Bracket.«term⁅_,_⁆»
                       "⁅"
                       (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                       ", "
                       (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                       "⁆"))
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                      "⁆"))
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Algebra.Group.Defs.«term_•_»
                      (num "2")
                      " • "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                   "⁆"))
                 "+"
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     («term_+_»
                      (Data.Bracket.«term⁅_,_⁆»
                       "⁅"
                       (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                       ", "
                       (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                       "⁆")
                      "+"
                      (Data.Bracket.«term⁅_,_⁆»
                       "⁅"
                       (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                       ", "
                       (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                       "⁆"))
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                      "⁆"))
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Algebra.Group.Defs.«term_•_»
                      (num "2")
                      " • "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                   "⁆")))
                "+"
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                      "⁆"))
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                  "⁆"))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `add_lie)
                     ","
                     (Tactic.rwRule [] `add_lie)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)
                     ","
                     (Tactic.rwRule [] `lie_add)]
                    "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                      "⁆"))
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Algebra.Group.Defs.«term_•_»
                      (num "2")
                      " • "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                   "⁆"))
                 "+"
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                      "⁆"))
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Algebra.Group.Defs.«term_•_»
                      (num "2")
                      " • "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                   "⁆")))
                "+"
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                  "⁆"))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      []
                      (Term.proj (Term.app `commute_lmul_lmul_sq [`a]) "." `lie_eq))
                     ","
                     (Tactic.rwRule
                      []
                      (Term.proj (Term.app `commute_lmul_lmul_sq [`b]) "." `lie_eq))
                     ","
                     (Tactic.rwRule
                      []
                      (Term.proj (Term.app `commute_lmul_lmul_sq [`c]) "." `lie_eq))
                     ","
                     (Tactic.rwRule [] `zero_add)
                     ","
                     (Tactic.rwRule [] `add_zero)
                     ","
                     (Tactic.rwRule [] `add_zero)]
                    "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                      "⁆"))
                    "+"
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                      "⁆")))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                     "⁆")))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                    "⁆")))
                 "+"
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                      "⁆"))
                    "+"
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                      "⁆")))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                     "⁆")))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                    "⁆"))))
                "+"
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                     "⁆"))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                     "⁆")))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                    "⁆")))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                   "⁆")))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `lie_nsmul)] "]"]
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                     "⁆"))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                      "⁆"))))
                  "+"
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                     "⁆"))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                      "⁆")))))
                 "+"
                 («term_+_»
                  («term_+_»
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                    "⁆")
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                    "⁆"))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                     "⁆")))))
                "+"
                («term_+_»
                 («term_+_»
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                    "⁆"))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                    "⁆")))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                   "⁆")))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.abel "abel" [] [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                («term_+_»
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                   "⁆"))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                   "⁆")))
                "+"
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                  "⁆"))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_left_eq_self)] "]")
                   [])
                  []
                  (Mathlib.Tactic.nthRwSeq
                   "nth_rw"
                   []
                   (num "2")
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`a `b]))]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.nthRwSeq
                   "nth_rw"
                   []
                   (num "1")
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `a]))]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.nthRwSeq
                   "nth_rw"
                   []
                   (num "2")
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`b `c]))]
                    "]")
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                     ","
                     (Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                     ","
                     (Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `lie_skew
                       [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `lie_skew
                       [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `lie_skew
                       [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `lie_skew
                       [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `lie_skew
                       [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `lie_skew
                       [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])]))]
                    "]")
                   [])
                  []
                  (Tactic.abel "abel" [] [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                («term_+_»
                 («term_+_»
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                   "⁆")
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                  "⁆"))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `nsmul_add) "," (Tactic.rwRule [] `nsmul_add)]
                    "]")
                   [])]))))])])))
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
         [(Mathlib.Tactic.tacticSymm_ "symm" [])
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             (num "0")
             "="
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_+_» («term_+_» `a "+" `b) "+" `c)])
              ", "
              (Term.app
               (Algebra.Jordan.Basic.termL "L")
               [(«term_*_»
                 («term_+_» («term_+_» `a "+" `b) "+" `c)
                 "*"
                 («term_+_» («term_+_» `a "+" `b) "+" `c))])
              "⁆"))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    []
                    (Term.proj
                     (Term.app `commute_lmul_lmul_sq [(«term_+_» («term_+_» `a "+" `b) "+" `c)])
                     "."
                     `lie_eq))]
                  "]")
                 [])]))))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               («term_+_»
                («term_+_»
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 "+"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
                "+"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
               ", "
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `c)]))
                 "+"
                 («term_+_»
                  («term_+_»
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
                "+"
                («term_+_»
                 («term_+_»
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `b)]))
                 "+"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])))
               "⁆"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `add_mul)
                    ","
                    (Tactic.rwRule [] `add_mul)
                    ","
                    (Tactic.rwRule [] `mul_add)
                    ","
                    (Tactic.rwRule [] `mul_add)
                    ","
                    (Tactic.rwRule [] `mul_add)
                    ","
                    (Tactic.rwRule [] `mul_add)
                    ","
                    (Tactic.rwRule [] `mul_add)
                    ","
                    (Tactic.rwRule [] `mul_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)
                    ","
                    (Tactic.rwRule [] `map_add)]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               («term_+_»
                («term_+_»
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 "+"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
                "+"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
               ", "
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                 "+"
                 («term_+_»
                  («term_+_»
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
                "+"
                («term_+_»
                 («term_+_»
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                  "+"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                 "+"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])))
               "⁆"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`b `a]))
                    ","
                    (Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `a]))
                    ","
                    (Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `b]))]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               («term_+_»
                («term_+_»
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 "+"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
                "+"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
               ", "
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                    "+"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
                   "+"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)]))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])))
                "+"
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
               "⁆"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `two_smul)
                    ","
                    (Tactic.rwRule [] `two_smul)
                    ","
                    (Tactic.rwRule [] `two_smul)]
                   "]")
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `lie_add)
                    ","
                    (Tactic.simpLemma [] [] `add_lie)
                    ","
                    (Tactic.simpLemma [] [] `commute_lmul_lmul_sq)
                    ","
                    (Tactic.simpLemma [] [] `zero_add)
                    ","
                    (Tactic.simpLemma [] [] `add_zero)]
                   "]"]
                  [])
                 []
                 (Tactic.abel "abel" [] [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                      "⁆"))
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                  "⁆"))
                "+"
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                      "⁆")
                     "+"
                     (Data.Bracket.«term⁅_,_⁆»
                      "⁅"
                      (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                      ", "
                      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                      "⁆"))
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                  "⁆")))
               "+"
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                  "⁆"))
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                 "⁆"))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `add_lie)
                    ","
                    (Tactic.rwRule [] `add_lie)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)
                    ","
                    (Tactic.rwRule [] `lie_add)]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                  "⁆"))
                "+"
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                     "⁆"))
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Algebra.Group.Defs.«term_•_»
                     (num "2")
                     " • "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                  "⁆")))
               "+"
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                    "⁆")
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                    "⁆"))
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                   ", "
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                   "⁆"))
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
                  "⁆"))
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
                 "⁆"))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.proj (Term.app `commute_lmul_lmul_sq [`a]) "." `lie_eq))
                    ","
                    (Tactic.rwRule [] (Term.proj (Term.app `commute_lmul_lmul_sq [`b]) "." `lie_eq))
                    ","
                    (Tactic.rwRule [] (Term.proj (Term.app `commute_lmul_lmul_sq [`c]) "." `lie_eq))
                    ","
                    (Tactic.rwRule [] `zero_add)
                    ","
                    (Tactic.rwRule [] `add_zero)
                    ","
                    (Tactic.rwRule [] `add_zero)]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                     "⁆"))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                     "⁆")))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                    "⁆")))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                   "⁆")))
                "+"
                («term_+_»
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                     "⁆"))
                   "+"
                   (Algebra.Group.Defs.«term_•_»
                    (num "2")
                    " • "
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                     "⁆")))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                    "⁆")))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                   "⁆"))))
               "+"
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                    "⁆")
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                    "⁆"))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                    "⁆")))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                   "⁆")))
                "+"
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                  "⁆")))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `lie_nsmul)] "]"]
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               («term_+_»
                («term_+_»
                 («term_+_»
                  («term_+_»
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                    "⁆")
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                    "⁆"))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                     "⁆"))))
                 "+"
                 («term_+_»
                  («term_+_»
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                    "⁆")
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                    "⁆"))
                  "+"
                  (Algebra.Group.Defs.«term_•_»
                   (num "2")
                   " • "
                   («term_+_»
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                     "⁆")
                    "+"
                    (Data.Bracket.«term⁅_,_⁆»
                     "⁅"
                     (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                     ", "
                     (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                     "⁆")))))
                "+"
                («term_+_»
                 («term_+_»
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                   "⁆")
                  "+"
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                   "⁆"))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  («term_+_»
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                    "⁆")
                   "+"
                   (Data.Bracket.«term⁅_,_⁆»
                    "⁅"
                    (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                    ", "
                    (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                    "⁆")))))
               "+"
               («term_+_»
                («term_+_»
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                   "⁆"))
                 "+"
                 (Algebra.Group.Defs.«term_•_»
                  (num "2")
                  " • "
                  (Data.Bracket.«term⁅_,_⁆»
                   "⁅"
                   (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                   ", "
                   (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                   "⁆")))
                "+"
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                  "⁆")))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.abel "abel" [] [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               («term_+_»
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                  "⁆"))
                "+"
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                  "⁆")))
               "+"
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                 "⁆"))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_left_eq_self)] "]")
                  [])
                 []
                 (Mathlib.Tactic.nthRwSeq
                  "nth_rw"
                  []
                  (num "2")
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`a `b]))]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.nthRwSeq
                  "nth_rw"
                  []
                  (num "1")
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `a]))]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.nthRwSeq
                  "nth_rw"
                  []
                  (num "2")
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`b `c]))]
                   "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                    ","
                    (Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                    ","
                    (Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `lie_skew
                      [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `lie_skew
                      [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `lie_skew
                      [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `lie_skew
                      [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `lie_skew
                      [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `lie_skew
                      [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])]))]
                   "]")
                  [])
                 []
                 (Tactic.abel "abel" [] [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               («term_+_»
                («term_+_»
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                  "⁆")
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                  "⁆"))
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                 "⁆"))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `nsmul_add) "," (Tactic.rwRule [] `nsmul_add)]
                   "]")
                  [])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (num "0")
         "="
         (Data.Bracket.«term⁅_,_⁆»
          "⁅"
          (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_+_» («term_+_» `a "+" `b) "+" `c)])
          ", "
          (Term.app
           (Algebra.Jordan.Basic.termL "L")
           [(«term_*_»
             («term_+_» («term_+_» `a "+" `b) "+" `c)
             "*"
             («term_+_» («term_+_» `a "+" `b) "+" `c))])
          "⁆"))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.proj
                 (Term.app `commute_lmul_lmul_sq [(«term_+_» («term_+_» `a "+" `b) "+" `c)])
                 "."
                 `lie_eq))]
              "]")
             [])]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           («term_+_»
            («term_+_»
             (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
             "+"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
            "+"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
           ", "
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
               "+"
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
              "+"
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `c)]))
             "+"
             («term_+_»
              («term_+_»
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `a)])
               "+"
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
              "+"
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
            "+"
            («term_+_»
             («term_+_»
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
              "+"
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `b)]))
             "+"
             (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])))
           "⁆"))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `add_mul)
                ","
                (Tactic.rwRule [] `add_mul)
                ","
                (Tactic.rwRule [] `mul_add)
                ","
                (Tactic.rwRule [] `mul_add)
                ","
                (Tactic.rwRule [] `mul_add)
                ","
                (Tactic.rwRule [] `mul_add)
                ","
                (Tactic.rwRule [] `mul_add)
                ","
                (Tactic.rwRule [] `mul_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           («term_+_»
            («term_+_»
             (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
             "+"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
            "+"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
           ", "
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
               "+"
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
              "+"
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
             "+"
             («term_+_»
              («term_+_»
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
               "+"
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
              "+"
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
            "+"
            («term_+_»
             («term_+_»
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
              "+"
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
             "+"
             (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])))
           "⁆"))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`b `a]))
                ","
                (Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `a]))
                ","
                (Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `b]))]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           («term_+_»
            («term_+_»
             (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
             "+"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`b]))
            "+"
            (Term.app (Algebra.Jordan.Basic.termL "L") [`c]))
           ", "
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               («term_+_»
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                "+"
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)]))
               "+"
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)]))
              "+"
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])))
             "+"
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])))
            "+"
            (Algebra.Group.Defs.«term_•_»
             (num "2")
             " • "
             (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])))
           "⁆"))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `two_smul)
                ","
                (Tactic.rwRule [] `two_smul)
                ","
                (Tactic.rwRule [] `two_smul)]
               "]")
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `lie_add)
                ","
                (Tactic.simpLemma [] [] `add_lie)
                ","
                (Tactic.simpLemma [] [] `commute_lmul_lmul_sq)
                ","
                (Tactic.simpLemma [] [] `zero_add)
                ","
                (Tactic.simpLemma [] [] `add_zero)]
               "]"]
              [])
             []
             (Tactic.abel "abel" [] [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               («term_+_»
                («term_+_»
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                  "⁆")
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                  "⁆"))
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                 "⁆"))
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                ", "
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                "⁆"))
              "+"
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
               ", "
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
               "⁆"))
             "+"
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
              ", "
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
              "⁆"))
            "+"
            («term_+_»
             («term_+_»
              («term_+_»
               («term_+_»
                («term_+_»
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                  "⁆")
                 "+"
                 (Data.Bracket.«term⁅_,_⁆»
                  "⁅"
                  (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                  ", "
                  (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                  "⁆"))
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                 "⁆"))
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                ", "
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                "⁆"))
              "+"
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
               ", "
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
               "⁆"))
             "+"
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
              ", "
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
              "⁆")))
           "+"
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               («term_+_»
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                 "⁆")
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                 "⁆"))
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                "⁆"))
              "+"
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
               ", "
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
               "⁆"))
             "+"
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
              ", "
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
              "⁆"))
            "+"
            (Data.Bracket.«term⁅_,_⁆»
             "⁅"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
             ", "
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
             "⁆"))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `add_lie)
                ","
                (Tactic.rwRule [] `add_lie)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)
                ","
                (Tactic.rwRule [] `lie_add)]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               («term_+_»
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                 "⁆")
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                 "⁆"))
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                ", "
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                "⁆"))
              "+"
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
               ", "
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
               "⁆"))
             "+"
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
              ", "
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
              "⁆"))
            "+"
            («term_+_»
             («term_+_»
              («term_+_»
               («term_+_»
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                 "⁆")
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                 "⁆"))
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                ", "
                (Algebra.Group.Defs.«term_•_»
                 (num "2")
                 " • "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
                "⁆"))
              "+"
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
               ", "
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
               "⁆"))
             "+"
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
              ", "
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
              "⁆")))
           "+"
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                "⁆")
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                "⁆"))
              "+"
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
               ", "
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)]))
               "⁆"))
             "+"
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
              ", "
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)]))
              "⁆"))
            "+"
            (Data.Bracket.«term⁅_,_⁆»
             "⁅"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
             ", "
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)]))
             "⁆"))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.proj (Term.app `commute_lmul_lmul_sq [`a]) "." `lie_eq))
                ","
                (Tactic.rwRule [] (Term.proj (Term.app `commute_lmul_lmul_sq [`b]) "." `lie_eq))
                ","
                (Tactic.rwRule [] (Term.proj (Term.app `commute_lmul_lmul_sq [`c]) "." `lie_eq))
                ","
                (Tactic.rwRule [] `zero_add)
                ","
                (Tactic.rwRule [] `add_zero)
                ","
                (Tactic.rwRule [] `add_zero)]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               («term_+_»
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                 "⁆")
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                 "⁆"))
               "+"
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                 "⁆")))
              "+"
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                "⁆")))
             "+"
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
               ", "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
               "⁆")))
            "+"
            («term_+_»
             («term_+_»
              («term_+_»
               («term_+_»
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                 "⁆")
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                 "⁆"))
               "+"
               (Algebra.Group.Defs.«term_•_»
                (num "2")
                " • "
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                 "⁆")))
              "+"
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                "⁆")))
             "+"
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
               ", "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
               "⁆"))))
           "+"
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                "⁆")
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                "⁆"))
              "+"
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                "⁆")))
             "+"
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
               ", "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
               "⁆")))
            "+"
            (Algebra.Group.Defs.«term_•_»
             (num "2")
             " • "
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
              ", "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
              "⁆")))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `lie_nsmul)] "]"]
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           («term_+_»
            («term_+_»
             («term_+_»
              («term_+_»
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
                "⁆")
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                "⁆"))
              "+"
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               («term_+_»
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                 "⁆")
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
                 "⁆"))))
             "+"
             («term_+_»
              («term_+_»
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
                "⁆")
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])
                "⁆"))
              "+"
              (Algebra.Group.Defs.«term_•_»
               (num "2")
               " • "
               («term_+_»
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                 "⁆")
                "+"
                (Data.Bracket.«term⁅_,_⁆»
                 "⁅"
                 (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                 ", "
                 (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
                 "⁆")))))
            "+"
            («term_+_»
             («term_+_»
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
               ", "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])
               "⁆")
              "+"
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
               ", "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])
               "⁆"))
             "+"
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              («term_+_»
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                "⁆")
               "+"
               (Data.Bracket.«term⁅_,_⁆»
                "⁅"
                (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
                ", "
                (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
                "⁆")))))
           "+"
           («term_+_»
            («term_+_»
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
               ", "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
               "⁆"))
             "+"
             (Algebra.Group.Defs.«term_•_»
              (num "2")
              " • "
              (Data.Bracket.«term⁅_,_⁆»
               "⁅"
               (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
               ", "
               (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
               "⁆")))
            "+"
            (Algebra.Group.Defs.«term_•_»
             (num "2")
             " • "
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
              ", "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
              "⁆")))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.abel "abel" [] [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           («term_+_»
            (Algebra.Group.Defs.«term_•_»
             (num "2")
             " • "
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
              ", "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
              "⁆"))
            "+"
            (Algebra.Group.Defs.«term_•_»
             (num "2")
             " • "
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
              ", "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
              "⁆")))
           "+"
           (Algebra.Group.Defs.«term_•_»
            (num "2")
            " • "
            (Data.Bracket.«term⁅_,_⁆»
             "⁅"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
             ", "
             (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
             "⁆"))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_left_eq_self)] "]")
              [])
             []
             (Mathlib.Tactic.nthRwSeq
              "nth_rw"
              []
              (num "2")
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`a `b]))]
               "]")
              [])
             []
             (Mathlib.Tactic.nthRwSeq
              "nth_rw"
              []
              (num "1")
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`c `a]))]
               "]")
              [])
             []
             (Mathlib.Tactic.nthRwSeq
              "nth_rw"
              []
              (num "2")
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `IsCommJordan.mul_comm [`b `c]))]
               "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                ","
                (Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                ","
                (Tactic.rwRule [] `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add)
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `lie_skew
                  [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])]))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `lie_skew
                  [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])]))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `lie_skew
                  [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])]))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `lie_skew
                  [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `a)])]))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `lie_skew
                  [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `b)])]))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `lie_skew
                  [(Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `c)])]))]
               "]")
              [])
             []
             (Tactic.abel "abel" [] [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Algebra.Group.Defs.«term_•_»
           (num "2")
           " • "
           («term_+_»
            («term_+_»
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
              ", "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
              "⁆")
             "+"
             (Data.Bracket.«term⁅_,_⁆»
              "⁅"
              (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
              ", "
              (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
              "⁆"))
            "+"
            (Data.Bracket.«term⁅_,_⁆»
             "⁅"
             (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
             ", "
             (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
             "⁆"))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `nsmul_add) "," (Tactic.rwRule [] `nsmul_add)]
               "]")
              [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `nsmul_add) "," (Tactic.rwRule [] `nsmul_add)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `nsmul_add) "," (Tactic.rwRule [] `nsmul_add)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nsmul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nsmul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Algebra.Group.Defs.«term_•_»
        (num "2")
        " • "
        («term_+_»
         («term_+_»
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
           ", "
           (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
           "⁆")
          "+"
          (Data.Bracket.«term⁅_,_⁆»
           "⁅"
           (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
           ", "
           (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
           "⁆"))
         "+"
         (Data.Bracket.«term⁅_,_⁆»
          "⁅"
          (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
          ", "
          (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
          "⁆"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (num "2")
       " • "
       («term_+_»
        («term_+_»
         (Data.Bracket.«term⁅_,_⁆»
          "⁅"
          (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
          ", "
          (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
          "⁆")
         "+"
         (Data.Bracket.«term⁅_,_⁆»
          "⁅"
          (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
          ", "
          (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
          "⁆"))
        "+"
        (Data.Bracket.«term⁅_,_⁆»
         "⁅"
         (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
         ", "
         (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
         "⁆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_+_»
        (Data.Bracket.«term⁅_,_⁆»
         "⁅"
         (Term.app (Algebra.Jordan.Basic.termL "L") [`a])
         ", "
         (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `b "*" `c)])
         "⁆")
        "+"
        (Data.Bracket.«term⁅_,_⁆»
         "⁅"
         (Term.app (Algebra.Jordan.Basic.termL "L") [`b])
         ", "
         (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `c "*" `a)])
         "⁆"))
       "+"
       (Data.Bracket.«term⁅_,_⁆»
        "⁅"
        (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
        ", "
        (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
        "⁆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Bracket.«term⁅_,_⁆»
       "⁅"
       (Term.app (Algebra.Jordan.Basic.termL "L") [`c])
       ", "
       (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
       "⁆")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Algebra.Jordan.Basic.termL "L") [(«term_*_» `a "*" `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `a "*" `b) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Jordan.Basic.termL "L")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Jordan.Basic.termL', expected 'Algebra.Jordan.Basic.termL._@.Algebra.Jordan.Basic._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  two_nsmul_lie_lmul_lmul_add_add_eq_zero
  ( a b c : A ) : 2 • ⁅ L a , L b * c ⁆ + ⁅ L b , L c * a ⁆ + ⁅ L c , L a * b ⁆ = 0
  :=
    by
      symm
        calc
          0 = ⁅ L a + b + c , L a + b + c * a + b + c ⁆
            :=
            by rw [ commute_lmul_lmul_sq a + b + c . lie_eq ]
          _
                =
                ⁅
                  L a + L b + L c
                  ,
                  L a * a + L a * b + L a * c + L b * a + L b * b + L b * c
                    +
                    L c * a + L c * b + L c * c
                  ⁆
              :=
              by
                rw
                  [
                    add_mul
                      ,
                      add_mul
                      ,
                      mul_add
                      ,
                      mul_add
                      ,
                      mul_add
                      ,
                      mul_add
                      ,
                      mul_add
                      ,
                      mul_add
                      ,
                      map_add
                      ,
                      map_add
                      ,
                      map_add
                      ,
                      map_add
                      ,
                      map_add
                      ,
                      map_add
                      ,
                      map_add
                      ,
                      map_add
                      ,
                      map_add
                      ,
                      map_add
                    ]
            _
                =
                ⁅
                  L a + L b + L c
                  ,
                  L a * a + L a * b + L c * a + L a * b + L b * b + L b * c
                    +
                    L c * a + L b * c + L c * c
                  ⁆
              :=
              by
                rw
                  [
                    IsCommJordan.mul_comm b a
                      ,
                      IsCommJordan.mul_comm c a
                      ,
                      IsCommJordan.mul_comm c b
                    ]
            _
                =
                ⁅
                  L a + L b + L c
                  ,
                  L a * a + L b * b + L c * c + 2 • L a * b + 2 • L c * a + 2 • L b * c
                  ⁆
              :=
              by
                rw [ two_smul , two_smul , two_smul ]
                  simp only [ lie_add , add_lie , commute_lmul_lmul_sq , zero_add , add_zero ]
                  abel
            _
                =
                ⁅ L a , L a * a ⁆ + ⁅ L a , L b * b ⁆ + ⁅ L a , L c * c ⁆ + ⁅ L a , 2 • L a * b ⁆
                        +
                        ⁅ L a , 2 • L c * a ⁆
                      +
                      ⁅ L a , 2 • L b * c ⁆
                    +
                    ⁅ L b , L a * a ⁆ + ⁅ L b , L b * b ⁆ + ⁅ L b , L c * c ⁆
                          +
                          ⁅ L b , 2 • L a * b ⁆
                        +
                        ⁅ L b , 2 • L c * a ⁆
                      +
                      ⁅ L b , 2 • L b * c ⁆
                  +
                  ⁅ L c , L a * a ⁆ + ⁅ L c , L b * b ⁆ + ⁅ L c , L c * c ⁆ + ⁅ L c , 2 • L a * b ⁆
                      +
                      ⁅ L c , 2 • L c * a ⁆
                    +
                    ⁅ L c , 2 • L b * c ⁆
              :=
              by
                rw
                  [
                    add_lie
                      ,
                      add_lie
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                      ,
                      lie_add
                    ]
            _
                =
                ⁅ L a , L b * b ⁆ + ⁅ L a , L c * c ⁆ + ⁅ L a , 2 • L a * b ⁆
                        +
                        ⁅ L a , 2 • L c * a ⁆
                      +
                      ⁅ L a , 2 • L b * c ⁆
                    +
                    ⁅ L b , L a * a ⁆ + ⁅ L b , L c * c ⁆ + ⁅ L b , 2 • L a * b ⁆
                        +
                        ⁅ L b , 2 • L c * a ⁆
                      +
                      ⁅ L b , 2 • L b * c ⁆
                  +
                  ⁅ L c , L a * a ⁆ + ⁅ L c , L b * b ⁆ + ⁅ L c , 2 • L a * b ⁆
                      +
                      ⁅ L c , 2 • L c * a ⁆
                    +
                    ⁅ L c , 2 • L b * c ⁆
              :=
              by
                rw
                  [
                    commute_lmul_lmul_sq a . lie_eq
                      ,
                      commute_lmul_lmul_sq b . lie_eq
                      ,
                      commute_lmul_lmul_sq c . lie_eq
                      ,
                      zero_add
                      ,
                      add_zero
                      ,
                      add_zero
                    ]
            _
                =
                ⁅ L a , L b * b ⁆ + ⁅ L a , L c * c ⁆ + 2 • ⁅ L a , L a * b ⁆
                        +
                        2 • ⁅ L a , L c * a ⁆
                      +
                      2 • ⁅ L a , L b * c ⁆
                    +
                    ⁅ L b , L a * a ⁆ + ⁅ L b , L c * c ⁆ + 2 • ⁅ L b , L a * b ⁆
                        +
                        2 • ⁅ L b , L c * a ⁆
                      +
                      2 • ⁅ L b , L b * c ⁆
                  +
                  ⁅ L c , L a * a ⁆ + ⁅ L c , L b * b ⁆ + 2 • ⁅ L c , L a * b ⁆
                      +
                      2 • ⁅ L c , L c * a ⁆
                    +
                    2 • ⁅ L c , L b * c ⁆
              :=
              by simp only [ lie_nsmul ]
            _
                =
                ⁅ L a , L b * b ⁆ + ⁅ L b , L a * a ⁆ + 2 • ⁅ L a , L a * b ⁆ + ⁅ L b , L a * b ⁆
                      +
                      ⁅ L a , L c * c ⁆ + ⁅ L c , L a * a ⁆
                        +
                        2 • ⁅ L a , L c * a ⁆ + ⁅ L c , L c * a ⁆
                    +
                    ⁅ L b , L c * c ⁆ + ⁅ L c , L b * b ⁆
                      +
                      2 • ⁅ L b , L b * c ⁆ + ⁅ L c , L b * c ⁆
                  +
                  2 • ⁅ L a , L b * c ⁆ + 2 • ⁅ L b , L c * a ⁆ + 2 • ⁅ L c , L a * b ⁆
              :=
              by abel
            _ = 2 • ⁅ L a , L b * c ⁆ + 2 • ⁅ L b , L c * a ⁆ + 2 • ⁅ L c , L a * b ⁆
              :=
              by
                rw [ add_left_eq_self ]
                  nth_rw 2 [ IsCommJordan.mul_comm a b ]
                  nth_rw 1 [ IsCommJordan.mul_comm c a ]
                  nth_rw 2 [ IsCommJordan.mul_comm b c ]
                  rw
                    [
                      two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add
                        ,
                        two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add
                        ,
                        two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add
                        ,
                        ← lie_skew L a * a
                        ,
                        ← lie_skew L b * b
                        ,
                        ← lie_skew L c * c
                        ,
                        ← lie_skew L a * a
                        ,
                        ← lie_skew L b * b
                        ,
                        ← lie_skew L c * c
                      ]
                  abel
            _ = 2 • ⁅ L a , L b * c ⁆ + ⁅ L b , L c * a ⁆ + ⁅ L c , L a * b ⁆
              :=
              by rw [ nsmul_add , nsmul_add ]
#align two_nsmul_lie_lmul_lmul_add_add_eq_zero two_nsmul_lie_lmul_lmul_add_add_eq_zero

