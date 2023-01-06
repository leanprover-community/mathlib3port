/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau

! This file was ported from Lean 3 source module number_theory.kummer_dedekind
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.AdjoinRoot
import Mathbin.RingTheory.DedekindDomain.Ideal
import Mathbin.RingTheory.AlgebraTower

/-!
# Kummer-Dedekind theorem

This file proves the monogenic version of the Kummer-Dedekind theorem on the splitting of prime
ideals in an extension of the ring of integers. This states that if `I` is a prime ideal of
Dedekind domain `R` and `S = R[α]` for some `α` that is integral over `R` with minimal polynomial
`f`, then the prime factorisations of `I * S` and `f mod I` have the same shape, i.e. they have the
same number of prime factors, and each prime factors of `I * S` can be paired with a prime factor
of `f mod I` in a way that ensures multiplicities match (in fact, this pairing can be made explicit
with a formula).

## Main definitions

 * `normalized_factors_map_equiv_normalized_factors_min_poly_mk` : The bijection in the
    Kummer-Dedekind theorem. This is the pairing between the prime factors of `I * S` and the prime
    factors of `f mod I`.

## Main results

 * `normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map` : The Kummer-Dedekind
    theorem.
 * `ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebra_map R S)` is irreducible if
    `(map I^.quotient.mk (minpoly R pb.gen))` is irreducible, where `pb` is a power basis of `S`
    over `R`.

## TODO

 * Prove the Kummer-Dedekind theorem in full generality.

 * Prove the converse of `ideal.irreducible_map_of_irreducible_minpoly`.

 * Prove that `normalized_factors_map_equiv_normalized_factors_min_poly_mk` can be expressed as
    `normalized_factors_map_equiv_normalized_factors_min_poly_mk g = ⟨I, G(α)⟩` for `g` a prime
    factor of `f mod I` and `G` a lift of `g` to `R[X]`.

## References

 * [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/


variable (R : Type _) {S : Type _} [CommRing R] [CommRing S] [Algebra R S]

open Ideal Polynomial DoubleQuot UniqueFactorizationMonoid Algebra RingHom

-- mathport name: «expr < >»
local notation:max R "<" x ">" => adjoin R ({x} : Set S)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Let `S / R` be a ring extension and `x : S`, then the conductor of `R<x>` is the\n    biggest ideal of `S` contained in `R<x>`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `conductor [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" `S] [] ")")]
       [(Term.typeSpec ":" (Term.app `Ideal [`S]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `carrier
           []
           []
           ":="
           (Set.«term{_|_}»
            "{"
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
            "|"
            (Term.forall
             "∀"
             [`b]
             [(Term.typeSpec ":" `S)]
             ","
             («term_∈_»
              («term_*_» `a "*" `b)
              "∈"
              (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")))
            "}"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `zero_mem'
           [`b]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `zero_mul)] "]")]
                 ["using" (Term.app `Subalgebra.zero_mem [(Term.hole "_")])]))]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `add_mem'
           [`a `b `ha `hb `c]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `add_mul)] "]")]
                 ["using"
                  (Term.app
                   `Subalgebra.add_mem
                   [(Term.hole "_") (Term.app `ha [`c]) (Term.app `hb [`c])])]))]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `smul_mem'
           [`c `a `ha `b]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma [] [] `smul_eq_mul)
                    ","
                    (Tactic.simpLemma [] [] `mul_left_comm)
                    ","
                    (Tactic.simpLemma [] [] `mul_assoc)]
                   "]")]
                 ["using" (Term.app `ha [(«term_*_» `c "*" `b)])]))]))))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `smul_eq_mul)
               ","
               (Tactic.simpLemma [] [] `mul_left_comm)
               ","
               (Tactic.simpLemma [] [] `mul_assoc)]
              "]")]
            ["using" (Term.app `ha [(«term_*_» `c "*" `b)])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `smul_eq_mul)
           ","
           (Tactic.simpLemma [] [] `mul_left_comm)
           ","
           (Tactic.simpLemma [] [] `mul_assoc)]
          "]")]
        ["using" (Term.app `ha [(«term_*_» `c "*" `b)])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ha [(«term_*_» `c "*" `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `c "*" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `c "*" `b) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_left_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `add_mul)] "]")]
            ["using"
             (Term.app
              `Subalgebra.add_mem
              [(Term.hole "_") (Term.app `ha [`c]) (Term.app `hb [`c])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `add_mul)] "]")]
        ["using"
         (Term.app `Subalgebra.add_mem [(Term.hole "_") (Term.app `ha [`c]) (Term.app `hb [`c])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subalgebra.add_mem [(Term.hole "_") (Term.app `ha [`c]) (Term.app `hb [`c])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hb [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hb [`c]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ha [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ha [`c]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra.add_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `zero_mul)] "]")]
            ["using" (Term.app `Subalgebra.zero_mem [(Term.hole "_")])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `zero_mul)] "]")]
        ["using" (Term.app `Subalgebra.zero_mem [(Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subalgebra.zero_mem [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra.zero_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [])
       "|"
       (Term.forall
        "∀"
        [`b]
        [(Term.typeSpec ":" `S)]
        ","
        («term_∈_»
         («term_*_» `a "*" `b)
         "∈"
         (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`b]
       [(Term.typeSpec ":" `S)]
       ","
       («term_∈_» («term_*_» `a "*" `b) "∈" (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» («term_*_» `a "*" `b) "∈" (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'NumberTheory.KummerDedekind.term_<_>._@.NumberTheory.KummerDedekind._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Let `S / R` be a ring extension and `x : S`, then the conductor of `R<x>` is the
        biggest ideal of `S` contained in `R<x>`. -/
  def
    conductor
    ( x : S ) : Ideal S
    where
      carrier := { a | ∀ b : S , a * b ∈ R < x > }
        zero_mem' b := by simpa only [ zero_mul ] using Subalgebra.zero_mem _
        add_mem' a b ha hb c := by simpa only [ add_mul ] using Subalgebra.add_mem _ ha c hb c
        smul_mem'
          c a ha b
          :=
          by simpa only [ smul_eq_mul , mul_left_comm , mul_assoc ] using ha c * b
#align conductor conductor

variable {R} {x : S}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `conductor_eq_of_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`y] [":" `S] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.typeAscription
            "("
            (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
            ":"
            [(Term.app `Set [`S])]
            ")")
           "="
           (NumberTheory.KummerDedekind.«term_<_>» `R "<" `y ">"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_» (Term.app `conductor [`R `x]) "=" (Term.app `conductor [`R `y]))))
      (Command.declValSimple
       ":="
       (Term.app
        `Ideal.ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.app
            `forall_congr'
            [(Term.fun
              "fun"
              (Term.basicFun
               [`b]
               []
               "=>"
               (Term.app (Term.proj `Set.ext_iff "." `mp) [`h (Term.hole "_")])))])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
          []
          "=>"
          (Term.app
           `forall_congr'
           [(Term.fun
             "fun"
             (Term.basicFun
              [`b]
              []
              "=>"
              (Term.app (Term.proj `Set.ext_iff "." `mp) [`h (Term.hole "_")])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.app
         `forall_congr'
         [(Term.fun
           "fun"
           (Term.basicFun
            [`b]
            []
            "=>"
            (Term.app (Term.proj `Set.ext_iff "." `mp) [`h (Term.hole "_")])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `forall_congr'
       [(Term.fun
         "fun"
         (Term.basicFun
          [`b]
          []
          "=>"
          (Term.app (Term.proj `Set.ext_iff "." `mp) [`h (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b]
        []
        "=>"
        (Term.app (Term.proj `Set.ext_iff "." `mp) [`h (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Set.ext_iff "." `mp) [`h (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Set.ext_iff "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Set.ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
      `forall_congr'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app `conductor [`R `x]) "=" (Term.app `conductor [`R `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `conductor [`R `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conductor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `conductor [`R `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conductor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
        ":"
        [(Term.app `Set [`S])]
        ")")
       "="
       (NumberTheory.KummerDedekind.«term_<_>» `R "<" `y ">"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.KummerDedekind.«term_<_>» `R "<" `y ">")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'NumberTheory.KummerDedekind.term_<_>._@.NumberTheory.KummerDedekind._hyg.6'
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
  conductor_eq_of_eq
  { y : S } ( h : ( R < x > : Set S ) = R < y > ) : conductor R x = conductor R y
  := Ideal.ext fun a => forall_congr' fun b => Set.ext_iff . mp h _
#align conductor_eq_of_eq conductor_eq_of_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `conductor_subset_adjoin [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_⊆_»
         (Term.typeAscription "(" (Term.app `conductor [`R `x]) ":" [(Term.app `Set [`S])] ")")
         "⊆"
         (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">"))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`y `hy]
         []
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_one)] "]")]
               ["using" (Term.app `hy [(num "1")])]))])))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y `hy]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              ["only"]
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_one)] "]")]
              ["using" (Term.app `hy [(num "1")])]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_one)] "]")]
            ["using" (Term.app `hy [(num "1")])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `mul_one)] "]")]
        ["using" (Term.app `hy [(num "1")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hy [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_⊆_»
       (Term.typeAscription "(" (Term.app `conductor [`R `x]) ":" [(Term.app `Set [`S])] ")")
       "⊆"
       (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'NumberTheory.KummerDedekind.term_<_>._@.NumberTheory.KummerDedekind._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  conductor_subset_adjoin
  : ( conductor R x : Set S ) ⊆ R < x >
  := fun y hy => by simpa only [ mul_one ] using hy 1
#align conductor_subset_adjoin conductor_subset_adjoin

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_conductor_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`y] [":" `S] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `y "∈" (Term.app `conductor [`R `x]))
         "↔"
         (Term.forall
          "∀"
          [`b]
          [(Term.typeSpec ":" `S)]
          ","
          («term_∈_»
           («term_*_» `y "*" `b)
           "∈"
           (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">"))))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`h] [] "=>" `h))
         ","
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" `h))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`h] [] "=>" `h))
        ","
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" `h))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" `h))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" `h))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `y "∈" (Term.app `conductor [`R `x]))
       "↔"
       (Term.forall
        "∀"
        [`b]
        [(Term.typeSpec ":" `S)]
        ","
        («term_∈_»
         («term_*_» `y "*" `b)
         "∈"
         (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`b]
       [(Term.typeSpec ":" `S)]
       ","
       («term_∈_» («term_*_» `y "*" `b) "∈" (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» («term_*_» `y "*" `b) "∈" (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'NumberTheory.KummerDedekind.term_<_>._@.NumberTheory.KummerDedekind._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mem_conductor_iff
  { y : S } : y ∈ conductor R x ↔ ∀ b : S , y * b ∈ R < x >
  := ⟨ fun h => h , fun h => h ⟩
#align mem_conductor_iff mem_conductor_iff

variable {I : Ideal R}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This technical lemma tell us that if `C` is the conductor of `R<x>` and `I` is an ideal of `R`\n  then `p * (I * S) ⊆ I * R<x>` for any `p` in `C ∩ R` -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `prod_mem_ideal_map_of_mem_conductor [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p] [":" `R] "}")
        (Term.implicitBinder "{" [`z] [":" `S] "}")
        (Term.explicitBinder
         "("
         [`hp]
         [":"
          («term_∈_»
           `p
           "∈"
           (Term.app `Ideal.comap [(Term.app `algebraMap [`R `S]) (Term.app `conductor [`R `x])]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hz']
         [":"
          («term_∈_» `z "∈" (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_»
         («term_*_» (Term.app `algebraMap [`R `S `p]) "*" `z)
         "∈"
         (Set.Data.Set.Image.term_''_
          (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
          " '' "
          (coeNotation
           "↑"
           (Term.app
            (Term.proj `I "." `map)
            [(Term.app
              `algebraMap
              [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])]))))))
      (Command.declValSimple
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
             [(Tactic.rwRule [] `Ideal.map)
              ","
              (Tactic.rwRule [] `Ideal.span)
              ","
              (Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hz'] []))])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `l)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H')])
                  [])]
                "⟩")])]
            []
            [":=" [`hz']])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finsupp.total_apply)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`H'] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H')
              ","
              (Tactic.rwRule [] `mul_comm)
              ","
              (Tactic.rwRule [] `Finsupp.sum_mul)]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`lem []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [(Term.implicitBinder "{" [`a] [":" `R] "}")]
                 []
                 ","
                 (Term.arrow
                  («term_∈_» `a "∈" `I)
                  "→"
                  («term_∈_»
                   («term_*_»
                    (Algebra.Group.Defs.«term_•_»
                     (Term.app `l [`a])
                     " • "
                     (Term.app `algebraMap [`R `S `a]))
                    "*"
                    (Term.app `algebraMap [`R `S `p]))
                   "∈"
                   (Set.Data.Set.Image.term_''_
                    (Term.app
                     `algebraMap
                     [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                    " '' "
                    (Term.app
                     `I.map
                     [(Term.app
                       `algebraMap
                       [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])]))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`a `ha])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                     ","
                     (Tactic.rwRule [] `mul_assoc)
                     ","
                     (Tactic.rwRule [] `mul_comm)
                     ","
                     (Tactic.rwRule [] `mul_assoc)
                     ","
                     (Tactic.rwRule [] `Set.mem_image)]
                    "]")
                   [])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `Exists.intro
                    [(«term_*_»
                      (Term.app
                       `algebraMap
                       [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `a])
                      "*"
                      (Term.anonymousCtor
                       "⟨"
                       [(«term_*_» (Term.app `l [`a]) "*" (Term.app `algebraMap [`R `S `p]))
                        ","
                        (Term.show
                         "show"
                         («term_∈_»
                          («term_*_» (Term.app `l [`a]) "*" (Term.app `algebraMap [`R `S `p]))
                          "∈"
                          (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">"))
                         (Term.fromTerm "from" (Term.hole "_")))]
                       "⟩"))
                     (Term.hole "_")]))
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `mem_conductor_iff.mp
                      [(Term.app `ideal.mem_comap.mp [`hp]) (Term.hole "_")]))])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.hole "_")
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Simpa.simpa
                          "simpa"
                          []
                          []
                          (Std.Tactic.Simpa.simpaArgsRest
                           []
                           []
                           ["only"]
                           [(Tactic.simpArgs
                             "["
                             [(Tactic.simpLemma [] [] `RingHom.map_mul)
                              ","
                              (Tactic.simpLemma
                               []
                               []
                               (Term.app
                                `mul_comm
                                [(Term.app `algebraMap [`R `S `p]) (Term.app `l [`a])]))]
                             "]")]
                           []))])))]
                    "⟩"))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                   [])
                  []
                  (Tactic.apply
                   "apply"
                   (Term.app
                    `Ideal.mul_mem_left
                    [(Term.app
                      `I.map
                      [(Term.app
                        `algebraMap
                        [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
                     (Term.hole "_")
                     (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `ha])]))]))))))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `Finset.sum_induction
             [(Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [`u]
                []
                "=>"
                («term_∈_»
                 `u
                 "∈"
                 (Set.Data.Set.Image.term_''_
                  (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                  " '' "
                  (Term.app
                   `I.map
                   [(Term.app
                     `algebraMap
                     [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))))
              (Term.fun "fun" (Term.basicFun [`a `b] [] "=>" (Term.hole "_")))
              (Term.hole "_")
              (Term.hole "_")]))
           []
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩"))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩"))]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `RingHom.map_add)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.anonymousCtor
             "⟨"
             [(«term_+_» `z "+" `y)
              ","
              (Term.app `Ideal.add_mem [(Term.hole "_") (Term.app `set_like.mem_coe.mp [`hz]) `hy])
              ","
              `rfl]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(num "0")
                ","
                («term_<|_» `set_like.mem_coe.mpr "<|" (Term.app `Ideal.zero_mem [(Term.hole "_")]))
                ","
                (Term.app `RingHom.map_zero [(Term.hole "_")])]
               "⟩"))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`y `hy])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `lem
               [(Term.app
                 (Term.proj (Term.app `Finsupp.mem_supported [(Term.hole "_") `l]) "." `mp)
                 [`H `hy])]))])])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Ideal.map)
             ","
             (Tactic.rwRule [] `Ideal.span)
             ","
             (Tactic.rwRule [] `Finsupp.mem_span_image_iff_total)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hz'] []))])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `l)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H')])
                 [])]
               "⟩")])]
           []
           [":=" [`hz']])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finsupp.total_apply)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`H'] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H')
             ","
             (Tactic.rwRule [] `mul_comm)
             ","
             (Tactic.rwRule [] `Finsupp.sum_mul)]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`lem []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.implicitBinder "{" [`a] [":" `R] "}")]
                []
                ","
                (Term.arrow
                 («term_∈_» `a "∈" `I)
                 "→"
                 («term_∈_»
                  («term_*_»
                   (Algebra.Group.Defs.«term_•_»
                    (Term.app `l [`a])
                    " • "
                    (Term.app `algebraMap [`R `S `a]))
                   "*"
                   (Term.app `algebraMap [`R `S `p]))
                  "∈"
                  (Set.Data.Set.Image.term_''_
                   (Term.app
                    `algebraMap
                    [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                   " '' "
                   (Term.app
                    `I.map
                    [(Term.app
                      `algebraMap
                      [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])]))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`a `ha])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                    ","
                    (Tactic.rwRule [] `mul_assoc)
                    ","
                    (Tactic.rwRule [] `mul_comm)
                    ","
                    (Tactic.rwRule [] `mul_assoc)
                    ","
                    (Tactic.rwRule [] `Set.mem_image)]
                   "]")
                  [])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `Exists.intro
                   [(«term_*_»
                     (Term.app
                      `algebraMap
                      [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `a])
                     "*"
                     (Term.anonymousCtor
                      "⟨"
                      [(«term_*_» (Term.app `l [`a]) "*" (Term.app `algebraMap [`R `S `p]))
                       ","
                       (Term.show
                        "show"
                        («term_∈_»
                         («term_*_» (Term.app `l [`a]) "*" (Term.app `algebraMap [`R `S `p]))
                         "∈"
                         (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">"))
                        (Term.fromTerm "from" (Term.hole "_")))]
                      "⟩"))
                    (Term.hole "_")]))
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `mem_conductor_iff.mp
                     [(Term.app `ideal.mem_comap.mp [`hp]) (Term.hole "_")]))])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.hole "_")
                    ","
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.Simpa.simpa
                         "simpa"
                         []
                         []
                         (Std.Tactic.Simpa.simpaArgsRest
                          []
                          []
                          ["only"]
                          [(Tactic.simpArgs
                            "["
                            [(Tactic.simpLemma [] [] `RingHom.map_mul)
                             ","
                             (Tactic.simpLemma
                              []
                              []
                              (Term.app
                               `mul_comm
                               [(Term.app `algebraMap [`R `S `p]) (Term.app `l [`a])]))]
                            "]")]
                          []))])))]
                   "⟩"))
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
                 []
                 (Tactic.apply
                  "apply"
                  (Term.app
                   `Ideal.mul_mem_left
                   [(Term.app
                     `I.map
                     [(Term.app
                       `algebraMap
                       [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
                    (Term.hole "_")
                    (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `ha])]))]))))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `Finset.sum_induction
            [(Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [`u]
               []
               "=>"
               («term_∈_»
                `u
                "∈"
                (Set.Data.Set.Image.term_''_
                 (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                 " '' "
                 (Term.app
                  `I.map
                  [(Term.app
                    `algebraMap
                    [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))))
             (Term.fun "fun" (Term.basicFun [`a `b] [] "=>" (Term.hole "_")))
             (Term.hole "_")
             (Term.hole "_")]))
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `RingHom.map_add)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(«term_+_» `z "+" `y)
             ","
             (Term.app `Ideal.add_mem [(Term.hole "_") (Term.app `set_like.mem_coe.mp [`hz]) `hy])
             ","
             `rfl]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(num "0")
               ","
               («term_<|_» `set_like.mem_coe.mpr "<|" (Term.app `Ideal.zero_mem [(Term.hole "_")]))
               ","
               (Term.app `RingHom.map_zero [(Term.hole "_")])]
              "⟩"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`y `hy])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `lem
              [(Term.app
                (Term.proj (Term.app `Finsupp.mem_supported [(Term.hole "_") `l]) "." `mp)
                [`H `hy])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`y `hy])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `lem
          [(Term.app
            (Term.proj (Term.app `Finsupp.mem_supported [(Term.hole "_") `l]) "." `mp)
            [`H `hy])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `lem
        [(Term.app
          (Term.proj (Term.app `Finsupp.mem_supported [(Term.hole "_") `l]) "." `mp)
          [`H `hy])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lem
       [(Term.app
         (Term.proj (Term.app `Finsupp.mem_supported [(Term.hole "_") `l]) "." `mp)
         [`H `hy])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `Finsupp.mem_supported [(Term.hole "_") `l]) "." `mp) [`H `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Finsupp.mem_supported [(Term.hole "_") `l]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Finsupp.mem_supported [(Term.hole "_") `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finsupp.mem_supported
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Finsupp.mem_supported [(Term.hole "_") `l])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `Finsupp.mem_supported [(Term.hole "_") `l]) ")")
       "."
       `mp)
      [`H `hy])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`y `hy])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(num "0")
           ","
           («term_<|_» `set_like.mem_coe.mpr "<|" (Term.app `Ideal.zero_mem [(Term.hole "_")]))
           ","
           (Term.app `RingHom.map_zero [(Term.hole "_")])]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(num "0")
         ","
         («term_<|_» `set_like.mem_coe.mpr "<|" (Term.app `Ideal.zero_mem [(Term.hole "_")]))
         ","
         (Term.app `RingHom.map_zero [(Term.hole "_")])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(num "0")
        ","
        («term_<|_» `set_like.mem_coe.mpr "<|" (Term.app `Ideal.zero_mem [(Term.hole "_")]))
        ","
        (Term.app `RingHom.map_zero [(Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `RingHom.map_zero [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.map_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `set_like.mem_coe.mpr "<|" (Term.app `Ideal.zero_mem [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.zero_mem [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.zero_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `set_like.mem_coe.mpr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(«term_+_» `z "+" `y)
         ","
         (Term.app `Ideal.add_mem [(Term.hole "_") (Term.app `set_like.mem_coe.mp [`hz]) `hy])
         ","
         `rfl]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_+_» `z "+" `y)
        ","
        (Term.app `Ideal.add_mem [(Term.hole "_") (Term.app `set_like.mem_coe.mp [`hz]) `hy])
        ","
        `rfl]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.add_mem [(Term.hole "_") (Term.app `set_like.mem_coe.mp [`hz]) `hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `set_like.mem_coe.mp [`hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_like.mem_coe.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `set_like.mem_coe.mp [`hz])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.add_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `z "+" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `RingHom.map_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
            [])]
          "⟩"))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Finset.sum_induction
        [(Term.hole "_")
         (Term.fun
          "fun"
          (Term.basicFun
           [`u]
           []
           "=>"
           («term_∈_»
            `u
            "∈"
            (Set.Data.Set.Image.term_''_
             (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
             " '' "
             (Term.app
              `I.map
              [(Term.app
                `algebraMap
                [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))))
         (Term.fun "fun" (Term.basicFun [`a `b] [] "=>" (Term.hole "_")))
         (Term.hole "_")
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finset.sum_induction
       [(Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [`u]
          []
          "=>"
          («term_∈_»
           `u
           "∈"
           (Set.Data.Set.Image.term_''_
            (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
            " '' "
            (Term.app
             `I.map
             [(Term.app
               `algebraMap
               [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))))
        (Term.fun "fun" (Term.basicFun [`a `b] [] "=>" (Term.hole "_")))
        (Term.hole "_")
        (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`a `b] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`a `b] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`u]
        []
        "=>"
        («term_∈_»
         `u
         "∈"
         (Set.Data.Set.Image.term_''_
          (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
          " '' "
          (Term.app
           `I.map
           [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `u
       "∈"
       (Set.Data.Set.Image.term_''_
        (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
        " '' "
        (Term.app
         `I.map
         [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
       " '' "
       (Term.app
        `I.map
        [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `I.map
       [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'NumberTheory.KummerDedekind.term_<_>._@.NumberTheory.KummerDedekind._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    This technical lemma tell us that if `C` is the conductor of `R<x>` and `I` is an ideal of `R`
      then `p * (I * S) ⊆ I * R<x>` for any `p` in `C ∩ R` -/
  theorem
    prod_mem_ideal_map_of_mem_conductor
    { p : R }
        { z : S }
        ( hp : p ∈ Ideal.comap algebraMap R S conductor R x )
        ( hz' : z ∈ I . map algebraMap R S )
      : algebraMap R S p * z ∈ algebraMap R < x > S '' ↑ I . map algebraMap R R < x >
    :=
      by
        rw [ Ideal.map , Ideal.span , Finsupp.mem_span_image_iff_total ] at hz'
          obtain ⟨ l , H , H' ⟩ := hz'
          rw [ Finsupp.total_apply ] at H'
          rw [ ← H' , mul_comm , Finsupp.sum_mul ]
          have
            lem
              :
                ∀
                  { a : R }
                  ,
                  a ∈ I
                    →
                    l a • algebraMap R S a * algebraMap R S p
                      ∈
                      algebraMap R < x > S '' I.map algebraMap R R < x >
              :=
              by
                intro a ha
                  rw [ Algebra.id.smul_eq_mul , mul_assoc , mul_comm , mul_assoc , Set.mem_image ]
                  refine'
                    Exists.intro
                      algebraMap R R < x > a
                          *
                          ⟨ l a * algebraMap R S p , show l a * algebraMap R S p ∈ R < x > from _ ⟩
                        _
                  · rw [ mul_comm ] exact mem_conductor_iff.mp ideal.mem_comap.mp hp _
                  refine' ⟨ _ , by simpa only [ RingHom.map_mul , mul_comm algebraMap R S p l a ] ⟩
                  rw [ mul_comm ]
                  apply Ideal.mul_mem_left I.map algebraMap R R < x > _ Ideal.mem_map_of_mem _ ha
          refine'
            Finset.sum_induction
              _ fun u => u ∈ algebraMap R < x > S '' I.map algebraMap R R < x > fun a b => _ _ _
          rintro ⟨ z , hz , rfl ⟩ ⟨ y , hy , rfl ⟩
          rw [ ← RingHom.map_add ]
          exact ⟨ z + y , Ideal.add_mem _ set_like.mem_coe.mp hz hy , rfl ⟩
          · refine' ⟨ 0 , set_like.mem_coe.mpr <| Ideal.zero_mem _ , RingHom.map_zero _ ⟩
          · intro y hy exact lem Finsupp.mem_supported _ l . mp H hy
#align prod_mem_ideal_map_of_mem_conductor prod_mem_ideal_map_of_mem_conductor

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A technical result telling us that `(I * S) ∩ R<x> = I * R<x>` for any ideal `I` of `R`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `comap_map_eq_map_adjoin_of_coprime_conductor [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hx]
         [":"
          («term_=_»
           (Order.Basic.«term_⊔_»
            (Term.app
             (Term.proj (Term.app `conductor [`R `x]) "." `comap)
             [(Term.app `algebraMap [`R `S])])
            " ⊔ "
            `I)
           "="
           (Order.BoundedOrder.«term⊤» "⊤"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h_alg]
         [":"
          (Term.app
           `Function.Injective
           [(Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])]) "." `comap)
          [(Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])])
         "="
         (Term.app
          (Term.proj `I "." `map)
          [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" `le_antisymm)
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`y `hy])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                    [])]
                  "⟩")])]
              []
              [":=" [`y]])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hpq)])
                    [])]
                  "⟩")])]
              []
              [":="
               [(Term.app
                 `submodule.mem_sup.mp
                 [(Term.app
                   (Term.proj (Term.app `Ideal.eq_top_iff_one [(Term.hole "_")]) "." `mp)
                   [`hx])])]])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`temp []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   («term_+_»
                    («term_*_» (Term.app `algebraMap [`R `S `p]) "*" `z)
                    "+"
                    («term_*_» (Term.app `algebraMap [`R `S `q]) "*" `z))
                   "="
                   `z))]
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
                     ["["
                      [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `add_mul)
                       ","
                       (Tactic.simpLemma
                        []
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app `RingHom.map_add [(Term.app `algebraMap [`R `S])]))
                       ","
                       (Tactic.simpLemma [] [] `hpq)
                       ","
                       (Tactic.simpLemma [] [] `map_one)
                       ","
                       (Tactic.simpLemma [] [] `one_mul)]
                      "]"]
                     [])]))))))
             []
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_↔_»
                («term_∈_»
                 `z
                 "∈"
                 (Set.Data.Set.Image.term_''_
                  (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                  " '' "
                  (Term.app
                   `I.map
                   [(Term.app
                     `algebraMap
                     [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))
                "↔"
                («term_∈_»
                 (Term.typeAscription
                  "("
                  (Term.anonymousCtor "⟨" [`z "," `hz] "⟩")
                  ":"
                  [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")]
                  ")")
                 "∈"
                 (Term.app
                  `I.map
                  [(Term.app
                    `algebraMap
                    [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)
                      ","
                      (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `temp)]
                     "]")
                    [])
                   []
                   (Std.Tactic.obtain
                    "obtain"
                    [(Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                          [])]
                        "⟩")])]
                    []
                    [":="
                     [(Term.app
                       (Term.proj
                        (Term.app `Set.mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                        "."
                        `mp)
                       [(Term.app
                         `prod_mem_ideal_map_of_mem_conductor
                         [`hp
                          (Term.show
                           "show"
                           («term_∈_» `z "∈" (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
                           (Term.byTactic'
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Std.Tactic.tacticRwa__
                                "rwa"
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.mem_comap)] "]")
                                [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])]))))])])]])
                   []
                   (Mathlib.Tactic.«tacticUse_,,»
                    "use"
                    [(«term_+_»
                      `a
                      "+"
                      («term_*_»
                       (Term.app
                        `algebraMap
                        [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `q])
                       "*"
                       (Term.anonymousCtor "⟨" [`z "," `hz] "⟩")))])
                   []
                   (Tactic.refine'
                    "refine'"
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.app
                       `Ideal.add_mem
                       [(Term.app
                         `I.map
                         [(Term.app
                           `algebraMap
                           [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
                        `ha.left
                        (Term.hole "_")])
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Std.Tactic.Simpa.simpa
                           "simpa"
                           []
                           []
                           (Std.Tactic.Simpa.simpaArgsRest
                            []
                            []
                            ["only"]
                            [(Tactic.simpArgs
                              "["
                              [(Tactic.simpLemma [] [] `ha.right)
                               ","
                               (Tactic.simpLemma [] [] `map_add)
                               ","
                               (Tactic.simpLemma [] [] `AlgHom.map_mul)
                               ","
                               (Tactic.simpLemma [] [] `add_right_inj)]
                              "]")]
                            []))])))]
                     "⟩"))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `Ideal.mul_mem_left
                     [(Term.app
                       `I.map
                       [(Term.app
                         `algebraMap
                         [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
                      (Term.hole "_")
                      (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hq])]))])))))
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`h]
                  []
                  "=>"
                  (Term.app
                   (Term.proj
                    (Term.app `Set.mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                    "."
                    `mpr)
                   [(Term.app
                     `Exists.intro
                     [(Term.anonymousCtor "⟨" [`z "," `hz] "⟩")
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.simp
                             "simp"
                             []
                             []
                             []
                             ["[" [(Tactic.simpLemma [] [] `h)] "]"]
                             [])])))
                        ","
                        `rfl]
                       "⟩")])])))]
               "⟩"))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₂)])
                      [])]
                    "⟩")])]
                []
                [":="
                 [(Term.app
                   (Term.proj
                    (Term.app `Set.mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                    "."
                    `mp)
                   [`h])]])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_=_» `x₁ "=" (Term.anonymousCtor "⟨" [`z "," `hz] "⟩")))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.apply "apply" `h_alg)
                      []
                      (Std.Tactic.Simpa.simpa
                       "simpa"
                       []
                       []
                       (Std.Tactic.Simpa.simpaArgsRest
                        []
                        []
                        []
                        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx₂)] "]")]
                        []))]))))))
               []
               (Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)]
                 "]")
                [])])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app `algebraMap [`R `S])
                   "="
                   (Term.app
                    (Term.proj (Term.app `algebraMap [(Term.hole "_") `S]) "." `comp)
                    [(Term.app
                      `algebraMap
                      [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")]))))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `this)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
               "]")
              [])
             []
             (Tactic.apply "apply" `Ideal.le_comap_map)])])))
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
         [(Tactic.apply "apply" `le_antisymm)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`y `hy])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                   [])]
                 "⟩")])]
             []
             [":=" [`y]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hpq)])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                `submodule.mem_sup.mp
                [(Term.app
                  (Term.proj (Term.app `Ideal.eq_top_iff_one [(Term.hole "_")]) "." `mp)
                  [`hx])])]])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`temp []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  («term_+_»
                   («term_*_» (Term.app `algebraMap [`R `S `p]) "*" `z)
                   "+"
                   («term_*_» (Term.app `algebraMap [`R `S `q]) "*" `z))
                  "="
                  `z))]
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
                    ["["
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `add_mul)
                      ","
                      (Tactic.simpLemma
                       []
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `RingHom.map_add [(Term.app `algebraMap [`R `S])]))
                      ","
                      (Tactic.simpLemma [] [] `hpq)
                      ","
                      (Tactic.simpLemma [] [] `map_one)
                      ","
                      (Tactic.simpLemma [] [] `one_mul)]
                     "]"]
                    [])]))))))
            []
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_↔_»
               («term_∈_»
                `z
                "∈"
                (Set.Data.Set.Image.term_''_
                 (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                 " '' "
                 (Term.app
                  `I.map
                  [(Term.app
                    `algebraMap
                    [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))
               "↔"
               («term_∈_»
                (Term.typeAscription
                 "("
                 (Term.anonymousCtor "⟨" [`z "," `hz] "⟩")
                 ":"
                 [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")]
                 ")")
                "∈"
                (Term.app
                 `I.map
                 [(Term.app
                   `algebraMap
                   [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `temp)]
                    "]")
                   [])
                  []
                  (Std.Tactic.obtain
                   "obtain"
                   [(Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                         [])]
                       "⟩")])]
                   []
                   [":="
                    [(Term.app
                      (Term.proj
                       (Term.app `Set.mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                       "."
                       `mp)
                      [(Term.app
                        `prod_mem_ideal_map_of_mem_conductor
                        [`hp
                         (Term.show
                          "show"
                          («term_∈_» `z "∈" (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
                          (Term.byTactic'
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Std.Tactic.tacticRwa__
                               "rwa"
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.mem_comap)] "]")
                               [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])]))))])])]])
                  []
                  (Mathlib.Tactic.«tacticUse_,,»
                   "use"
                   [(«term_+_»
                     `a
                     "+"
                     («term_*_»
                      (Term.app
                       `algebraMap
                       [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `q])
                      "*"
                      (Term.anonymousCtor "⟨" [`z "," `hz] "⟩")))])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.app
                      `Ideal.add_mem
                      [(Term.app
                        `I.map
                        [(Term.app
                          `algebraMap
                          [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
                       `ha.left
                       (Term.hole "_")])
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Simpa.simpa
                          "simpa"
                          []
                          []
                          (Std.Tactic.Simpa.simpaArgsRest
                           []
                           []
                           ["only"]
                           [(Tactic.simpArgs
                             "["
                             [(Tactic.simpLemma [] [] `ha.right)
                              ","
                              (Tactic.simpLemma [] [] `map_add)
                              ","
                              (Tactic.simpLemma [] [] `AlgHom.map_mul)
                              ","
                              (Tactic.simpLemma [] [] `add_right_inj)]
                             "]")]
                           []))])))]
                    "⟩"))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `Ideal.mul_mem_left
                    [(Term.app
                      `I.map
                      [(Term.app
                        `algebraMap
                        [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
                     (Term.hole "_")
                     (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hq])]))])))))
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [`h]
                 []
                 "=>"
                 (Term.app
                  (Term.proj
                   (Term.app `Set.mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                   "."
                   `mpr)
                  [(Term.app
                    `Exists.intro
                    [(Term.anonymousCtor "⟨" [`z "," `hz] "⟩")
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.simp
                            "simp"
                            []
                            []
                            []
                            ["[" [(Tactic.simpLemma [] [] `h)] "]"]
                            [])])))
                       ","
                       `rfl]
                      "⟩")])])))]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₁)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx₂)])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  (Term.proj
                   (Term.app `Set.mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                   "."
                   `mp)
                  [`h])]])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec ":" («term_=_» `x₁ "=" (Term.anonymousCtor "⟨" [`z "," `hz] "⟩")))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.apply "apply" `h_alg)
                     []
                     (Std.Tactic.Simpa.simpa
                      "simpa"
                      []
                      []
                      (Std.Tactic.Simpa.simpaArgsRest
                       []
                       []
                       []
                       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `hx₂)] "]")]
                       []))]))))))
              []
              (Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)] "]")
               [])])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app `algebraMap [`R `S])
                  "="
                  (Term.app
                   (Term.proj (Term.app `algebraMap [(Term.hole "_") `S]) "." `comp)
                   [(Term.app
                     `algebraMap
                     [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")]))))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `this)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
              "]")
             [])
            []
            (Tactic.apply "apply" `Ideal.le_comap_map)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app `algebraMap [`R `S])
              "="
              (Term.app
               (Term.proj (Term.app `algebraMap [(Term.hole "_") `S]) "." `comp)
               [(Term.app
                 `algebraMap
                 [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")]))))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `this)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
          "]")
         [])
        []
        (Tactic.apply "apply" `Ideal.le_comap_map)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Ideal.le_comap_map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.le_comap_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.map_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app `algebraMap [`R `S])
            "="
            (Term.app
             (Term.proj (Term.app `algebraMap [(Term.hole "_") `S]) "." `comp)
             [(Term.app
               `algebraMap
               [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `algebraMap [`R `S])
       "="
       (Term.app
        (Term.proj (Term.app `algebraMap [(Term.hole "_") `S]) "." `comp)
        [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `algebraMap [(Term.hole "_") `S]) "." `comp)
       [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'NumberTheory.KummerDedekind.term_<_>._@.NumberTheory.KummerDedekind._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A technical result telling us that `(I * S) ∩ R<x> = I * R<x>` for any ideal `I` of `R`. -/
  theorem
    comap_map_eq_map_adjoin_of_coprime_conductor
    ( hx : conductor R x . comap algebraMap R S ⊔ I = ⊤ )
        ( h_alg : Function.Injective algebraMap R < x > S )
      : I . map algebraMap R S . comap algebraMap R < x > S = I . map algebraMap R R < x >
    :=
      by
        apply le_antisymm
          ·
            intro y hy
              obtain ⟨ z , hz ⟩ := y
              obtain
                ⟨ p , hp , q , hq , hpq ⟩
                := submodule.mem_sup.mp Ideal.eq_top_iff_one _ . mp hx
              have
                temp
                  : algebraMap R S p * z + algebraMap R S q * z = z
                  :=
                  by
                    simp
                      only
                      [ ← add_mul , ← RingHom.map_add algebraMap R S , hpq , map_one , one_mul ]
              suffices
                z ∈ algebraMap R < x > S '' I.map algebraMap R R < x >
                    ↔
                    ( ⟨ z , hz ⟩ : R < x > ) ∈ I.map algebraMap R R < x >
                  by
                    rw [ ← this , ← temp ]
                      obtain
                        ⟨ a , ha ⟩
                        :=
                          Set.mem_image _ _ _ . mp
                            prod_mem_ideal_map_of_mem_conductor
                              hp show z ∈ I.map algebraMap R S by rwa [ Ideal.mem_comap ] at hy
                      use a + algebraMap R R < x > q * ⟨ z , hz ⟩
                      refine'
                        ⟨
                          Ideal.add_mem I.map algebraMap R R < x > ha.left _
                            ,
                            by simpa only [ ha.right , map_add , AlgHom.map_mul , add_right_inj ]
                          ⟩
                      rw [ mul_comm ]
                      exact
                        Ideal.mul_mem_left I.map algebraMap R R < x > _ Ideal.mem_map_of_mem _ hq
              refine'
                ⟨
                  fun h => _
                    ,
                    fun
                      h => Set.mem_image _ _ _ . mpr Exists.intro ⟨ z , hz ⟩ ⟨ by simp [ h ] , rfl ⟩
                  ⟩
              ·
                obtain ⟨ x₁ , hx₁ , hx₂ ⟩ := Set.mem_image _ _ _ . mp h
                  have : x₁ = ⟨ z , hz ⟩ := by apply h_alg simpa [ hx₂ ]
                  rwa [ ← this ]
          ·
            have : algebraMap R S = algebraMap _ S . comp algebraMap R R < x > := by ext rfl
              rw [ this , ← Ideal.map_map ]
              apply Ideal.le_comap_map
#align comap_map_eq_map_adjoin_of_coprime_conductor comap_map_eq_map_adjoin_of_coprime_conductor

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The canonical morphism of rings from `R<x> ⧸ (I*R<x>)` to `S ⧸ (I*S)` is an isomorphism\n    when `I` and `(conductor R x) ∩ R` are coprime. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `quotAdjoinEquivQuotMap [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`hx]
         [":"
          («term_=_»
           (Order.Basic.«term_⊔_»
            (Term.app
             (Term.proj (Term.app `conductor [`R `x]) "." `comap)
             [(Term.app `algebraMap [`R `S])])
            " ⊔ "
            `I)
           "="
           (Order.BoundedOrder.«term⊤» "⊤"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h_alg]
         [":"
          (Term.app
           `Function.Injective
           [(Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])])]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Algebra.Ring.Equiv.«term_≃+*_»
          (Algebra.Quotient.«term_⧸_»
           (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
           " ⧸ "
           (Term.app
            (Term.proj `I "." `map)
            [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])]))
          " ≃+* "
          (Algebra.Quotient.«term_⧸_»
           `S
           " ⧸ "
           (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])]))))])
      (Command.declValSimple
       ":="
       (Term.app
        `RingEquiv.ofBijective
        [(Term.app
          `Ideal.Quotient.lift
          [(Term.app
            (Term.proj `I "." `map)
            [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
           (Term.app
            (Term.proj
             (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])])
             "."
             `comp)
            [(Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])])
           (Term.fun
            "fun"
            (Term.basicFun
             [`r `hr]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.app `algebraMap [`R `S])
                       "="
                       (Term.app
                        (Term.proj
                         (Term.app
                          `algebraMap
                          [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                         "."
                         `comp)
                        [(Term.app
                          `algebraMap
                          [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                        []
                        (Tactic.tacticRfl "rfl")]))))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `RingHom.comp_apply)
                    ","
                    (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
                    ","
                    (Tactic.rwRule [] `this)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hr]))])))))])
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.constructor "constructor")
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.refine'
                "refine'"
                (Term.app
                 `RingHom.lift_injective_of_ker_le_ideal
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.fun "fun" (Term.basicFun [`u `hu] [] "=>" (Term.hole "_")))]))
               []
               (Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `RingHom.mem_ker)
                  ","
                  (Tactic.rwRule [] `RingHom.comp_apply)
                  ","
                  (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_comap)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `comap_map_eq_map_adjoin_of_coprime_conductor [`hx `h_alg]))]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hu] []))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.refine'
                "refine'"
                (Term.app
                 `Ideal.Quotient.lift_surjective_of_surjective
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))]))
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                      [])]
                    "⟩")])]
                []
                [":=" [(Term.app `Ideal.Quotient.mk_surjective [`y])]])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_∈_»
                     `z
                     "∈"
                     (Order.Basic.«term_⊔_»
                      (Term.app `conductor [`R `x])
                      " ⊔ "
                      (Term.app `I.map [(Term.app `algebraMap [`R `S])]))))]
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
                         (Order.Basic.«term_⊔_»
                          (Term.app `conductor [`R `x])
                          " ⊔ "
                          (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
                         "="
                         (Order.BoundedOrder.«term⊤» "⊤"))
                        (Term.byTactic'
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.simp
                             "simp"
                             []
                             []
                             ["only"]
                             ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                             [])])))))
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.eq_top_iff_one)] "]")
                       [(Tactic.location
                         "at"
                         (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
                      []
                      (Mathlib.Tactic.tacticReplace_
                       "replace"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         [`hx []]
                         []
                         ":="
                         (Term.app `Ideal.mem_map_of_mem [(Term.app `algebraMap [`R `S]) `hx]))))
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `Ideal.map_sup) "," (Tactic.rwRule [] `RingHom.map_one)]
                        "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                      []
                      (Tactic.exact
                       "exact"
                       (Term.app
                        (Term.app
                         `sup_le_sup
                         [(Term.show
                           "show"
                           («term_≤_»
                            (Term.app
                             (Term.proj
                              (Term.app
                               (Term.proj (Term.app `conductor [`R `x]) "." `comap)
                               [(Term.app `algebraMap [`R `S])])
                              "."
                              `map)
                             [(Term.app `algebraMap [`R `S])])
                            "≤"
                            (Term.app `conductor [`R `x]))
                           (Term.fromTerm "from" `Ideal.map_comap_le))
                          (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
                        [`hx]))]))))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_quotient_iff_mem_sup)
                  ","
                  (Tactic.rwRule [] `hz)
                  ","
                  (Tactic.rwRule [] `Ideal.mem_map_iff_of_surjective)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu')])
                      [])]
                    "⟩")])]
                []
                [":=" [`this]])
               []
               (Mathlib.Tactic.«tacticUse_,,»
                "use"
                [(Term.anonymousCtor "⟨" [`u "," (Term.app `conductor_subset_adjoin [`hu])] "⟩")])
               []
               (Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hu')]
                   "]")]
                 []))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact "exact" `Ideal.Quotient.mk_surjective)])])])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `RingEquiv.ofBijective
       [(Term.app
         `Ideal.Quotient.lift
         [(Term.app
           (Term.proj `I "." `map)
           [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
          (Term.app
           (Term.proj (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])]) "." `comp)
           [(Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])])
          (Term.fun
           "fun"
           (Term.basicFun
            [`r `hr]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Term.app `algebraMap [`R `S])
                      "="
                      (Term.app
                       (Term.proj
                        (Term.app
                         `algebraMap
                         [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                        "."
                        `comp)
                       [(Term.app
                         `algebraMap
                         [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                       []
                       (Tactic.tacticRfl "rfl")]))))))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `RingHom.comp_apply)
                   ","
                   (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
                   ","
                   (Tactic.rwRule [] `this)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
                  "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hr]))])))))])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.constructor "constructor")
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.app
                `RingHom.lift_injective_of_ker_le_ideal
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.fun "fun" (Term.basicFun [`u `hu] [] "=>" (Term.hole "_")))]))
              []
              (Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `RingHom.mem_ker)
                 ","
                 (Tactic.rwRule [] `RingHom.comp_apply)
                 ","
                 (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_comap)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app `comap_map_eq_map_adjoin_of_coprime_conductor [`hx `h_alg]))]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`hu] []))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.app
                `Ideal.Quotient.lift_surjective_of_surjective
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))]))
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                     [])]
                   "⟩")])]
               []
               [":=" [(Term.app `Ideal.Quotient.mk_surjective [`y])]])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   («term_∈_»
                    `z
                    "∈"
                    (Order.Basic.«term_⊔_»
                     (Term.app `conductor [`R `x])
                     " ⊔ "
                     (Term.app `I.map [(Term.app `algebraMap [`R `S])]))))]
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
                        (Order.Basic.«term_⊔_»
                         (Term.app `conductor [`R `x])
                         " ⊔ "
                         (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
                        "="
                        (Order.BoundedOrder.«term⊤» "⊤"))
                       (Term.byTactic'
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.simp
                            "simp"
                            []
                            []
                            ["only"]
                            ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                            [])])))))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.eq_top_iff_one)] "]")
                      [(Tactic.location
                        "at"
                        (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
                     []
                     (Mathlib.Tactic.tacticReplace_
                      "replace"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`hx []]
                        []
                        ":="
                        (Term.app `Ideal.mem_map_of_mem [(Term.app `algebraMap [`R `S]) `hx]))))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Ideal.map_sup) "," (Tactic.rwRule [] `RingHom.map_one)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       (Term.app
                        `sup_le_sup
                        [(Term.show
                          "show"
                          («term_≤_»
                           (Term.app
                            (Term.proj
                             (Term.app
                              (Term.proj (Term.app `conductor [`R `x]) "." `comap)
                              [(Term.app `algebraMap [`R `S])])
                             "."
                             `map)
                            [(Term.app `algebraMap [`R `S])])
                           "≤"
                           (Term.app `conductor [`R `x]))
                          (Term.fromTerm "from" `Ideal.map_comap_le))
                         (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
                       [`hx]))]))))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_quotient_iff_mem_sup)
                 ","
                 (Tactic.rwRule [] `hz)
                 ","
                 (Tactic.rwRule [] `Ideal.mem_map_iff_of_surjective)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu')])
                     [])]
                   "⟩")])]
               []
               [":=" [`this]])
              []
              (Mathlib.Tactic.«tacticUse_,,»
               "use"
               [(Term.anonymousCtor "⟨" [`u "," (Term.app `conductor_subset_adjoin [`hu])] "⟩")])
              []
              (Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                ["only"]
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hu')]
                  "]")]
                []))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact "exact" `Ideal.Quotient.mk_surjective)])])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              `RingHom.lift_injective_of_ker_le_ideal
              [(Term.hole "_")
               (Term.hole "_")
               (Term.fun "fun" (Term.basicFun [`u `hu] [] "=>" (Term.hole "_")))]))
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `RingHom.mem_ker)
               ","
               (Tactic.rwRule [] `RingHom.comp_apply)
               ","
               (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_comap)
               ","
               (Tactic.rwRule
                []
                (Term.app `comap_map_eq_map_adjoin_of_coprime_conductor [`hx `h_alg]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hu] []))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              `Ideal.Quotient.lift_surjective_of_surjective
              [(Term.hole "_")
               (Term.hole "_")
               (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))]))
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `Ideal.Quotient.mk_surjective [`y])]])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_∈_»
                  `z
                  "∈"
                  (Order.Basic.«term_⊔_»
                   (Term.app `conductor [`R `x])
                   " ⊔ "
                   (Term.app `I.map [(Term.app `algebraMap [`R `S])]))))]
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
                      (Order.Basic.«term_⊔_»
                       (Term.app `conductor [`R `x])
                       " ⊔ "
                       (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
                      "="
                      (Order.BoundedOrder.«term⊤» "⊤"))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                          [])])))))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.eq_top_iff_one)] "]")
                    [(Tactic.location
                      "at"
                      (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
                   []
                   (Mathlib.Tactic.tacticReplace_
                    "replace"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hx []]
                      []
                      ":="
                      (Term.app `Ideal.mem_map_of_mem [(Term.app `algebraMap [`R `S]) `hx]))))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `Ideal.map_sup) "," (Tactic.rwRule [] `RingHom.map_one)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     (Term.app
                      `sup_le_sup
                      [(Term.show
                        "show"
                        («term_≤_»
                         (Term.app
                          (Term.proj
                           (Term.app
                            (Term.proj (Term.app `conductor [`R `x]) "." `comap)
                            [(Term.app `algebraMap [`R `S])])
                           "."
                           `map)
                          [(Term.app `algebraMap [`R `S])])
                         "≤"
                         (Term.app `conductor [`R `x]))
                        (Term.fromTerm "from" `Ideal.map_comap_le))
                       (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
                     [`hx]))]))))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_quotient_iff_mem_sup)
               ","
               (Tactic.rwRule [] `hz)
               ","
               (Tactic.rwRule [] `Ideal.mem_map_iff_of_surjective)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu')])
                   [])]
                 "⟩")])]
             []
             [":=" [`this]])
            []
            (Mathlib.Tactic.«tacticUse_,,»
             "use"
             [(Term.anonymousCtor "⟨" [`u "," (Term.app `conductor_subset_adjoin [`hu])] "⟩")])
            []
            (Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              ["only"]
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hu')]
                "]")]
              []))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" `Ideal.Quotient.mk_surjective)])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          `Ideal.Quotient.lift_surjective_of_surjective
          [(Term.hole "_")
           (Term.hole "_")
           (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))]))
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `Ideal.Quotient.mk_surjective [`y])]])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_∈_»
              `z
              "∈"
              (Order.Basic.«term_⊔_»
               (Term.app `conductor [`R `x])
               " ⊔ "
               (Term.app `I.map [(Term.app `algebraMap [`R `S])]))))]
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
                  (Order.Basic.«term_⊔_»
                   (Term.app `conductor [`R `x])
                   " ⊔ "
                   (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
                  "="
                  (Order.BoundedOrder.«term⊤» "⊤"))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      ["only"]
                      ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                      [])])))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.eq_top_iff_one)] "]")
                [(Tactic.location
                  "at"
                  (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
               []
               (Mathlib.Tactic.tacticReplace_
                "replace"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hx []]
                  []
                  ":="
                  (Term.app `Ideal.mem_map_of_mem [(Term.app `algebraMap [`R `S]) `hx]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Ideal.map_sup) "," (Tactic.rwRule [] `RingHom.map_one)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.app
                  `sup_le_sup
                  [(Term.show
                    "show"
                    («term_≤_»
                     (Term.app
                      (Term.proj
                       (Term.app
                        (Term.proj (Term.app `conductor [`R `x]) "." `comap)
                        [(Term.app `algebraMap [`R `S])])
                       "."
                       `map)
                      [(Term.app `algebraMap [`R `S])])
                     "≤"
                     (Term.app `conductor [`R `x]))
                    (Term.fromTerm "from" `Ideal.map_comap_le))
                   (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
                 [`hx]))]))))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_quotient_iff_mem_sup)
           ","
           (Tactic.rwRule [] `hz)
           ","
           (Tactic.rwRule [] `Ideal.mem_map_iff_of_surjective)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu')])
               [])]
             "⟩")])]
         []
         [":=" [`this]])
        []
        (Mathlib.Tactic.«tacticUse_,,»
         "use"
         [(Term.anonymousCtor "⟨" [`u "," (Term.app `conductor_subset_adjoin [`hu])] "⟩")])
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          ["only"]
          [(Tactic.simpArgs
            "["
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hu')]
            "]")]
          []))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" `Ideal.Quotient.mk_surjective)])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" `Ideal.Quotient.mk_surjective)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `Ideal.Quotient.mk_surjective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.mk_surjective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hu')] "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.«tacticUse_,,»
       "use"
       [(Term.anonymousCtor "⟨" [`u "," (Term.app `conductor_subset_adjoin [`hu])] "⟩")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`u "," (Term.app `conductor_subset_adjoin [`hu])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `conductor_subset_adjoin [`hu])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conductor_subset_adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu')])
             [])]
           "⟩")])]
       []
       [":=" [`this]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_quotient_iff_mem_sup)
         ","
         (Tactic.rwRule [] `hz)
         ","
         (Tactic.rwRule [] `Ideal.mem_map_iff_of_surjective)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.mem_map_iff_of_surjective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.mem_quotient_iff_mem_sup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_∈_»
            `z
            "∈"
            (Order.Basic.«term_⊔_»
             (Term.app `conductor [`R `x])
             " ⊔ "
             (Term.app `I.map [(Term.app `algebraMap [`R `S])]))))]
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
                (Order.Basic.«term_⊔_»
                 (Term.app `conductor [`R `x])
                 " ⊔ "
                 (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
                "="
                (Order.BoundedOrder.«term⊤» "⊤"))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                    [])])))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.eq_top_iff_one)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
             []
             (Mathlib.Tactic.tacticReplace_
              "replace"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hx []]
                []
                ":="
                (Term.app `Ideal.mem_map_of_mem [(Term.app `algebraMap [`R `S]) `hx]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Ideal.map_sup) "," (Tactic.rwRule [] `RingHom.map_one)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
             []
             (Tactic.exact
              "exact"
              (Term.app
               (Term.app
                `sup_le_sup
                [(Term.show
                  "show"
                  («term_≤_»
                   (Term.app
                    (Term.proj
                     (Term.app
                      (Term.proj (Term.app `conductor [`R `x]) "." `comap)
                      [(Term.app `algebraMap [`R `S])])
                     "."
                     `map)
                    [(Term.app `algebraMap [`R `S])])
                   "≤"
                   (Term.app `conductor [`R `x]))
                  (Term.fromTerm "from" `Ideal.map_comap_le))
                 (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
               [`hx]))]))))))
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
             (Order.Basic.«term_⊔_»
              (Term.app `conductor [`R `x])
              " ⊔ "
              (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
             "="
             (Order.BoundedOrder.«term⊤» "⊤"))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                 [])])))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.eq_top_iff_one)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hx []]
             []
             ":="
             (Term.app `Ideal.mem_map_of_mem [(Term.app `algebraMap [`R `S]) `hx]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Ideal.map_sup) "," (Tactic.rwRule [] `RingHom.map_one)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.app
             `sup_le_sup
             [(Term.show
               "show"
               («term_≤_»
                (Term.app
                 (Term.proj
                  (Term.app
                   (Term.proj (Term.app `conductor [`R `x]) "." `comap)
                   [(Term.app `algebraMap [`R `S])])
                  "."
                  `map)
                 [(Term.app `algebraMap [`R `S])])
                "≤"
                (Term.app `conductor [`R `x]))
               (Term.fromTerm "from" `Ideal.map_comap_le))
              (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
            [`hx]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.app
         `sup_le_sup
         [(Term.show
           "show"
           («term_≤_»
            (Term.app
             (Term.proj
              (Term.app
               (Term.proj (Term.app `conductor [`R `x]) "." `comap)
               [(Term.app `algebraMap [`R `S])])
              "."
              `map)
             [(Term.app `algebraMap [`R `S])])
            "≤"
            (Term.app `conductor [`R `x]))
           (Term.fromTerm "from" `Ideal.map_comap_le))
          (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
        [`hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app
        `sup_le_sup
        [(Term.show
          "show"
          («term_≤_»
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj (Term.app `conductor [`R `x]) "." `comap)
              [(Term.app `algebraMap [`R `S])])
             "."
             `map)
            [(Term.app `algebraMap [`R `S])])
           "≤"
           (Term.app `conductor [`R `x]))
          (Term.fromTerm "from" `Ideal.map_comap_le))
         (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
       [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app
       `sup_le_sup
       [(Term.show
         "show"
         («term_≤_»
          (Term.app
           (Term.proj
            (Term.app
             (Term.proj (Term.app `conductor [`R `x]) "." `comap)
             [(Term.app `algebraMap [`R `S])])
            "."
            `map)
           [(Term.app `algebraMap [`R `S])])
          "≤"
          (Term.app `conductor [`R `x]))
         (Term.fromTerm "from" `Ideal.map_comap_le))
        (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_refl [(Term.app `I.map [(Term.app `algebraMap [`R `S])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `I.map [(Term.app `algebraMap [`R `S])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`R `S]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `I.map [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_refl
      [(Term.paren
        "("
        (Term.app `I.map [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.show
       "show"
       («term_≤_»
        (Term.app
         (Term.proj
          (Term.app
           (Term.proj (Term.app `conductor [`R `x]) "." `comap)
           [(Term.app `algebraMap [`R `S])])
          "."
          `map)
         [(Term.app `algebraMap [`R `S])])
        "≤"
        (Term.app `conductor [`R `x]))
       (Term.fromTerm "from" `Ideal.map_comap_le))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.map_comap_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj (Term.app `conductor [`R `x]) "." `comap)
          [(Term.app `algebraMap [`R `S])])
         "."
         `map)
        [(Term.app `algebraMap [`R `S])])
       "≤"
       (Term.app `conductor [`R `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `conductor [`R `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conductor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj (Term.app `conductor [`R `x]) "." `comap)
         [(Term.app `algebraMap [`R `S])])
        "."
        `map)
       [(Term.app `algebraMap [`R `S])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`R `S]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `conductor [`R `x]) "." `comap)
        [(Term.app `algebraMap [`R `S])])
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `conductor [`R `x]) "." `comap)
       [(Term.app `algebraMap [`R `S])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`R `S]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `conductor [`R `x]) "." `comap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `conductor [`R `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conductor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `conductor [`R `x]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `conductor [`R `x]) ")") "." `comap)
      [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.show
      "show"
      («term_≤_»
       (Term.app
        (Term.proj
         (Term.paren
          "("
          (Term.app
           (Term.proj (Term.paren "(" (Term.app `conductor [`R `x]) ")") "." `comap)
           [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
          ")")
         "."
         `map)
        [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
       "≤"
       (Term.app `conductor [`R `x]))
      (Term.fromTerm "from" `Ideal.map_comap_le))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sup_le_sup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `sup_le_sup
      [(Term.paren
        "("
        (Term.show
         "show"
         («term_≤_»
          (Term.app
           (Term.proj
            (Term.paren
             "("
             (Term.app
              (Term.proj (Term.paren "(" (Term.app `conductor [`R `x]) ")") "." `comap)
              [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
             ")")
            "."
            `map)
           [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
          "≤"
          (Term.app `conductor [`R `x]))
         (Term.fromTerm "from" `Ideal.map_comap_le))
        ")")
       (Term.paren
        "("
        (Term.app
         `le_refl
         [(Term.paren
           "("
           (Term.app `I.map [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
           ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Ideal.map_sup) "," (Tactic.rwRule [] `RingHom.map_one)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.map_sup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hx []]
         []
         ":="
         (Term.app `Ideal.mem_map_of_mem [(Term.app `algebraMap [`R `S]) `hx]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.mem_map_of_mem [(Term.app `algebraMap [`R `S]) `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `algebraMap [`R `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`R `S]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mem_map_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.eq_top_iff_one)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.eq_top_iff_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_=_»
         (Order.Basic.«term_⊔_»
          (Term.app `conductor [`R `x])
          " ⊔ "
          (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
         "="
         (Order.BoundedOrder.«term⊤» "⊤"))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Order.Basic.«term_⊔_»
        (Term.app `conductor [`R `x])
        " ⊔ "
        (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
       "="
       (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Order.Basic.«term_⊔_»
       (Term.app `conductor [`R `x])
       " ⊔ "
       (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `I.map [(Term.app `algebraMap [`R `S])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`R `S]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 68, term))
      (Term.app `conductor [`R `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conductor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1022, (some 1023, term) <=? (some 68, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 68, (some 69, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `z
       "∈"
       (Order.Basic.«term_⊔_»
        (Term.app `conductor [`R `x])
        " ⊔ "
        (Term.app `I.map [(Term.app `algebraMap [`R `S])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊔_»
       (Term.app `conductor [`R `x])
       " ⊔ "
       (Term.app `I.map [(Term.app `algebraMap [`R `S])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `I.map [(Term.app `algebraMap [`R `S])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`R `S]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `I.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 68, term))
      (Term.app `conductor [`R `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `conductor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1022, (some 1023, term) <=? (some 68, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 68, (some 69, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `Ideal.Quotient.mk_surjective [`y])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.Quotient.mk_surjective [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.Quotient.mk_surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Ideal.Quotient.lift_surjective_of_surjective
        [(Term.hole "_")
         (Term.hole "_")
         (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.Quotient.lift_surjective_of_surjective
       [(Term.hole "_")
        (Term.hole "_")
        (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.Quotient.lift_surjective_of_surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          `RingHom.lift_injective_of_ker_le_ideal
          [(Term.hole "_")
           (Term.hole "_")
           (Term.fun "fun" (Term.basicFun [`u `hu] [] "=>" (Term.hole "_")))]))
        []
        (Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `RingHom.mem_ker)
           ","
           (Tactic.rwRule [] `RingHom.comp_apply)
           ","
           (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_comap)
           ","
           (Tactic.rwRule [] (Term.app `comap_map_eq_map_adjoin_of_coprime_conductor [`hx `h_alg]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hu] []))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `RingHom.mem_ker)
         ","
         (Tactic.rwRule [] `RingHom.comp_apply)
         ","
         (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_comap)
         ","
         (Tactic.rwRule [] (Term.app `comap_map_eq_map_adjoin_of_coprime_conductor [`hx `h_alg]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hu] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `comap_map_eq_map_adjoin_of_coprime_conductor [`hx `h_alg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_alg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comap_map_eq_map_adjoin_of_coprime_conductor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.mem_comap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.eq_zero_iff_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.mem_ker
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `RingHom.lift_injective_of_ker_le_ideal
        [(Term.hole "_")
         (Term.hole "_")
         (Term.fun "fun" (Term.basicFun [`u `hu] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `RingHom.lift_injective_of_ker_le_ideal
       [(Term.hole "_")
        (Term.hole "_")
        (Term.fun "fun" (Term.basicFun [`u `hu] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`u `hu] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.lift_injective_of_ker_le_ideal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.constructor "constructor")
         []
         (tactic__
          (cdotTk (patternIgnore (token.«· » "·")))
          [(Tactic.refine'
            "refine'"
            (Term.app
             `RingHom.lift_injective_of_ker_le_ideal
             [(Term.hole "_")
              (Term.hole "_")
              (Term.fun "fun" (Term.basicFun [`u `hu] [] "=>" (Term.hole "_")))]))
           []
           (Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `RingHom.mem_ker)
              ","
              (Tactic.rwRule [] `RingHom.comp_apply)
              ","
              (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_comap)
              ","
              (Tactic.rwRule
               []
               (Term.app `comap_map_eq_map_adjoin_of_coprime_conductor [`hx `h_alg]))]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hu] []))])])
         []
         (tactic__
          (cdotTk (patternIgnore (token.«· » "·")))
          [(Tactic.refine'
            "refine'"
            (Term.app
             `Ideal.Quotient.lift_surjective_of_surjective
             [(Term.hole "_")
              (Term.hole "_")
              (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))]))
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                  [])]
                "⟩")])]
            []
            [":=" [(Term.app `Ideal.Quotient.mk_surjective [`y])]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_∈_»
                 `z
                 "∈"
                 (Order.Basic.«term_⊔_»
                  (Term.app `conductor [`R `x])
                  " ⊔ "
                  (Term.app `I.map [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")]))))]
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
                     (Order.Basic.«term_⊔_»
                      (Term.app `conductor [`R `x])
                      " ⊔ "
                      (Term.app `I.map [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")]))
                     "="
                     (Order.BoundedOrder.«term⊤» "⊤"))
                    (Term.byTactic'
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                         [])])))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Ideal.eq_top_iff_one)] "]")
                   [(Tactic.location
                     "at"
                     (Tactic.locationHyp [`hx] [(patternIgnore (token.«⊢» "⊢"))]))])
                  []
                  (Mathlib.Tactic.tacticReplace_
                   "replace"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hx []]
                     []
                     ":="
                     (Term.app
                      `Ideal.mem_map_of_mem
                      [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")") `hx]))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Ideal.map_sup) "," (Tactic.rwRule [] `RingHom.map_one)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.paren
                     "("
                     (Term.app
                      `sup_le_sup
                      [(Term.paren
                        "("
                        (Term.show
                         "show"
                         («term_≤_»
                          (Term.app
                           (Term.proj
                            (Term.paren
                             "("
                             (Term.app
                              (Term.proj
                               (Term.paren "(" (Term.app `conductor [`R `x]) ")")
                               "."
                               `comap)
                              [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
                             ")")
                            "."
                            `map)
                           [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
                          "≤"
                          (Term.app `conductor [`R `x]))
                         (Term.fromTerm "from" `Ideal.map_comap_le))
                        ")")
                       (Term.paren
                        "("
                        (Term.app
                         `le_refl
                         [(Term.paren
                           "("
                           (Term.app `I.map [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
                           ")")])
                        ")")])
                     ")")
                    [`hx]))]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.mem_quotient_iff_mem_sup)
              ","
              (Tactic.rwRule [] `hz)
              ","
              (Tactic.rwRule [] `Ideal.mem_map_iff_of_surjective)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `u)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hu')])
                  [])]
                "⟩")])]
            []
            [":=" [`this]])
           []
           (Mathlib.Tactic.«tacticUse_,,»
            "use"
            [(Term.anonymousCtor "⟨" [`u "," (Term.app `conductor_subset_adjoin [`hu])] "⟩")])
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hu')]
               "]")]
             []))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" `Ideal.Quotient.mk_surjective)])])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Ideal.Quotient.lift
       [(Term.app
         (Term.proj `I "." `map)
         [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
        (Term.app
         (Term.proj (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])]) "." `comp)
         [(Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])])
        (Term.fun
         "fun"
         (Term.basicFun
          [`r `hr]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Term.app `algebraMap [`R `S])
                    "="
                    (Term.app
                     (Term.proj
                      (Term.app
                       `algebraMap
                       [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                      "."
                      `comp)
                     [(Term.app
                       `algebraMap
                       [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                     []
                     (Tactic.tacticRfl "rfl")]))))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `RingHom.comp_apply)
                 ","
                 (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
                "]")
               [])
              []
              (Tactic.exact "exact" (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hr]))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`r `hr]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app `algebraMap [`R `S])
                  "="
                  (Term.app
                   (Term.proj
                    (Term.app
                     `algebraMap
                     [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                    "."
                    `comp)
                   [(Term.app
                     `algebraMap
                     [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")]))))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `RingHom.comp_apply)
               ","
               (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
               ","
               (Tactic.rwRule [] `this)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
              "]")
             [])
            []
            (Tactic.exact "exact" (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hr]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app `algebraMap [`R `S])
                "="
                (Term.app
                 (Term.proj
                  (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
                  "."
                  `comp)
                 [(Term.app
                   `algebraMap
                   [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `RingHom.comp_apply)
             ","
             (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
             ","
             (Tactic.rwRule [] `this)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hr]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hr]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") `hr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mem_map_of_mem
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
        [(Tactic.rwRule [] `RingHom.comp_apply)
         ","
         (Tactic.rwRule [] `Ideal.Quotient.eq_zero_iff_mem)
         ","
         (Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.map_map)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.map_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.eq_zero_iff_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app `algebraMap [`R `S])
            "="
            (Term.app
             (Term.proj
              (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
              "."
              `comp)
             [(Term.app
               `algebraMap
               [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) [] (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `algebraMap [`R `S])
       "="
       (Term.app
        (Term.proj
         (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
         "."
         `comp)
        [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])
        "."
        `comp)
       [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'NumberTheory.KummerDedekind.term_<_>._@.NumberTheory.KummerDedekind._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      The canonical morphism of rings from `R<x> ⧸ (I*R<x>)` to `S ⧸ (I*S)` is an isomorphism
          when `I` and `(conductor R x) ∩ R` are coprime. -/
    noncomputable
  def
    quotAdjoinEquivQuotMap
    ( hx : conductor R x . comap algebraMap R S ⊔ I = ⊤ )
        ( h_alg : Function.Injective algebraMap R < x > S )
      : R < x > ⧸ I . map algebraMap R R < x > ≃+* S ⧸ I . map algebraMap R S
    :=
      RingEquiv.ofBijective
        Ideal.Quotient.lift
            I . map algebraMap R R < x >
              I . map algebraMap R S . comp algebraMap R < x > S
              fun
                r hr
                  =>
                  by
                    have
                        : algebraMap R S = algebraMap R < x > S . comp algebraMap R R < x >
                          :=
                          by ext rfl
                      rw
                        [
                          RingHom.comp_apply
                            ,
                            Ideal.Quotient.eq_zero_iff_mem
                            ,
                            this
                            ,
                            ← Ideal.map_map
                          ]
                      exact Ideal.mem_map_of_mem _ hr
          by
            constructor
              ·
                refine' RingHom.lift_injective_of_ker_le_ideal _ _ fun u hu => _
                  rwa
                    [
                      RingHom.mem_ker
                        ,
                        RingHom.comp_apply
                        ,
                        Ideal.Quotient.eq_zero_iff_mem
                        ,
                        ← Ideal.mem_comap
                        ,
                        comap_map_eq_map_adjoin_of_coprime_conductor hx h_alg
                      ]
                    at hu
              ·
                refine' Ideal.Quotient.lift_surjective_of_surjective _ _ fun y => _
                  obtain ⟨ z , hz ⟩ := Ideal.Quotient.mk_surjective y
                  have
                    : z ∈ conductor R x ⊔ I.map algebraMap R S
                      :=
                      by
                        suffices conductor R x ⊔ I.map algebraMap R S = ⊤ by simp only [ this ]
                          rw [ Ideal.eq_top_iff_one ] at hx ⊢
                          replace hx := Ideal.mem_map_of_mem algebraMap R S hx
                          rw [ Ideal.map_sup , RingHom.map_one ] at hx
                          exact
                            sup_le_sup
                                show
                                    conductor R x . comap algebraMap R S . map algebraMap R S
                                      ≤
                                      conductor R x
                                    from Ideal.map_comap_le
                                  le_refl I.map algebraMap R S
                              hx
                  rw
                    [ ← Ideal.mem_quotient_iff_mem_sup , hz , Ideal.mem_map_iff_of_surjective ]
                    at this
                  obtain ⟨ u , hu , hu' ⟩ := this
                  use ⟨ u , conductor_subset_adjoin hu ⟩
                  simpa only [ ← hu' ]
                  · exact Ideal.Quotient.mk_surjective
#align quot_adjoin_equiv_quot_map quotAdjoinEquivQuotMap

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
      (Command.declId `quot_adjoin_equiv_quot_map_apply_mk [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hx]
         [":"
          («term_=_»
           (Order.Basic.«term_⊔_»
            (Term.app
             (Term.proj (Term.app `conductor [`R `x]) "." `comap)
             [(Term.app `algebraMap [`R `S])])
            " ⊔ "
            `I)
           "="
           (Order.BoundedOrder.«term⊤» "⊤"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h_alg]
         [":"
          (Term.app
           `Function.Injective
           [(Term.app `algebraMap [(NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">") `S])])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`a]
         [":" (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `quotAdjoinEquivQuotMap
          [`hx
           `h_alg
           (Term.app
            (Term.app
             (Term.proj `I "." `map)
             [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
            [`a])])
         "="
         (Term.app
          (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])])
          [(coeNotation "↑" `a)]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `quotAdjoinEquivQuotMap
        [`hx
         `h_alg
         (Term.app
          (Term.app
           (Term.proj `I "." `map)
           [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
          [`a])])
       "="
       (Term.app
        (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])])
        [(coeNotation "↑" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])])
       [(coeNotation "↑" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app (Term.proj `I "." `map) [(Term.app `algebraMap [`R `S])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`R `S]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `I "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `I "." `map) [(Term.paren "(" (Term.app `algebraMap [`R `S]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `quotAdjoinEquivQuotMap
       [`hx
        `h_alg
        (Term.app
         (Term.app
          (Term.proj `I "." `map)
          [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
         [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app
        (Term.proj `I "." `map)
        [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
       [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app
       (Term.proj `I "." `map)
       [(Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.KummerDedekind.«term_<_>» `R "<" `x ">")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.KummerDedekind.«term_<_>»', expected 'NumberTheory.KummerDedekind.term_<_>._@.NumberTheory.KummerDedekind._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    quot_adjoin_equiv_quot_map_apply_mk
    ( hx : conductor R x . comap algebraMap R S ⊔ I = ⊤ )
        ( h_alg : Function.Injective algebraMap R < x > S )
        ( a : R < x > )
      : quotAdjoinEquivQuotMap hx h_alg I . map algebraMap R R < x > a = I . map algebraMap R S ↑ a
    := rfl
#align quot_adjoin_equiv_quot_map_apply_mk quot_adjoin_equiv_quot_map_apply_mk

namespace KummerDedekind

open BigOperators Polynomial Classical

variable [IsDomain R] [IsDomain S] [IsDedekindDomain S]

variable (pb : PowerBasis R S)

attribute [local instance] Ideal.Quotient.field

/-- The first half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the prime
    factors of `I*S` are in bijection with those of the minimal polynomial of the generator of `S`
    over `R`, taken `mod I`.-/
noncomputable def normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : IsMaximal I)
    (hI' : I ≠ ⊥) :
    { J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S)) } ≃
      { d : (R ⧸ I)[X] | d ∈ normalizedFactors (map I (minpoly R pb.gen)) } :=
  (--show that `I * S` ≠ ⊥
        --show that the ideal spanned by `(minpoly R pb.gen) mod I` is non-zero
        normalizedFactorsEquivOfQuotEquiv
        (↑(pb.quotientEquivQuotientMinpolyMap I))
        (show I.map (algebraMap R S) ≠ ⊥ by
          rwa [Ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective, ← Ne.def])
        (by
          by_contra
          exact
            (show map I (minpoly R pb.gen) ≠ 0 from
                Polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen))
              (span_singleton_eq_bot.mp h))).trans
    (normalizedFactorsEquivSpanNormalizedFactors
        (show map I (minpoly R pb.gen) ≠ 0 from
          Polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen))).symm
#align
  kummer_dedekind.normalized_factors_map_equiv_normalized_factors_min_poly_mk KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk

/-- The second half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the
    bijection `factors_equiv'` defined in the first half preserves multiplicities. -/
theorem multiplicity_factors_map_eq_multiplicity (hI : IsMaximal I) (hI' : I ≠ ⊥) {J : Ideal S}
    (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    multiplicity J (I.map (algebraMap R S)) =
      multiplicity (↑(normalizedFactorsMapEquivNormalizedFactorsMinPolyMk pb hI hI' ⟨J, hJ⟩))
        (map I (minpoly R pb.gen)) :=
  by
  rw [normalized_factors_map_equiv_normalized_factors_min_poly_mk, Equiv.coe_trans,
    Function.comp_apply,
    multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity,
    normalized_factors_equiv_of_quot_equiv_multiplicity_eq_multiplicity]
#align
  kummer_dedekind.multiplicity_factors_map_eq_multiplicity KummerDedekind.multiplicity_factors_map_eq_multiplicity

/-- The **Kummer-Dedekind Theorem**. -/
theorem normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map (hI : IsMaximal I)
    (hI' : I ≠ ⊥) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f =>
          ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk pb hI hI').symm f : Ideal S))
        (normalizedFactors (Polynomial.map I (minpoly R pb.gen))).attach :=
  by
  ext J
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J ∈ normalized_factors (I.map (algebraMap R S))
  swap
  · rw [multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    simp only [Multiset.mem_attach, true_and_iff, not_exists]
    rintro J' rfl
    exact hJ ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm J').Prop
  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := multiplicity_factors_map_eq_multiplicity pb hI hI' hJ
  rw [multiplicity_eq_count_normalized_factors, multiplicity_eq_count_normalized_factors,
    UniqueFactorizationMonoid.normalize_normalized_factor _ hJ,
    UniqueFactorizationMonoid.normalize_normalized_factor, PartEnat.coe_inj] at this
  refine' this.trans _
  -- Get rid of the `map` by applying the equiv to both sides.
  generalize hJ' : (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI') ⟨J, hJ⟩ =
    J'
  have :
    ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm J' : Ideal S) =
      J :=
    by rw [← hJ', Equiv.symm_apply_apply _ _, Subtype.coe_mk]
  subst this
  -- Get rid of the `attach` by applying the subtype `coe` to both sides.
  rw [Multiset.count_map_eq_count' fun f =>
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm f : Ideal S),
    Multiset.attach_count_eq_count_coe]
  · exact subtype.coe_injective.comp (Equiv.injective _)
  · exact (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' _).Prop
  ·
    exact
      irreducible_of_normalized_factor _
        (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' _).Prop
  · exact Polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen)
  · exact irreducible_of_normalized_factor _ hJ
  · rwa [← bot_eq_zero, Ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective]
#align
  kummer_dedekind.normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map KummerDedekind.normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map

theorem Ideal.irreducible_map_of_irreducible_minpoly (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hf : Irreducible (map I (minpoly R pb.gen))) : Irreducible (I.map (algebraMap R S)) :=
  by
  have mem_norm_factors :
    normalize (map I (minpoly R pb.gen)) ∈ normalized_factors (map I (minpoly R pb.gen)) := by
    simp [normalized_factors_irreducible hf]
  suffices ∃ x, normalized_factors (I.map (algebraMap R S)) = {x}
    by
    obtain ⟨x, hx⟩ := this
    have h :=
      normalized_factors_prod
        (show I.map (algebraMap R S) ≠ 0 by
          rwa [← bot_eq_zero, Ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective])
    rw [associated_iff_eq, hx, Multiset.prod_singleton] at h
    rw [← h]
    exact
      irreducible_of_normalized_factor x
        (show x ∈ normalized_factors (I.map (algebraMap R S)) by simp [hx])
  rw [normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map pb hI hI']
  use
    ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm
        ⟨normalize (map I (minpoly R pb.gen)), mem_norm_factors⟩ :
      Ideal S)
  rw [Multiset.map_eq_singleton]
  use ⟨normalize (map I (minpoly R pb.gen)), mem_norm_factors⟩
  refine' ⟨_, rfl⟩
  apply Multiset.map_injective Subtype.coe_injective
  rw [Multiset.attach_map_coe, Multiset.map_singleton, Subtype.coe_mk]
  exact normalized_factors_irreducible hf
#align
  kummer_dedekind.ideal.irreducible_map_of_irreducible_minpoly KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly

end KummerDedekind

