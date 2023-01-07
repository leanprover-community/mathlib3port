/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.witt_vector.teichmuller
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.WittVector.Basic

/-!
# Teichmüller lifts

This file defines `witt_vector.teichmuller`, a monoid hom `R →* 𝕎 R`, which embeds `r : R` as the
`0`-th component of a Witt vector whose other coefficients are `0`.

## Main declarations

- `witt_vector.teichmuller`: the Teichmuller map.
- `witt_vector.map_teichmuller`: `witt_vector.teichmuller` is a natural transformation.
- `witt_vector.ghost_component_teichmuller`:
  the `n`-th ghost component of `witt_vector.teichmuller p r` is `r ^ p ^ n`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

open MvPolynomial

variable (p : ℕ) {R S : Type _} [hp : Fact p.Prime] [CommRing R] [CommRing S]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The underlying function of the monoid hom `witt_vector.teichmuller`.\nThe `0`-th coefficient of `teichmuller_fun p r` is `r`, and all others are `0`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `teichmullerFun [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app (WittVector.RingTheory.WittVector.Teichmuller.term𝕎 "𝕎") [`R]))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [`p
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (termIfThenElse "if" («term_=_» `n "=" (num "0")) "then" `r "else" (num "0"))))]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`p
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (termIfThenElse "if" («term_=_» `n "=" (num "0")) "then" `r "else" (num "0"))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (termIfThenElse "if" («term_=_» `n "=" (num "0")) "then" `r "else" (num "0"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse "if" («term_=_» `n "=" (num "0")) "then" `r "else" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `n "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Teichmuller.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Teichmuller.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Teichmuller.term𝕎', expected 'WittVector.RingTheory.WittVector.Teichmuller.term𝕎._@.RingTheory.WittVector.Teichmuller._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The underlying function of the monoid hom `witt_vector.teichmuller`.
    The `0`-th coefficient of `teichmuller_fun p r` is `r`, and all others are `0`.
    -/
  def teichmullerFun ( r : R ) : 𝕎 R := ⟨ p , fun n => if n = 0 then r else 0 ⟩
#align witt_vector.teichmuller_fun WittVector.teichmullerFun

/-!
## `teichmuller` is a monoid homomorphism

On ghost components, it is clear that `teichmuller_fun` is a monoid homomorphism.
But in general the ghost map is not injective.
We follow the same strategy as for proving that the ring operations on `𝕎 R`
satisfy the ring axioms.

1. We first prove it for rings `R` where `p` is invertible,
   because then the ghost map is in fact an isomorphism.
2. After that, we derive the result for `mv_polynomial R ℤ`,
3. and from that we can prove the result for arbitrary `R`.
-/


include hp

private theorem ghost_component_teichmuller_fun (r : R) (n : ℕ) :
    ghostComponent n (teichmullerFun p r) = r ^ p ^ n :=
  by
  rw [ghost_component_apply, aeval_witt_polynomial, Finset.sum_eq_single 0, pow_zero, one_mul,
    tsub_zero]
  · rfl
  · intro i hi h0
    convert mul_zero _
    convert zero_pow _
    · cases i
      · contradiction
      · rfl
    · exact pow_pos hp.1.Pos _
  · rw [Finset.mem_range]
    intro h
    exact (h (Nat.succ_pos n)).elim
#align witt_vector.ghost_component_teichmuller_fun witt_vector.ghost_component_teichmuller_fun

private theorem map_teichmuller_fun (f : R →+* S) (r : R) :
    map f (teichmullerFun p r) = teichmullerFun p (f r) :=
  by
  ext n
  cases n
  · rfl
  · exact f.map_zero
#align witt_vector.map_teichmuller_fun witt_vector.map_teichmuller_fun

private theorem teichmuller_mul_aux₁ (x y : MvPolynomial R ℚ) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y :=
  by
  apply (ghost_map.bijective_of_invertible p (MvPolynomial R ℚ)).1
  rw [RingHom.map_mul]
  ext1 n
  simp only [Pi.mul_apply, ghost_map_apply, ghost_component_teichmuller_fun, mul_pow]
#align witt_vector.teichmuller_mul_aux₁ witt_vector.teichmuller_mul_aux₁

private theorem teichmuller_mul_aux₂ (x y : MvPolynomial R ℤ) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y :=
  by
  refine'
    map_injective (MvPolynomial.map (Int.castRingHom ℚ))
      (MvPolynomial.map_injective _ Int.cast_injective) _
  simp only [teichmuller_mul_aux₁, map_teichmuller_fun, RingHom.map_mul]
#align witt_vector.teichmuller_mul_aux₂ witt_vector.teichmuller_mul_aux₂

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The Teichmüller lift of an element of `R` to `𝕎 R`.\nThe `0`-th coefficient of `teichmuller p r` is `r`, and all others are `0`.\nThis is a monoid homomorphism. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `teichmuller [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Group.«term_→*_»
          `R
          " →* "
          (Term.app (WittVector.RingTheory.WittVector.Teichmuller.term𝕎 "𝕎") [`R])))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl (Term.letIdDecl `toFun [] [] ":=" (Term.app `teichmullerFun [`p]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_one'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.«tacticExt___:_»
                "ext"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
                [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `one_coeff_zero)] "]")
                  [])
                 []
                 (Tactic.tacticRfl "rfl")])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `one_coeff_eq_of_pos
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.hole "_")
                       (Term.app `Nat.succ_pos [`n])]))]
                   "]")
                  [])
                 []
                 (Tactic.tacticRfl "rfl")])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_mul'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`x `y])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `counit_surjective [`R `x]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `counit_surjective [`R `y]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `map_teichmuller_fun)
                  ","
                  (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingHom.map_mul)
                  ","
                  (Tactic.simpLemma [] [] `teichmuller_mul_aux₂)]
                 "]"]
                [])]))))))]
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
         [(Tactic.intro "intro" [`x `y])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `counit_surjective [`R `x]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `counit_surjective [`R `y]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `map_teichmuller_fun)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingHom.map_mul)
             ","
             (Tactic.simpLemma [] [] `teichmuller_mul_aux₂)]
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
        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `map_teichmuller_fun)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingHom.map_mul)
         ","
         (Tactic.simpLemma [] [] `teichmuller_mul_aux₂)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `teichmuller_mul_aux₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_teichmuller_fun
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `counit_surjective [`R `y]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `counit_surjective [`R `y])
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
      `counit_surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `counit_surjective [`R `x]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `counit_surjective [`R `x])
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
      `counit_surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `one_coeff_zero)] "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `one_coeff_eq_of_pos
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `Nat.succ_pos [`n])]))]
              "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `one_coeff_eq_of_pos
             [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `Nat.succ_pos [`n])]))]
          "]")
         [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `one_coeff_eq_of_pos
           [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `Nat.succ_pos [`n])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `one_coeff_eq_of_pos
       [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `Nat.succ_pos [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.succ_pos [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.succ_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Nat.succ_pos [`n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
      `one_coeff_eq_of_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `one_coeff_zero)] "]") [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `one_coeff_zero)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_coeff_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `teichmullerFun [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `teichmullerFun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Hom.Group.«term_→*_»
       `R
       " →* "
       (Term.app (WittVector.RingTheory.WittVector.Teichmuller.term𝕎 "𝕎") [`R]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.Teichmuller.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.Teichmuller.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.Teichmuller.term𝕎', expected 'WittVector.RingTheory.WittVector.Teichmuller.term𝕎._@.RingTheory.WittVector.Teichmuller._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The Teichmüller lift of an element of `R` to `𝕎 R`.
    The `0`-th coefficient of `teichmuller p r` is `r`, and all others are `0`.
    This is a monoid homomorphism. -/
  def
    teichmuller
    : R →* 𝕎 R
    where
      toFun := teichmullerFun p
        map_one'
          :=
          by
            ext ⟨ ⟩
              · rw [ one_coeff_zero ] rfl
              · rw [ one_coeff_eq_of_pos _ _ _ Nat.succ_pos n ] rfl
        map_mul'
          :=
          by
            intro x y
              rcases counit_surjective R x with ⟨ x , rfl ⟩
              rcases counit_surjective R y with ⟨ y , rfl ⟩
              simp only [ ← map_teichmuller_fun , ← RingHom.map_mul , teichmuller_mul_aux₂ ]
#align witt_vector.teichmuller WittVector.teichmuller

@[simp]
theorem teichmuller_coeff_zero (r : R) : (teichmuller p r).coeff 0 = r :=
  rfl
#align witt_vector.teichmuller_coeff_zero WittVector.teichmuller_coeff_zero

@[simp]
theorem teichmuller_coeff_pos (r : R) : ∀ (n : ℕ) (hn : 0 < n), (teichmuller p r).coeff n = 0
  | n + 1, _ => rfl
#align witt_vector.teichmuller_coeff_pos WittVector.teichmuller_coeff_pos

@[simp]
theorem teichmuller_zero : teichmuller p (0 : R) = 0 := by
  ext ⟨⟩ <;>
    · rw [zero_coeff]
      rfl
#align witt_vector.teichmuller_zero WittVector.teichmuller_zero

/-- `teichmuller` is a natural transformation. -/
@[simp]
theorem map_teichmuller (f : R →+* S) (r : R) : map f (teichmuller p r) = teichmuller p (f r) :=
  map_teichmuller_fun _ _ _
#align witt_vector.map_teichmuller WittVector.map_teichmuller

/-- The `n`-th ghost component of `teichmuller p r` is `r ^ p ^ n`. -/
@[simp]
theorem ghost_component_teichmuller (r : R) (n : ℕ) :
    ghostComponent n (teichmuller p r) = r ^ p ^ n :=
  ghost_component_teichmuller_fun _ _ _
#align witt_vector.ghost_component_teichmuller WittVector.ghost_component_teichmuller

end WittVector

