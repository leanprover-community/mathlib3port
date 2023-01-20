/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.bezout
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.PrincipalIdealDomain
import Mathbin.Algebra.GcdMonoid.IntegrallyClosed

/-!

# Bézout rings

A Bézout ring (Bezout ring) is a ring whose finitely generated ideals are principal.
Notible examples include principal ideal rings, valuation rings, and the ring of algebraic integers.

## Main results
- `is_bezout.iff_span_pair_is_principal`: It suffices to verify every `span {x, y}` is principal.
- `is_bezout.to_gcd_monoid`: Every Bézout domain is a GCD domain. This is not an instance.
- `is_bezout.tfae`: For a Bézout domain, noetherian ↔ PID ↔ UFD ↔ ACCP

-/


universe u v

variable (R : Type u) [CommRing R]

/-- A Bézout ring is a ring whose finitely generated ideals are principal. -/
class IsBezout : Prop where
  isPrincipalOfFg : ∀ I : Ideal R, I.Fg → I.IsPrincipal
#align is_bezout IsBezout

namespace IsBezout

variable {R}

instance spanPairIsPrincipal [IsBezout R] (x y : R) : (Ideal.span {x, y} : Ideal R).IsPrincipal :=
  by classical exact is_principal_of_fg (Ideal.span {x, y}) ⟨{x, y}, by simp⟩
#align is_bezout.span_pair_is_principal IsBezout.spanPairIsPrincipal

theorem iff_span_pair_is_principal :
    IsBezout R ↔ ∀ x y : R, (Ideal.span {x, y} : Ideal R).IsPrincipal := by
  classical
    constructor
    · intro H x y
      infer_instance
    · intro H
      constructor
      apply Submodule.fgInduction
      · exact fun _ => ⟨⟨_, rfl⟩⟩
      · rintro _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩
        rw [← Submodule.span_insert]
        exact H _ _
#align is_bezout.iff_span_pair_is_principal IsBezout.iff_span_pair_is_principal

section Gcd

variable [IsBezout R]

/-- The gcd of two elements in a bezout domain. -/
noncomputable def gcd (x y : R) : R :=
  Submodule.IsPrincipal.generator (Ideal.span {x, y})
#align is_bezout.gcd IsBezout.gcd

theorem span_gcd (x y : R) : (Ideal.span {gcd x y} : Ideal R) = Ideal.span {x, y} :=
  Ideal.span_singleton_generator _
#align is_bezout.span_gcd IsBezout.span_gcd

theorem gcd_dvd_left (x y : R) : gcd x y ∣ x :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))
#align is_bezout.gcd_dvd_left IsBezout.gcd_dvd_left

theorem gcd_dvd_right (x y : R) : gcd x y ∣ y :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))
#align is_bezout.gcd_dvd_right IsBezout.gcd_dvd_right

theorem dvd_gcd {x y z : R} (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y :=
  by
  rw [← Ideal.span_singleton_le_span_singleton] at hx hy⊢
  rw [span_gcd, Ideal.span_insert, sup_le_iff]
  exact ⟨hx, hy⟩
#align is_bezout.dvd_gcd IsBezout.dvd_gcd

theorem gcd_eq_sum (x y : R) : ∃ a b : R, a * x + b * y = gcd x y :=
  Ideal.mem_span_pair.mp
    (by
      rw [← span_gcd]
      apply Ideal.subset_span
      simp)
#align is_bezout.gcd_eq_sum IsBezout.gcd_eq_sum

variable (R)

/-- Any bezout domain is a GCD domain. This is not an instance since `gcd_monoid` contains data,
and this might not be how we would like to construct it. -/
noncomputable def toGcdDomain [IsDomain R] [DecidableEq R] : GCDMonoid R :=
  gcdMonoidOfGCD gcd gcd_dvd_left gcd_dvd_right fun _ _ _ => dvd_gcd
#align is_bezout.to_gcd_domain IsBezout.toGcdDomain

end Gcd

attribute [local instance] to_gcd_domain

-- Note that the proof, despite being `infer_instance`, depends on the `local attribute [instance]`
-- lemma above, and is thus necessary to be restated.
instance (priority := 100) [IsDomain R] [IsBezout R] : IsIntegrallyClosed R :=
  inferInstance

theorem Function.Surjective.isBezout {S : Type v} [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) [IsBezout R] : IsBezout S :=
  by
  rw [iff_span_pair_is_principal]
  intro x y
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hf x, hf y
  use f (gcd x y)
  trans Ideal.map f (Ideal.span {gcd x y})
  · rw [span_gcd, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  · rw [Ideal.map_span, Set.image_singleton]
    rfl
#align function.surjective.is_bezout Function.Surjective.isBezout

instance (priority := 100) ofIsPrincipalIdealRing [IsPrincipalIdealRing R] : IsBezout R :=
  ⟨fun I _ => IsPrincipalIdealRing.principal I⟩
#align is_bezout.of_is_principal_ideal_ring IsBezout.ofIsPrincipalIdealRing

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tfae [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsBezout [`R]) "]")
        (Term.instBinder "[" [] (Term.app `IsDomain [`R]) "]")]
       (Term.typeSpec
        ":"
        (Term.app
         `TFAE
         [(«term[_]»
           "["
           [(Term.app `IsNoetherianRing [`R])
            ","
            (Term.app `IsPrincipalIdealRing [`R])
            ","
            (Term.app `UniqueFactorizationMonoid [`R])
            ","
            (Term.app `WfDvdMonoid [`R])]
           "]")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.intro "intro" [`H])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`I]
                      []
                      "=>"
                      (Term.app
                       `is_principal_of_fg
                       [(Term.hole "_") (Term.app `IsNoetherian.noetherian [(Term.hole "_")])])))]
                   "⟩"))])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "3"))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.intro "intro" []) [] (Tactic.tacticInfer_instance "infer_instance")])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "4"))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.intro "intro" []) [] (Tactic.tacticInfer_instance "infer_instance")])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "1"))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `is_noetherian_ring_iff)
                    ","
                    (Tactic.rwRule [] `is_noetherian_iff_fg_well_founded)]
                   "]")
                  [])
                 []
                 (Tactic.apply "apply" (Term.app `RelEmbedding.wellFounded [(Term.hole "_") `h]))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.forall
                       "∀"
                       [`I]
                       [(Term.typeSpec
                         ":"
                         («term{_:_//_}»
                          "{"
                          `J
                          [":" (Term.app `Ideal [`R])]
                          "//"
                          (Term.proj `J "." `Fg)
                          "}"))]
                       ","
                       («term∃_,_»
                        "∃"
                        (Lean.explicitBinders
                         (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `R]))
                        ","
                        («term_=_»
                         (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
                         "="
                         (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])))))]
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.anonymousCtor "⟨" [`I "," `hI] "⟩")]
                      []
                      "=>"
                      (Term.proj
                       (Term.app `IsBezout.isPrincipalOfFg [`I `hI])
                       "."
                       (fieldIdx "1")))))))
                 []
                 (Mathlib.Tactic.Choose.choose
                  "choose"
                  []
                  [(Lean.binderIdent `f) (Lean.binderIdent `hf)]
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.structInst
                   "{"
                   []
                   [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `f)
                    []
                    (Term.structInstField
                     (Term.structInstLVal `inj' [])
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`x `y `e]
                       []
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
                           []
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [] `hf)
                              ","
                              (Tactic.rwRule [] `hf)
                              ","
                              (Tactic.rwRule [] `e)]
                             "]")
                            [])]))))))
                    []
                    (Term.structInstField
                     (Term.structInstLVal `map_rel_iff' [])
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`x `y]
                       []
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.dsimp "dsimp" [] [] [] [] [])
                           []
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule
                               [(patternIgnore (token.«← » "←"))]
                               `Ideal.span_singleton_lt_span_singleton)
                              ","
                              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
                              ","
                              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
                             "]")
                            [])
                           []
                           (Tactic.tacticRfl "rfl")]))))))]
                   (Term.optEllipsis [])
                   []
                   "}"))])
               []
               (Tactic.tfaeFinish "tfae_finish")])))])))
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
         [(Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.intro "intro" [`H])
                []
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`I]
                     []
                     "=>"
                     (Term.app
                      `is_principal_of_fg
                      [(Term.hole "_") (Term.app `IsNoetherian.noetherian [(Term.hole "_")])])))]
                  "⟩"))])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "3"))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.intro "intro" []) [] (Tactic.tacticInfer_instance "infer_instance")])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "4"))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.intro "intro" []) [] (Tactic.tacticInfer_instance "infer_instance")])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "1"))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Std.Tactic.rintro
                 "rintro"
                 [(Std.Tactic.RCases.rintroPat.one
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                      [])]
                    "⟩"))]
                 [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `is_noetherian_ring_iff)
                   ","
                   (Tactic.rwRule [] `is_noetherian_iff_fg_well_founded)]
                  "]")
                 [])
                []
                (Tactic.apply "apply" (Term.app `RelEmbedding.wellFounded [(Term.hole "_") `h]))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     (Term.forall
                      "∀"
                      [`I]
                      [(Term.typeSpec
                        ":"
                        («term{_:_//_}»
                         "{"
                         `J
                         [":" (Term.app `Ideal [`R])]
                         "//"
                         (Term.proj `J "." `Fg)
                         "}"))]
                      ","
                      («term∃_,_»
                       "∃"
                       (Lean.explicitBinders
                        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `R]))
                       ","
                       («term_=_»
                        (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
                        "="
                        (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])))))]
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.anonymousCtor "⟨" [`I "," `hI] "⟩")]
                     []
                     "=>"
                     (Term.proj
                      (Term.app `IsBezout.isPrincipalOfFg [`I `hI])
                      "."
                      (fieldIdx "1")))))))
                []
                (Mathlib.Tactic.Choose.choose
                 "choose"
                 []
                 [(Lean.binderIdent `f) (Lean.binderIdent `hf)]
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.structInst
                  "{"
                  []
                  [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `f)
                   []
                   (Term.structInstField
                    (Term.structInstLVal `inj' [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`x `y `e]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
                          []
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [] `hf)
                             ","
                             (Tactic.rwRule [] `hf)
                             ","
                             (Tactic.rwRule [] `e)]
                            "]")
                           [])]))))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `map_rel_iff' [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`x `y]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.dsimp "dsimp" [] [] [] [] [])
                          []
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule
                              [(patternIgnore (token.«← » "←"))]
                              `Ideal.span_singleton_lt_span_singleton)
                             ","
                             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
                             ","
                             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
                            "]")
                           [])
                          []
                          (Tactic.tacticRfl "rfl")]))))))]
                  (Term.optEllipsis [])
                  []
                  "}"))])
              []
              (Tactic.tfaeFinish "tfae_finish")])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`H])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`I]
                 []
                 "=>"
                 (Term.app
                  `is_principal_of_fg
                  [(Term.hole "_") (Term.app `IsNoetherian.noetherian [(Term.hole "_")])])))]
              "⟩"))])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "3"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" []) [] (Tactic.tacticInfer_instance "infer_instance")])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "4"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" []) [] (Tactic.tacticInfer_instance "infer_instance")])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "1"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `is_noetherian_ring_iff)
               ","
               (Tactic.rwRule [] `is_noetherian_iff_fg_well_founded)]
              "]")
             [])
            []
            (Tactic.apply "apply" (Term.app `RelEmbedding.wellFounded [(Term.hole "_") `h]))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [`I]
                  [(Term.typeSpec
                    ":"
                    («term{_:_//_}»
                     "{"
                     `J
                     [":" (Term.app `Ideal [`R])]
                     "//"
                     (Term.proj `J "." `Fg)
                     "}"))]
                  ","
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `R]))
                   ","
                   («term_=_»
                    (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
                    "="
                    (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])))))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`I "," `hI] "⟩")]
                 []
                 "=>"
                 (Term.proj (Term.app `IsBezout.isPrincipalOfFg [`I `hI]) "." (fieldIdx "1")))))))
            []
            (Mathlib.Tactic.Choose.choose
             "choose"
             []
             [(Lean.binderIdent `f) (Lean.binderIdent `hf)]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.structInst
              "{"
              []
              [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `f)
               []
               (Term.structInstField
                (Term.structInstLVal `inj' [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x `y `e]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `hf)
                         ","
                         (Tactic.rwRule [] `hf)
                         ","
                         (Tactic.rwRule [] `e)]
                        "]")
                       [])]))))))
               []
               (Term.structInstField
                (Term.structInstLVal `map_rel_iff' [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x `y]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.dsimp "dsimp" [] [] [] [] [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          [(patternIgnore (token.«← » "←"))]
                          `Ideal.span_singleton_lt_span_singleton)
                         ","
                         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
                         ","
                         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
                        "]")
                       [])
                      []
                      (Tactic.tacticRfl "rfl")]))))))]
              (Term.optEllipsis [])
              []
              "}"))])
          []
          (Tactic.tfaeFinish "tfae_finish")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeFinish "tfae_finish")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `is_noetherian_ring_iff)
           ","
           (Tactic.rwRule [] `is_noetherian_iff_fg_well_founded)]
          "]")
         [])
        []
        (Tactic.apply "apply" (Term.app `RelEmbedding.wellFounded [(Term.hole "_") `h]))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`I]
              [(Term.typeSpec
                ":"
                («term{_:_//_}»
                 "{"
                 `J
                 [":" (Term.app `Ideal [`R])]
                 "//"
                 (Term.proj `J "." `Fg)
                 "}"))]
              ","
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `R]))
               ","
               («term_=_»
                (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
                "="
                (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`I "," `hI] "⟩")]
             []
             "=>"
             (Term.proj (Term.app `IsBezout.isPrincipalOfFg [`I `hI]) "." (fieldIdx "1")))))))
        []
        (Mathlib.Tactic.Choose.choose "choose" [] [(Lean.binderIdent `f) (Lean.binderIdent `hf)] [])
        []
        (Tactic.exact
         "exact"
         (Term.structInst
          "{"
          []
          [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `f)
           []
           (Term.structInstField
            (Term.structInstLVal `inj' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`x `y `e]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `e)]
                    "]")
                   [])]))))))
           []
           (Term.structInstField
            (Term.structInstLVal `map_rel_iff' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`x `y]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.dsimp "dsimp" [] [] [] [] [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      `Ideal.span_singleton_lt_span_singleton)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
                    "]")
                   [])
                  []
                  (Tactic.tacticRfl "rfl")]))))))]
          (Term.optEllipsis [])
          []
          "}"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `f)
         []
         (Term.structInstField
          (Term.structInstLVal `inj' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `y `e]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `e)]
                  "]")
                 [])]))))))
         []
         (Term.structInstField
          (Term.structInstLVal `map_rel_iff' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `y]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.dsimp "dsimp" [] [] [] [] [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    `Ideal.span_singleton_lt_span_singleton)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
                  "]")
                 [])
                []
                (Tactic.tacticRfl "rfl")]))))))]
        (Term.optEllipsis [])
        []
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `toFun []) ":=" `f)
        []
        (Term.structInstField
         (Term.structInstLVal `inj' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y `e]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `e)]
                 "]")
                [])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_rel_iff' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.dsimp "dsimp" [] [] [] [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `Ideal.span_singleton_lt_span_singleton)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
                 "]")
                [])
               []
               (Tactic.tacticRfl "rfl")]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                `Ideal.span_singleton_lt_span_singleton)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
              "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              `Ideal.span_singleton_lt_span_singleton)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Ideal.span_singleton_lt_span_singleton)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hf)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.span_singleton_lt_span_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y `e]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `e)]
              "]")
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `e)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `hf) "," (Tactic.rwRule [] `e)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Choose.choose "choose" [] [(Lean.binderIdent `f) (Lean.binderIdent `hf)] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`I]
            [(Term.typeSpec
              ":"
              («term{_:_//_}» "{" `J [":" (Term.app `Ideal [`R])] "//" (Term.proj `J "." `Fg) "}"))]
            ","
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `R]))
             ","
             («term_=_»
              (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
              "="
              (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])))))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`I "," `hI] "⟩")]
           []
           "=>"
           (Term.proj (Term.app `IsBezout.isPrincipalOfFg [`I `hI]) "." (fieldIdx "1")))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`I "," `hI] "⟩")]
        []
        "=>"
        (Term.proj (Term.app `IsBezout.isPrincipalOfFg [`I `hI]) "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `IsBezout.isPrincipalOfFg [`I `hI]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsBezout.isPrincipalOfFg [`I `hI])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hI
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsBezout.isPrincipalOfFg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsBezout.isPrincipalOfFg [`I `hI])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`I "," `hI] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hI
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`I]
       [(Term.typeSpec
         ":"
         («term{_:_//_}» "{" `J [":" (Term.app `Ideal [`R])] "//" (Term.proj `J "." `Fg) "}"))]
       ","
       («term∃_,_»
        "∃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `R]))
        ","
        («term_=_»
         (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
         "="
         (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `R]))
       ","
       («term_=_»
        (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
        "="
        (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
       "="
       (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [`x] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.span
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `I ":" [(Term.app `Ideal [`R])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `J [":" (Term.app `Ideal [`R])] "//" (Term.proj `J "." `Fg) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `J "." `Fg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `RelEmbedding.wellFounded [(Term.hole "_") `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `RelEmbedding.wellFounded [(Term.hole "_") `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RelEmbedding.wellFounded
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
        [(Tactic.rwRule [] `is_noetherian_ring_iff)
         ","
         (Tactic.rwRule [] `is_noetherian_iff_fg_well_founded)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_noetherian_iff_fg_well_founded
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_noetherian_ring_iff
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
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« → »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ↔ »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ← »'
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
  tfae
  [ IsBezout R ] [ IsDomain R ]
    :
      TFAE
        [
          IsNoetherianRing R , IsPrincipalIdealRing R , UniqueFactorizationMonoid R , WfDvdMonoid R
          ]
  :=
    by
      classical
        tfae_have 1 → 2
          · intro H exact ⟨ fun I => is_principal_of_fg _ IsNoetherian.noetherian _ ⟩
          tfae_have 2 → 3
          · intro infer_instance
          tfae_have 3 → 4
          · intro infer_instance
          tfae_have 4 → 1
          ·
            rintro ⟨ h ⟩
              rw [ is_noetherian_ring_iff , is_noetherian_iff_fg_well_founded ]
              apply RelEmbedding.wellFounded _ h
              have
                : ∀ I : { J : Ideal R // J . Fg } , ∃ x : R , ( I : Ideal R ) = Ideal.span { x }
                  :=
                  fun ⟨ I , hI ⟩ => IsBezout.isPrincipalOfFg I hI . 1
              choose f hf
              exact
                {
                  toFun := f
                    inj' := fun x y e => by ext1 rw [ hf , hf , e ]
                    map_rel_iff'
                      :=
                      fun
                        x y
                          =>
                          by dsimp rw [ ← Ideal.span_singleton_lt_span_singleton , ← hf , ← hf ] rfl
                  }
          tfae_finish
#align is_bezout.tfae IsBezout.tfae

end IsBezout

