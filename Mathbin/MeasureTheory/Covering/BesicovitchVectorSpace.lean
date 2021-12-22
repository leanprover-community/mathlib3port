import Mathbin.MeasureTheory.Measure.HaarLebesgue
import Mathbin.MeasureTheory.Covering.Besicovitch

/-!
# Satellite configurations for Besicovitch covering lemma in vector spaces

The Besicovitch covering theorem ensures that, in a nice metric space, there exists a number `N`
such that, from any family of balls with bounded radii, one can extract `N` families, each made of
disjoint balls, covering together all the centers of the initial family.

A key tool in the proof of this theorem is the notion of a satellite configuration, i.e., a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This is a technical notion, but it shows
up naturally in the proof of the Besicovitch theorem (which goes through a greedy algorithm): to
ensure that in the end one needs at most `N` families of balls, the crucial property of the
underlying metric space is that there should be no satellite configuration of `N + 1` points.

This file is devoted to the study of this property in vector spaces: we prove the main result
of [Füredi and Loeb, On the best constant for the Besicovitch covering theorem][furedi-loeb1994],
which shows that the optimal such `N` in a vector space coincides with the maximal number
of points one can put inside the unit ball of radius `2` under the condition that their distances
are bounded below by `1`.
In particular, this number is bounded by `5 ^ dim` by a straightforward measure argument.

## Main definitions and results

* `multiplicity E` is the maximal number of points one can put inside the unit ball
  of radius `2` in the vector space `E`, under the condition that their distances
  are bounded below by `1`.
* `multiplicity_le E` shows that `multiplicity E ≤ 5 ^ (dim E)`.
* `good_τ E` is a constant `> 1`, but close enough to `1` that satellite configurations
  with this parameter `τ` are not worst than for `τ = 1`.
* `is_empty_satellite_config_multiplicity` is the main theorem, saying that there are
  no satellite configurations of `(multiplicity E) + 1` points, for the parameter `good_τ E`.
-/


universe u

open Metric Set FiniteDimensional MeasureTheory Filter Finₓ

open_locale Ennreal TopologicalSpace

noncomputable section

namespace Besicovitch

variable {E : Type _} [NormedGroup E]

namespace SatelliteConfig

variable [NormedSpace ℝ E] {N : ℕ} {τ : ℝ} (a : satellite_config E N τ)

/--  Rescaling a satellite configuration in a vector space, to put the basepoint at `0` and the base
radius at `1`. -/
def center_and_rescale : satellite_config E N τ :=
  { c := fun i => a.r (last N)⁻¹ • (a.c i - a.c (last N)), R := fun i => a.r (last N)⁻¹*a.r i,
    rpos := fun i => mul_pos (inv_pos.2 (a.rpos _)) (a.rpos _),
    h := fun i j hij => by
      rcases a.h i j hij with (H | H)
      ·
        left
        constructor
        ·
          rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
          refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
          rw [dist_eq_norm] at H
          convert H.1 using 2
          abel
        ·
          rw [← mul_assocₓ, mul_commₓ τ, mul_assocₓ]
          refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
          exact H.2
      ·
        right
        constructor
        ·
          rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
          refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
          rw [dist_eq_norm] at H
          convert H.1 using 2
          abel
        ·
          rw [← mul_assocₓ, mul_commₓ τ, mul_assocₓ]
          refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
          exact H.2,
    hlast := fun i hi => by
      have H := a.hlast i hi
      constructor
      ·
        rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le)]
        refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
        rw [dist_eq_norm] at H
        convert H.1 using 2
        abel
      ·
        rw [← mul_assocₓ, mul_commₓ τ, mul_assocₓ]
        refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
        exact H.2,
    inter := fun i hi => by
      have H := a.inter i hi
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (a.rpos _).le), ← mul_addₓ]
      refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (a.rpos _).le)
      rw [dist_eq_norm] at H
      convert H using 2
      abel }

theorem center_and_rescale_center : a.center_and_rescale.c (last N) = 0 := by
  simp [satellite_config.center_and_rescale]

theorem center_and_rescale_radius {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) : a.center_and_rescale.r (last N) = 1 :=
  by
  simp [satellite_config.center_and_rescale, inv_mul_cancel (a.rpos _).ne']

end SatelliteConfig

/-! ### Disjoint balls of radius close to `1` in the radius `2` ball. -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The maximum cardinality of a `1`-separated set in the ball of radius `2`. This is also the\noptimal number of families in the Besicovitch covering theorem. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `multiplicity [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`E] [":" (Term.type "Type" [(Level.hole "_")])] [] ")")
    (Term.instBinder "[" [] (Term.app `NormedGroup [`E]) "]")]
   [])
  (Command.declValSimple
   ":="
   (Term.app
    `Sup
    [(Set.«term{_|_}»
      "{"
      `N
      "|"
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Finset [`E])]))
       ","
       («term_∧_»
        («term_=_» `s.card "=" `N)
        "∧"
        («term_∧_»
         (Term.forall
          "∀"
          []
          ","
          (Mathlib.ExtendedBinder.«term∀___,_»
           "∀"
           `c
           («binderTerm∈_» "∈" `s)
           ","
           (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))
         "∧"
         (Term.forall
          "∀"
          []
          ","
          (Mathlib.ExtendedBinder.«term∀___,_»
           "∀"
           `c
           («binderTerm∈_» "∈" `s)
           ","
           (Term.forall
            "∀"
            []
            ","
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `d
              («binderTerm∈_» "∈" `s)
              ","
              (Term.forall
               "∀"
               []
               ","
               (Term.arrow
                («term_≠_» `c "≠" `d)
                "→"
                («term_≤_»
                 (numLit "1")
                 "≤"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))))))))))
      "}")])
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
  (Term.app
   `Sup
   [(Set.«term{_|_}»
     "{"
     `N
     "|"
     («term∃_,_»
      "∃"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Finset [`E])]))
      ","
      («term_∧_»
       («term_=_» `s.card "=" `N)
       "∧"
       («term_∧_»
        (Term.forall
         "∀"
         []
         ","
         (Mathlib.ExtendedBinder.«term∀___,_»
          "∀"
          `c
          («binderTerm∈_» "∈" `s)
          ","
          (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))
        "∧"
        (Term.forall
         "∀"
         []
         ","
         (Mathlib.ExtendedBinder.«term∀___,_»
          "∀"
          `c
          («binderTerm∈_» "∈" `s)
          ","
          (Term.forall
           "∀"
           []
           ","
           (Term.forall
            "∀"
            []
            ","
            (Mathlib.ExtendedBinder.«term∀___,_»
             "∀"
             `d
             («binderTerm∈_» "∈" `s)
             ","
             (Term.forall
              "∀"
              []
              ","
              (Term.arrow
               («term_≠_» `c "≠" `d)
               "→"
               («term_≤_»
                (numLit "1")
                "≤"
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))))))))))
     "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `N
   "|"
   («term∃_,_»
    "∃"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Finset [`E])]))
    ","
    («term_∧_»
     («term_=_» `s.card "=" `N)
     "∧"
     («term_∧_»
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `c
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))
      "∧"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `c
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall
         "∀"
         []
         ","
         (Term.forall
          "∀"
          []
          ","
          (Mathlib.ExtendedBinder.«term∀___,_»
           "∀"
           `d
           («binderTerm∈_» "∈" `s)
           ","
           (Term.forall
            "∀"
            []
            ","
            (Term.arrow
             («term_≠_» `c "≠" `d)
             "→"
             («term_≤_»
              (numLit "1")
              "≤"
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))))))))))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Finset [`E])]))
   ","
   («term_∧_»
    («term_=_» `s.card "=" `N)
    "∧"
    («term_∧_»
     (Term.forall
      "∀"
      []
      ","
      (Mathlib.ExtendedBinder.«term∀___,_»
       "∀"
       `c
       («binderTerm∈_» "∈" `s)
       ","
       (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))
     "∧"
     (Term.forall
      "∀"
      []
      ","
      (Mathlib.ExtendedBinder.«term∀___,_»
       "∀"
       `c
       («binderTerm∈_» "∈" `s)
       ","
       (Term.forall
        "∀"
        []
        ","
        (Term.forall
         "∀"
         []
         ","
         (Mathlib.ExtendedBinder.«term∀___,_»
          "∀"
          `d
          («binderTerm∈_» "∈" `s)
          ","
          (Term.forall
           "∀"
           []
           ","
           (Term.arrow
            («term_≠_» `c "≠" `d)
            "→"
            («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   («term_=_» `s.card "=" `N)
   "∧"
   («term_∧_»
    (Term.forall
     "∀"
     []
     ","
     (Mathlib.ExtendedBinder.«term∀___,_»
      "∀"
      `c
      («binderTerm∈_» "∈" `s)
      ","
      (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))
    "∧"
    (Term.forall
     "∀"
     []
     ","
     (Mathlib.ExtendedBinder.«term∀___,_»
      "∀"
      `c
      («binderTerm∈_» "∈" `s)
      ","
      (Term.forall
       "∀"
       []
       ","
       (Term.forall
        "∀"
        []
        ","
        (Mathlib.ExtendedBinder.«term∀___,_»
         "∀"
         `d
         («binderTerm∈_» "∈" `s)
         ","
         (Term.forall
          "∀"
          []
          ","
          (Term.arrow
           («term_≠_» `c "≠" `d)
           "→"
           («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥")))))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   (Term.forall
    "∀"
    []
    ","
    (Mathlib.ExtendedBinder.«term∀___,_»
     "∀"
     `c
     («binderTerm∈_» "∈" `s)
     ","
     (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))
   "∧"
   (Term.forall
    "∀"
    []
    ","
    (Mathlib.ExtendedBinder.«term∀___,_»
     "∀"
     `c
     («binderTerm∈_» "∈" `s)
     ","
     (Term.forall
      "∀"
      []
      ","
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `d
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall
         "∀"
         []
         ","
         (Term.arrow
          («term_≠_» `c "≠" `d)
          "→"
          («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   []
   ","
   (Mathlib.ExtendedBinder.«term∀___,_»
    "∀"
    `c
    («binderTerm∈_» "∈" `s)
    ","
    (Term.forall
     "∀"
     []
     ","
     (Term.forall
      "∀"
      []
      ","
      (Mathlib.ExtendedBinder.«term∀___,_»
       "∀"
       `d
       («binderTerm∈_» "∈" `s)
       ","
       (Term.forall
        "∀"
        []
        ","
        (Term.arrow
         («term_≠_» `c "≠" `d)
         "→"
         («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥")))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.ExtendedBinder.«term∀___,_»
   "∀"
   `c
   («binderTerm∈_» "∈" `s)
   ","
   (Term.forall
    "∀"
    []
    ","
    (Term.forall
     "∀"
     []
     ","
     (Mathlib.ExtendedBinder.«term∀___,_»
      "∀"
      `d
      («binderTerm∈_» "∈" `s)
      ","
      (Term.forall
       "∀"
       []
       ","
       (Term.arrow
        («term_≠_» `c "≠" `d)
        "→"
        («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.ExtendedBinder.«term∀___,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   []
   ","
   (Term.forall
    "∀"
    []
    ","
    (Mathlib.ExtendedBinder.«term∀___,_»
     "∀"
     `d
     («binderTerm∈_» "∈" `s)
     ","
     (Term.forall
      "∀"
      []
      ","
      (Term.arrow
       («term_≠_» `c "≠" `d)
       "→"
       («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥")))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   []
   ","
   (Mathlib.ExtendedBinder.«term∀___,_»
    "∀"
    `d
    («binderTerm∈_» "∈" `s)
    ","
    (Term.forall
     "∀"
     []
     ","
     (Term.arrow
      («term_≠_» `c "≠" `d)
      "→"
      («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.ExtendedBinder.«term∀___,_»
   "∀"
   `d
   («binderTerm∈_» "∈" `s)
   ","
   (Term.forall
    "∀"
    []
    ","
    (Term.arrow
     («term_≠_» `c "≠" `d)
     "→"
     («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.ExtendedBinder.«term∀___,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   []
   ","
   (Term.arrow
    («term_≠_» `c "≠" `d)
    "→"
    («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   («term_≠_» `c "≠" `d)
   "→"
   («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `c "-" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  («term_≠_» `c "≠" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«binderTerm∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«binderTerm∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  (Term.forall
   "∀"
   []
   ","
   (Mathlib.ExtendedBinder.«term∀___,_»
    "∀"
    `c
    («binderTerm∈_» "∈" `s)
    ","
    (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.ExtendedBinder.«term∀___,_»
   "∀"
   `c
   («binderTerm∈_» "∈" `s)
   ","
   (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.ExtendedBinder.«term∀___,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«binderTerm∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 0, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.forall
   "∀"
   []
   ","
   (Mathlib.ExtendedBinder.«term∀___,_»
    "∀"
    `c
    («binderTerm∈_» "∈" `s)
    ","
    (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  («term_=_» `s.card "=" `N)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `N
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `s.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset [`E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
    The maximum cardinality of a `1`-separated set in the ball of radius `2`. This is also the
    optimal number of families in the Besicovitch covering theorem. -/
  def
    multiplicity
    ( E : Type _ ) [ NormedGroup E ]
    :=
      Sup
        {
          N
          |
          ∃
            s : Finset E
            ,
            s.card = N ∧ ∀ , ∀ c ∈ s , ∀ , ∥ c ∥ ≤ 2 ∧ ∀ , ∀ c ∈ s , ∀ , ∀ , ∀ d ∈ s , ∀ , c ≠ d → 1 ≤ ∥ c - d ∥
          }

section

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (c «expr ∈ » s)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Any `1`-separated set in the ball of radius `2` has cardinality at most `5 ^ dim`. This is\nuseful to show that the supremum in the definition of `besicovitch.multiplicity E` is\nwell behaved. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `card_le_of_separated [])
  (Command.declSig
   [(Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`E])] [] ")")
    (Term.explicitBinder
     "("
     [`hs]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `c
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall "∀" [] "," («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `c "∥") "≤" (numLit "2")))))]
     []
     ")")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `c
        («binderTerm∈_» "∈" `s)
        ","
        (Term.forall
         "∀"
         []
         ","
         (Mathlib.ExtendedBinder.«term∀___,_»
          "∀"
          `d
          («binderTerm∈_» "∈" `s)
          ","
          (Term.forall
           "∀"
           []
           ","
           (Term.arrow
            («term_≠_» `c "≠" `d)
            "→"
            («term_≤_» (numLit "1") "≤" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `c "-" `d) "∥"))))))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     `s.card
     "≤"
     (Cardinal.SetTheory.Cofinality.«term_^_» (numLit "5") "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `MeasurableSpace [`E]))]
           ":="
           (Term.app `borel [`E]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `BorelSpace [`E]))]
           ":="
           (Term.anonymousCtor "⟨" [`rfl] "⟩"))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl (Term.letIdDecl `μ [(Term.typeSpec ":" (Term.app `Measureₓ [`E]))] ":=" `measure.add_haar)))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `δ
           [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
           ":="
           («term_/_»
            (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
            "/"
            (numLit "2")))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `ρ
           [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
           ":="
           («term_/_»
            (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
            "/"
            (numLit "2")))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`ρpos []]
           [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `ρ))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `ρ)] "]"] []) [])]))))))
        [])
       (group
        (Tactic.set
         "set"
         `A
         []
         ":="
         (Set.Data.Set.Lattice.«term⋃_,_»
          "⋃"
          (Lean.explicitBinders
           [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `c)] ":" (Term.hole "_") ")")
            (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `c " ∈ " `s) ")")])
          ", "
          (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))
         ["with" [] `hA])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`D []]
           [(Term.typeSpec
             ":"
             (Term.app
              `Set.Pairwise
              [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")
               (Function.Init.Function.term_on_
                `Disjoint
                " on "
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`c] [])]
                  "=>"
                  (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))))]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one (Tactic.rcasesPat.one `c))
                  (Tactic.rintroPat.one (Tactic.rcasesPat.one `hc))
                  (Tactic.rintroPat.one (Tactic.rcasesPat.one `d))
                  (Tactic.rintroPat.one (Tactic.rcasesPat.one `hd))
                  (Tactic.rintroPat.one (Tactic.rcasesPat.one `hcd))]
                 [])
                [])
               (group (Tactic.apply "apply" `ball_disjoint_ball) [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm)] "]") []) [])
               (group (Tactic.convert "convert" [] (Term.app `h [`c `hc `d `hd `hcd]) []) [])
               (group (Lean.Tactic.normNum "norm_num" [] []) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`A_subset []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_⊆_»
              `A
              " ⊆ "
              (Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `bUnion_subset
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
                [])
               (group (Tactic.apply "apply" `ball_subset_ball') [])
               (group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_≤_»
                    (Init.Logic.«term_+_» `δ "+" (Term.app `dist [`x (numLit "0")]))
                    "≤"
                    (Init.Logic.«term_+_» `δ "+" (numLit "2")))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_zero_right)] "]") [])
                        [])
                       (group (Tactic.exact "exact" (Term.app `add_le_add [`le_rfl (Term.app `hs [`x `hx])])) [])]))))
                  (calcStep
                   («term_=_» (Term.hole "_") "=" («term_/_» (numLit "5") "/" (numLit "2")))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`I []]
           [(Term.typeSpec
             ":"
             («term_≤_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Finset.Data.Finset.Fold.«term_*_»
                (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
                "*"
                (Term.app
                 `Ennreal.ofReal
                 [(Cardinal.SetTheory.Cofinality.«term_^_»
                   `δ
                   "^"
                   (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
               "*"
               (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
              "≤"
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.app
                `Ennreal.ofReal
                [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
               "*"
               (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))))]
           ":="
           (calc
            "calc"
            [(calcStep
              («term_=_»
               (Finset.Data.Finset.Fold.«term_*_»
                (Finset.Data.Finset.Fold.«term_*_»
                 (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
                 "*"
                 (Term.app
                  `Ennreal.ofReal
                  [(Cardinal.SetTheory.Cofinality.«term_^_»
                    `δ
                    "^"
                    (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
                "*"
                (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
               "="
               (Term.app `μ [`A]))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `hA)
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app
                        `measure_bUnion_finset
                        [`D
                         (Term.fun
                          "fun"
                          (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" `measurable_set_ball))]))]
                     "]")
                    [])
                   [])
                  (group
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`I []]
                      [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `δ))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))))
                   [])
                  (group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `I]))
                      ","
                      (Tactic.simpLemma [] [] `one_div)
                      ","
                      (Tactic.simpLemma [] [] `one_pow)
                      ","
                      (Tactic.simpLemma [] [] `Finset.sum_const)
                      ","
                      (Tactic.simpLemma [] [] `nsmul_eq_mul)
                      ","
                      (Tactic.simpLemma [] [] `div_pow)
                      ","
                      (Tactic.simpLemma [] [] `mul_assocₓ)]
                     "]"]
                    [])
                   [])]))))
             (calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               (Term.app `μ [(Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])]))
              ":="
              (Term.app `measure_mono [`A_subset]))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Finset.Data.Finset.Fold.«term_*_»
                (Term.app
                 `Ennreal.ofReal
                 [(Cardinal.SetTheory.Cofinality.«term_^_»
                   `ρ
                   "^"
                   (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
                "*"
                (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `ρpos]))] "]"]
                    [])
                   [])]))))]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`J []]
           [(Term.typeSpec
             ":"
             («term_≤_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
               "*"
               (Term.app
                `Ennreal.ofReal
                [(Cardinal.SetTheory.Cofinality.«term_^_»
                  `δ
                  "^"
                  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
              "≤"
              (Term.app
               `Ennreal.ofReal
               [(Cardinal.SetTheory.Cofinality.«term_^_»
                 `ρ
                 "^"
                 (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])))]
           ":="
           (Term.app
            (Term.proj
             (Term.app
              `Ennreal.mul_le_mul_right
              [(Term.proj (Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) "." `ne')
               `measure_ball_lt_top.ne])
             "."
             (fieldIdx "1"))
            [`I]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`K []]
           [(Term.typeSpec
             ":"
             («term_≤_»
              (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
              "≤"
              (Cardinal.SetTheory.Cofinality.«term_^_»
               (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
               "^"
               (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simpa
                 "simpa"
                 []
                 []
                 ["[" [(Tactic.simpLemma [] [] `Ennreal.to_real_mul) "," (Tactic.simpLemma [] [] `div_eq_mul_inv)] "]"]
                 []
                 ["using"
                  (Term.app `Ennreal.to_real_le_of_le_of_real [(Term.app `pow_nonneg [`ρpos.le (Term.hole "_")]) `J])])
                [])]))))))
        [])
       (group (Tactic.exactModCast "exact_mod_cast" `K) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl `this' [] [(Term.typeSpec ":" (Term.app `MeasurableSpace [`E]))] ":=" (Term.app `borel [`E]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this'
          []
          [(Term.typeSpec ":" (Term.app `BorelSpace [`E]))]
          ":="
          (Term.anonymousCtor "⟨" [`rfl] "⟩"))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl (Term.letIdDecl `μ [(Term.typeSpec ":" (Term.app `Measureₓ [`E]))] ":=" `measure.add_haar)))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `δ
          [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
          ":="
          («term_/_»
           (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
           "/"
           (numLit "2")))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `ρ
          [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
          ":="
          («term_/_»
           (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
           "/"
           (numLit "2")))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`ρpos []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `ρ))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `ρ)] "]"] []) [])]))))))
       [])
      (group
       (Tactic.set
        "set"
        `A
        []
        ":="
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `c)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `c " ∈ " `s) ")")])
         ", "
         (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))
        ["with" [] `hA])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`D []]
          [(Term.typeSpec
            ":"
            (Term.app
             `Set.Pairwise
             [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")
              (Function.Init.Function.term_on_
               `Disjoint
               " on "
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`c] [])]
                 "=>"
                 (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))))]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `c))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `hc))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `d))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `hd))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `hcd))]
                [])
               [])
              (group (Tactic.apply "apply" `ball_disjoint_ball) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm)] "]") []) [])
              (group (Tactic.convert "convert" [] (Term.app `h [`c `hc `d `hd `hcd]) []) [])
              (group (Lean.Tactic.normNum "norm_num" [] []) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`A_subset []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_⊆_»
             `A
             " ⊆ "
             (Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `bUnion_subset
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
               [])
              (group (Tactic.apply "apply" `ball_subset_ball') [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_≤_»
                   (Init.Logic.«term_+_» `δ "+" (Term.app `dist [`x (numLit "0")]))
                   "≤"
                   (Init.Logic.«term_+_» `δ "+" (numLit "2")))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_zero_right)] "]") [])
                       [])
                      (group (Tactic.exact "exact" (Term.app `add_le_add [`le_rfl (Term.app `hs [`x `hx])])) [])]))))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" («term_/_» (numLit "5") "/" (numLit "2")))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`I []]
          [(Term.typeSpec
            ":"
            («term_≤_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
               "*"
               (Term.app
                `Ennreal.ofReal
                [(Cardinal.SetTheory.Cofinality.«term_^_»
                  `δ
                  "^"
                  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
              "*"
              (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
             "≤"
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app
               `Ennreal.ofReal
               [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
              "*"
              (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))))]
          ":="
          (calc
           "calc"
           [(calcStep
             («term_=_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Finset.Data.Finset.Fold.«term_*_»
                (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
                "*"
                (Term.app
                 `Ennreal.ofReal
                 [(Cardinal.SetTheory.Cofinality.«term_^_»
                   `δ
                   "^"
                   (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
               "*"
               (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
              "="
              (Term.app `μ [`A]))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `hA)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app
                       `measure_bUnion_finset
                       [`D
                        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" `measurable_set_ball))]))]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`I []]
                     [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `δ))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))))
                  [])
                 (group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `I]))
                     ","
                     (Tactic.simpLemma [] [] `one_div)
                     ","
                     (Tactic.simpLemma [] [] `one_pow)
                     ","
                     (Tactic.simpLemma [] [] `Finset.sum_const)
                     ","
                     (Tactic.simpLemma [] [] `nsmul_eq_mul)
                     ","
                     (Tactic.simpLemma [] [] `div_pow)
                     ","
                     (Tactic.simpLemma [] [] `mul_assocₓ)]
                    "]"]
                   [])
                  [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              (Term.app `μ [(Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])]))
             ":="
             (Term.app `measure_mono [`A_subset]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.app
                `Ennreal.ofReal
                [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
               "*"
               (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `ρpos]))] "]"]
                   [])
                  [])]))))]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`J []]
          [(Term.typeSpec
            ":"
            («term_≤_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
              "*"
              (Term.app
               `Ennreal.ofReal
               [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
             "≤"
             (Term.app
              `Ennreal.ofReal
              [(Cardinal.SetTheory.Cofinality.«term_^_»
                `ρ
                "^"
                (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])))]
          ":="
          (Term.app
           (Term.proj
            (Term.app
             `Ennreal.mul_le_mul_right
             [(Term.proj (Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) "." `ne')
              `measure_ball_lt_top.ne])
            "."
            (fieldIdx "1"))
           [`I]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`K []]
          [(Term.typeSpec
            ":"
            («term_≤_»
             (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
             "≤"
             (Cardinal.SetTheory.Cofinality.«term_^_»
              (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
              "^"
              (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simpa
                "simpa"
                []
                []
                ["[" [(Tactic.simpLemma [] [] `Ennreal.to_real_mul) "," (Tactic.simpLemma [] [] `div_eq_mul_inv)] "]"]
                []
                ["using"
                 (Term.app `Ennreal.to_real_le_of_le_of_real [(Term.app `pow_nonneg [`ρpos.le (Term.hole "_")]) `J])])
               [])]))))))
       [])
      (group (Tactic.exactModCast "exact_mod_cast" `K) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exactModCast "exact_mod_cast" `K)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exactModCast', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`K []]
     [(Term.typeSpec
       ":"
       («term_≤_»
        (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
        "≤"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
         "^"
         (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simpa
           "simpa"
           []
           []
           ["[" [(Tactic.simpLemma [] [] `Ennreal.to_real_mul) "," (Tactic.simpLemma [] [] `div_eq_mul_inv)] "]"]
           []
           ["using"
            (Term.app `Ennreal.to_real_le_of_le_of_real [(Term.app `pow_nonneg [`ρpos.le (Term.hole "_")]) `J])])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpa
        "simpa"
        []
        []
        ["[" [(Tactic.simpLemma [] [] `Ennreal.to_real_mul) "," (Tactic.simpLemma [] [] `div_eq_mul_inv)] "]"]
        []
        ["using" (Term.app `Ennreal.to_real_le_of_le_of_real [(Term.app `pow_nonneg [`ρpos.le (Term.hole "_")]) `J])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   []
   ["[" [(Tactic.simpLemma [] [] `Ennreal.to_real_mul) "," (Tactic.simpLemma [] [] `div_eq_mul_inv)] "]"]
   []
   ["using" (Term.app `Ennreal.to_real_le_of_le_of_real [(Term.app `pow_nonneg [`ρpos.le (Term.hole "_")]) `J])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Ennreal.to_real_le_of_le_of_real [(Term.app `pow_nonneg [`ρpos.le (Term.hole "_")]) `J])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `J
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `pow_nonneg [`ρpos.le (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `ρpos.le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pow_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `pow_nonneg [`ρpos.le (Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ennreal.to_real_le_of_le_of_real
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `div_eq_mul_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Ennreal.to_real_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "≤"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
    "^"
    (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "^"
   (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finrank
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "5")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   (Term.paren "(" [(numLit "5") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "^"
   (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `s.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`J []]
     [(Term.typeSpec
       ":"
       («term_≤_»
        (Finset.Data.Finset.Fold.«term_*_»
         (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
         "*"
         (Term.app
          `Ennreal.ofReal
          [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
        "≤"
        (Term.app
         `Ennreal.ofReal
         [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])))]
     ":="
     (Term.app
      (Term.proj
       (Term.app
        `Ennreal.mul_le_mul_right
        [(Term.proj (Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) "." `ne') `measure_ball_lt_top.ne])
       "."
       (fieldIdx "1"))
      [`I]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     `Ennreal.mul_le_mul_right
     [(Term.proj (Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) "." `ne') `measure_ball_lt_top.ne])
    "."
    (fieldIdx "1"))
   [`I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app
    `Ennreal.mul_le_mul_right
    [(Term.proj (Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) "." `ne') `measure_ball_lt_top.ne])
   "."
   (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `Ennreal.mul_le_mul_right
   [(Term.proj (Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) "." `ne') `measure_ball_lt_top.ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `measure_ball_lt_top.ne
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) "." `ne')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_lt_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ.add_haar_ball_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ennreal.mul_le_mul_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Ennreal.mul_le_mul_right
   [(Term.proj (Term.paren "(" [(Term.app `μ.add_haar_ball_pos [(Term.hole "_") `zero_lt_one]) []] ")") "." `ne')
    `measure_ball_lt_top.ne])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
    "*"
    (Term.app
     `Ennreal.ofReal
     [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
   "≤"
   (Term.app
    `Ennreal.ofReal
    [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Ennreal.ofReal
   [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finrank
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `ρ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ennreal.ofReal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
   "*"
   (Term.app
    `Ennreal.ofReal
    [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Ennreal.ofReal
   [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finrank
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ennreal.ofReal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Ennreal.«termℝ≥0∞»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `s.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
   "*"
   (Term.app
    `Ennreal.ofReal
    [(Term.paren
      "("
      [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
      ")")]))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`I []]
     [(Term.typeSpec
       ":"
       («term_≤_»
        (Finset.Data.Finset.Fold.«term_*_»
         (Finset.Data.Finset.Fold.«term_*_»
          (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
          "*"
          (Term.app
           `Ennreal.ofReal
           [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
         "*"
         (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
        "≤"
        (Finset.Data.Finset.Fold.«term_*_»
         (Term.app
          `Ennreal.ofReal
          [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
         "*"
         (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))))]
     ":="
     (calc
      "calc"
      [(calcStep
        («term_=_»
         (Finset.Data.Finset.Fold.«term_*_»
          (Finset.Data.Finset.Fold.«term_*_»
           (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
           "*"
           (Term.app
            `Ennreal.ofReal
            [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
          "*"
          (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
         "="
         (Term.app `μ [`A]))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `hA)
                ","
                (Tactic.rwRule
                 []
                 (Term.app
                  `measure_bUnion_finset
                  [`D (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" `measurable_set_ball))]))]
               "]")
              [])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`I []]
                [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `δ))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `I]))
                ","
                (Tactic.simpLemma [] [] `one_div)
                ","
                (Tactic.simpLemma [] [] `one_pow)
                ","
                (Tactic.simpLemma [] [] `Finset.sum_const)
                ","
                (Tactic.simpLemma [] [] `nsmul_eq_mul)
                ","
                (Tactic.simpLemma [] [] `div_pow)
                ","
                (Tactic.simpLemma [] [] `mul_assocₓ)]
               "]"]
              [])
             [])]))))
       (calcStep
        («term_≤_»
         (Term.hole "_")
         "≤"
         (Term.app `μ [(Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])]))
        ":="
        (Term.app `measure_mono [`A_subset]))
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Finset.Data.Finset.Fold.«term_*_»
          (Term.app
           `Ennreal.ofReal
           [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
          "*"
          (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `ρpos]))] "]"]
              [])
             [])]))))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (calc
   "calc"
   [(calcStep
     («term_=_»
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
        "*"
        (Term.app
         `Ennreal.ofReal
         [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
       "*"
       (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
      "="
      (Term.app `μ [`A]))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `hA)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `measure_bUnion_finset
               [`D (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" `measurable_set_ball))]))]
            "]")
           [])
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`I []]
             [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `δ))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))))
          [])
         (group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `I]))
             ","
             (Tactic.simpLemma [] [] `one_div)
             ","
             (Tactic.simpLemma [] [] `one_pow)
             ","
             (Tactic.simpLemma [] [] `Finset.sum_const)
             ","
             (Tactic.simpLemma [] [] `nsmul_eq_mul)
             ","
             (Tactic.simpLemma [] [] `div_pow)
             ","
             (Tactic.simpLemma [] [] `mul_assocₓ)]
            "]"]
           [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Term.app `μ [(Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])]))
     ":="
     (Term.app `measure_mono [`A_subset]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.app
        `Ennreal.ofReal
        [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
       "*"
       (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `ρpos]))] "]"]
           [])
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `ρpos]))] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `ρpos]))] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `ρpos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ρpos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ.add_haar_ball_of_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app
     `Ennreal.ofReal
     [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
    "*"
    (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app
    `Ennreal.ofReal
    [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
   "*"
   (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ball [(numLit "0") (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `ball [(numLit "0") (numLit "1")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app
   `Ennreal.ofReal
   [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finrank
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `ρ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ennreal.ofReal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `measure_mono [`A_subset])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A_subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `measure_mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Term.app `μ [(Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `μ [(Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ρ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `hA)
          ","
          (Tactic.rwRule
           []
           (Term.app
            `measure_bUnion_finset
            [`D (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" `measurable_set_ball))]))]
         "]")
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`I []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `δ))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `I]))
          ","
          (Tactic.simpLemma [] [] `one_div)
          ","
          (Tactic.simpLemma [] [] `one_pow)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_const)
          ","
          (Tactic.simpLemma [] [] `nsmul_eq_mul)
          ","
          (Tactic.simpLemma [] [] `div_pow)
          ","
          (Tactic.simpLemma [] [] `mul_assocₓ)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `I]))
     ","
     (Tactic.simpLemma [] [] `one_div)
     ","
     (Tactic.simpLemma [] [] `one_pow)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_const)
     ","
     (Tactic.simpLemma [] [] `nsmul_eq_mul)
     ","
     (Tactic.simpLemma [] [] `div_pow)
     ","
     (Tactic.simpLemma [] [] `mul_assocₓ)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `div_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nsmul_eq_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_div
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `μ.add_haar_ball_of_pos [(Term.hole "_") `I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ.add_haar_ball_of_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`I []]
     [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `δ))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Tactic.normNum', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (numLit "0") "<" `δ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `hA)
     ","
     (Tactic.rwRule
      []
      (Term.app
       `measure_bUnion_finset
       [`D (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" `measurable_set_ball))]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `measure_bUnion_finset
   [`D (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" `measurable_set_ball))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" `measurable_set_ball))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `measurable_set_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `D
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `measure_bUnion_finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hA
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
     "*"
     (Term.app
      `Ennreal.ofReal
      [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
    "*"
    (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
   "="
   (Term.app `μ [`A]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `μ [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
    "*"
    (Term.app
     `Ennreal.ofReal
     [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
   "*"
   (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ball [(numLit "0") (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `ball [(numLit "0") (numLit "1")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
   "*"
   (Term.app
    `Ennreal.ofReal
    [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Ennreal.ofReal
   [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finrank
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ennreal.ofReal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Ennreal.«termℝ≥0∞»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `s.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
   "*"
   (Term.app
    `Ennreal.ofReal
    [(Term.paren
      "("
      [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
      ")")]))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
      "*"
      (Term.app
       `Ennreal.ofReal
       [(Term.paren
         "("
         [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
         ")")]))
     []]
    ")")
   "*"
   (Term.app `μ [(Term.paren "(" [(Term.app `ball [(numLit "0") (numLit "1")]) []] ")")]))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
     "*"
     (Term.app
      `Ennreal.ofReal
      [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
    "*"
    (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app
     `Ennreal.ofReal
     [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
    "*"
    (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app
    `Ennreal.ofReal
    [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
   "*"
   (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ball [(numLit "0") (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `ball [(numLit "0") (numLit "1")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app
   `Ennreal.ofReal
   [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finrank
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `ρ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `ρ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ennreal.ofReal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
    "*"
    (Term.app
     `Ennreal.ofReal
     [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
   "*"
   (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `μ [(Term.app `ball [(numLit "0") (numLit "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ball [(numLit "0") (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `ball [(numLit "0") (numLit "1")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
   "*"
   (Term.app
    `Ennreal.ofReal
    [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Ennreal.ofReal
   [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finrank
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ennreal.ofReal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Ennreal.«termℝ≥0∞»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `s.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
   "*"
   (Term.app
    `Ennreal.ofReal
    [(Term.paren
      "("
      [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
      ")")]))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Term.paren "(" [`s.card [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
      "*"
      (Term.app
       `Ennreal.ofReal
       [(Term.paren
         "("
         [(Cardinal.SetTheory.Cofinality.«term_^_» `δ "^" (Term.app `finrank [(Data.Real.Basic.termℝ "ℝ") `E])) []]
         ")")]))
     []]
    ")")
   "*"
   (Term.app `μ [(Term.paren "(" [(Term.app `ball [(numLit "0") (numLit "1")]) []] ")")]))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`A_subset []]
     [(Term.typeSpec
       ":"
       (Init.Core.«term_⊆_»
        `A
        " ⊆ "
        (Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.refine'
           "refine'"
           (Term.app
            `bUnion_subset
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
          [])
         (group (Tactic.apply "apply" `ball_subset_ball') [])
         (group
          (tacticCalc_
           "calc"
           [(calcStep
             («term_≤_»
              (Init.Logic.«term_+_» `δ "+" (Term.app `dist [`x (numLit "0")]))
              "≤"
              (Init.Logic.«term_+_» `δ "+" (numLit "2")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_zero_right)] "]") []) [])
                 (group (Tactic.exact "exact" (Term.app `add_le_add [`le_rfl (Term.app `hs [`x `hx])])) [])]))))
            (calcStep
             («term_=_» (Term.hole "_") "=" («term_/_» (numLit "5") "/" (numLit "2")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         `bUnion_subset
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
       [])
      (group (Tactic.apply "apply" `ball_subset_ball') [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (Init.Logic.«term_+_» `δ "+" (Term.app `dist [`x (numLit "0")]))
           "≤"
           (Init.Logic.«term_+_» `δ "+" (numLit "2")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_zero_right)] "]") []) [])
              (group (Tactic.exact "exact" (Term.app `add_le_add [`le_rfl (Term.app `hs [`x `hx])])) [])]))))
         (calcStep
          («term_=_» (Term.hole "_") "=" («term_/_» (numLit "5") "/" (numLit "2")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_≤_»
      (Init.Logic.«term_+_» `δ "+" (Term.app `dist [`x (numLit "0")]))
      "≤"
      (Init.Logic.«term_+_» `δ "+" (numLit "2")))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_zero_right)] "]") []) [])
         (group (Tactic.exact "exact" (Term.app `add_le_add [`le_rfl (Term.app `hs [`x `hx])])) [])]))))
    (calcStep
     («term_=_» (Term.hole "_") "=" («term_/_» (numLit "5") "/" (numLit "2")))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Lean.Tactic.normNum "norm_num" ["[" [(Tactic.simpLemma [] [] `δ)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Tactic.normNum', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" («term_/_» (numLit "5") "/" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (numLit "5") "/" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "5")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_zero_right)] "]") []) [])
      (group (Tactic.exact "exact" (Term.app `add_le_add [`le_rfl (Term.app `hs [`x `hx])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `add_le_add [`le_rfl (Term.app `hs [`x `hx])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `add_le_add [`le_rfl (Term.app `hs [`x `hx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hs [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hs [`x `hx]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `le_rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_le_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_zero_right)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dist_zero_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Init.Logic.«term_+_» `δ "+" (Term.app `dist [`x (numLit "0")]))
   "≤"
   (Init.Logic.«term_+_» `δ "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `δ "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Logic.«term_+_» `δ "+" (Term.app `dist [`x (numLit "0")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dist [`x (numLit "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_» `δ "+" (Term.app `dist [`x (numLit "0")])) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `ball_subset_ball')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ball_subset_ball'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app `bUnion_subset [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bUnion_subset [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bUnion_subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_⊆_»
   `A
   " ⊆ "
   (Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `ρ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ρ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`D []]
     [(Term.typeSpec
       ":"
       (Term.app
        `Set.Pairwise
        [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")
         (Function.Init.Function.term_on_
          `Disjoint
          " on "
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`c] [])]
            "=>"
            (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))))]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rintro
           "rintro"
           [(Tactic.rintroPat.one (Tactic.rcasesPat.one `c))
            (Tactic.rintroPat.one (Tactic.rcasesPat.one `hc))
            (Tactic.rintroPat.one (Tactic.rcasesPat.one `d))
            (Tactic.rintroPat.one (Tactic.rcasesPat.one `hd))
            (Tactic.rintroPat.one (Tactic.rcasesPat.one `hcd))]
           [])
          [])
         (group (Tactic.apply "apply" `ball_disjoint_ball) [])
         (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm)] "]") []) [])
         (group (Tactic.convert "convert" [] (Term.app `h [`c `hc `d `hd `hcd]) []) [])
         (group (Lean.Tactic.normNum "norm_num" [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.one `c))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `hc))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `d))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `hd))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `hcd))]
        [])
       [])
      (group (Tactic.apply "apply" `ball_disjoint_ball) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm)] "]") []) [])
      (group (Tactic.convert "convert" [] (Term.app `h [`c `hc `d `hd `hcd]) []) [])
      (group (Lean.Tactic.normNum "norm_num" [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Lean.Tactic.normNum "norm_num" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Tactic.normNum', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert "convert" [] (Term.app `h [`c `hc `d `hd `hcd]) [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h [`c `hc `d `hd `hcd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hcd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dist_eq_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `ball_disjoint_ball)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ball_disjoint_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one (Tactic.rcasesPat.one `c))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `hc))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `d))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `hd))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `hcd))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Set.Pairwise
   [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")
    (Function.Init.Function.term_on_
     `Disjoint
     " on "
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`c] [])]
       "=>"
       (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Function.term_on_', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Function.term_on_', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Function.term_on_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Function.term_on_', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Function.term_on_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Function.Init.Function.term_on_
   `Disjoint
   " on "
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`c] [])]
     "=>"
     (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Function.term_on_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`c] [])]
    "=>"
    (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 3 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 2, term))
  `Disjoint
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024, (none, [anonymous]) <=? (some 2, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 2, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Function.Init.Function.term_on_
   `Disjoint
   " on "
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`c] [])]
     "=>"
     (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [`E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set.Pairwise
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.set
   "set"
   `A
   []
   ":="
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `c)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `c " ∈ " `s) ")")])
    ", "
    (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))
   ["with" [] `hA])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.set', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `c)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `c " ∈ " `s) ")")])
   ", "
   (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ball [(Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")") `δ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`c [(Term.typeAscription ":" `E)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Any `1`-separated set in the ball of radius `2` has cardinality at most `5 ^ dim`. This is
    useful to show that the supremum in the definition of `besicovitch.multiplicity E` is
    well behaved. -/
  theorem
    card_le_of_separated
    ( s : Finset E ) ( hs : ∀ , ∀ c ∈ s , ∀ , ∥ c ∥ ≤ 2 ) ( h : ∀ , ∀ c ∈ s , ∀ , ∀ d ∈ s , ∀ , c ≠ d → 1 ≤ ∥ c - d ∥ )
      : s.card ≤ 5 ^ finrank ℝ E
    :=
      by
        let this' : MeasurableSpace E := borel E
          let this' : BorelSpace E := ⟨ rfl ⟩
          let μ : Measureₓ E := measure.add_haar
          let δ : ℝ := ( 1 : ℝ ) / 2
          let ρ : ℝ := ( 5 : ℝ ) / 2
          have ρpos : 0 < ρ := by norm_num [ ρ ]
          set A := ⋃ ( c : _ ) ( _ : c ∈ s ) , ball ( c : E ) δ with hA
          have
            D
              : Set.Pairwise ( s : Set E ) Disjoint on fun c => ball ( c : E ) δ
              :=
              by rintro c hc d hd hcd apply ball_disjoint_ball rw [ dist_eq_norm ] convert h c hc d hd hcd norm_num
          have
            A_subset
              : A ⊆ ball ( 0 : E ) ρ
              :=
              by
                refine' bUnion_subset fun x hx => _
                  apply ball_subset_ball'
                  calc
                    δ + dist x 0 ≤ δ + 2 := by rw [ dist_zero_right ] exact add_le_add le_rfl hs x hx
                      _ = 5 / 2 := by norm_num [ δ ]
          have
            I
              :
                ( s.card : ℝ≥0∞ ) * Ennreal.ofReal δ ^ finrank ℝ E * μ ball 0 1
                  ≤
                  Ennreal.ofReal ρ ^ finrank ℝ E * μ ball 0 1
              :=
              calc
                ( s.card : ℝ≥0∞ ) * Ennreal.ofReal δ ^ finrank ℝ E * μ ball 0 1 = μ A
                    :=
                    by
                      rw [ hA , measure_bUnion_finset D fun c hc => measurable_set_ball ]
                        have I : 0 < δ := by norm_num [ δ ]
                        simp
                          only
                          [
                            μ.add_haar_ball_of_pos _ I
                              ,
                              one_div
                              ,
                              one_pow
                              ,
                              Finset.sum_const
                              ,
                              nsmul_eq_mul
                              ,
                              div_pow
                              ,
                              mul_assocₓ
                            ]
                  _ ≤ μ ball ( 0 : E ) ρ := measure_mono A_subset
                  _ = Ennreal.ofReal ρ ^ finrank ℝ E * μ ball 0 1 := by simp only [ μ.add_haar_ball_of_pos _ ρpos ]
          have
            J
              : ( s.card : ℝ≥0∞ ) * Ennreal.ofReal δ ^ finrank ℝ E ≤ Ennreal.ofReal ρ ^ finrank ℝ E
              :=
              Ennreal.mul_le_mul_right μ.add_haar_ball_pos _ zero_lt_one . ne' measure_ball_lt_top.ne . 1 I
          have
            K
              : ( s.card : ℝ ) ≤ ( 5 : ℝ ) ^ finrank ℝ E
              :=
              by
                simpa
                  [ Ennreal.to_real_mul , div_eq_mul_inv ]
                  using Ennreal.to_real_le_of_le_of_real pow_nonneg ρpos.le _ J
          exact_mod_cast K

theorem multiplicity_le : multiplicity E ≤ (5^finrank ℝ E) := by
  apply cSup_le
  ·
    refine'
      ⟨0,
        ⟨∅, by
          simp ⟩⟩
  ·
    rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2

theorem card_le_multiplicity {s : Finset E} (hs : ∀, ∀ c ∈ s, ∀, ∥c∥ ≤ 2)
    (h's : ∀, ∀ c ∈ s, ∀, ∀ d ∈ s, ∀, c ≠ d → 1 ≤ ∥c - d∥) : s.card ≤ multiplicity E := by
  apply le_cSup
  ·
    refine' ⟨5^finrank ℝ E, _⟩
    rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2
  ·
    simp only [mem_set_of_eq, Ne.def]
    exact ⟨s, rfl, hs, h's⟩

variable (E)

/--  If `δ` is small enough, a `(1-δ)`-separated set in the ball of radius `2` also has cardinality
at most `multiplicity E`. -/
theorem exists_good_δ :
    ∃ δ : ℝ,
      0 < δ ∧
        δ < 1 ∧
          ∀ s : Finset E,
            (∀, ∀ c ∈ s, ∀, ∥c∥ ≤ 2) → (∀, ∀ c ∈ s, ∀, ∀ d ∈ s, ∀, c ≠ d → 1 - δ ≤ ∥c - d∥) → s.card ≤ multiplicity E :=
  by
  classical
  by_contra h
  push_neg  at h
  set N := multiplicity E+1 with hN
  have : ∀ δ : ℝ, 0 < δ → ∃ f : Finₓ N → E, (∀ i : Finₓ N, ∥f i∥ ≤ 2) ∧ ∀ i j, i ≠ j → 1 - δ ≤ ∥f i - f j∥ := by
    intro δ hδ
    rcases lt_or_leₓ δ 1 with (hδ' | hδ')
    ·
      rcases h δ hδ hδ' with ⟨s, hs, h's, s_card⟩
      obtain ⟨f, f_inj, hfs⟩ : ∃ f : Finₓ N → E, Function.Injective f ∧ range f ⊆ ↑s
      ·
        have : Fintype.card (Finₓ N) ≤ s.card := by
          simp only [Fintype.card_fin]
          exact s_card
        rcases Function.Embedding.exists_of_card_le_finset this with ⟨f, hf⟩
        exact ⟨f, f.injective, hf⟩
      simp only [range_subset_iff, Finset.mem_coe] at hfs
      refine' ⟨f, fun i => hs _ (hfs i), fun i j hij => h's _ (hfs i) _ (hfs j) (f_inj.ne hij)⟩
    ·
      exact
        ⟨fun i => 0, fun i => by
          simp , fun i j hij => by
          simpa only [norm_zero, sub_nonpos, sub_self]⟩
  choose! F hF using this
  have : ∃ f : Finₓ N → E, (∀ i : Finₓ N, ∥f i∥ ≤ 2) ∧ ∀ i j, i ≠ j → 1 ≤ ∥f i - f j∥ := by
    obtain ⟨u, u_mono, zero_lt_u, hu⟩ :
      ∃ u : ℕ → ℝ, (∀ m n : ℕ, m < n → u n < u m) ∧ (∀ n : ℕ, 0 < u n) ∧ Filter.Tendsto u Filter.atTop (𝓝 0) :=
      exists_seq_strict_anti_tendsto (0 : ℝ)
    have A : ∀ n, F (u n) ∈ closed_ball (0 : Finₓ N → E) 2 := by
      intro n
      simp only [pi_norm_le_iff zero_le_two, mem_closed_ball, dist_zero_right, (hF (u n) (zero_lt_u n)).left,
        forall_const]
    obtain ⟨f, fmem, φ, φ_mono, hf⟩ :
      ∃ f ∈ closed_ball (0 : Finₓ N → E) 2, ∃ φ : ℕ → ℕ, StrictMono φ ∧ tendsto ((F ∘ u) ∘ φ) at_top (𝓝 f) :=
      IsCompact.tendsto_subseq (ProperSpace.is_compact_closed_ball _ _) A
    refine' ⟨f, fun i => _, fun i j hij => _⟩
    ·
      simp only [pi_norm_le_iff zero_le_two, mem_closed_ball, dist_zero_right] at fmem
      exact fmem i
    ·
      have A : tendsto (fun n => ∥F (u (φ n)) i - F (u (φ n)) j∥) at_top (𝓝 ∥f i - f j∥) :=
        ((hf.apply i).sub (hf.apply j)).norm
      have B : tendsto (fun n => 1 - u (φ n)) at_top (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (hu.comp φ_mono.tendsto_at_top)
      rw [sub_zero] at B
      exact le_of_tendsto_of_tendsto' B A fun n => (hF (u (φ n)) (zero_lt_u _)).2 i j hij
  rcases this with ⟨f, hf, h'f⟩
  have finj : Function.Injective f := by
    intro i j hij
    by_contra
    have : 1 ≤ ∥f i - f j∥ := h'f i j h
    simp only [hij, norm_zero, sub_self] at this
    exact lt_irreflₓ _ (this.trans_lt zero_lt_one)
  let s := Finset.image f Finset.univ
  have s_card : s.card = N := by
    ·
      rw [Finset.card_image_of_injective _ finj]
      exact Finset.card_fin N
  have hs : ∀, ∀ c ∈ s, ∀, ∥c∥ ≤ 2 := by
    simp only [hf, forall_apply_eq_imp_iff', forall_const, forall_exists_index, Finset.mem_univ, Finset.mem_image]
  have h's : ∀, ∀ c ∈ s, ∀, ∀ d ∈ s, ∀, c ≠ d → 1 ≤ ∥c - d∥ := by
    simp only [s, forall_apply_eq_imp_iff', forall_exists_index, Finset.mem_univ, Finset.mem_image, Ne.def,
      exists_true_left, forall_apply_eq_imp_iff', forall_true_left]
    intro i j hij
    have : i ≠ j := fun h => by
      rw [h] at hij
      exact hij rfl
    exact h'f i j this
  have : s.card ≤ multiplicity E := card_le_multiplicity hs h's
  rw [s_card, hN] at this
  exact lt_irreflₓ _ ((Nat.lt_succ_selfₓ (multiplicity E)).trans_le this)

/--  A small positive number such that any `1 - δ`-separated set in the ball of radius `2` has
cardinality at most `besicovitch.multiplicity E`. -/
def good_δ : ℝ :=
  (exists_good_δ E).some

theorem good_δ_lt_one : good_δ E < 1 :=
  (exists_good_δ E).some_spec.2.1

/--  A number `τ > 1`, but chosen close enough to `1` so that the construction in the Besicovitch
covering theorem using this parameter `τ` will give the smallest possible number of covering
families. -/
def good_τ : ℝ :=
  1+good_δ E / 4

theorem one_lt_good_τ : 1 < good_τ E := by
  dsimp [good_τ, good_δ]
  linarith [(exists_good_δ E).some_spec.1]

variable {E}

theorem card_le_multiplicity_of_δ {s : Finset E} (hs : ∀, ∀ c ∈ s, ∀, ∥c∥ ≤ 2)
    (h's : ∀, ∀ c ∈ s, ∀, ∀ d ∈ s, ∀, c ≠ d → 1 - good_δ E ≤ ∥c - d∥) : s.card ≤ multiplicity E :=
  (Classical.some_spec (exists_good_δ E)).2.2 s hs h's

theorem le_multiplicity_of_δ_of_fin {n : ℕ} (f : Finₓ n → E) (h : ∀ i, ∥f i∥ ≤ 2)
    (h' : ∀ i j, i ≠ j → 1 - good_δ E ≤ ∥f i - f j∥) : n ≤ multiplicity E := by
  classical
  have finj : Function.Injective f := by
    intro i j hij
    by_contra
    have : 1 - good_δ E ≤ ∥f i - f j∥ := h' i j h
    simp only [hij, norm_zero, sub_self] at this
    linarith [good_δ_lt_one E]
  let s := Finset.image f Finset.univ
  have s_card : s.card = n := by
    ·
      rw [Finset.card_image_of_injective _ finj]
      exact Finset.card_fin n
  have hs : ∀, ∀ c ∈ s, ∀, ∥c∥ ≤ 2 := by
    simp only [h, forall_apply_eq_imp_iff', forall_const, forall_exists_index, Finset.mem_univ, Finset.mem_image,
      implies_true_iff]
  have h's : ∀, ∀ c ∈ s, ∀, ∀ d ∈ s, ∀, c ≠ d → 1 - good_δ E ≤ ∥c - d∥ := by
    simp only [s, forall_apply_eq_imp_iff', forall_exists_index, Finset.mem_univ, Finset.mem_image, Ne.def,
      exists_true_left, forall_apply_eq_imp_iff', forall_true_left]
    intro i j hij
    have : i ≠ j := fun h => by
      rw [h] at hij
      exact hij rfl
    exact h' i j this
  have : s.card ≤ multiplicity E := card_le_multiplicity_of_δ hs h's
  rwa [s_card] at this

end

namespace SatelliteConfig

/-!
### Relating satellite configurations to separated points in the ball of radius `2`.

We prove that the number of points in a satellite configuration is bounded by the maximal number
of `1`-separated points in the ball of radius `2`. For this, start from a satellite congifuration
`c`. Without loss of generality, one can assume that the last ball is centered at `0` and of
radius `1`. Define `c' i = c i` if `∥c i∥ ≤ 2`, and `c' i = (2/∥c i∥) • c i` if `∥c i∥ > 2`.
It turns out that these points are `1 - δ`-separated, where `δ` is arbitrarily small if `τ` is
close enough to `1`. The number of such configurations is bounded by `multiplicity E` if `δ` is
suitably small.

To check that the points `c' i` are `1 - δ`-separated, one treats separately the cases where
both `∥c i∥` and `∥c j∥` are `≤ 2`, where one of them is `≤ 2` and the other one is `> 2`, and
where both of them are `> 2`.
-/


theorem exists_normalized_aux1 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ)
    (δ : ℝ) (hδ1 : τ ≤ 1+δ / 4) (hδ2 : δ ≤ 1) (i j : Finₓ N.succ) (inej : i ≠ j) : 1 - δ ≤ ∥a.c i - a.c j∥ := by
  have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ*a.r i) ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ*a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by
    linarith only [hτ, hδ1]
  have D : 0 ≤ 1 - δ / 4 := by
    linarith only [hδ2]
  have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ
  have I : ((1 - δ / 4)*τ) ≤ 1 :=
    calc ((1 - δ / 4)*τ) ≤ (1 - δ / 4)*1+δ / 4 := mul_le_mul_of_nonneg_left hδ1 D
      _ = 1 - (δ^2) / 16 := by
      ring
      _ ≤ 1 := by
      linarith only [sq_nonneg δ]
      
  have J : 1 - δ ≤ 1 - δ / 4 := by
    linarith only [δnonneg]
  have K : 1 - δ / 4 ≤ τ⁻¹ := by
    ·
      rw [inv_eq_one_div, le_div_iff τpos]
      exact I
  suffices L : τ⁻¹ ≤ ∥a.c i - a.c j∥
  ·
    linarith only [J, K, L]
  have hτ' : ∀ k, τ⁻¹ ≤ a.r k := by
    intro k
    rw [inv_eq_one_div, div_le_iff τpos, ← lastr, mul_commₓ]
    exact a.hlast' k hτ
  rcases ah i j inej with (H | H)
  ·
    apply le_transₓ _ H.1
    exact hτ' i
  ·
    rw [norm_sub_rev]
    apply le_transₓ _ H.1
    exact hτ' j

variable [NormedSpace ℝ E]

theorem exists_normalized_aux2 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) (lastc : a.c (last N) = 0)
    (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1+δ / 4) (hδ2 : δ ≤ 1) (i j : Finₓ N.succ) (inej : i ≠ j)
    (hi : ∥a.c i∥ ≤ 2) (hj : 2 < ∥a.c j∥) : 1 - δ ≤ ∥a.c i - (2 / ∥a.c j∥) • a.c j∥ := by
  have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ*a.r i) ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ*a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by
    linarith only [hτ, hδ1]
  have D : 0 ≤ 1 - δ / 4 := by
    linarith only [hδ2]
  have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ
  have hcrj : ∥a.c j∥ ≤ a.r j+1 := by
    simpa only [lastc, lastr, dist_zero_right] using a.inter' j
  have I : a.r i ≤ 2 := by
    rcases lt_or_leₓ i (last N) with (H | H)
    ·
      apply (a.hlast i H).1.trans
      simpa only [dist_eq_norm, lastc, sub_zero] using hi
    ·
      have : i = last N := top_le_iff.1 H
      rw [this, lastr]
      exact one_le_two
  have J : ((1 - δ / 4)*τ) ≤ 1 :=
    calc ((1 - δ / 4)*τ) ≤ (1 - δ / 4)*1+δ / 4 := mul_le_mul_of_nonneg_left hδ1 D
      _ = 1 - (δ^2) / 16 := by
      ring
      _ ≤ 1 := by
      linarith only [sq_nonneg δ]
      
  have A : a.r j - δ ≤ ∥a.c i - a.c j∥ := by
    rcases ah j i inej.symm with (H | H)
    ·
      rw [norm_sub_rev]
      linarith [H.1]
    have C : a.r j ≤ 4 :=
      calc a.r j ≤ τ*a.r i := H.2
        _ ≤ τ*2 := mul_le_mul_of_nonneg_left I τpos.le
        _ ≤ (5 / 4)*2 :=
        mul_le_mul_of_nonneg_right
          (by
            linarith only [hδ1, hδ2])
          zero_le_two
        _ ≤ 4 := by
        norm_num
        
    calc a.r j - δ ≤ a.r j - (a.r j / 4)*δ := by
      refine' sub_le_sub le_rfl _
      refine' mul_le_of_le_one_left δnonneg _
      linarith only [C]_ = (1 - δ / 4)*a.r j := by
      ring _ ≤ (1 - δ / 4)*τ*a.r i := mul_le_mul_of_nonneg_left H.2 D _ ≤ 1*a.r i := by
      rw [← mul_assocₓ]
      apply mul_le_mul_of_nonneg_right J (a.rpos _).le _ ≤ ∥a.c i - a.c j∥ := by
      rw [one_mulₓ]
      exact H.1
  set d := (2 / ∥a.c j∥) • a.c j with hd
  have : a.r j - δ ≤ ∥a.c i - d∥+a.r j - 1 :=
    calc a.r j - δ ≤ ∥a.c i - a.c j∥ := A
      _ ≤ ∥a.c i - d∥+∥d - a.c j∥ := by
      simp only [← dist_eq_norm, dist_triangle]
      _ ≤ ∥a.c i - d∥+a.r j - 1 := by
      apply add_le_add_left
      have A : 0 ≤ 1 - 2 / ∥a.c j∥ := by
        simpa [div_le_iff (zero_le_two.trans_lt hj)] using hj.le
      rw [← one_smul ℝ (a.c j), hd, ← sub_smul, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg A, sub_mul]
      field_simp [(zero_le_two.trans_lt hj).ne']
      linarith only [hcrj]
      
  linarith only [this]

theorem exists_normalized_aux3 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) (lastc : a.c (last N) = 0)
    (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1+δ / 4) (i j : Finₓ N.succ) (inej : i ≠ j)
    (hi : 2 < ∥a.c i∥) (hij : ∥a.c i∥ ≤ ∥a.c j∥) : 1 - δ ≤ ∥(2 / ∥a.c i∥) • a.c i - (2 / ∥a.c j∥) • a.c j∥ := by
  have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ*a.r i) ∨ a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ*a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by
    linarith only [hτ, hδ1]
  have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ
  have hcrj : ∥a.c j∥ ≤ a.r j+1 := by
    simpa only [lastc, lastr, dist_zero_right] using a.inter' j
  have A : a.r i ≤ ∥a.c i∥ := by
    have : i < last N := by
      apply lt_top_iff_ne_top.2
      intro iN
      change i = last N at iN
      rw [iN, lastc, norm_zero] at hi
      exact lt_irreflₓ _ (zero_le_two.trans_lt hi)
    convert (a.hlast i this).1
    rw [dist_eq_norm, lastc, sub_zero]
  have hj : 2 < ∥a.c j∥ := hi.trans_le hij
  set s := ∥a.c i∥ with hs
  have spos : 0 < s := zero_lt_two.trans hi
  set d := (s / ∥a.c j∥) • a.c j with hd
  have I : ∥a.c j - a.c i∥ ≤ (∥a.c j∥ - s)+∥d - a.c i∥ :=
    calc ∥a.c j - a.c i∥ ≤ ∥a.c j - d∥+∥d - a.c i∥ := by
      simp [← dist_eq_norm, dist_triangle]
      _ = (∥a.c j∥ - ∥a.c i∥)+∥d - a.c i∥ := by
      nth_rw 0[← one_smul ℝ (a.c j)]
      rw [add_left_injₓ, hd, ← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg, sub_mul, one_mulₓ,
        div_mul_cancel _ (zero_le_two.trans_lt hj).ne']
      rwa [sub_nonneg, div_le_iff (zero_lt_two.trans hj), one_mulₓ]
      
  have J : a.r j - ∥a.c j - a.c i∥ ≤ (s / 2)*δ :=
    calc a.r j - ∥a.c j - a.c i∥ ≤ s*τ - 1 := by
      rcases ah j i inej.symm with (H | H)
      ·
        calc a.r j - ∥a.c j - a.c i∥ ≤ 0 := sub_nonpos.2 H.1_ ≤ s*τ - 1 := mul_nonneg spos.le (sub_nonneg.2 hτ)
      ·
        rw [norm_sub_rev] at H
        calc a.r j - ∥a.c j - a.c i∥ ≤ (τ*a.r i) - a.r i := sub_le_sub H.2 H.1_ = a.r i*τ - 1 := by
          ring _ ≤ s*τ - 1 := mul_le_mul_of_nonneg_right A (sub_nonneg.2 hτ)
      _ ≤ s*δ / 2 :=
      mul_le_mul_of_nonneg_left
        (by
          linarith only [δnonneg, hδ1])
        spos.le
      _ = (s / 2)*δ := by
      ring
      
  have invs_nonneg : 0 ≤ 2 / s := div_nonneg zero_le_two (zero_le_two.trans hi.le)
  calc 1 - δ = (2 / s)*s / 2 - (s / 2)*δ := by
    field_simp [spos.ne']
    ring _ ≤ (2 / s)*∥d - a.c i∥ :=
    mul_le_mul_of_nonneg_left
      (by
        linarith only [hcrj, I, J, hi])
      invs_nonneg _ = ∥(2 / s) • a.c i - (2 / ∥a.c j∥) • a.c j∥ :=
    by
    conv_lhs => rw [norm_sub_rev, ← abs_of_nonneg invs_nonneg]
    rw [← Real.norm_eq_abs, ← norm_smul, smul_sub, hd, smul_smul]
    congr 3
    field_simp [spos.ne']

theorem exists_normalized {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) (lastc : a.c (last N) = 0)
    (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1+δ / 4) (hδ2 : δ ≤ 1) :
    ∃ c' : Finₓ N.succ → E, (∀ n, ∥c' n∥ ≤ 2) ∧ ∀ i j, i ≠ j → 1 - δ ≤ ∥c' i - c' j∥ := by
  let c' : Finₓ N.succ → E := fun i => if ∥a.c i∥ ≤ 2 then a.c i else (2 / ∥a.c i∥) • a.c i
  have norm_c'_le : ∀ i, ∥c' i∥ ≤ 2 := by
    intro i
    simp only [c']
    split_ifs
    ·
      exact h
    by_cases' hi : ∥a.c i∥ = 0 <;> field_simp [norm_smul, hi]
  refine' ⟨c', fun n => norm_c'_le n, fun i j inej => _⟩
  wlog (discharger := tactic.skip) hij : ∥a.c i∥ ≤ ∥a.c j∥ := le_totalₓ ∥a.c i∥ ∥a.c j∥ using i j, j i
  swap
  ·
    intro i_ne_j
    rw [norm_sub_rev]
    exact this i_ne_j.symm
  rcases le_or_ltₓ ∥a.c j∥ 2 with (Hj | Hj)
  ·
    simp_rw [c', Hj, hij.trans Hj, if_true]
    exact exists_normalized_aux1 a lastr hτ δ hδ1 hδ2 i j inej
  ·
    have H'j : ∥a.c j∥ ≤ 2 ↔ False := by
      simpa only [not_leₓ, iff_falseₓ] using Hj
    rcases le_or_ltₓ ∥a.c i∥ 2 with (Hi | Hi)
    ·
      simp_rw [c', Hi, if_true, H'j, if_false]
      exact exists_normalized_aux2 a lastc lastr hτ δ hδ1 hδ2 i j inej Hi Hj
    ·
      have H'i : ∥a.c i∥ ≤ 2 ↔ False := by
        simpa only [not_leₓ, iff_falseₓ] using Hi
      simp_rw [c', H'i, if_false, H'j, if_false]
      exact exists_normalized_aux3 a lastc lastr hτ δ hδ1 i j inej Hi hij

end SatelliteConfig

variable (E) [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/--  In a normed vector space `E`, there can be no satellite configuration with `multiplicity E + 1`
points and the parameter `good_τ E`. This will ensure that in the inductive construction to get
the Besicovitch covering families, there will never be more than `multiplicity E` nonempty
families. -/
theorem is_empty_satellite_config_multiplicity : IsEmpty (satellite_config E (multiplicity E) (good_τ E)) :=
  ⟨by
    intro a
    let b := a.center_and_rescale
    rcases b.exists_normalized a.center_and_rescale_center a.center_and_rescale_radius (one_lt_good_τ E).le (good_δ E)
        le_rfl (good_δ_lt_one E).le with
      ⟨c', c'_le_two, hc'⟩
    exact lt_irreflₓ _ ((Nat.lt_succ_selfₓ _).trans_le (le_multiplicity_of_δ_of_fin c' c'_le_two hc'))⟩

instance (priority := 100) : HasBesicovitchCovering E :=
  ⟨⟨multiplicity E, good_τ E, one_lt_good_τ E, is_empty_satellite_config_multiplicity E⟩⟩

end Besicovitch

