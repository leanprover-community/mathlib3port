/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module number_theory.well_approximable
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Dynamics.Ergodic.AddCircle
import Mathbin.MeasureTheory.Covering.LiminfLimsup
import Mathbin.Data.Nat.Totient

/-!
# Well-approximable numbers and Gallagher's ergodic theorem

Gallagher's ergodic theorem is a result in metric number theory. It thus belongs to that branch of
mathematics concerning arithmetic properties of real numbers which hold almost eveywhere with
respect to the Lebesgue measure.

Gallagher's theorem concerns the approximation of real numbers by rational numbers. The input is a
sequence of distances `δ₁, δ₂, ...`, and the theorem concerns the set of real numbers `x` for which
there is an infinity of solutions to:
$$
  |x - m/n| < δₙ,
$$
where the rational number `m/n` is in lowest terms. The result is that for any `δ`, this set is
either almost all `x` or almost no `x`.

This result was proved by Gallagher in 1959
[P. Gallagher, *Approximation by reduced fractions*](Gallagher1961). It is formalised here as
`add_circle.add_well_approximable_ae_empty_or_univ` except with `x` belonging to the circle `ℝ ⧸ ℤ`
since this turns out to be more natural.

Given a particular `δ`, the Duffin-Schaeffer conjecture (now a theorem) gives a criterion for
deciding which of the two cases in the conclusion of Gallagher's theorem actually occurs. It was
proved by Koukoulopoulos and Maynard in 2019
[D. Koukoulopoulos, J. Maynard, *On the Duffin-Schaeffer conjecture*](KoukoulopoulosMaynard2020).
We do *not* include a formalisation of the Koukoulopoulos-Maynard result here.

## Main definitions and results:

 * `approx_order_of`: in a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approx_order_of A n δ`
   is the set of elements within a distance `δ` of a point of order `n`.
 * `well_approximable`: in a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`,
   `well_approximable A δ` is the limsup as `n → ∞` of the sets `approx_order_of A n δₙ`. Thus, it
   is the set of points that lie in infinitely many of the sets `approx_order_of A n δₙ`.
 * `add_circle.add_well_approximable_ae_empty_or_univ`: *Gallagher's ergodic theorem* says that for
   for the (additive) circle `𝕊`, for any sequence of distances `δ`, the set
   `add_well_approximable 𝕊 δ` is almost empty or almost full.

## TODO:

The hypothesis `hδ` in `add_circle.add_well_approximable_ae_empty_or_univ` can be dropped.
An elementary (non-measure-theoretic) argument shows that if `¬ hδ` holds then
`add_well_approximable 𝕊 δ = univ` (provided `δ` is non-negative).
-/


open Set Filter Function Metric MeasureTheory

open MeasureTheory TopologicalSpace Pointwise

/-- In a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approx_order_of A n δ` is the set of
elements within a distance `δ` of a point of order `n`. -/
@[to_additive approxAddOrderOf
      "In a seminormed additive group `A`, given `n : ℕ` and `δ : ℝ`,\n`approx_add_order_of A n δ` is the set of elements within a distance `δ` of a point of order `n`."]
def approxOrderOf (A : Type _) [SeminormedGroup A] (n : ℕ) (δ : ℝ) : Set A :=
  thickening δ { y | orderOf y = n }
#align approx_order_of approxOrderOf

@[to_additive mem_approx_add_order_of_iff]
theorem mem_approx_order_of_iff {A : Type _} [SeminormedGroup A] {n : ℕ} {δ : ℝ} {a : A} :
    a ∈ approxOrderOf A n δ ↔ ∃ b : A, orderOf b = n ∧ a ∈ ball b δ := by
  simp only [approxOrderOf, thickening_eq_bUnion_ball, mem_Union₂, mem_set_of_eq, exists_prop]
#align mem_approx_order_of_iff mem_approx_order_of_iff

/-- In a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`, `well_approximable A δ`
is the limsup as `n → ∞` of the sets `approx_order_of A n δₙ`. Thus, it is the set of points that
lie in infinitely many of the sets `approx_order_of A n δₙ`. -/
@[to_additive addWellApproximable
      "In a seminormed additive group `A`, given a sequence of\ndistances `δ₁, δ₂, ...`, `add_well_approximable A δ` is the limsup as `n → ∞` of the sets\n`approx_add_order_of A n δₙ`. Thus, it is the set of points that lie in infinitely many of the sets\n`approx_add_order_of A n δₙ`."]
def wellApproximable (A : Type _) [SeminormedGroup A] (δ : ℕ → ℝ) : Set A :=
  blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n
#align well_approximable wellApproximable

@[to_additive mem_add_well_approximable_iff]
theorem mem_well_approximable_iff {A : Type _} [SeminormedGroup A] {δ : ℕ → ℝ} {a : A} :
    a ∈ wellApproximable A δ ↔
      a ∈ blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n :=
  Iff.rfl
#align mem_well_approximable_iff mem_well_approximable_iff

namespace approxOrderOf

variable {A : Type _} [SeminormedCommGroup A] {a : A} {m n : ℕ} (δ : ℝ)

@[to_additive]
theorem image_pow_subset_of_coprime (hm : 0 < m) (hmn : n.Coprime m) :
    (fun y => y ^ m) '' approxOrderOf A n δ ⊆ approxOrderOf A n (m * δ) :=
  by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hab⟩ := mem_approx_order_of_iff.mp ha
  replace hb : b ^ m ∈ { u : A | orderOf u = n };
  · rw [← hb] at hmn⊢
    exact order_of_pow_coprime hmn
  apply ball_subset_thickening hb ((m : ℝ) • δ)
  convert pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul, Algebra.id.smul_eq_mul]
#align approx_order_of.image_pow_subset_of_coprime approxOrderOf.image_pow_subset_of_coprime

@[to_additive]
theorem image_pow_subset (n : ℕ) (hm : 0 < m) :
    (fun y => y ^ m) '' approxOrderOf A (n * m) δ ⊆ approxOrderOf A n (m * δ) :=
  by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb : orderOf b = n * m, hab : a ∈ ball b δ⟩ := mem_approx_order_of_iff.mp ha
  replace hb : b ^ m ∈ { y : A | orderOf y = n }
  · rw [mem_set_of_eq, order_of_pow' b hm.ne', hb, Nat.gcd_mul_left_left, n.mul_div_cancel hm]
  apply ball_subset_thickening hb (m * δ)
  convert pow_mem_ball hm hab
  simp only [nsmul_eq_mul]
#align approx_order_of.image_pow_subset approxOrderOf.image_pow_subset

@[to_additive]
theorem smul_subset_of_coprime (han : (orderOf a).Coprime n) :
    a • approxOrderOf A n δ ⊆ approxOrderOf A (orderOf a * n) δ :=
  by
  simp_rw [approxOrderOf, thickening_eq_bUnion_ball, ← image_smul, image_Union₂, image_smul,
    smul_ball'', smul_eq_mul, mem_set_of_eq]
  refine' Union₂_subset_iff.mpr fun b hb c hc => _
  simp only [mem_Union, exists_prop]
  refine' ⟨a * b, _, hc⟩
  rw [← hb] at han⊢
  exact (Commute.all a b).order_of_mul_eq_mul_order_of_of_coprime han
#align approx_order_of.smul_subset_of_coprime approxOrderOf.smul_subset_of_coprime

@[to_additive vadd_eq_of_mul_dvd]
theorem smul_eq_of_mul_dvd (hn : 0 < n) (han : orderOf a ^ 2 ∣ n) :
    a • approxOrderOf A n δ = approxOrderOf A n δ :=
  by
  simp_rw [approxOrderOf, thickening_eq_bUnion_ball, ← image_smul, image_Union₂, image_smul,
    smul_ball'', smul_eq_mul, mem_set_of_eq]
  replace han : ∀ {b : A}, orderOf b = n → orderOf (a * b) = n
  · intro b hb
    rw [← hb] at han hn
    rw [sq] at han
    rwa [(Commute.all a b).order_of_mul_eq_right_of_forall_prime_mul_dvd (order_of_pos_iff.mp hn)
        fun p hp hp' => dvd_trans (mul_dvd_mul_right hp' <| orderOf a) han]
  let f : { b : A | orderOf b = n } → { b : A | orderOf b = n } := fun b => ⟨a * b, han b.property⟩
  have hf : surjective f := by
    rintro ⟨b, hb⟩
    refine' ⟨⟨a⁻¹ * b, _⟩, _⟩
    · rw [mem_set_of_eq, ← order_of_inv, mul_inv_rev, inv_inv, mul_comm]
      apply han
      simpa
    · simp only [Subtype.mk_eq_mk, Subtype.coe_mk, mul_inv_cancel_left]
  simpa only [f, mem_set_of_eq, Subtype.coe_mk, Union_coe_set] using
    hf.Union_comp fun b => ball (b : A) δ
#align approx_order_of.smul_eq_of_mul_dvd approxOrderOf.smul_eq_of_mul_dvd

end approxOrderOf

namespace UnitAddCircle

theorem mem_approx_add_order_of_iff {δ : ℝ} {x : UnitAddCircle} {n : ℕ} (hn : 0 < n) :
    x ∈ approxAddOrderOf UnitAddCircle n δ ↔ ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ :=
  by
  haveI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  simp only [mem_approx_add_order_of_iff, mem_set_of_eq, ball, exists_prop, dist_eq_norm,
    AddCircle.add_order_of_eq_pos_iff hn, mul_one]
  constructor
  · rintro ⟨y, ⟨m, hm₁, hm₂, rfl⟩, hx⟩
    exact ⟨m, hm₁, hm₂, hx⟩
  · rintro ⟨m, hm₁, hm₂, hx⟩
    exact ⟨↑((m : ℝ) / n), ⟨m, hm₁, hm₂, rfl⟩, hx⟩
#align unit_add_circle.mem_approx_add_order_of_iff UnitAddCircle.mem_approx_add_order_of_iff

theorem mem_add_well_approximable_iff (δ : ℕ → ℝ) (x : UnitAddCircle) :
    x ∈ addWellApproximable UnitAddCircle δ ↔
      { n : ℕ | ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ n }.Infinite :=
  by
  simp only [mem_add_well_approximable_iff, ← Nat.cofinite_eq_at_top, cofinite.blimsup_set_eq,
    mem_set_of_eq]
  refine' iff_of_eq (congr_arg Set.Infinite <| ext fun n => ⟨fun hn => _, fun hn => _⟩)
  · exact (mem_approx_add_order_of_iff hn.1).mp hn.2
  · have h : 0 < n := by
      obtain ⟨m, hm₁, hm₂, hm₃⟩ := hn
      exact pos_of_gt hm₁
    exact ⟨h, (mem_approx_add_order_of_iff h).mpr hn⟩
#align unit_add_circle.mem_add_well_approximable_iff UnitAddCircle.mem_add_well_approximable_iff

end UnitAddCircle

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

include hT

-- mathport name: «expr ∤ »
local notation a "∤" b => ¬a ∣ b

-- mathport name: «expr ∣∣ »
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.notation
     []
     []
     (Term.attrKind [(Term.local "local")])
     "notation"
     []
     []
     []
     [(Command.identPrec `a []) (str "\"∣∣\"") (Command.identPrec `b [])]
     "=>"
     («term_∧_»
      («term_∣_» `a "∣" `b)
      "∧"
      (AddCircle.NumberTheory.WellApproximable.«term_∤_» («term_*_» `a "*" `a) "∤" `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_∣_» `a "∣" `b)
       "∧"
       (AddCircle.NumberTheory.WellApproximable.«term_∤_» («term_*_» `a "*" `a) "∤" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AddCircle.NumberTheory.WellApproximable.«term_∤_» («term_*_» `a "*" `a) "∤" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AddCircle.NumberTheory.WellApproximable.«term_∤_»', expected 'AddCircle.NumberTheory.WellApproximable.term_∤_._@.NumberTheory.WellApproximable._hyg.11'-/-- failed to format: format: uncaught backtrack exception
local notation a "∣∣" b => a ∣ b ∧ a * a ∤ b

-- mathport name: expr𝕊
local notation "𝕊" => AddCircle T

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "*Gallagher's ergodic theorem* on Diophantine approximation. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `add_well_approximable_ae_empty_or_univ [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`δ]
         [":" (Term.arrow (termℕ "ℕ") "→" (Data.Real.Basic.termℝ "ℝ"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hδ]
         [":"
          (Term.app
           `Tendsto
           [`δ `atTop (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∨_»
         (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_,_»
          "∀ᵐ"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          («term¬_»
           "¬"
           (Term.app
            `addWellApproximable
            [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊") `δ `x])))
         "∨"
         (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_,_»
          "∀ᵐ"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          (Term.app
           `addWellApproximable
           [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊") `δ `x])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `SemilatticeSup [`Nat.Primes]))]
              ":="
              (Term.app `Nat.Subtype.semilatticeSup [(Term.hole "_")]))))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `μ
             [":" (Term.app `Measure [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
             ":="
             `volume
             []))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `u
             [":" (Term.arrow `Nat.Primes "→" (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊"))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`p]
               []
               "=>"
               (coeNotation
                "↑"
                («term_*_»
                 («term_/_»
                  (Term.typeAscription
                   "("
                   (coeNotation "↑" (Term.typeAscription "(" (num "1") ":" [(termℕ "ℕ")] ")"))
                   ":"
                   [(Data.Real.Basic.termℝ "ℝ")]
                   ")")
                  "/"
                  `p)
                 "*"
                 `T))))
             []))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hu₀ []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p]
                 [(Term.typeSpec ":" `Nat.Primes)]
                 ","
                 («term_=_»
                  (Term.app `addOrderOf [(Term.app `u [`p])])
                  "="
                  (Term.typeAscription "(" `p ":" [(termℕ "ℕ")] ")"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `add_order_of_div_of_gcd_eq_one
                    [`hp.pos (Term.app `gcd_one_left [`p])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hu []]
              [(Term.typeSpec
                ":"
                (Term.app `tendsto [(«term_∘_» `addOrderOf "∘" `u) `at_top `at_top]))]
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
                      (Term.typeAscription
                       "("
                       (Term.app `funext [`hu₀])
                       ":"
                       [(«term_=_» («term_∘_» `addOrderOf "∘" `u) "=" `coe)]
                       ")"))]
                    "]")
                   [])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h_mono []]
                     [(Term.typeSpec
                       ":"
                       (Term.app
                        `Monotone
                        [(Term.typeAscription
                          "("
                          `coe
                          ":"
                          [(Term.arrow `Nat.Primes "→" (termℕ "ℕ"))]
                          ")")]))]
                     ":="
                     (Term.fun "fun" (Term.basicFun [`p `q `hpq] [] "=>" `hpq)))))
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `h_mono.tendsto_at_top_at_top
                    [(Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]))
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
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp')])
                         [])]
                       "⟩")])]
                   []
                   [":=" [`n.exists_infinite_primes]])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.anonymousCtor "⟨" [`p "," `hp'] "⟩") "," `hp]
                    "⟩"))]))))))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `E
             []
             ":="
             (Term.app
              `addWellApproximable
              [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊") `δ])
             []))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `X
             [":"
              (Term.arrow
               (termℕ "ℕ")
               "→"
               (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")]))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`n]
               []
               "=>"
               (Term.app
                `approxAddOrderOf
                [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊") `n (Term.app `δ [`n])])))
             []))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `A
             [":"
              (Term.arrow
               (termℕ "ℕ")
               "→"
               (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")]))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`p]
               []
               "=>"
               (Term.app
                `blimsup
                [`X
                 `at_top
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`n]
                   []
                   "=>"
                   («term_∧_»
                    («term_<_» (num "0") "<" `n)
                    "∧"
                    (AddCircle.NumberTheory.WellApproximable.«term_∤_» `p "∤" `n))))])))
             []))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `B
             [":"
              (Term.arrow
               (termℕ "ℕ")
               "→"
               (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")]))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`p]
               []
               "=>"
               (Term.app
                `blimsup
                [`X
                 `at_top
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`n]
                   []
                   "=>"
                   («term_∧_»
                    («term_<_» (num "0") "<" `n)
                    "∧"
                    (AddCircle.NumberTheory.WellApproximable.«term_∣∣_» `p "∣∣" `n))))])))
             []))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `C
             [":"
              (Term.arrow
               (termℕ "ℕ")
               "→"
               (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")]))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`p]
               []
               "=>"
               (Term.app
                `blimsup
                [`X
                 `at_top
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`n]
                   []
                   "=>"
                   («term_∧_»
                    («term_<_» (num "0") "<" `n)
                    "∧"
                    («term_∣_» («term_^_» `p "^" (num "2")) "∣" `n))))])))
             []))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hA₀ []]
              [(Term.typeSpec
                ":"
                (Term.forall "∀" [`p] [] "," (Term.app `MeasurableSet [(Term.app `A [`p])])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`p]
                []
                "=>"
                (Term.app
                 `MeasurableSet.measurable_set_blimsup
                 [(Term.fun
                   "fun"
                   (Term.basicFun [`n `hn] [] "=>" `is_open_thickening.measurable_set))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hB₀ []]
              [(Term.typeSpec
                ":"
                (Term.forall "∀" [`p] [] "," (Term.app `MeasurableSet [(Term.app `B [`p])])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`p]
                []
                "=>"
                (Term.app
                 `MeasurableSet.measurable_set_blimsup
                 [(Term.fun
                   "fun"
                   (Term.basicFun [`n `hn] [] "=>" `is_open_thickening.measurable_set))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hE₀ []]
              [(Term.typeSpec ":" (Term.app `null_measurable_set [`E `μ]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine'
                   "refine'"
                   (Term.proj
                    (Term.app
                     `MeasurableSet.measurable_set_blimsup
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`n `hn]
                        []
                        "=>"
                        (Term.app `IsOpen.measurable_set [(Term.hole "_")])))])
                    "."
                    `NullMeasurableSet))
                  []
                  (Tactic.exact "exact" `is_open_thickening)]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hE₁ []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p]
                 []
                 ","
                 («term_=_»
                  `E
                  "="
                  («term_∪_»
                   («term_∪_» (Term.app `A [`p]) "∪" (Term.app `B [`p]))
                   "∪"
                   (Term.app `C [`p])))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`p])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `E)
                     ","
                     (Tactic.simpLemma [] [] `addWellApproximable)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `blimsup_or_eq_sup)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `and_or_left)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sup_eq_union)
                     ","
                     (Tactic.simpLemma [] [] `sq)]
                    "]"]
                   [])
                  []
                  (Tactic.congr "congr" [])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `funext
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`n]
                       []
                       "=>"
                       («term_<|_»
                        `propext
                        "<|"
                        (Term.app
                         `iff_self_and.mpr
                         [(Term.fun "fun" (Term.basicFun [`hn] [] "=>" (Term.hole "_")))]))))]))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma
                      []
                      []
                      (Term.proj (Term.app `em [(«term_∣_» `p "∣" `n)]) "." `symm))
                     ","
                     (Tactic.simpLemma
                      []
                      []
                      (Term.proj
                       (Term.app `em [(«term_∣_» («term_*_» `p "*" `p) "∣" `n)])
                       "."
                       `symm))
                     ","
                     (Tactic.simpLemma [] [] `or_and_left)
                     ","
                     (Tactic.simpLemma [] [] `or_true_iff)
                     ","
                     (Tactic.simpLemma [] [] `true_and_iff)
                     ","
                     (Tactic.simpLemma [] [] `or_assoc')]
                    "]"]
                   [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hE₂ []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p]
                 [(Term.typeSpec ":" `Nat.Primes)]
                 ","
                 (Term.arrow
                  («term_∧_»
                   (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                    (Term.app `A [`p])
                    " =ᵐ["
                    `μ
                    "] "
                    (Term.typeAscription
                     "("
                     («term∅» "∅")
                     ":"
                     [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                     ")"))
                   "∧"
                   (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                    (Term.app `B [`p])
                    " =ᵐ["
                    `μ
                    "] "
                    (Term.typeAscription
                     "("
                     («term∅» "∅")
                     ":"
                     [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                     ")")))
                  "→"
                  (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                   `E
                   " =ᵐ["
                   `μ
                   "] "
                   (Term.app `C [`p])))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `p))
                    (Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hA)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hB)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hE₁ [`p]))] "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `union_ae_eq_right_of_ae_eq_empty
                    [(Term.app
                      (Term.proj (Term.app `union_ae_eq_right_of_ae_eq_empty [`hA]) "." `trans)
                      [`hB])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hA []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p]
                 [(Term.typeSpec ":" `Nat.Primes)]
                 ","
                 («term_∨_»
                  (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                   (Term.app `A [`p])
                   " =ᵐ["
                   `μ
                   "] "
                   (Term.typeAscription
                    "("
                    («term∅» "∅")
                    ":"
                    [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                    ")"))
                  "∨"
                  (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                   (Term.app `A [`p])
                   " =ᵐ["
                   `μ
                   "] "
                   `univ))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `f
                     []
                     [(Term.typeSpec
                       ":"
                       (Term.arrow
                        (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                        "→"
                        (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")))]
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`y]
                       []
                       "=>"
                       (Algebra.Group.Defs.«term_•_»
                        (Term.typeAscription "(" `p ":" [(termℕ "ℕ")] ")")
                        " • "
                        `y))))))
                  []
                  (Tactic.tacticSuffices_
                   "suffices"
                   (Term.sufficesDecl
                    []
                    («term_⊆_»
                     (Set.Data.Set.Image.term_''_ `f " '' " (Term.app `A [`p]))
                     "⊆"
                     (Term.app
                      `blimsup
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`n]
                         []
                         "=>"
                         (Term.app
                          `approxAddOrderOf
                          [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                           `n
                           («term_*_» `p "*" (Term.app `δ [`n]))])))
                       `at_top
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`n]
                         []
                         "=>"
                         («term_∧_»
                          («term_<_» (num "0") "<" `n)
                          "∧"
                          (AddCircle.NumberTheory.WellApproximable.«term_∤_» `p "∤" `n))))]))
                    (Term.byTactic'
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.apply
                         "apply"
                         (Term.app
                          (Term.proj
                           (Term.app `ergodic_nsmul [`hp.one_lt])
                           "."
                           `ae_empty_or_univ_of_image_ae_le)
                          [(Term.app `hA₀ [`p])]))
                        []
                        (Tactic.apply
                         "apply"
                         (Term.app
                          (Term.proj (Term.app `HasSubset.Subset.eventually_le [`this]) "." `congr)
                          [`eventually_eq.rfl]))
                        []
                        (Tactic.exact
                         "exact"
                         (Term.app
                          `blimsup_thickening_mul_ae_eq
                          [`μ
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`n]
                             []
                             "=>"
                             («term_∧_»
                              («term_<_» (num "0") "<" `n)
                              "∧"
                              (AddCircle.NumberTheory.WellApproximable.«term_∤_» `p "∤" `n))))
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`n]
                             []
                             "=>"
                             (Set.«term{_|_}»
                              "{"
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
                              "|"
                              («term_=_» (Term.app `addOrderOf [`y]) "=" `n)
                              "}")))
                           (Term.app `nat.cast_pos.mpr [`hp.pos])
                           (Term.hole "_")
                           `hδ]))])))))
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.app `SupHom.setImage [`f]) "." `apply_blimsup_le)
                     "."
                     `trans)
                    [(Term.app
                      `mono_blimsup
                      [(Term.fun "fun" (Term.basicFun [`n `hn] [] "=>" (Term.hole "_")))])]))
                  []
                  (Mathlib.Tactic.tacticReplace_
                   "replace"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hn []]
                     []
                     ":="
                     (Term.app
                      `nat.coprime_comm.mp
                      [(Term.app
                        (Term.proj `hp.coprime_iff_not_dvd "." (fieldIdx "2"))
                        [(Term.proj `hn "." (fieldIdx "2"))])]))))
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `approxAddOrderOf.image_nsmul_subset_of_coprime
                    [(Term.app `δ [`n]) `hp.pos `hn]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hB []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p]
                 [(Term.typeSpec ":" `Nat.Primes)]
                 ","
                 («term_∨_»
                  (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                   (Term.app `B [`p])
                   " =ᵐ["
                   `μ
                   "] "
                   (Term.typeAscription
                    "("
                    («term∅» "∅")
                    ":"
                    [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                    ")"))
                  "∨"
                  (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                   (Term.app `B [`p])
                   " =ᵐ["
                   `μ
                   "] "
                   `univ))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `x
                     []
                     []
                     ":="
                     (Term.app `u [(Term.anonymousCtor "⟨" [`p "," `hp] "⟩")]))))
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `f
                     []
                     [(Term.typeSpec
                       ":"
                       (Term.arrow
                        (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                        "→"
                        (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")))]
                     ":="
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`y]
                       []
                       "=>"
                       («term_+_» (Algebra.Group.Defs.«term_•_» `p " • " `y) "+" `x))))))
                  []
                  (Tactic.tacticSuffices_
                   "suffices"
                   (Term.sufficesDecl
                    []
                    («term_⊆_»
                     (Set.Data.Set.Image.term_''_ `f " '' " (Term.app `B [`p]))
                     "⊆"
                     (Term.app
                      `blimsup
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`n]
                         []
                         "=>"
                         (Term.app
                          `approxAddOrderOf
                          [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                           `n
                           («term_*_» `p "*" (Term.app `δ [`n]))])))
                       `at_top
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`n]
                         []
                         "=>"
                         («term_∧_»
                          («term_<_» (num "0") "<" `n)
                          "∧"
                          (AddCircle.NumberTheory.WellApproximable.«term_∣∣_» `p "∣∣" `n))))]))
                    (Term.byTactic'
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.apply
                         "apply"
                         (Term.app
                          (Term.proj
                           (Term.app `ergodic_nsmul_add [`x `hp.one_lt])
                           "."
                           `ae_empty_or_univ_of_image_ae_le)
                          [(Term.app `hB₀ [`p])]))
                        []
                        (Tactic.apply
                         "apply"
                         (Term.app
                          (Term.proj (Term.app `HasSubset.Subset.eventually_le [`this]) "." `congr)
                          [`eventually_eq.rfl]))
                        []
                        (Tactic.exact
                         "exact"
                         (Term.app
                          `blimsup_thickening_mul_ae_eq
                          [`μ
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`n]
                             []
                             "=>"
                             («term_∧_»
                              («term_<_» (num "0") "<" `n)
                              "∧"
                              (AddCircle.NumberTheory.WellApproximable.«term_∣∣_» `p "∣∣" `n))))
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`n]
                             []
                             "=>"
                             (Set.«term{_|_}»
                              "{"
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
                              "|"
                              («term_=_» (Term.app `addOrderOf [`y]) "=" `n)
                              "}")))
                           (Term.app `nat.cast_pos.mpr [`hp.pos])
                           (Term.hole "_")
                           `hδ]))])))))
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.app `SupHom.setImage [`f]) "." `apply_blimsup_le)
                     "."
                     `trans)
                    [(Term.app `mono_blimsup [(Term.hole "_")])]))
                  []
                  (Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))
                    (Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_div)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_ndiv)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h_cop []]
                     [(Term.typeSpec
                       ":"
                       (Term.app
                        (Term.proj (Term.app `addOrderOf [`x]) "." `Coprime)
                        [(«term_/_» `n "/" `p)]))]
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
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `q)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                                [])]
                              "⟩")])]
                          []
                          [":=" [`h_div]])
                         []
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `hu₀)
                            ","
                            (Tactic.rwRule [] `Subtype.coe_mk)
                            ","
                            (Tactic.rwRule [] `hp.coprime_iff_not_dvd)
                            ","
                            (Tactic.rwRule [] (Term.app `q.mul_div_cancel_left [`hp.pos]))]
                           "]")
                          [])
                         []
                         (Tactic.exact
                          "exact"
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`contra]
                            []
                            "=>"
                            (Term.app `h_ndiv [(Term.app `mul_dvd_mul_left [`p `contra])]))))]))))))
                  []
                  (Mathlib.Tactic.tacticReplace_
                   "replace"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h_div []]
                     [(Term.typeSpec
                       ":"
                       («term_=_» («term_*_» («term_/_» `n "/" `p) "*" `p) "=" `n))]
                     ":="
                     (Term.app `Nat.div_mul_cancel [`h_div]))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hf []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        `f
                        "="
                        («term_∘_»
                         (Term.fun "fun" (Term.basicFun [`y] [] "=>" («term_+_» `x "+" `y)))
                         "∘"
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`y]
                           []
                           "=>"
                           (Algebra.Group.Defs.«term_•_» `p " • " `y))))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                         []
                         (Tactic.simp
                          "simp"
                          []
                          []
                          []
                          ["[" [(Tactic.simpLemma [] [] (Term.app `add_comm [`x]))] "]"]
                          [])]))))))
                  []
                  (Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_app)] "]")
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `le_eq_subset)
                     ","
                     (Tactic.rwRule [] `SupHom.set_image_to_fun)
                     ","
                     (Tactic.rwRule [] `hf)
                     ","
                     (Tactic.rwRule [] `image_comp)]
                    "]")
                   [])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     []
                     ":="
                     (Term.app
                      (Term.explicit "@" `monotone_image)
                      [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                       (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                       (Term.fun "fun" (Term.basicFun [`y] [] "=>" («term_+_» `x "+" `y)))]))))
                  []
                  (Tactic.specialize
                   "specialize"
                   (Term.app
                    `this
                    [(Term.app
                      `approxAddOrderOf.image_nsmul_subset
                      [(Term.app `δ [`n]) («term_/_» `n "/" `p) `hp.pos])]))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `h_div)] "]"]
                   [(Tactic.location
                     "at"
                     (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
                  []
                  (Tactic.refine' "refine'" (Term.app `this.trans [(Term.hole "_")]))
                  []
                  (convert
                   "convert"
                   []
                   (Term.app
                    `approxAddOrderOf.vadd_subset_of_coprime
                    [(«term_*_» `p "*" (Term.app `δ [`n])) `h_cop])
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `hu₀)
                     ","
                     (Tactic.simpLemma [] [] `Subtype.coe_mk)
                     ","
                     (Tactic.simpLemma [] [] `h_div)
                     ","
                     (Tactic.simpLemma [] [] (Term.app `mul_comm [`p]))]
                    "]"]
                   [])]))))))
           []
           (Tactic.change
            "change"
            («term_∨_»
             (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_,_»
              "∀ᵐ"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
              ", "
              («term_∉_» `x "∉" `E))
             "∨"
             («term_∈_» `E "∈" `volume.ae))
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eventually_eq_empty)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eventually_eq_univ)]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hC []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p]
                 [(Term.typeSpec ":" `Nat.Primes)]
                 ","
                 («term_=_»
                  (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " (Term.app `C [`p]))
                  "="
                  (Term.app `C [`p]))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`p])
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `e
                     []
                     []
                     ":="
                     (Term.proj
                      (Term.typeAscription
                       "("
                       (Term.app `AddAction.toPerm [(Term.app `u [`p])])
                       ":"
                       [(Term.app
                         `Equiv.Perm
                         [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                       ")")
                      "."
                      `toOrderIsoSet))))
                  []
                  (Tactic.change
                   "change"
                   («term_=_» (Term.app `e [(Term.app `C [`p])]) "=" (Term.app `C [`p]))
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `e.apply_blimsup)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `hu₀ [`p]))]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `blimsup_congr
                    [(Term.app
                      `eventually_of_forall
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`n `hn]
                         []
                         "=>"
                         (Term.app
                          `approxAddOrderOf.vadd_eq_of_mul_dvd
                          [(Term.app `δ [`n])
                           (Term.proj `hn "." (fieldIdx "1"))
                           (Term.proj `hn "." (fieldIdx "2"))])))])]))]))))))
           []
           (Classical.«tacticBy_cases_:_»
            "by_cases"
            [`h ":"]
            (Term.forall
             "∀"
             [`p]
             [(Term.typeSpec ":" `Nat.Primes)]
             ","
             («term_∧_»
              (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
               (Term.app `A [`p])
               " =ᵐ["
               `μ
               "] "
               (Term.typeAscription
                "("
                («term∅» "∅")
                ":"
                [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                ")"))
              "∧"
              (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
               (Term.app `B [`p])
               " =ᵐ["
               `μ
               "] "
               (Term.typeAscription
                "("
                («term∅» "∅")
                ":"
                [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                ")")))))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.replace'
              "replace"
              [`h []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`p]
                 [(Term.typeSpec ":" `Nat.Primes)]
                 ","
                 (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                  (Term.typeAscription
                   "("
                   (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " `E)
                   ":"
                   [(Term.app `Set [(Term.hole "_")])]
                   ")")
                  " =ᵐ["
                  `μ
                  "] "
                  `E)))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.intro "intro" [`p])
               []
               (Mathlib.Tactic.tacticReplace_
                "replace"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hE₂ []]
                  [(Term.typeSpec
                    ":"
                    (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                     `E
                     " =ᵐ["
                     `μ
                     "] "
                     (Term.app `C [`p])))]
                  ":="
                  (Term.app `hE₂ [`p (Term.app `h [`p])]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h_qmp []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `MeasureTheory.Measure.QuasiMeasurePreserving
                     [(Term.app
                       (Term.paren
                        "("
                        (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·"))
                        ")")
                       [(«term-_» "-" (Term.app `u [`p]))])
                      `μ
                      `μ]))]
                  ":="
                  (Term.proj
                   (Term.app `measure_preserving_vadd [(Term.hole "_") `μ])
                   "."
                   `QuasiMeasurePreserving))))
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj
                  (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.app `u [`p]) `hE₂])
                  "."
                  `trans)
                 [(Term.app `ae_eq_trans [(Term.hole "_") `hE₂.symm])]))
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hC)] "]") [])])
             []
             (Tactic.exact
              "exact"
              (Term.app `ae_empty_or_univ_of_forall_vadd_ae_eq_self [`hE₀ `h `hu]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticRight "right")
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `not_forall) "," (Tactic.simpLemma [] [] `not_and_or)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
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
                    [])]
                  "⟩")])]
              []
              [":=" [`h]])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hE₁ [`p]))] "]")
              [])
             []
             (Tactic.cases "cases" [(Tactic.casesTarget [] `hp)] [] [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hA [`p]))] [] [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.contradiction "contradiction")])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `h)
                  ","
                  (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)]
                 "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hB [`p]))] [] [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.contradiction "contradiction")])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `h)
                  ","
                  (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)
                  ","
                  (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_right)]
                 "]"]
                [])])])])))
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
         [(Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `SemilatticeSup [`Nat.Primes]))]
             ":="
             (Term.app `Nat.Subtype.semilatticeSup [(Term.hole "_")]))))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `μ
            [":" (Term.app `Measure [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
            ":="
            `volume
            []))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `u
            [":" (Term.arrow `Nat.Primes "→" (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊"))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`p]
              []
              "=>"
              (coeNotation
               "↑"
               («term_*_»
                («term_/_»
                 (Term.typeAscription
                  "("
                  (coeNotation "↑" (Term.typeAscription "(" (num "1") ":" [(termℕ "ℕ")] ")"))
                  ":"
                  [(Data.Real.Basic.termℝ "ℝ")]
                  ")")
                 "/"
                 `p)
                "*"
                `T))))
            []))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hu₀ []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p]
                [(Term.typeSpec ":" `Nat.Primes)]
                ","
                («term_=_»
                 (Term.app `addOrderOf [(Term.app `u [`p])])
                 "="
                 (Term.typeAscription "(" `p ":" [(termℕ "ℕ")] ")"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `add_order_of_div_of_gcd_eq_one
                   [`hp.pos (Term.app `gcd_one_left [`p])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hu []]
             [(Term.typeSpec
               ":"
               (Term.app `tendsto [(«term_∘_» `addOrderOf "∘" `u) `at_top `at_top]))]
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
                     (Term.typeAscription
                      "("
                      (Term.app `funext [`hu₀])
                      ":"
                      [(«term_=_» («term_∘_» `addOrderOf "∘" `u) "=" `coe)]
                      ")"))]
                   "]")
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h_mono []]
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `Monotone
                       [(Term.typeAscription
                         "("
                         `coe
                         ":"
                         [(Term.arrow `Nat.Primes "→" (termℕ "ℕ"))]
                         ")")]))]
                    ":="
                    (Term.fun "fun" (Term.basicFun [`p `q `hpq] [] "=>" `hpq)))))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `h_mono.tendsto_at_top_at_top
                   [(Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]))
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
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp')])
                        [])]
                      "⟩")])]
                  []
                  [":=" [`n.exists_infinite_primes]])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.anonymousCtor "⟨" [`p "," `hp'] "⟩") "," `hp]
                   "⟩"))]))))))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `E
            []
            ":="
            (Term.app `addWellApproximable [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊") `δ])
            []))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `X
            [":"
             (Term.arrow
              (termℕ "ℕ")
              "→"
              (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")]))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`n]
              []
              "=>"
              (Term.app
               `approxAddOrderOf
               [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊") `n (Term.app `δ [`n])])))
            []))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `A
            [":"
             (Term.arrow
              (termℕ "ℕ")
              "→"
              (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")]))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`p]
              []
              "=>"
              (Term.app
               `blimsup
               [`X
                `at_top
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`n]
                  []
                  "=>"
                  («term_∧_»
                   («term_<_» (num "0") "<" `n)
                   "∧"
                   (AddCircle.NumberTheory.WellApproximable.«term_∤_» `p "∤" `n))))])))
            []))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `B
            [":"
             (Term.arrow
              (termℕ "ℕ")
              "→"
              (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")]))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`p]
              []
              "=>"
              (Term.app
               `blimsup
               [`X
                `at_top
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`n]
                  []
                  "=>"
                  («term_∧_»
                   («term_<_» (num "0") "<" `n)
                   "∧"
                   (AddCircle.NumberTheory.WellApproximable.«term_∣∣_» `p "∣∣" `n))))])))
            []))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `C
            [":"
             (Term.arrow
              (termℕ "ℕ")
              "→"
              (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")]))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`p]
              []
              "=>"
              (Term.app
               `blimsup
               [`X
                `at_top
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`n]
                  []
                  "=>"
                  («term_∧_»
                   («term_<_» (num "0") "<" `n)
                   "∧"
                   («term_∣_» («term_^_» `p "^" (num "2")) "∣" `n))))])))
            []))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hA₀ []]
             [(Term.typeSpec
               ":"
               (Term.forall "∀" [`p] [] "," (Term.app `MeasurableSet [(Term.app `A [`p])])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`p]
               []
               "=>"
               (Term.app
                `MeasurableSet.measurable_set_blimsup
                [(Term.fun
                  "fun"
                  (Term.basicFun [`n `hn] [] "=>" `is_open_thickening.measurable_set))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hB₀ []]
             [(Term.typeSpec
               ":"
               (Term.forall "∀" [`p] [] "," (Term.app `MeasurableSet [(Term.app `B [`p])])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`p]
               []
               "=>"
               (Term.app
                `MeasurableSet.measurable_set_blimsup
                [(Term.fun
                  "fun"
                  (Term.basicFun [`n `hn] [] "=>" `is_open_thickening.measurable_set))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hE₀ []]
             [(Term.typeSpec ":" (Term.app `null_measurable_set [`E `μ]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.proj
                   (Term.app
                    `MeasurableSet.measurable_set_blimsup
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`n `hn]
                       []
                       "=>"
                       (Term.app `IsOpen.measurable_set [(Term.hole "_")])))])
                   "."
                   `NullMeasurableSet))
                 []
                 (Tactic.exact "exact" `is_open_thickening)]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hE₁ []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p]
                []
                ","
                («term_=_»
                 `E
                 "="
                 («term_∪_»
                  («term_∪_» (Term.app `A [`p]) "∪" (Term.app `B [`p]))
                  "∪"
                  (Term.app `C [`p])))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`p])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `E)
                    ","
                    (Tactic.simpLemma [] [] `addWellApproximable)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `blimsup_or_eq_sup)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `and_or_left)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sup_eq_union)
                    ","
                    (Tactic.simpLemma [] [] `sq)]
                   "]"]
                  [])
                 []
                 (Tactic.congr "congr" [])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `funext
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`n]
                      []
                      "=>"
                      («term_<|_»
                       `propext
                       "<|"
                       (Term.app
                        `iff_self_and.mpr
                        [(Term.fun "fun" (Term.basicFun [`hn] [] "=>" (Term.hole "_")))]))))]))
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.proj (Term.app `em [(«term_∣_» `p "∣" `n)]) "." `symm))
                    ","
                    (Tactic.simpLemma
                     []
                     []
                     (Term.proj
                      (Term.app `em [(«term_∣_» («term_*_» `p "*" `p) "∣" `n)])
                      "."
                      `symm))
                    ","
                    (Tactic.simpLemma [] [] `or_and_left)
                    ","
                    (Tactic.simpLemma [] [] `or_true_iff)
                    ","
                    (Tactic.simpLemma [] [] `true_and_iff)
                    ","
                    (Tactic.simpLemma [] [] `or_assoc')]
                   "]"]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hE₂ []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p]
                [(Term.typeSpec ":" `Nat.Primes)]
                ","
                (Term.arrow
                 («term_∧_»
                  (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                   (Term.app `A [`p])
                   " =ᵐ["
                   `μ
                   "] "
                   (Term.typeAscription
                    "("
                    («term∅» "∅")
                    ":"
                    [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                    ")"))
                  "∧"
                  (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                   (Term.app `B [`p])
                   " =ᵐ["
                   `μ
                   "] "
                   (Term.typeAscription
                    "("
                    («term∅» "∅")
                    ":"
                    [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                    ")")))
                 "→"
                 (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                  `E
                  " =ᵐ["
                  `μ
                  "] "
                  (Term.app `C [`p])))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `p))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hA)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hB)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hE₁ [`p]))] "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `union_ae_eq_right_of_ae_eq_empty
                   [(Term.app
                     (Term.proj (Term.app `union_ae_eq_right_of_ae_eq_empty [`hA]) "." `trans)
                     [`hB])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hA []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p]
                [(Term.typeSpec ":" `Nat.Primes)]
                ","
                («term_∨_»
                 (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                  (Term.app `A [`p])
                  " =ᵐ["
                  `μ
                  "] "
                  (Term.typeAscription
                   "("
                   («term∅» "∅")
                   ":"
                   [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                   ")"))
                 "∨"
                 (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                  (Term.app `A [`p])
                  " =ᵐ["
                  `μ
                  "] "
                  `univ))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `f
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.arrow
                       (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                       "→"
                       (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")))]
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`y]
                      []
                      "=>"
                      (Algebra.Group.Defs.«term_•_»
                       (Term.typeAscription "(" `p ":" [(termℕ "ℕ")] ")")
                       " • "
                       `y))))))
                 []
                 (Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   («term_⊆_»
                    (Set.Data.Set.Image.term_''_ `f " '' " (Term.app `A [`p]))
                    "⊆"
                    (Term.app
                     `blimsup
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`n]
                        []
                        "=>"
                        (Term.app
                         `approxAddOrderOf
                         [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                          `n
                          («term_*_» `p "*" (Term.app `δ [`n]))])))
                      `at_top
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`n]
                        []
                        "=>"
                        («term_∧_»
                         («term_<_» (num "0") "<" `n)
                         "∧"
                         (AddCircle.NumberTheory.WellApproximable.«term_∤_» `p "∤" `n))))]))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.apply
                        "apply"
                        (Term.app
                         (Term.proj
                          (Term.app `ergodic_nsmul [`hp.one_lt])
                          "."
                          `ae_empty_or_univ_of_image_ae_le)
                         [(Term.app `hA₀ [`p])]))
                       []
                       (Tactic.apply
                        "apply"
                        (Term.app
                         (Term.proj (Term.app `HasSubset.Subset.eventually_le [`this]) "." `congr)
                         [`eventually_eq.rfl]))
                       []
                       (Tactic.exact
                        "exact"
                        (Term.app
                         `blimsup_thickening_mul_ae_eq
                         [`μ
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`n]
                            []
                            "=>"
                            («term_∧_»
                             («term_<_» (num "0") "<" `n)
                             "∧"
                             (AddCircle.NumberTheory.WellApproximable.«term_∤_» `p "∤" `n))))
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`n]
                            []
                            "=>"
                            (Set.«term{_|_}»
                             "{"
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
                             "|"
                             («term_=_» (Term.app `addOrderOf [`y]) "=" `n)
                             "}")))
                          (Term.app `nat.cast_pos.mpr [`hp.pos])
                          (Term.hole "_")
                          `hδ]))])))))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.proj
                    (Term.proj (Term.app `SupHom.setImage [`f]) "." `apply_blimsup_le)
                    "."
                    `trans)
                   [(Term.app
                     `mono_blimsup
                     [(Term.fun "fun" (Term.basicFun [`n `hn] [] "=>" (Term.hole "_")))])]))
                 []
                 (Mathlib.Tactic.tacticReplace_
                  "replace"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hn []]
                    []
                    ":="
                    (Term.app
                     `nat.coprime_comm.mp
                     [(Term.app
                       (Term.proj `hp.coprime_iff_not_dvd "." (fieldIdx "2"))
                       [(Term.proj `hn "." (fieldIdx "2"))])]))))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `approxAddOrderOf.image_nsmul_subset_of_coprime
                   [(Term.app `δ [`n]) `hp.pos `hn]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hB []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p]
                [(Term.typeSpec ":" `Nat.Primes)]
                ","
                («term_∨_»
                 (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                  (Term.app `B [`p])
                  " =ᵐ["
                  `μ
                  "] "
                  (Term.typeAscription
                   "("
                   («term∅» "∅")
                   ":"
                   [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                   ")"))
                 "∨"
                 (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                  (Term.app `B [`p])
                  " =ᵐ["
                  `μ
                  "] "
                  `univ))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `x
                    []
                    []
                    ":="
                    (Term.app `u [(Term.anonymousCtor "⟨" [`p "," `hp] "⟩")]))))
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `f
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.arrow
                       (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                       "→"
                       (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")))]
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`y]
                      []
                      "=>"
                      («term_+_» (Algebra.Group.Defs.«term_•_» `p " • " `y) "+" `x))))))
                 []
                 (Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   («term_⊆_»
                    (Set.Data.Set.Image.term_''_ `f " '' " (Term.app `B [`p]))
                    "⊆"
                    (Term.app
                     `blimsup
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`n]
                        []
                        "=>"
                        (Term.app
                         `approxAddOrderOf
                         [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                          `n
                          («term_*_» `p "*" (Term.app `δ [`n]))])))
                      `at_top
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`n]
                        []
                        "=>"
                        («term_∧_»
                         («term_<_» (num "0") "<" `n)
                         "∧"
                         (AddCircle.NumberTheory.WellApproximable.«term_∣∣_» `p "∣∣" `n))))]))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.apply
                        "apply"
                        (Term.app
                         (Term.proj
                          (Term.app `ergodic_nsmul_add [`x `hp.one_lt])
                          "."
                          `ae_empty_or_univ_of_image_ae_le)
                         [(Term.app `hB₀ [`p])]))
                       []
                       (Tactic.apply
                        "apply"
                        (Term.app
                         (Term.proj (Term.app `HasSubset.Subset.eventually_le [`this]) "." `congr)
                         [`eventually_eq.rfl]))
                       []
                       (Tactic.exact
                        "exact"
                        (Term.app
                         `blimsup_thickening_mul_ae_eq
                         [`μ
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`n]
                            []
                            "=>"
                            («term_∧_»
                             («term_<_» (num "0") "<" `n)
                             "∧"
                             (AddCircle.NumberTheory.WellApproximable.«term_∣∣_» `p "∣∣" `n))))
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`n]
                            []
                            "=>"
                            (Set.«term{_|_}»
                             "{"
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
                             "|"
                             («term_=_» (Term.app `addOrderOf [`y]) "=" `n)
                             "}")))
                          (Term.app `nat.cast_pos.mpr [`hp.pos])
                          (Term.hole "_")
                          `hδ]))])))))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.proj
                    (Term.proj (Term.app `SupHom.setImage [`f]) "." `apply_blimsup_le)
                    "."
                    `trans)
                   [(Term.app `mono_blimsup [(Term.hole "_")])]))
                 []
                 (Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_div)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_ndiv)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h_cop []]
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       (Term.proj (Term.app `addOrderOf [`x]) "." `Coprime)
                       [(«term_/_» `n "/" `p)]))]
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
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `q)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                               [])]
                             "⟩")])]
                         []
                         [":=" [`h_div]])
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `hu₀)
                           ","
                           (Tactic.rwRule [] `Subtype.coe_mk)
                           ","
                           (Tactic.rwRule [] `hp.coprime_iff_not_dvd)
                           ","
                           (Tactic.rwRule [] (Term.app `q.mul_div_cancel_left [`hp.pos]))]
                          "]")
                         [])
                        []
                        (Tactic.exact
                         "exact"
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`contra]
                           []
                           "=>"
                           (Term.app `h_ndiv [(Term.app `mul_dvd_mul_left [`p `contra])]))))]))))))
                 []
                 (Mathlib.Tactic.tacticReplace_
                  "replace"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h_div []]
                    [(Term.typeSpec
                      ":"
                      («term_=_» («term_*_» («term_/_» `n "/" `p) "*" `p) "=" `n))]
                    ":="
                    (Term.app `Nat.div_mul_cancel [`h_div]))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hf []]
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       `f
                       "="
                       («term_∘_»
                        (Term.fun "fun" (Term.basicFun [`y] [] "=>" («term_+_» `x "+" `y)))
                        "∘"
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`y]
                          []
                          "=>"
                          (Algebra.Group.Defs.«term_•_» `p " • " `y))))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                        []
                        (Tactic.simp
                         "simp"
                         []
                         []
                         []
                         ["[" [(Tactic.simpLemma [] [] (Term.app `add_comm [`x]))] "]"]
                         [])]))))))
                 []
                 (Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_app)] "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `le_eq_subset)
                    ","
                    (Tactic.rwRule [] `SupHom.set_image_to_fun)
                    ","
                    (Tactic.rwRule [] `hf)
                    ","
                    (Tactic.rwRule [] `image_comp)]
                   "]")
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app
                     (Term.explicit "@" `monotone_image)
                     [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                      (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
                      (Term.fun "fun" (Term.basicFun [`y] [] "=>" («term_+_» `x "+" `y)))]))))
                 []
                 (Tactic.specialize
                  "specialize"
                  (Term.app
                   `this
                   [(Term.app
                     `approxAddOrderOf.image_nsmul_subset
                     [(Term.app `δ [`n]) («term_/_» `n "/" `p) `hp.pos])]))
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `h_div)] "]"]
                  [(Tactic.location
                    "at"
                    (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
                 []
                 (Tactic.refine' "refine'" (Term.app `this.trans [(Term.hole "_")]))
                 []
                 (convert
                  "convert"
                  []
                  (Term.app
                   `approxAddOrderOf.vadd_subset_of_coprime
                   [(«term_*_» `p "*" (Term.app `δ [`n])) `h_cop])
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `hu₀)
                    ","
                    (Tactic.simpLemma [] [] `Subtype.coe_mk)
                    ","
                    (Tactic.simpLemma [] [] `h_div)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `mul_comm [`p]))]
                   "]"]
                  [])]))))))
          []
          (Tactic.change
           "change"
           («term_∨_»
            (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term∀ᵐ_,_»
             "∀ᵐ"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             («term_∉_» `x "∉" `E))
            "∨"
            («term_∈_» `E "∈" `volume.ae))
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eventually_eq_empty)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eventually_eq_univ)]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hC []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p]
                [(Term.typeSpec ":" `Nat.Primes)]
                ","
                («term_=_»
                 (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " (Term.app `C [`p]))
                 "="
                 (Term.app `C [`p]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`p])
                 []
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `e
                    []
                    []
                    ":="
                    (Term.proj
                     (Term.typeAscription
                      "("
                      (Term.app `AddAction.toPerm [(Term.app `u [`p])])
                      ":"
                      [(Term.app `Equiv.Perm [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
                      ")")
                     "."
                     `toOrderIsoSet))))
                 []
                 (Tactic.change
                  "change"
                  («term_=_» (Term.app `e [(Term.app `C [`p])]) "=" (Term.app `C [`p]))
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `e.apply_blimsup)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `hu₀ [`p]))]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `blimsup_congr
                   [(Term.app
                     `eventually_of_forall
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`n `hn]
                        []
                        "=>"
                        (Term.app
                         `approxAddOrderOf.vadd_eq_of_mul_dvd
                         [(Term.app `δ [`n])
                          (Term.proj `hn "." (fieldIdx "1"))
                          (Term.proj `hn "." (fieldIdx "2"))])))])]))]))))))
          []
          (Classical.«tacticBy_cases_:_»
           "by_cases"
           [`h ":"]
           (Term.forall
            "∀"
            [`p]
            [(Term.typeSpec ":" `Nat.Primes)]
            ","
            («term_∧_»
             (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
              (Term.app `A [`p])
              " =ᵐ["
              `μ
              "] "
              (Term.typeAscription
               "("
               («term∅» "∅")
               ":"
               [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
               ")"))
             "∧"
             (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
              (Term.app `B [`p])
              " =ᵐ["
              `μ
              "] "
              (Term.typeAscription
               "("
               («term∅» "∅")
               ":"
               [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
               ")")))))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.replace'
             "replace"
             [`h []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`p]
                [(Term.typeSpec ":" `Nat.Primes)]
                ","
                (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                 (Term.typeAscription
                  "("
                  (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " `E)
                  ":"
                  [(Term.app `Set [(Term.hole "_")])]
                  ")")
                 " =ᵐ["
                 `μ
                 "] "
                 `E)))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.intro "intro" [`p])
              []
              (Mathlib.Tactic.tacticReplace_
               "replace"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hE₂ []]
                 [(Term.typeSpec
                   ":"
                   (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                    `E
                    " =ᵐ["
                    `μ
                    "] "
                    (Term.app `C [`p])))]
                 ":="
                 (Term.app `hE₂ [`p (Term.app `h [`p])]))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h_qmp []]
                 [(Term.typeSpec
                   ":"
                   (Term.app
                    `MeasureTheory.Measure.QuasiMeasurePreserving
                    [(Term.app
                      (Term.paren
                       "("
                       (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·"))
                       ")")
                      [(«term-_» "-" (Term.app `u [`p]))])
                     `μ
                     `μ]))]
                 ":="
                 (Term.proj
                  (Term.app `measure_preserving_vadd [(Term.hole "_") `μ])
                  "."
                  `QuasiMeasurePreserving))))
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj
                 (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.app `u [`p]) `hE₂])
                 "."
                 `trans)
                [(Term.app `ae_eq_trans [(Term.hole "_") `hE₂.symm])]))
              []
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hC)] "]") [])])
            []
            (Tactic.exact
             "exact"
             (Term.app `ae_empty_or_univ_of_forall_vadd_ae_eq_self [`hE₀ `h `hu]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticRight "right")
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `not_forall) "," (Tactic.simpLemma [] [] `not_and_or)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
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
                   [])]
                 "⟩")])]
             []
             [":=" [`h]])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hE₁ [`p]))] "]")
             [])
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `hp)] [] [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hA [`p]))] [] [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.contradiction "contradiction")])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `h)
                 ","
                 (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)]
                "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hB [`p]))] [] [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.contradiction "contradiction")])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `h)
                 ","
                 (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)
                 ","
                 (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_right)]
                "]"]
               [])])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticRight "right")
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `not_forall) "," (Tactic.simpLemma [] [] `not_and_or)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
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
               [])]
             "⟩")])]
         []
         [":=" [`h]])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hE₁ [`p]))] "]")
         [])
        []
        (Tactic.cases "cases" [(Tactic.casesTarget [] `hp)] [] [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hA [`p]))] [] [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.contradiction "contradiction")])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `h)
             ","
             (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)]
            "]"]
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hB [`p]))] [] [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.contradiction "contradiction")])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `h)
             ","
             (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)
             ","
             (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_right)]
            "]"]
           [])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hB [`p]))] [] [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.contradiction "contradiction")])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `h)
           ","
           (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)
           ","
           (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_right)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `h)
         ","
         (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)
         ","
         (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_right)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `union_ae_eq_univ_of_ae_eq_univ_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `union_ae_eq_univ_of_ae_eq_univ_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.contradiction "contradiction")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.contradiction "contradiction")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hB [`p]))] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hB [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hB
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hA [`p]))] [] [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.contradiction "contradiction")])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `h)
           ","
           (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `h)
         ","
         (Tactic.simpLemma [] [] `union_ae_eq_univ_of_ae_eq_univ_left)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `union_ae_eq_univ_of_ae_eq_univ_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.contradiction "contradiction")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.contradiction "contradiction")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `hA [`p]))] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hA [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hA
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `hp)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hE₁ [`p]))] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hE₁ [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hE₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
             [])]
           "⟩")])]
       []
       [":=" [`h]])
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
       ["[" [(Tactic.simpLemma [] [] `not_forall) "," (Tactic.simpLemma [] [] `not_and_or)] "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_and_or
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_forall
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticRight "right")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.replace'
         "replace"
         [`h []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`p]
            [(Term.typeSpec ":" `Nat.Primes)]
            ","
            (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
             (Term.typeAscription
              "("
              (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " `E)
              ":"
              [(Term.app `Set [(Term.hole "_")])]
              ")")
             " =ᵐ["
             `μ
             "] "
             `E)))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.intro "intro" [`p])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hE₂ []]
             [(Term.typeSpec
               ":"
               (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
                `E
                " =ᵐ["
                `μ
                "] "
                (Term.app `C [`p])))]
             ":="
             (Term.app `hE₂ [`p (Term.app `h [`p])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_qmp []]
             [(Term.typeSpec
               ":"
               (Term.app
                `MeasureTheory.Measure.QuasiMeasurePreserving
                [(Term.app
                  (Term.paren
                   "("
                   (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·"))
                   ")")
                  [(«term-_» "-" (Term.app `u [`p]))])
                 `μ
                 `μ]))]
             ":="
             (Term.proj
              (Term.app `measure_preserving_vadd [(Term.hole "_") `μ])
              "."
              `QuasiMeasurePreserving))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.app `u [`p]) `hE₂]) "." `trans)
            [(Term.app `ae_eq_trans [(Term.hole "_") `hE₂.symm])]))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hC)] "]") [])])
        []
        (Tactic.exact
         "exact"
         (Term.app `ae_empty_or_univ_of_forall_vadd_ae_eq_self [`hE₀ `h `hu]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `ae_empty_or_univ_of_forall_vadd_ae_eq_self [`hE₀ `h `hu]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ae_empty_or_univ_of_forall_vadd_ae_eq_self [`hE₀ `h `hu])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hE₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ae_empty_or_univ_of_forall_vadd_ae_eq_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`p])
        []
        (Mathlib.Tactic.tacticReplace_
         "replace"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hE₂ []]
           [(Term.typeSpec
             ":"
             (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
              `E
              " =ᵐ["
              `μ
              "] "
              (Term.app `C [`p])))]
           ":="
           (Term.app `hE₂ [`p (Term.app `h [`p])]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_qmp []]
           [(Term.typeSpec
             ":"
             (Term.app
              `MeasureTheory.Measure.QuasiMeasurePreserving
              [(Term.app
                (Term.paren
                 "("
                 (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·"))
                 ")")
                [(«term-_» "-" (Term.app `u [`p]))])
               `μ
               `μ]))]
           ":="
           (Term.proj
            (Term.app `measure_preserving_vadd [(Term.hole "_") `μ])
            "."
            `QuasiMeasurePreserving))))
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.app `u [`p]) `hE₂]) "." `trans)
          [(Term.app `ae_eq_trans [(Term.hole "_") `hE₂.symm])]))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hC)] "]") [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hC)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hC
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.app `u [`p]) `hE₂]) "." `trans)
        [(Term.app `ae_eq_trans [(Term.hole "_") `hE₂.symm])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.app `u [`p]) `hE₂]) "." `trans)
       [(Term.app `ae_eq_trans [(Term.hole "_") `hE₂.symm])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ae_eq_trans [(Term.hole "_") `hE₂.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hE₂.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ae_eq_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ae_eq_trans [(Term.hole "_") `hE₂.symm])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.app `u [`p]) `hE₂]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.app `u [`p]) `hE₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hE₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `u [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `u [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h_qmp.vadd_ae_eq_of_ae_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `h_qmp.vadd_ae_eq_of_ae_eq [(Term.paren "(" (Term.app `u [`p]) ")") `hE₂])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h_qmp []]
         [(Term.typeSpec
           ":"
           (Term.app
            `MeasureTheory.Measure.QuasiMeasurePreserving
            [(Term.app
              (Term.paren
               "("
               (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·"))
               ")")
              [(«term-_» "-" (Term.app `u [`p]))])
             `μ
             `μ]))]
         ":="
         (Term.proj
          (Term.app `measure_preserving_vadd [(Term.hole "_") `μ])
          "."
          `QuasiMeasurePreserving))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `measure_preserving_vadd [(Term.hole "_") `μ])
       "."
       `QuasiMeasurePreserving)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `measure_preserving_vadd [(Term.hole "_") `μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `measure_preserving_vadd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `measure_preserving_vadd [(Term.hole "_") `μ])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `MeasureTheory.Measure.QuasiMeasurePreserving
       [(Term.app
         (Term.paren "(" (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·")) ")")
         [(«term-_» "-" (Term.app `u [`p]))])
        `μ
        `μ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.paren "(" (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·")) ")")
       [(«term-_» "-" (Term.app `u [`p]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (Term.app `u [`p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `u [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" (Term.app `u [`p])) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.paren "(" (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.paren "(" (Algebra.Group.Defs.«term_+ᵥ_» (Term.cdot "·") " +ᵥ " (Term.cdot "·")) ")")
      [(Term.paren "(" («term-_» "-" (Term.app `u [`p])) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MeasureTheory.Measure.QuasiMeasurePreserving
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hE₂ []]
         [(Term.typeSpec
           ":"
           (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
            `E
            " =ᵐ["
            `μ
            "] "
            (Term.app `C [`p])))]
         ":="
         (Term.app `hE₂ [`p (Term.app `h [`p])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hE₂ [`p (Term.app `h [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`p]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hE₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
       `E
       " =ᵐ["
       `μ
       "] "
       (Term.app `C [`p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `C [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`p])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.replace'
       "replace"
       [`h []]
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [`p]
          [(Term.typeSpec ":" `Nat.Primes)]
          ","
          (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
           (Term.typeAscription
            "("
            (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " `E)
            ":"
            [(Term.app `Set [(Term.hole "_")])]
            ")")
           " =ᵐ["
           `μ
           "] "
           `E)))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`p]
       [(Term.typeSpec ":" `Nat.Primes)]
       ","
       (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
        (Term.typeAscription
         "("
         (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " `E)
         ":"
         [(Term.app `Set [(Term.hole "_")])]
         ")")
        " =ᵐ["
        `μ
        "] "
        `E))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
       (Term.typeAscription
        "("
        (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " `E)
        ":"
        [(Term.app `Set [(Term.hole "_")])]
        ")")
       " =ᵐ["
       `μ
       "] "
       `E)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " `E)
       ":"
       [(Term.app `Set [(Term.hole "_")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_+ᵥ_» (Term.app `u [`p]) " +ᵥ " `E)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `u [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.Primes
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_»
       "by_cases"
       [`h ":"]
       (Term.forall
        "∀"
        [`p]
        [(Term.typeSpec ":" `Nat.Primes)]
        ","
        («term_∧_»
         (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
          (Term.app `A [`p])
          " =ᵐ["
          `μ
          "] "
          (Term.typeAscription
           "("
           («term∅» "∅")
           ":"
           [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
           ")"))
         "∧"
         (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
          (Term.app `B [`p])
          " =ᵐ["
          `μ
          "] "
          (Term.typeAscription
           "("
           («term∅» "∅")
           ":"
           [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
           ")")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`p]
       [(Term.typeSpec ":" `Nat.Primes)]
       ","
       («term_∧_»
        (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
         (Term.app `A [`p])
         " =ᵐ["
         `μ
         "] "
         (Term.typeAscription
          "("
          («term∅» "∅")
          ":"
          [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
          ")"))
        "∧"
        (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
         (Term.app `B [`p])
         " =ᵐ["
         `μ
         "] "
         (Term.typeAscription
          "("
          («term∅» "∅")
          ":"
          [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
          ")"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
        (Term.app `A [`p])
        " =ᵐ["
        `μ
        "] "
        (Term.typeAscription
         "("
         («term∅» "∅")
         ":"
         [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
         ")"))
       "∧"
       (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
        (Term.app `B [`p])
        " =ᵐ["
        `μ
        "] "
        (Term.typeAscription
         "("
         («term∅» "∅")
         ":"
         [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MeasureTheory.MeasureTheory.Measure.MeasureSpaceDef.«term_=ᵐ[_]_»
       (Term.app `B [`p])
       " =ᵐ["
       `μ
       "] "
       (Term.typeAscription
        "("
        («term∅» "∅")
        ":"
        [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term∅» "∅")
       ":"
       [(Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [(AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AddCircle.NumberTheory.WellApproximable.term𝕊', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AddCircle.NumberTheory.WellApproximable.term𝕊', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (AddCircle.NumberTheory.WellApproximable.term𝕊 "𝕊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AddCircle.NumberTheory.WellApproximable.term𝕊', expected 'AddCircle.NumberTheory.WellApproximable.term𝕊._@.NumberTheory.WellApproximable._hyg.103'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- *Gallagher's ergodic theorem* on Diophantine approximation. -/
  theorem
    add_well_approximable_ae_empty_or_univ
    ( δ : ℕ → ℝ ) ( hδ : Tendsto δ atTop 𝓝 0 )
      : ∀ᵐ x , ¬ addWellApproximable 𝕊 δ x ∨ ∀ᵐ x , addWellApproximable 𝕊 δ x
    :=
      by
        letI : SemilatticeSup Nat.Primes := Nat.Subtype.semilatticeSup _
          set μ : Measure 𝕊 := volume
          set u : Nat.Primes → 𝕊 := fun p => ↑ ( ↑ ( 1 : ℕ ) : ℝ ) / p * T
          have
            hu₀
              : ∀ p : Nat.Primes , addOrderOf u p = ( p : ℕ )
              :=
              by rintro ⟨ p , hp ⟩ exact add_order_of_div_of_gcd_eq_one hp.pos gcd_one_left p
          have
            hu
              : tendsto addOrderOf ∘ u at_top at_top
              :=
              by
                rw [ ( funext hu₀ : addOrderOf ∘ u = coe ) ]
                  have h_mono : Monotone ( coe : Nat.Primes → ℕ ) := fun p q hpq => hpq
                  refine' h_mono.tendsto_at_top_at_top fun n => _
                  obtain ⟨ p , hp , hp' ⟩ := n.exists_infinite_primes
                  exact ⟨ ⟨ p , hp' ⟩ , hp ⟩
          set E := addWellApproximable 𝕊 δ
          set X : ℕ → Set 𝕊 := fun n => approxAddOrderOf 𝕊 n δ n
          set A : ℕ → Set 𝕊 := fun p => blimsup X at_top fun n => 0 < n ∧ p ∤ n
          set B : ℕ → Set 𝕊 := fun p => blimsup X at_top fun n => 0 < n ∧ p ∣∣ n
          set C : ℕ → Set 𝕊 := fun p => blimsup X at_top fun n => 0 < n ∧ p ^ 2 ∣ n
          have
            hA₀
              : ∀ p , MeasurableSet A p
              :=
              fun
                p
                  =>
                  MeasurableSet.measurable_set_blimsup fun n hn => is_open_thickening.measurable_set
          have
            hB₀
              : ∀ p , MeasurableSet B p
              :=
              fun
                p
                  =>
                  MeasurableSet.measurable_set_blimsup fun n hn => is_open_thickening.measurable_set
          have
            hE₀
              : null_measurable_set E μ
              :=
              by
                refine'
                    MeasurableSet.measurable_set_blimsup fun n hn => IsOpen.measurable_set _
                      .
                      NullMeasurableSet
                  exact is_open_thickening
          have
            hE₁
              : ∀ p , E = A p ∪ B p ∪ C p
              :=
              by
                intro p
                  simp
                    only
                    [
                      E
                        ,
                        addWellApproximable
                        ,
                        ← blimsup_or_eq_sup
                        ,
                        ← and_or_left
                        ,
                        ← sup_eq_union
                        ,
                        sq
                      ]
                  congr
                  refine' funext fun n => propext <| iff_self_and.mpr fun hn => _
                  simp
                    only
                    [
                      em p ∣ n . symm
                        ,
                        em p * p ∣ n . symm
                        ,
                        or_and_left
                        ,
                        or_true_iff
                        ,
                        true_and_iff
                        ,
                        or_assoc'
                      ]
          have
            hE₂
              :
                ∀
                  p
                  : Nat.Primes
                  ,
                  A p =ᵐ[ μ ] ( ∅ : Set 𝕊 ) ∧ B p =ᵐ[ μ ] ( ∅ : Set 𝕊 ) → E =ᵐ[ μ ] C p
              :=
              by
                rintro p ⟨ hA , hB ⟩
                  rw [ hE₁ p ]
                  exact
                    union_ae_eq_right_of_ae_eq_empty union_ae_eq_right_of_ae_eq_empty hA . trans hB
          have
            hA
              : ∀ p : Nat.Primes , A p =ᵐ[ μ ] ( ∅ : Set 𝕊 ) ∨ A p =ᵐ[ μ ] univ
              :=
              by
                rintro ⟨ p , hp ⟩
                  let f : 𝕊 → 𝕊 := fun y => ( p : ℕ ) • y
                  suffices
                    f '' A p
                        ⊆
                        blimsup fun n => approxAddOrderOf 𝕊 n p * δ n at_top fun n => 0 < n ∧ p ∤ n
                      by
                        apply ergodic_nsmul hp.one_lt . ae_empty_or_univ_of_image_ae_le hA₀ p
                          apply HasSubset.Subset.eventually_le this . congr eventually_eq.rfl
                          exact
                            blimsup_thickening_mul_ae_eq
                              μ
                                fun n => 0 < n ∧ p ∤ n
                                fun n => { y | addOrderOf y = n }
                                nat.cast_pos.mpr hp.pos
                                _
                                hδ
                  refine' SupHom.setImage f . apply_blimsup_le . trans mono_blimsup fun n hn => _
                  replace hn := nat.coprime_comm.mp hp.coprime_iff_not_dvd . 2 hn . 2
                  exact approxAddOrderOf.image_nsmul_subset_of_coprime δ n hp.pos hn
          have
            hB
              : ∀ p : Nat.Primes , B p =ᵐ[ μ ] ( ∅ : Set 𝕊 ) ∨ B p =ᵐ[ μ ] univ
              :=
              by
                rintro ⟨ p , hp ⟩
                  let x := u ⟨ p , hp ⟩
                  let f : 𝕊 → 𝕊 := fun y => p • y + x
                  suffices
                    f '' B p
                        ⊆
                        blimsup fun n => approxAddOrderOf 𝕊 n p * δ n at_top fun n => 0 < n ∧ p ∣∣ n
                      by
                        apply ergodic_nsmul_add x hp.one_lt . ae_empty_or_univ_of_image_ae_le hB₀ p
                          apply HasSubset.Subset.eventually_le this . congr eventually_eq.rfl
                          exact
                            blimsup_thickening_mul_ae_eq
                              μ
                                fun n => 0 < n ∧ p ∣∣ n
                                fun n => { y | addOrderOf y = n }
                                nat.cast_pos.mpr hp.pos
                                _
                                hδ
                  refine' SupHom.setImage f . apply_blimsup_le . trans mono_blimsup _
                  rintro n ⟨ hn , h_div , h_ndiv ⟩
                  have
                    h_cop
                      : addOrderOf x . Coprime n / p
                      :=
                      by
                        obtain ⟨ q , rfl ⟩ := h_div
                          rw
                            [
                              hu₀
                                ,
                                Subtype.coe_mk
                                ,
                                hp.coprime_iff_not_dvd
                                ,
                                q.mul_div_cancel_left hp.pos
                              ]
                          exact fun contra => h_ndiv mul_dvd_mul_left p contra
                  replace h_div : n / p * p = n := Nat.div_mul_cancel h_div
                  have hf : f = fun y => x + y ∘ fun y => p • y := by ext simp [ add_comm x ]
                  simp_rw [ comp_app ]
                  rw [ le_eq_subset , SupHom.set_image_to_fun , hf , image_comp ]
                  have := @ monotone_image 𝕊 𝕊 fun y => x + y
                  specialize this approxAddOrderOf.image_nsmul_subset δ n n / p hp.pos
                  simp only [ h_div ] at this ⊢
                  refine' this.trans _
                  convert approxAddOrderOf.vadd_subset_of_coprime p * δ n h_cop
                  simp only [ hu₀ , Subtype.coe_mk , h_div , mul_comm p ]
          change ∀ᵐ x , x ∉ E ∨ E ∈ volume.ae
          rw [ ← eventually_eq_empty , ← eventually_eq_univ ]
          have
            hC
              : ∀ p : Nat.Primes , u p +ᵥ C p = C p
              :=
              by
                intro p
                  let e := ( AddAction.toPerm u p : Equiv.Perm 𝕊 ) . toOrderIsoSet
                  change e C p = C p
                  rw [ e.apply_blimsup , ← hu₀ p ]
                  exact
                    blimsup_congr
                      eventually_of_forall
                        fun n hn => approxAddOrderOf.vadd_eq_of_mul_dvd δ n hn . 1 hn . 2
          by_cases h : ∀ p : Nat.Primes , A p =ᵐ[ μ ] ( ∅ : Set 𝕊 ) ∧ B p =ᵐ[ μ ] ( ∅ : Set 𝕊 )
          ·
            replace h : ∀ p : Nat.Primes , ( u p +ᵥ E : Set _ ) =ᵐ[ μ ] E
              ·
                intro p
                  replace hE₂ : E =ᵐ[ μ ] C p := hE₂ p h p
                  have
                    h_qmp
                      : MeasureTheory.Measure.QuasiMeasurePreserving ( · +ᵥ · ) - u p μ μ
                      :=
                      measure_preserving_vadd _ μ . QuasiMeasurePreserving
                  refine' h_qmp.vadd_ae_eq_of_ae_eq u p hE₂ . trans ae_eq_trans _ hE₂.symm
                  rw [ hC ]
              exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hE₀ h hu
          ·
            right
              simp only [ not_forall , not_and_or ] at h
              obtain ⟨ p , hp ⟩ := h
              rw [ hE₁ p ]
              cases hp
              · cases hA p · contradiction simp only [ h , union_ae_eq_univ_of_ae_eq_univ_left ]
              ·
                cases hB p
                  · contradiction
                  simp
                    only
                    [
                      h , union_ae_eq_univ_of_ae_eq_univ_left , union_ae_eq_univ_of_ae_eq_univ_right
                      ]
#align
  add_circle.add_well_approximable_ae_empty_or_univ AddCircle.add_well_approximable_ae_empty_or_univ

end AddCircle

