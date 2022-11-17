/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Yury G. Kudryashov, Dylan MacKenzie, Patrick Massot
-/
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.SpecificLimits.Basic

/-!
# A collection of specific limit computations

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
as well as such computations in `ℝ` when the natural proof passes through a fact about normed
spaces.

-/


noncomputable section

open Classical Set Function Filter Finset Metric Asymptotics

open Classical TopologicalSpace Nat BigOperators uniformity Nnreal Ennreal

variable {α : Type _} {β : Type _} {ι : Type _}

theorem tendsto_norm_at_top_at_top : Tendsto (norm : ℝ → ℝ) atTop atTop :=
  tendsto_abs_at_top_at_top
#align tendsto_norm_at_top_at_top tendsto_norm_at_top_at_top

theorem summable_of_absolute_convergence_real {f : ℕ → ℝ} :
    (∃ r, Tendsto (fun n => ∑ i in range n, |f i|) atTop (𝓝 r)) → Summable f
  | ⟨r, hr⟩ => by
    refine' summable_of_summable_norm ⟨r, (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩
    exact fun i => norm_nonneg _
    simpa only using hr
#align summable_of_absolute_convergence_real summable_of_absolute_convergence_real

/-! ### Powers -/


theorem tendsto_norm_zero' {𝕜 : Type _} [NormedAddCommGroup 𝕜] : Tendsto (norm : 𝕜 → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
  tendsto_norm_zero.inf $ tendsto_principal_principal.2 $ fun x hx => norm_pos_iff.2 hx
#align tendsto_norm_zero' tendsto_norm_zero'

namespace NormedField

theorem tendsto_norm_inverse_nhds_within_0_at_top {𝕜 : Type _} [NormedField 𝕜] :
    Tendsto (fun x : 𝕜 => ∥x⁻¹∥) (𝓝[≠] 0) atTop :=
  (tendsto_inv_zero_at_top.comp tendsto_norm_zero').congr $ fun x => (norm_inv x).symm
#align normed_field.tendsto_norm_inverse_nhds_within_0_at_top NormedField.tendsto_norm_inverse_nhds_within_0_at_top

theorem tendsto_norm_zpow_nhds_within_0_at_top {𝕜 : Type _} [NormedField 𝕜] {m : ℤ} (hm : m < 0) :
    Tendsto (fun x : 𝕜 => ∥x ^ m∥) (𝓝[≠] 0) atTop := by
  rcases neg_surjective m with ⟨m, rfl⟩
  rw [neg_lt_zero] at hm
  lift m to ℕ using hm.le
  rw [Int.coe_nat_pos] at hm
  simp only [norm_pow, zpow_neg, zpow_coe_nat, ← inv_pow]
  exact (tendsto_pow_at_top hm.ne').comp NormedField.tendsto_norm_inverse_nhds_within_0_at_top
#align normed_field.tendsto_norm_zpow_nhds_within_0_at_top NormedField.tendsto_norm_zpow_nhds_within_0_at_top

/-- The (scalar) product of a sequence that tends to zero with a bounded one also tends to zero. -/
theorem tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 𝔸 : Type _} [NormedField 𝕜] [NormedAddCommGroup 𝔸]
    [NormedSpace 𝕜 𝔸] {l : Filter ι} {ε : ι → 𝕜} {f : ι → 𝔸} (hε : Tendsto ε l (𝓝 0))
    (hf : Filter.IsBoundedUnder (· ≤ ·) l (norm ∘ f)) : Tendsto (ε • f) l (𝓝 0) := by
  rw [← is_o_one_iff 𝕜] at hε⊢
  simpa using is_o.smul_is_O hε (hf.is_O_const (one_ne_zero : (1 : 𝕜) ≠ 0))
#align
  normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded

@[simp]
theorem continuous_at_zpow {𝕜 : Type _} [NontriviallyNormedField 𝕜] {m : ℤ} {x : 𝕜} :
    ContinuousAt (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m := by
  refine' ⟨_, continuous_at_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact
    not_tendsto_at_top_of_tendsto_nhds (hc.tendsto.mono_left nhds_within_le_nhds).norm
      (tendsto_norm_zpow_nhds_within_0_at_top hm)
#align normed_field.continuous_at_zpow NormedField.continuous_at_zpow

@[simp]
theorem continuous_at_inv {𝕜 : Type _} [NontriviallyNormedField 𝕜] {x : 𝕜} : ContinuousAt Inv.inv x ↔ x ≠ 0 := by
  simpa [(@zero_lt_one ℤ _ _).not_le] using @continuous_at_zpow _ _ (-1) x
#align normed_field.continuous_at_inv NormedField.continuous_at_inv

end NormedField

theorem is_o_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
    (fun n : ℕ => r₁ ^ n) =o[at_top] fun n => r₂ ^ n :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (is_o_of_tendsto fun n hn => False.elim $ H.ne' $ pow_eq_zero hn) $
    (tendsto_pow_at_top_nhds_0_of_lt_1 (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun n =>
      div_pow _ _ _
#align is_o_pow_pow_of_lt_left is_o_pow_pow_of_lt_left

theorem is_O_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    (fun n : ℕ => r₁ ^ n) =O[at_top] fun n => r₂ ^ n :=
  h₂.eq_or_lt.elim (fun h => h ▸ is_O_refl _ _) fun h => (is_o_pow_pow_of_lt_left h₁ h).IsO
#align is_O_pow_pow_of_le_left is_O_pow_pow_of_le_left

theorem is_o_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : |r₁| < |r₂|) : (fun n : ℕ => r₁ ^ n) =o[at_top] fun n => r₂ ^ n :=
  by
  refine' (is_o.of_norm_left _).of_norm_right
  exact (is_o_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)
#align is_o_pow_pow_of_abs_lt_left is_o_pow_pow_of_abs_lt_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.\n\n* 0: $f n = o(a ^ n)$ for some $-R < a < R$;\n* 1: $f n = o(a ^ n)$ for some $0 < a < R$;\n* 2: $f n = O(a ^ n)$ for some $-R < a < R$;\n* 3: $f n = O(a ^ n)$ for some $0 < a < R$;\n* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$\n     for all `n`;\n* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;\n* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;\n* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.\n\nNB: For backwards compatibility, if you add more items to the list, please append them at the end of\nthe list. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `tfae_exists_lt_is_o_pow [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.arrow (Init.Data.Nat.Basic.termℕ "ℕ") "→" (Data.Real.Basic.termℝ "ℝ"))]
         []
         ")")
        (Term.explicitBinder "(" [`R] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tfae
         [(Init.Core.«term[_,»
           "["
           [(Init.Logic.«term∃_,_»
             "∃"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `a)
               [(«binderTerm∈_» "∈" (Term.app `ioo [(Init.Core.«term-_» "-" `R) `R]))]))
             ", "
             (Asymptotics.Analysis.Asymptotics.Asymptotics.«term_=o[_]_» `f " =o[" `at_top "] " (Term.app `pow [`a])))
            ","
            (Init.Logic.«term∃_,_»
             "∃"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `a)
               [(«binderTerm∈_» "∈" (Term.app `ioo [(num "0") `R]))]))
             ", "
             (Asymptotics.Analysis.Asymptotics.Asymptotics.«term_=o[_]_» `f " =o[" `at_top "] " (Term.app `pow [`a])))
            ","
            (Init.Logic.«term∃_,_»
             "∃"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `a)
               [(«binderTerm∈_» "∈" (Term.app `ioo [(Init.Core.«term-_» "-" `R) `R]))]))
             ", "
             (Asymptotics.Analysis.Asymptotics.Asymptotics.«term_=O[_]_» `f " =O[" `at_top "] " (Term.app `pow [`a])))
            ","
            (Init.Logic.«term∃_,_»
             "∃"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `a)
               [(«binderTerm∈_» "∈" (Term.app `ioo [(num "0") `R]))]))
             ", "
             (Asymptotics.Analysis.Asymptotics.Asymptotics.«term_=O[_]_» `f " =O[" `at_top "] " (Term.app `pow [`a])))
            ","
            (Init.Logic.«term∃_,_»
             "∃"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinderCollection
               [(Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(Std.ExtendedBinder.«binderTerm<_» "<" `R)])
                 ")")
                (Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `C) [])
                 ")")
                (Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `h₀)
                  [(group
                    ":"
                    (Init.Logic.«term_∨_»
                     (Init.Core.«term_<_» (num "0") " < " `C)
                     " ∨ "
                     (Init.Core.«term_<_» (num "0") " < " `R)))])
                 ")")]))
             ", "
             (Term.forall
              "∀"
              [`n]
              []
              ","
              (Init.Core.«term_≤_»
               (Algebra.Abs.«term|_|» "|" (Term.app `f [`n]) "|")
               " ≤ "
               (Init.Core.«term_*_» `C " * " (Init.Core.«term_^_» `a " ^ " `n)))))
            ","
            (Init.Logic.«term∃_,_»
             "∃"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinderCollection
               [(Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `a)
                  [(«binderTerm∈_» "∈" (Term.app `ioo [(num "0") `R]))])
                 ")")
                (Std.ExtendedBinder.extBinderParenthesized
                 "("
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `C)
                  [(Std.ExtendedBinder.«binderTerm>_» ">" (num "0"))])
                 ")")]))
             ", "
             (Term.forall
              "∀"
              [`n]
              []
              ","
              (Init.Core.«term_≤_»
               (Algebra.Abs.«term|_|» "|" (Term.app `f [`n]) "|")
               " ≤ "
               (Init.Core.«term_*_» `C " * " (Init.Core.«term_^_» `a " ^ " `n)))))
            ","
            (Init.Logic.«term∃_,_»
             "∃"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(Std.ExtendedBinder.«binderTerm<_» "<" `R)]))
             ", "
             (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
              "∀ᶠ"
              (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) []))
              " in "
              `at_top
              ", "
              (Init.Core.«term_≤_»
               (Algebra.Abs.«term|_|» "|" (Term.app `f [`n]) "|")
               " ≤ "
               (Init.Core.«term_^_» `a " ^ " `n))))
            ","
            (Init.Logic.«term∃_,_»
             "∃"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `a)
               [(«binderTerm∈_» "∈" (Term.app `ioo [(num "0") `R]))]))
             ", "
             (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
              "∀ᶠ"
              (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) []))
              " in "
              `at_top
              ", "
              (Init.Core.«term_≤_»
               (Algebra.Abs.«term|_|» "|" (Term.app `f [`n]) "|")
               " ≤ "
               (Init.Core.«term_^_» `a " ^ " `n))))]
           "]")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`A []]
              [(Term.typeSpec
                ":"
                (Init.Core.«term_⊆_»
                 (Term.app `Ico [(num "0") `R])
                 " ⊆ "
                 (Term.app `Ioo [(Init.Core.«term-_» "-" `R) `R])))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x `hx]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app
                   (Term.proj
                    (Term.app
                     (Term.proj `neg_lt_zero "." (fieldIdx "2"))
                     [(Term.app
                       (Term.proj (Term.proj `hx "." (fieldIdx "1")) "." `trans_lt)
                       [(Term.proj `hx "." (fieldIdx "2"))])])
                    "."
                    `trans_le)
                   [(Term.proj `hx "." (fieldIdx "1"))])
                  ","
                  (Term.proj `hx "." (fieldIdx "2"))]
                 "⟩"))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`B []]
              [(Term.typeSpec
                ":"
                (Init.Core.«term_⊆_»
                 (Term.app `Ioo [(num "0") `R])
                 " ⊆ "
                 (Term.app `Ioo [(Init.Core.«term-_» "-" `R) `R])))]
              ":="
              (Term.app `subset.trans [`Ioo_subset_Ico_self `A]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "3"))
           []
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
              []
              "=>"
              (Term.anonymousCtor "⟨" [`a "," `ha "," (Term.proj `H "." `IsO)] "⟩"))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "1"))
           []
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
              []
              "=>"
              (Term.anonymousCtor "⟨" [`a "," (Term.app `B [`ha]) "," `H] "⟩"))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "2"))
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                    [])]
                  "⟩"))]
               [])
              [])
             (group
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget
                 []
                 (Term.app `exists_between [(Term.app (Term.proj `abs_lt "." (fieldIdx "2")) [`ha])]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hab)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hbR)])
                      [])]
                    "⟩")])
                 [])])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`b
                 ","
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app (Term.proj (Term.app `abs_nonneg [`a]) "." `trans_lt) [`hab]) "," `hbR]
                  "⟩")
                 ","
                 (Term.app
                  `H.trans_is_o
                  [(Term.app `is_o_pow_pow_of_abs_lt_left [(Term.app `hab.trans_le [(Term.app `le_abs_self [`b])])])])]
                "⟩"))
              [])])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "4"))
           []
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
              []
              "=>"
              (Term.anonymousCtor "⟨" [`a "," `ha "," (Term.proj `H "." `IsO)] "⟩"))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "3"))
           []
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
              []
              "=>"
              (Term.anonymousCtor "⟨" [`a "," (Term.app `B [`ha]) "," `H] "⟩"))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "6"))
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                    [])]
                  "⟩"))]
               [])
              [])
             (group
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `bound_of_is_O_nat_at_top [`H]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hC₀)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hC)])
                      [])]
                    "⟩")])
                 [])])
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [`a "," `ha "," `C "," `hC₀ "," (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]
                "⟩"))
              [])
             (group
              (Std.Tactic.simpa
               "simpa"
               []
               []
               (Std.Tactic.simpaArgsRest
                []
                []
                ["only"]
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `Real.norm_eq_abs)
                   ","
                   (Tactic.simpLemma [] [] `abs_pow)
                   ","
                   (Tactic.simpLemma
                    []
                    []
                    (Term.app `abs_of_nonneg [(Term.proj (Term.proj `ha "." (fieldIdx "1")) "." `le)]))]
                  "]")]
                ["using"
                 (Term.app
                  `hC
                  [(Term.app `pow_ne_zero [`n (Term.proj (Term.proj `ha "." (fieldIdx "1")) "." `ne')])])]))
              [])])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "6") "→" (num "5"))
           []
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.anonymousCtor "⟨" [`a "," `ha "," `C "," `H₀ "," `H] "⟩")]
              []
              "=>"
              (Term.anonymousCtor
               "⟨"
               [`a "," (Term.proj `ha "." (fieldIdx "2")) "," `C "," (Term.app `Or.inl [`H₀]) "," `H]
               "⟩"))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "3"))
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₀)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                    [])]
                  "⟩"))]
               [])
              [])
             (group
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  `sign_cases_of_C_mul_pow_nonneg
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`n]
                     []
                     "=>"
                     (Term.app
                      (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans)
                      [(Term.app `H [`n])])))]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.paren
                    "("
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.one `rfl)
                       "|"
                       (Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hC₀)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₀)])
                          [])]
                        "⟩")])
                     [])
                    ")")])
                 [])])
              [])
             (group
              («tactic___;_»
               (cdotTk (patternIgnore (token.«·» "·")))
               [(group
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])]
                  [":" (Init.Core.«term_=_» `f " = " (num "0"))]
                  [":="
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.Ext.«tacticExt___:_»
                         "ext"
                         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
                         [])
                        []
                        (Std.Tactic.simpa
                         "simpa"
                         []
                         []
                         (Std.Tactic.simpaArgsRest [] [] [] [] ["using" (Term.app `H [`n])]))])))]])
                 [])
                (group
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `lt_irrefl) "," (Tactic.simpLemma [] [] `false_or_iff)] "]"]
                  [(Tactic.location "at" (Tactic.locationHyp [`h₀] []))])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(num "0")
                    ","
                    (Term.anonymousCtor "⟨" [(Term.app (Term.proj `neg_lt_zero "." (fieldIdx "2")) [`h₀]) "," `h₀] "⟩")
                    ","
                    (Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")])]
                   "⟩"))
                 [])])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`a
                 ","
                 (Term.app `A [(Term.anonymousCtor "⟨" [`ha₀ "," `ha] "⟩")])
                 ","
                 (Term.app
                  `is_O_of_le'
                  [(Term.hole "_")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`n]
                     []
                     "=>"
                     (Init.Core.«term_$_»
                      (Term.proj (Term.app `H [`n]) "." `trans)
                      " $ "
                      (Term.app `mul_le_mul_of_nonneg_left [(Term.app `le_abs_self [(Term.hole "_")]) `hC₀.le]))))])]
                "⟩"))
              [])])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "8"))
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                    [])]
                  "⟩"))]
               [])
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [`a
                 ","
                 `ha
                 ","
                 (Term.app
                  (Term.proj (Term.app `H.def [`zero_lt_one]) "." `mono)
                  [(Term.fun "fun" (Term.basicFun [`n `hn] [] "=>" (Term.hole "_")))])]
                "⟩"))
              [])
             (group
              (tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Real.norm_eq_abs)
                 ","
                 (Tactic.rwRule [] `Real.norm_eq_abs)
                 ","
                 (Tactic.rwRule [] `one_mul)
                 ","
                 (Tactic.rwRule [] `abs_pow)
                 ","
                 (Tactic.rwRule [] (Term.app `abs_of_pos [(Term.proj `ha "." (fieldIdx "1"))]))]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
              [])])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "8") "→" (num "7"))
           []
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
              []
              "=>"
              (Term.anonymousCtor "⟨" [`a "," (Term.proj `ha "." (fieldIdx "2")) "," `H] "⟩"))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "3"))
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                    [])]
                  "⟩"))]
               [])
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec ":" (Init.Core.«term_≤_» (num "0") " ≤ " `a))]
                 ":="
                 (Term.app
                  `nonneg_of_eventually_pow_nonneg
                  [(Init.Core.«term_$_»
                    `H.mono
                    " $ "
                    (Term.fun
                     "fun"
                     (Term.basicFun [`n] [] "=>" (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans))))]))))
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [`a
                 ","
                 (Term.app `A [(Term.anonymousCtor "⟨" [`this "," `ha] "⟩")])
                 ","
                 (Term.app `is_O.of_bound [(num "1") (Term.hole "_")])]
                "⟩"))
              [])
             (group
              (Std.Tactic.simpa
               "simpa"
               []
               []
               (Std.Tactic.simpaArgsRest
                []
                []
                ["only"]
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `Real.norm_eq_abs)
                   ","
                   (Tactic.simpLemma [] [] `one_mul)
                   ","
                   (Tactic.simpLemma [] [] `abs_pow)
                   ","
                   (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`this]))]
                  "]")]
                []))
              [])])
           []
           (Tactic.tfaeFinish "tfae_finish")])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`A []]
             [(Term.typeSpec
               ":"
               (Init.Core.«term_⊆_»
                (Term.app `Ico [(num "0") `R])
                " ⊆ "
                (Term.app `Ioo [(Init.Core.«term-_» "-" `R) `R])))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`x `hx]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.app
                  (Term.proj
                   (Term.app
                    (Term.proj `neg_lt_zero "." (fieldIdx "2"))
                    [(Term.app
                      (Term.proj (Term.proj `hx "." (fieldIdx "1")) "." `trans_lt)
                      [(Term.proj `hx "." (fieldIdx "2"))])])
                   "."
                   `trans_le)
                  [(Term.proj `hx "." (fieldIdx "1"))])
                 ","
                 (Term.proj `hx "." (fieldIdx "2"))]
                "⟩"))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`B []]
             [(Term.typeSpec
               ":"
               (Init.Core.«term_⊆_»
                (Term.app `Ioo [(num "0") `R])
                " ⊆ "
                (Term.app `Ioo [(Init.Core.«term-_» "-" `R) `R])))]
             ":="
             (Term.app `subset.trans [`Ioo_subset_Ico_self `A]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "3"))
          []
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
             []
             "=>"
             (Term.anonymousCtor "⟨" [`a "," `ha "," (Term.proj `H "." `IsO)] "⟩"))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "1"))
          []
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
             []
             "=>"
             (Term.anonymousCtor "⟨" [`a "," (Term.app `B [`ha]) "," `H] "⟩"))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "2"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                   [])]
                 "⟩"))]
              [])
             [])
            (group
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app `exists_between [(Term.app (Term.proj `abs_lt "." (fieldIdx "2")) [`ha])]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hab)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hbR)])
                     [])]
                   "⟩")])
                [])])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`b
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app (Term.proj (Term.app `abs_nonneg [`a]) "." `trans_lt) [`hab]) "," `hbR]
                 "⟩")
                ","
                (Term.app
                 `H.trans_is_o
                 [(Term.app `is_o_pow_pow_of_abs_lt_left [(Term.app `hab.trans_le [(Term.app `le_abs_self [`b])])])])]
               "⟩"))
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "4"))
          []
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
             []
             "=>"
             (Term.anonymousCtor "⟨" [`a "," `ha "," (Term.proj `H "." `IsO)] "⟩"))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "3"))
          []
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
             []
             "=>"
             (Term.anonymousCtor "⟨" [`a "," (Term.app `B [`ha]) "," `H] "⟩"))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "6"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                   [])]
                 "⟩"))]
              [])
             [])
            (group
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `bound_of_is_O_nat_at_top [`H]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hC₀)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hC)])
                     [])]
                   "⟩")])
                [])])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`a "," `ha "," `C "," `hC₀ "," (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))]
               "⟩"))
             [])
            (group
             (Std.Tactic.simpa
              "simpa"
              []
              []
              (Std.Tactic.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `Real.norm_eq_abs)
                  ","
                  (Tactic.simpLemma [] [] `abs_pow)
                  ","
                  (Tactic.simpLemma
                   []
                   []
                   (Term.app `abs_of_nonneg [(Term.proj (Term.proj `ha "." (fieldIdx "1")) "." `le)]))]
                 "]")]
               ["using"
                (Term.app `hC [(Term.app `pow_ne_zero [`n (Term.proj (Term.proj `ha "." (fieldIdx "1")) "." `ne')])])]))
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "6") "→" (num "5"))
          []
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`a "," `ha "," `C "," `H₀ "," `H] "⟩")]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [`a "," (Term.proj `ha "." (fieldIdx "2")) "," `C "," (Term.app `Or.inl [`H₀]) "," `H]
              "⟩"))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "3"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `C)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₀)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                   [])]
                 "⟩"))]
              [])
             [])
            (group
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 `sign_cases_of_C_mul_pow_nonneg
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`n]
                    []
                    "=>"
                    (Term.app
                     (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans)
                     [(Term.app `H [`n])])))]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.paren
                   "("
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.one `rfl)
                      "|"
                      (Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hC₀)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha₀)])
                         [])]
                       "⟩")])
                    [])
                   ")")])
                [])])
             [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])]
                 [":" (Init.Core.«term_=_» `f " = " (num "0"))]
                 [":="
                  [(Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.Ext.«tacticExt___:_»
                        "ext"
                        [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
                        [])
                       []
                       (Std.Tactic.simpa
                        "simpa"
                        []
                        []
                        (Std.Tactic.simpaArgsRest [] [] [] [] ["using" (Term.app `H [`n])]))])))]])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `lt_irrefl) "," (Tactic.simpLemma [] [] `false_or_iff)] "]"]
                 [(Tactic.location "at" (Tactic.locationHyp [`h₀] []))])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [(num "0")
                   ","
                   (Term.anonymousCtor "⟨" [(Term.app (Term.proj `neg_lt_zero "." (fieldIdx "2")) [`h₀]) "," `h₀] "⟩")
                   ","
                   (Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")])]
                  "⟩"))
                [])])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`a
                ","
                (Term.app `A [(Term.anonymousCtor "⟨" [`ha₀ "," `ha] "⟩")])
                ","
                (Term.app
                 `is_O_of_le'
                 [(Term.hole "_")
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`n]
                    []
                    "=>"
                    (Init.Core.«term_$_»
                     (Term.proj (Term.app `H [`n]) "." `trans)
                     " $ "
                     (Term.app `mul_le_mul_of_nonneg_left [(Term.app `le_abs_self [(Term.hole "_")]) `hC₀.le]))))])]
               "⟩"))
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "8"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                   [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`a
                ","
                `ha
                ","
                (Term.app
                 (Term.proj (Term.app `H.def [`zero_lt_one]) "." `mono)
                 [(Term.fun "fun" (Term.basicFun [`n `hn] [] "=>" (Term.hole "_")))])]
               "⟩"))
             [])
            (group
             (tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Real.norm_eq_abs)
                ","
                (Tactic.rwRule [] `Real.norm_eq_abs)
                ","
                (Tactic.rwRule [] `one_mul)
                ","
                (Tactic.rwRule [] `abs_pow)
                ","
                (Tactic.rwRule [] (Term.app `abs_of_pos [(Term.proj `ha "." (fieldIdx "1"))]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "8") "→" (num "7"))
          []
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`a "," `ha "," `H] "⟩")]
             []
             "=>"
             (Term.anonymousCtor "⟨" [`a "," (Term.proj `ha "." (fieldIdx "2")) "," `H] "⟩"))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "3"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                   [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Init.Core.«term_≤_» (num "0") " ≤ " `a))]
                ":="
                (Term.app
                 `nonneg_of_eventually_pow_nonneg
                 [(Init.Core.«term_$_»
                   `H.mono
                   " $ "
                   (Term.fun
                    "fun"
                    (Term.basicFun [`n] [] "=>" (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans))))]))))
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`a
                ","
                (Term.app `A [(Term.anonymousCtor "⟨" [`this "," `ha] "⟩")])
                ","
                (Term.app `is_O.of_bound [(num "1") (Term.hole "_")])]
               "⟩"))
             [])
            (group
             (Std.Tactic.simpa
              "simpa"
              []
              []
              (Std.Tactic.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `Real.norm_eq_abs)
                  ","
                  (Tactic.simpLemma [] [] `one_mul)
                  ","
                  (Tactic.simpLemma [] [] `abs_pow)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`this]))]
                 "]")]
               []))
             [])])
          []
          (Tactic.tfaeFinish "tfae_finish")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeFinish "tfae_finish")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Std.Tactic.rintro
          "rintro"
          [(Std.Tactic.RCases.rintroPat.one
            (Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)]) [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
               [])]
             "⟩"))]
          [])
         [])
        (group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec ":" (Init.Core.«term_≤_» (num "0") " ≤ " `a))]
            ":="
            (Term.app
             `nonneg_of_eventually_pow_nonneg
             [(Init.Core.«term_$_»
               `H.mono
               " $ "
               (Term.fun
                "fun"
                (Term.basicFun [`n] [] "=>" (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans))))]))))
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.anonymousCtor
           "⟨"
           [`a
            ","
            (Term.app `A [(Term.anonymousCtor "⟨" [`this "," `ha] "⟩")])
            ","
            (Term.app `is_O.of_bound [(num "1") (Term.hole "_")])]
           "⟩"))
         [])
        (group
         (Std.Tactic.simpa
          "simpa"
          []
          []
          (Std.Tactic.simpaArgsRest
           []
           []
           ["only"]
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `Real.norm_eq_abs)
              ","
              (Tactic.simpLemma [] [] `one_mul)
              ","
              (Tactic.simpLemma [] [] `abs_pow)
              ","
              (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`this]))]
             "]")]
           []))
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.simpa
       "simpa"
       []
       []
       (Std.Tactic.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `Real.norm_eq_abs)
           ","
           (Tactic.simpLemma [] [] `one_mul)
           ","
           (Tactic.simpLemma [] [] `abs_pow)
           ","
           (Tactic.simpLemma [] [] (Term.app `abs_of_nonneg [`this]))]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_of_nonneg [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_of_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [`a
         ","
         (Term.app `A [(Term.anonymousCtor "⟨" [`this "," `ha] "⟩")])
         ","
         (Term.app `is_O.of_bound [(num "1") (Term.hole "_")])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`a
        ","
        (Term.app `A [(Term.anonymousCtor "⟨" [`this "," `ha] "⟩")])
        ","
        (Term.app `is_O.of_bound [(num "1") (Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_O.of_bound [(num "1") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_O.of_bound
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `A [(Term.anonymousCtor "⟨" [`this "," `ha] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`this "," `ha] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" (Init.Core.«term_≤_» (num "0") " ≤ " `a))]
         ":="
         (Term.app
          `nonneg_of_eventually_pow_nonneg
          [(Init.Core.«term_$_»
            `H.mono
            " $ "
            (Term.fun
             "fun"
             (Term.basicFun [`n] [] "=>" (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans))))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nonneg_of_eventually_pow_nonneg
       [(Init.Core.«term_$_»
         `H.mono
         " $ "
         (Term.fun
          "fun"
          (Term.basicFun [`n] [] "=>" (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_$_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_$_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_$_»
       `H.mono
       " $ "
       (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `abs_nonneg [(Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `abs_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `abs_nonneg [(Term.hole "_")]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, term))
      `H.mono
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Core.«term_$_»
      `H.mono
      " $ "
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.proj (Term.paren "(" (Term.app `abs_nonneg [(Term.hole "_")]) ")") "." `trans))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nonneg_of_eventually_pow_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_≤_» (num "0") " ≤ " `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)]) [])
           ","
           (Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)]) [])
           ","
           (Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)]) [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "3"))
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
/--
    Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.
    
    * 0: $f n = o(a ^ n)$ for some $-R < a < R$;
    * 1: $f n = o(a ^ n)$ for some $0 < a < R$;
    * 2: $f n = O(a ^ n)$ for some $-R < a < R$;
    * 3: $f n = O(a ^ n)$ for some $0 < a < R$;
    * 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
         for all `n`;
    * 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
    * 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
    * 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.
    
    NB: For backwards compatibility, if you add more items to the list, please append them at the end of
    the list. -/
  theorem
    tfae_exists_lt_is_o_pow
    ( f : ℕ → ℝ ) ( R : ℝ )
      :
        Tfae
          [
            ∃ a ∈ ioo - R R , f =o[ at_top ] pow a
              ,
              ∃ a ∈ ioo 0 R , f =o[ at_top ] pow a
              ,
              ∃ a ∈ ioo - R R , f =O[ at_top ] pow a
              ,
              ∃ a ∈ ioo 0 R , f =O[ at_top ] pow a
              ,
              ∃ ( a < R ) ( C ) ( h₀ : 0 < C ∨ 0 < R ) , ∀ n , | f n | ≤ C * a ^ n
              ,
              ∃ ( a ∈ ioo 0 R ) ( C > 0 ) , ∀ n , | f n | ≤ C * a ^ n
              ,
              ∃ a < R , ∀ᶠ n in at_top , | f n | ≤ a ^ n
              ,
              ∃ a ∈ ioo 0 R , ∀ᶠ n in at_top , | f n | ≤ a ^ n
            ]
    :=
      by
        have
            A
              : Ico 0 R ⊆ Ioo - R R
              :=
              fun x hx => ⟨ neg_lt_zero . 2 hx . 1 . trans_lt hx . 2 . trans_le hx . 1 , hx . 2 ⟩
          have B : Ioo 0 R ⊆ Ioo - R R := subset.trans Ioo_subset_Ico_self A
          tfae_have 1 → 3
          exact fun ⟨ a , ha , H ⟩ => ⟨ a , ha , H . IsO ⟩
          tfae_have 2 → 1
          exact fun ⟨ a , ha , H ⟩ => ⟨ a , B ha , H ⟩
          tfae_have 3 → 2
          ·
            rintro ⟨ a , ha , H ⟩
              rcases exists_between abs_lt . 2 ha with ⟨ b , hab , hbR ⟩
              exact
                ⟨
                  b
                    ,
                    ⟨ abs_nonneg a . trans_lt hab , hbR ⟩
                    ,
                    H.trans_is_o is_o_pow_pow_of_abs_lt_left hab.trans_le le_abs_self b
                  ⟩
          tfae_have 2 → 4
          exact fun ⟨ a , ha , H ⟩ => ⟨ a , ha , H . IsO ⟩
          tfae_have 4 → 3
          exact fun ⟨ a , ha , H ⟩ => ⟨ a , B ha , H ⟩
          tfae_have 4 → 6
          ·
            rintro ⟨ a , ha , H ⟩
              rcases bound_of_is_O_nat_at_top H with ⟨ C , hC₀ , hC ⟩
              refine' ⟨ a , ha , C , hC₀ , fun n => _ ⟩
              simpa only [ Real.norm_eq_abs , abs_pow , abs_of_nonneg ha . 1 . le ] using hC pow_ne_zero n ha . 1 . ne'
          tfae_have 6 → 5
          exact fun ⟨ a , ha , C , H₀ , H ⟩ => ⟨ a , ha . 2 , C , Or.inl H₀ , H ⟩
          tfae_have 5 → 3
          ·
            rintro ⟨ a , ha , C , h₀ , H ⟩
              rcases sign_cases_of_C_mul_pow_nonneg fun n => abs_nonneg _ . trans H n with ( rfl | ⟨ hC₀ , ha₀ ⟩ )
              ·
                obtain rfl : f = 0 := by ext n simpa using H n
                  simp only [ lt_irrefl , false_or_iff ] at h₀
                  exact ⟨ 0 , ⟨ neg_lt_zero . 2 h₀ , h₀ ⟩ , is_O_zero _ _ ⟩
              exact
                ⟨
                  a
                    ,
                    A ⟨ ha₀ , ha ⟩
                    ,
                    is_O_of_le' _ fun n => H n . trans $ mul_le_mul_of_nonneg_left le_abs_self _ hC₀.le
                  ⟩
          tfae_have 2 → 8
          ·
            rintro ⟨ a , ha , H ⟩
              refine' ⟨ a , ha , H.def zero_lt_one . mono fun n hn => _ ⟩
              rwa [ Real.norm_eq_abs , Real.norm_eq_abs , one_mul , abs_pow , abs_of_pos ha . 1 ] at hn
          tfae_have 8 → 7
          exact fun ⟨ a , ha , H ⟩ => ⟨ a , ha . 2 , H ⟩
          tfae_have 7 → 3
          ·
            rintro ⟨ a , ha , H ⟩
              have : 0 ≤ a := nonneg_of_eventually_pow_nonneg H.mono $ fun n => abs_nonneg _ . trans
              refine' ⟨ a , A ⟨ this , ha ⟩ , is_O.of_bound 1 _ ⟩
              simpa only [ Real.norm_eq_abs , one_mul , abs_pow , abs_of_nonneg this ]
          tfae_finish
#align tfae_exists_lt_is_o_pow tfae_exists_lt_is_o_pow

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_const_pow_of_one_lt {R : Type _} [NormedRing R] (k : ℕ) {r : ℝ} (hr : 1 < r) :
    (fun n => n ^ k : ℕ → R) =o[at_top] fun n => r ^ n := by
  have : tendsto (fun x : ℝ => x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ := ((this.eventually (gt_mem_nhds hr)).And self_mem_nhds_within).exists
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le
  suffices : (fun n => n ^ k : ℕ → R) =O[at_top] fun n : ℕ => (r' ^ k) ^ n
  exact this.trans_is_o (is_o_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mul, mul_comm, pow_mul]
  suffices : ∀ n : ℕ, ∥(n : R)∥ ≤ (r' - 1)⁻¹ * ∥(1 : R)∥ * ∥r' ^ n∥
  exact (is_O_of_le' _ this).pow _
  intro n
  rw [mul_right_comm]
  refine' n.norm_cast_le.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))
  simpa [div_eq_inv_mul, Real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1
#align is_o_pow_const_const_pow_of_one_lt is_o_pow_const_const_pow_of_one_lt

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
theorem is_o_coe_const_pow_of_one_lt {R : Type _} [NormedRing R] {r : ℝ} (hr : 1 < r) :
    (coe : ℕ → R) =o[at_top] fun n => r ^ n := by
  simpa only [pow_one] using @is_o_pow_const_const_pow_of_one_lt R _ 1 _ hr
#align is_o_coe_const_pow_of_one_lt is_o_coe_const_pow_of_one_lt

/-- If `∥r₁∥ < r₂`, then for any naturak `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type _} [NormedRing R] (k : ℕ) {r₁ : R} {r₂ : ℝ}
    (h : ∥r₁∥ < r₂) : (fun n => n ^ k * r₁ ^ n : ℕ → R) =o[at_top] fun n => r₂ ^ n := by
  by_cases h0:r₁ = 0
  · refine' (is_o_zero _ _).congr' (mem_at_top_sets.2 $ ⟨1, fun n hn => _⟩) eventually_eq.rfl
    simp [zero_pow (zero_lt_one.trans_le hn), h0]
    
  rw [← Ne.def, ← norm_pos_iff] at h0
  have A : (fun n => n ^ k : ℕ → R) =o[at_top] fun n => (r₂ / ∥r₁∥) ^ n :=
    is_o_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices (fun n => r₁ ^ n) =O[at_top] fun n => ∥r₁∥ ^ n by
    simpa [div_mul_cancel _ (pow_pos h0 _).ne'] using A.mul_is_O this
  exact is_O.of_bound 1 (by simpa using eventually_norm_pow_le r₁)
#align is_o_pow_const_mul_const_pow_const_pow_of_norm_lt is_o_pow_const_mul_const_pow_const_pow_of_norm_lt

theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n => n ^ k / r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  (is_o_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero
#align tendsto_pow_const_div_const_pow_of_one_lt tendsto_pow_const_div_const_pow_of_one_lt

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n => n ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  by_cases h0:r = 0
  · exact tendsto_const_nhds.congr' (mem_at_top_sets.2 ⟨1, fun n hn => by simp [zero_lt_one.trans_le hn, h0]⟩)
    
  have hr' : 1 < |r|⁻¹ := one_lt_inv (abs_pos.2 h0) hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'
#align tendsto_pow_const_mul_const_pow_of_abs_lt_one tendsto_pow_const_mul_const_pow_of_abs_lt_one

/-- If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`, singled out
for ease of application. -/
theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n => n ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)
#align tendsto_pow_const_mul_const_pow_of_lt_one tendsto_pow_const_mul_const_pow_of_lt_one

/-- If `|r| < 1`, then `n * r ^ n` tends to zero. -/
theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n => n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr
#align tendsto_self_mul_const_pow_of_abs_lt_one tendsto_self_mul_const_pow_of_abs_lt_one

/-- If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application. -/
theorem tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n => n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r
#align tendsto_self_mul_const_pow_of_lt_one tendsto_self_mul_const_pow_of_lt_one

/-- In a normed ring, the powers of an element x with `∥x∥ < 1` tend to zero. -/
theorem tendsto_pow_at_top_nhds_0_of_norm_lt_1 {R : Type _} [NormedRing R] {x : R} (h : ∥x∥ < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _) h
#align tendsto_pow_at_top_nhds_0_of_norm_lt_1 tendsto_pow_at_top_nhds_0_of_norm_lt_1

theorem tendsto_pow_at_top_nhds_0_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  tendsto_pow_at_top_nhds_0_of_norm_lt_1 h
#align tendsto_pow_at_top_nhds_0_of_abs_lt_1 tendsto_pow_at_top_nhds_0_of_abs_lt_1

/-! ### Geometric series-/


section Geometric

variable {K : Type _} [NormedField K] {ξ : K}

theorem has_sum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : HasSum (fun n : ℕ => ξ ^ n) (1 - ξ)⁻¹ := by
  have xi_ne_one : ξ ≠ 1 := by
    contrapose! h
    simp [h]
  have A : tendsto (fun n => (ξ ^ n - 1) * (ξ - 1)⁻¹) at_top (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_at_top_nhds_0_of_norm_lt_1 h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [has_sum_iff_tendsto_nat_of_summable_norm]
  · simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A
    
  · simp [norm_pow, summable_geometric_of_lt_1 (norm_nonneg _) h]
    
#align has_sum_geometric_of_norm_lt_1 has_sum_geometric_of_norm_lt_1

theorem summable_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : Summable fun n : ℕ => ξ ^ n :=
  ⟨_, has_sum_geometric_of_norm_lt_1 h⟩
#align summable_geometric_of_norm_lt_1 summable_geometric_of_norm_lt_1

theorem tsum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : (∑' n : ℕ, ξ ^ n) = (1 - ξ)⁻¹ :=
  (has_sum_geometric_of_norm_lt_1 h).tsum_eq
#align tsum_geometric_of_norm_lt_1 tsum_geometric_of_norm_lt_1

theorem has_sum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
  has_sum_geometric_of_norm_lt_1 h
#align has_sum_geometric_of_abs_lt_1 has_sum_geometric_of_abs_lt_1

theorem summable_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : Summable fun n : ℕ => r ^ n :=
  summable_geometric_of_norm_lt_1 h
#align summable_geometric_of_abs_lt_1 summable_geometric_of_abs_lt_1

theorem tsum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_1 h
#align tsum_geometric_of_abs_lt_1 tsum_geometric_of_abs_lt_1

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
theorem summable_geometric_iff_norm_lt_1 : (Summable fun n : ℕ => ξ ^ n) ↔ ∥ξ∥ < 1 := by
  refine' ⟨fun h => _, summable_geometric_of_norm_lt_1⟩
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ := (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow _ zero_le_one hk
#align summable_geometric_iff_norm_lt_1 summable_geometric_iff_norm_lt_1

end Geometric

section MulGeometric

theorem summable_norm_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] (k : ℕ) {r : R} (hr : ∥r∥ < 1) :
    Summable fun n : ℕ => ∥(n ^ k * r ^ n : R)∥ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  exact
    summable_of_is_O_nat (summable_geometric_of_lt_1 ((norm_nonneg _).trans hrr'.le) h)
      (is_o_pow_const_mul_const_pow_const_pow_of_norm_lt _ hrr').IsO.norm_left
#align summable_norm_pow_mul_geometric_of_norm_lt_1 summable_norm_pow_mul_geometric_of_norm_lt_1

theorem summable_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] [CompleteSpace R] (k : ℕ) {r : R}
    (hr : ∥r∥ < 1) : Summable (fun n => n ^ k * r ^ n : ℕ → R) :=
  summable_of_summable_norm $ summable_norm_pow_mul_geometric_of_norm_lt_1 _ hr
#align summable_pow_mul_geometric_of_norm_lt_1 summable_pow_mul_geometric_of_norm_lt_1

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `has_sum` version. -/
theorem has_sum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜} (hr : ∥r∥ < 1) :
    HasSum (fun n => n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) := by
  have A : Summable (fun n => n * r ^ n : ℕ → 𝕜) := by simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hr
  have B : HasSum (pow r : ℕ → 𝕜) (1 - r)⁻¹ := has_sum_geometric_of_norm_lt_1 hr
  refine' A.has_sum_iff.2 _
  have hr' : r ≠ 1 := by
    rintro rfl
    simpa [lt_irrefl] using hr
  set s : 𝕜 := ∑' n : ℕ, n * r ^ n
  calc
    s = (1 - r) * s / (1 - r) := (mul_div_cancel_left _ (sub_ne_zero.2 hr'.symm)).symm
    _ = (s - r * s) / (1 - r) := by rw [sub_mul, one_mul]
    _ = (((0 : ℕ) * r ^ 0 + ∑' n : ℕ, (n + 1 : ℕ) * r ^ (n + 1)) - r * s) / (1 - r) := by rw [← tsum_eq_zero_add A]
    _ = ((r * ∑' n : ℕ, (n + 1) * r ^ n) - r * s) / (1 - r) := by simp [pow_succ, mul_left_comm _ r, tsum_mul_left]
    _ = r / (1 - r) ^ 2 := by simp [add_mul, tsum_add A B.summable, mul_add, B.tsum_eq, ← div_eq_mul_inv, sq, div_div]
    
#align has_sum_coe_mul_geometric_of_norm_lt_1 has_sum_coe_mul_geometric_of_norm_lt_1

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜} (hr : ∥r∥ < 1) :
    (∑' n : ℕ, n * r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
  (has_sum_coe_mul_geometric_of_norm_lt_1 hr).tsum_eq
#align tsum_coe_mul_geometric_of_norm_lt_1 tsum_coe_mul_geometric_of_norm_lt_1

end MulGeometric

section SummableLeGeometric

variable [SeminormedAddCommGroup α] {r C : ℝ} {f : ℕ → α}

theorem SeminormedAddCommGroup.cauchySeqOfLeGeometric {C : ℝ} {r : ℝ} (hr : r < 1) {u : ℕ → α}
    (h : ∀ n, ∥u n - u (n + 1)∥ ≤ C * r ^ n) : CauchySeq u :=
  cauchySeqOfLeGeometric r C hr (by simpa [dist_eq_norm] using h)
#align seminormed_add_comm_group.cauchy_seq_of_le_geometric SeminormedAddCommGroup.cauchySeqOfLeGeometric

theorem dist_partial_sum_le_of_le_geometric (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) (n : ℕ) :
    dist (∑ i in range n, f i) (∑ i in range (n + 1), f i) ≤ C * r ^ n := by
  rw [sum_range_succ, dist_eq_norm, ← norm_neg, neg_sub, add_sub_cancel']
  exact hf n
#align dist_partial_sum_le_of_le_geometric dist_partial_sum_le_of_le_geometric

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
theorem cauchySeqFinsetOfGeometricBound (hr : r < 1) (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) :
    CauchySeq fun s : Finset ℕ => ∑ x in s, f x :=
  cauchySeqFinsetOfNormBounded _ (aux_has_sum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).Summable hf
#align cauchy_seq_finset_of_geometric_bound cauchySeqFinsetOfGeometricBound

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
theorem norm_sub_le_of_geometric_bound_of_has_sum (hr : r < 1) (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) {a : α} (ha : HasSum f a)
    (n : ℕ) : ∥(∑ x in Finset.range n, f x) - a∥ ≤ C * r ^ n / (1 - r) := by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat
#align norm_sub_le_of_geometric_bound_of_has_sum norm_sub_le_of_geometric_bound_of_has_sum

@[simp]
theorem dist_partial_sum (u : ℕ → α) (n : ℕ) : dist (∑ k in range (n + 1), u k) (∑ k in range n, u k) = ∥u n∥ := by
  simp [dist_eq_norm, sum_range_succ]
#align dist_partial_sum dist_partial_sum

@[simp]
theorem dist_partial_sum' (u : ℕ → α) (n : ℕ) : dist (∑ k in range n, u k) (∑ k in range (n + 1), u k) = ∥u n∥ := by
  simp [dist_eq_norm', sum_range_succ]
#align dist_partial_sum' dist_partial_sum'

theorem cauchySeriesOfLeGeometric {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1) (h : ∀ n, ∥u n∥ ≤ C * r ^ n) :
    CauchySeq fun n => ∑ k in range n, u k :=
  cauchySeqOfLeGeometric r C hr (by simp [h])
#align cauchy_series_of_le_geometric cauchySeriesOfLeGeometric

theorem NormedAddCommGroup.cauchySeriesOfLeGeometric' {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ∥u n∥ ≤ C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k :=
  (cauchySeriesOfLeGeometric hr h).compTendsto $ tendsto_add_at_top_nat 1
#align normed_add_comm_group.cauchy_series_of_le_geometric' NormedAddCommGroup.cauchySeriesOfLeGeometric'

theorem NormedAddCommGroup.cauchySeriesOfLeGeometric'' {C : ℝ} {u : ℕ → α} {N : ℕ} {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)
    (h : ∀ n ≥ N, ∥u n∥ ≤ C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k := by
  set v : ℕ → α := fun n => if n < N then 0 else u n
  have hC : 0 ≤ C := (zero_le_mul_right $ pow_pos hr₀ N).mp ((norm_nonneg _).trans $ h N $ le_refl N)
  have : ∀ n ≥ N, u n = v n := by
    intro n hn
    simp [v, hn, if_neg (not_lt.mpr hn)]
  refine' cauchySeqSumOfEventuallyEq this (NormedAddCommGroup.cauchySeriesOfLeGeometric' hr₁ _)
  · exact C
    
  intro n
  dsimp [v]
  split_ifs with H H
  · rw [norm_zero]
    exact mul_nonneg hC (pow_nonneg hr₀.le _)
    
  · push_neg  at H
    exact h _ H
    
#align normed_add_comm_group.cauchy_series_of_le_geometric'' NormedAddCommGroup.cauchySeriesOfLeGeometric''

end SummableLeGeometric

section NormedRingGeometric

variable {R : Type _} [NormedRing R] [CompleteSpace R]

open NormedSpace

/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
theorem NormedRing.summable_geometric_of_norm_lt_1 (x : R) (h : ∥x∥ < 1) : Summable fun n : ℕ => x ^ n := by
  have h1 : Summable fun n : ℕ => ∥x∥ ^ n := summable_geometric_of_lt_1 (norm_nonneg _) h
  refine' summable_of_norm_bounded_eventually _ h1 _
  rw [Nat.cofinite_eq_at_top]
  exact eventually_norm_pow_le x
#align normed_ring.summable_geometric_of_norm_lt_1 NormedRing.summable_geometric_of_norm_lt_1

/-- Bound for the sum of a geometric series in a normed ring.  This formula does not assume that the
normed ring satisfies the axiom `∥1∥ = 1`. -/
theorem NormedRing.tsum_geometric_of_norm_lt_1 (x : R) (h : ∥x∥ < 1) :
    ∥∑' n : ℕ, x ^ n∥ ≤ ∥(1 : R)∥ - 1 + (1 - ∥x∥)⁻¹ := by
  rw [tsum_eq_zero_add (NormedRing.summable_geometric_of_norm_lt_1 x h)]
  simp only [pow_zero]
  refine' le_trans (norm_add_le _ _) _
  have : ∥∑' b : ℕ, (fun n => x ^ (n + 1)) b∥ ≤ (1 - ∥x∥)⁻¹ - 1 := by
    refine' tsum_of_norm_bounded _ fun b => norm_pow_le' _ (Nat.succ_pos b)
    convert (has_sum_nat_add_iff' 1).mpr (has_sum_geometric_of_lt_1 (norm_nonneg x) h)
    simp
  linarith
#align normed_ring.tsum_geometric_of_norm_lt_1 NormedRing.tsum_geometric_of_norm_lt_1

theorem geom_series_mul_neg (x : R) (h : ∥x∥ < 1) : (∑' i : ℕ, x ^ i) * (1 - x) = 1 := by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).HasSum.mulRight (1 - x)
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have : tendsto (fun n : ℕ => 1 - x ^ n) at_top (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h)
  convert ← this
  ext n
  rw [← geom_sum_mul_neg, Finset.sum_mul]
#align geom_series_mul_neg geom_series_mul_neg

theorem mul_neg_geom_series (x : R) (h : ∥x∥ < 1) : ((1 - x) * ∑' i : ℕ, x ^ i) = 1 := by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).HasSum.mulLeft (1 - x)
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have : tendsto (fun n : ℕ => 1 - x ^ n) at_top (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h)
  convert ← this
  ext n
  rw [← mul_neg_geom_sum, Finset.mul_sum]
#align mul_neg_geom_series mul_neg_geom_series

end NormedRingGeometric

/-! ### Summability tests based on comparison with geometric series -/


theorem summable_of_ratio_norm_eventually_le {α : Type _} [SeminormedAddCommGroup α] [CompleteSpace α] {f : ℕ → α}
    {r : ℝ} (hr₁ : r < 1) (h : ∀ᶠ n in at_top, ∥f (n + 1)∥ ≤ r * ∥f n∥) : Summable f := by
  by_cases hr₀:0 ≤ r
  · rw [eventually_at_top] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine'
      summable_of_norm_bounded (fun n => ∥f N∥ * r ^ n) (Summable.mul_left _ $ summable_geometric_of_lt_1 hr₀ hr₁)
        fun n => _
    conv_rhs => rw [mul_comm, ← zero_add N]
    refine' le_geom hr₀ n fun i _ => _
    convert hN (i + N) (N.le_add_left i) using 3
    ac_rfl
    
  · push_neg  at hr₀
    refine' summable_of_norm_bounded_eventually 0 summable_zero _
    rw [Nat.cofinite_eq_at_top]
    filter_upwards [h] with _ hn
    by_contra' h
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_lt hn $ mul_neg_of_neg_of_pos hr₀ h)
    
#align summable_of_ratio_norm_eventually_le summable_of_ratio_norm_eventually_le

theorem summable_of_ratio_test_tendsto_lt_one {α : Type _} [NormedAddCommGroup α] [CompleteSpace α] {f : ℕ → α} {l : ℝ}
    (hl₁ : l < 1) (hf : ∀ᶠ n in at_top, f n ≠ 0) (h : Tendsto (fun n => ∥f (n + 1)∥ / ∥f n∥) atTop (𝓝 l)) :
    Summable f := by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine' summable_of_ratio_norm_eventually_le hr₁ _
  filter_upwards [eventually_le_of_tendsto_lt hr₀ h, hf] with _ _ h₁
  rwa [← div_le_iff (norm_pos_iff.mpr h₁)]
#align summable_of_ratio_test_tendsto_lt_one summable_of_ratio_test_tendsto_lt_one

theorem not_summable_of_ratio_norm_eventually_ge {α : Type _} [SeminormedAddCommGroup α] {f : ℕ → α} {r : ℝ}
    (hr : 1 < r) (hf : ∃ᶠ n in at_top, ∥f n∥ ≠ 0) (h : ∀ᶠ n in at_top, r * ∥f n∥ ≤ ∥f (n + 1)∥) : ¬Summable f := by
  rw [eventually_at_top] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_at_top] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine' mt Summable.tendsto_at_top_zero fun h' => not_tendsto_at_top_of_tendsto_nhds (tendsto_norm_zero.comp h') _
  convert tendsto_at_top_of_geom_le _ hr _
  · refine' lt_of_le_of_ne (norm_nonneg _) _
    intro h''
    specialize hN₀ N hNN₀
    simp only [comp_app, zero_add] at h''
    exact hN h''.symm
    
  · intro i
    dsimp only [comp_app]
    convert hN₀ (i + N) (hNN₀.trans (N.le_add_left i)) using 3
    ac_rfl
    
#align not_summable_of_ratio_norm_eventually_ge not_summable_of_ratio_norm_eventually_ge

theorem not_summable_of_ratio_test_tendsto_gt_one {α : Type _} [SeminormedAddCommGroup α] {f : ℕ → α} {l : ℝ}
    (hl : 1 < l) (h : Tendsto (fun n => ∥f (n + 1)∥ / ∥f n∥) atTop (𝓝 l)) : ¬Summable f := by
  have key : ∀ᶠ n in at_top, ∥f n∥ ≠ 0 := by
    filter_upwards [eventually_ge_of_tendsto_gt hl h] with _ hn hc
    rw [hc, div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine' not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently _
  filter_upwards [eventually_ge_of_tendsto_gt hr₁ h, key] with _ _ h₁
  rwa [← le_div_iff (lt_of_le_of_ne (norm_nonneg _) h₁.symm)]
#align not_summable_of_ratio_test_tendsto_gt_one not_summable_of_ratio_test_tendsto_gt_one

section

/-! ### Dirichlet and alternating series tests -/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/-- **Dirichlet's Test** for monotone sequences. -/
theorem Monotone.cauchySeqSeriesMulOfTendstoZeroOfBounded (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hgb : ∀ n, ∥∑ i in range n, z i∥ ≤ b) : CauchySeq fun n => ∑ i in range (n + 1), f i • z i := by
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub, tsub_zero]
  apply
    (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
          ⟨b, eventually_map.mpr $ eventually_of_forall $ fun n => hgb $ n + 1⟩).CauchySeq.add
  refine' (cauchySeqRangeOfNormBounded _ _ (fun n => _ : ∀ n, _ ≤ b * |f (n + 1) - f n|)).neg
  · simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (Nat.le_succ _))), ← mul_sum]
    apply real.uniform_continuous_const_mul.comp_cauchy_seq
    simp_rw [sum_range_sub, sub_eq_add_neg]
    exact (tendsto.cauchy_seq hf0).AddConst
    
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)
    
#align monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded Monotone.cauchySeqSeriesMulOfTendstoZeroOfBounded

/-- **Dirichlet's test** for antitone sequences. -/
theorem Antitone.cauchySeqSeriesMulOfTendstoZeroOfBounded (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hzb : ∀ n, ∥∑ i in range n, z i∥ ≤ b) : CauchySeq fun n => ∑ i in range (n + 1), f i • z i := by
  have hfa' : Monotone fun n => -f n := fun _ _ hab => neg_le_neg $ hfa hab
  have hf0' : tendsto (fun n => -f n) at_top (𝓝 0) := by
    convert hf0.neg
    norm_num
  convert (hfa'.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  funext
  simp
#align antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded Antitone.cauchySeqSeriesMulOfTendstoZeroOfBounded

theorem norm_sum_neg_one_pow_le (n : ℕ) : ∥∑ i in range n, (-1 : ℝ) ^ i∥ ≤ 1 := by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num
#align norm_sum_neg_one_pow_le norm_sum_neg_one_pow_le

/-- The **alternating series test** for monotone sequences.
See also `tendsto_alternating_series_of_monotone_tendsto_zero`. -/
theorem Monotone.cauchySeqAlternatingSeriesOfTendstoZero (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    CauchySeq fun n => ∑ i in range (n + 1), (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
#align monotone.cauchy_seq_alternating_series_of_tendsto_zero Monotone.cauchySeqAlternatingSeriesOfTendstoZero

/-- The **alternating series test** for monotone sequences. -/
theorem Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n => ∑ i in range (n + 1), (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchy_seq_tendsto_of_complete $ hfa.cauchySeqAlternatingSeriesOfTendstoZero hf0
#align monotone.tendsto_alternating_series_of_tendsto_zero Monotone.tendsto_alternating_series_of_tendsto_zero

/-- The **alternating series test** for antitone sequences.
See also `tendsto_alternating_series_of_antitone_tendsto_zero`. -/
theorem Antitone.cauchySeqAlternatingSeriesOfTendstoZero (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    CauchySeq fun n => ∑ i in range (n + 1), (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
#align antitone.cauchy_seq_alternating_series_of_tendsto_zero Antitone.cauchySeqAlternatingSeriesOfTendstoZero

/-- The **alternating series test** for antitone sequences. -/
theorem Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n => ∑ i in range (n + 1), (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchy_seq_tendsto_of_complete $ hfa.cauchySeqAlternatingSeriesOfTendstoZero hf0
#align antitone.tendsto_alternating_series_of_tendsto_zero Antitone.tendsto_alternating_series_of_tendsto_zero

end

/-!
### Factorial
-/


/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `exp_series_div_summable`
for a version that also works in `ℂ`, and `exp_series_summable'` for a version that works in
any normed algebra over `ℝ` or `ℂ`. -/
theorem Real.summable_pow_div_factorial (x : ℝ) : Summable (fun n => x ^ n / n ! : ℕ → ℝ) := by
  -- We start with trivial extimates
  have A : (0 : ℝ) < ⌊∥x∥⌋₊ + 1 := zero_lt_one.trans_le (by simp)
  have B : ∥x∥ / (⌊∥x∥⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊∥x∥⌋₊`.
  suffices : ∀ n ≥ ⌊∥x∥⌋₊, ∥x ^ (n + 1) / (n + 1)!∥ ≤ ∥x∥ / (⌊∥x∥⌋₊ + 1) * ∥x ^ n / ↑n !∥
  exact summable_of_ratio_norm_eventually_le B (eventually_at_top.2 ⟨⌊∥x∥⌋₊, this⟩)
  -- Finally, we prove the upper estimate
  intro n hn
  calc
    ∥x ^ (n + 1) / (n + 1)!∥ = ∥x∥ / (n + 1) * ∥x ^ n / n !∥ := by
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, ← div_mul_div_comm, norm_mul, norm_div, Real.norm_coe_nat,
        Nat.cast_succ]
    _ ≤ ∥x∥ / (⌊∥x∥⌋₊ + 1) * ∥x ^ n / n !∥ := by mono* with 0 ≤ ∥x ^ n / n !∥, 0 ≤ ∥x∥ <;> apply norm_nonneg
    
#align real.summable_pow_div_factorial Real.summable_pow_div_factorial

theorem Real.tendsto_pow_div_factorial_at_top (x : ℝ) : Tendsto (fun n => x ^ n / n ! : ℕ → ℝ) atTop (𝓝 0) :=
  (Real.summable_pow_div_factorial x).tendsto_at_top_zero
#align real.tendsto_pow_div_factorial_at_top Real.tendsto_pow_div_factorial_at_top

