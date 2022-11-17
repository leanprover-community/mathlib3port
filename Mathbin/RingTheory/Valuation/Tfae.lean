/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.Valuation.ValuationSubring
import Mathbin.RingTheory.Ideal.Cotangent
import Mathbin.RingTheory.DedekindDomain.Basic

/-!

# Equivalent conditions for DVR

In `discrete_valuation_ring.tfae`, we show that the following are equivalent for a
noetherian local domain `(R, m, k)`:
- `R` is a discrete valuation ring
- `R` is a valuation ring
- `R` is a dedekind domain
- `R` is integrally closed with a unique prime ideal
- `m` is principal
- `dimₖ m/m² = 1`
- Every nonzero ideal is a power of `m`.

-/


variable (R : Type _) [CommRing R] (K : Type _) [Field K] [Algebra R K] [IsFractionRing R K]

open DiscreteValuation

open LocalRing

open BigOperators

theorem exists_maximal_ideal_pow_eq_of_principal [IsNoetherianRing R] [LocalRing R] [IsDomain R] (h : ¬IsField R)
    (h' : (maximalIdeal R).IsPrincipal) (I : Ideal R) (hI : I ≠ ⊥) : ∃ n : ℕ, I = maximalIdeal R ^ n := by classical
  obtain ⟨x, hx : _ = Ideal.span _⟩ := h'
  by_cases hI':I = ⊤
  · use 0
    rw [pow_zero, hI', Ideal.one_eq_top]
    
  have H : ∀ r : R, ¬IsUnit r ↔ x ∣ r := fun r => (set_like.ext_iff.mp hx r).trans Ideal.mem_span_singleton
  have : x ≠ 0 := by
    rintro rfl
    apply Ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal R) h
    simp [hx]
  have hx' := DiscreteValuationRing.irreducible_of_span_eq_maximal_ideal x this hx
  have H' : ∀ r : R, r ≠ 0 → r ∈ nonunits R → ∃ n : ℕ, Associated (x ^ n) r := by
    intro r hr₁ hr₂
    obtain ⟨f, hf₁, rfl, hf₂⟩ := (WfDvdMonoid.not_unit_iff_exists_factors_eq r hr₁).mp hr₂
    have : ∀ b ∈ f, Associated x b := by
      intro b hb
      exact Irreducible.associated_of_dvd hx' (hf₁ b hb) ((H b).mp (hf₁ b hb).1)
    clear hr₁ hr₂ hf₁
    induction' f using Multiset.induction with fa fs fh
    · exact (hf₂ rfl).elim
      
    rcases eq_or_ne fs ∅ with (rfl | hf')
    · use 1
      rw [pow_one, Multiset.prod_cons, Multiset.empty_eq_zero, Multiset.prod_zero, mul_one]
      exact this _ (Multiset.mem_cons_self _ _)
      
    · obtain ⟨n, hn⟩ := fh hf' fun b hb => this _ (Multiset.mem_cons_of_mem hb)
      use n + 1
      rw [pow_add, Multiset.prod_cons, mul_comm, pow_one]
      exact Associated.mul_mul (this _ (Multiset.mem_cons_self _ _)) hn
      
  have : ∃ n : ℕ, x ^ n ∈ I := by
    obtain ⟨r, hr₁, hr₂⟩ : ∃ r : R, r ∈ I ∧ r ≠ 0 := by
      by_contra h
      push_neg  at h
      apply hI
      rw [eq_bot_iff]
      exact h
    obtain ⟨n, u, rfl⟩ := H' r hr₂ (le_maximal_ideal hI' hr₁)
    use n
    rwa [← I.unit_mul_mem_iff_mem u.is_unit, mul_comm]
  use Nat.find this
  apply le_antisymm
  · change ∀ s ∈ I, s ∈ _
    by_contra hI''
    push_neg  at hI''
    obtain ⟨s, hs₁, hs₂⟩ := hI''
    apply hs₂
    by_cases hs₃:s = 0
    · rw [hs₃]
      exact zero_mem _
      
    obtain ⟨n, u, rfl⟩ := H' s hs₃ (le_maximal_ideal hI' hs₁)
    rw [mul_comm, Ideal.unit_mul_mem_iff_mem _ u.is_unit] at hs₁⊢
    apply Ideal.pow_le_pow (Nat.find_min' this hs₁)
    apply Ideal.pow_mem_pow
    exact (H _).mpr (dvd_refl _)
    
  · rw [hx, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact Nat.find_spec this
    
#align exists_maximal_ideal_pow_eq_of_principal exists_maximal_ideal_pow_eq_of_principal

theorem maximal_ideal_is_principal_of_is_dedekind_domain [LocalRing R] [IsDomain R] [IsDedekindDomain R] :
    (maximalIdeal R).IsPrincipal := by classical
  by_cases ne_bot:maximal_ideal R = ⊥
  · rw [ne_bot]
    infer_instance
    
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ maximal_ideal R, a ≠ (0 : R) := by
    by_contra h'
    push_neg  at h'
    apply ne_bot
    rwa [eq_bot_iff]
  have hle : Ideal.span {a} ≤ maximal_ideal R := by rwa [Ideal.span_le, Set.singleton_subset_iff]
  have : (Ideal.span {a}).radical = maximal_ideal R := by
    rw [Ideal.radical_eq_Inf]
    apply le_antisymm
    · exact Inf_le ⟨hle, inferInstance⟩
      
    · refine' le_Inf fun I hI => (eq_maximal_ideal $ IsDedekindDomain.dimension_le_one _ (fun e => ha₂ _) hI.2).ge
      rw [← Ideal.span_singleton_eq_bot, eq_bot_iff, ← e]
      exact hI.1
      
  have : ∃ n, maximal_ideal R ^ n ≤ Ideal.span {a} := by
    rw [← this]
    apply Ideal.exists_radical_pow_le_of_fg
    exact IsNoetherian.noetherian _
  cases hn : Nat.find this
  · have := Nat.find_spec this
    rw [hn, pow_zero, Ideal.one_eq_top] at this
    exact (Ideal.IsMaximal.ne_top inferInstance (eq_top_iff.mpr $ this.trans hle)).elim
    
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ maximal_ideal R ^ n, ¬b ∈ Ideal.span {a} := by
    by_contra h'
    push_neg  at h'
    rw [Nat.find_eq_iff] at hn
    exact hn.2 n n.lt_succ_self fun x hx => not_not.mp (h' x hx)
  have hb₃ : ∀ m ∈ maximal_ideal R, ∃ k : R, k * a = b * m := by
    intro m hm
    rw [← Ideal.mem_span_singleton']
    apply Nat.find_spec this
    rw [hn, pow_succ']
    exact Ideal.mul_mem_mul hb₁ hm
  have hb₄ : b ≠ 0 := by
    rintro rfl
    apply hb₂
    exact zero_mem _
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.ofId R K).toLinearMap (maximal_ideal R)
  have ha₃ : algebraMap R K a ≠ 0 := is_fraction_ring.to_map_eq_zero_iff.not.mpr ha₂
  by_cases hx:∀ y ∈ M, x * y ∈ M
  · have := isIntegralOfSmulMemSubmodule M _ _ x hx
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebra_map_eq_of_integral this
      refine' (hb₂ (ideal.mem_span_singleton'.mpr ⟨y, _⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul, e, div_mul_cancel _ ha₃]
      
    · rw [Submodule.ne_bot_iff]
      refine' ⟨_, ⟨a, ha₁, rfl⟩, _⟩
      exact is_fraction_ring.to_map_eq_zero_iff.not.mpr ha₂
      
    · apply Submodule.Fg.map
      exact IsNoetherian.noetherian _
      
    
  · have : (M.map (DistribMulAction.toLinearMap R K x)).comap (Algebra.ofId R K).toLinearMap = ⊤ := by
      by_contra h
      apply hx
      rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hb₃ m hm
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel _ ha₃]
      exact ⟨k, le_maximal_ideal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ maximal_ideal R, b * y = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at this
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := this
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq ha₃, ← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine' ⟨⟨y, _⟩⟩
    apply le_antisymm
    · intro m hm
      obtain ⟨k, hk⟩ := hb₃ m hm
      rw [← hy₂, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb₄ hk, mul_comm]
      exact ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
      
    · rwa [Submodule.span_le, Set.singleton_subset_iff]
      
    
#align maximal_ideal_is_principal_of_is_dedekind_domain maximal_ideal_is_principal_of_is_dedekind_domain

/- ./././Mathport/Syntax/Translate/Basic.lean:611:2: warning: expanding binder collection (I «expr ≠ » «expr⊥»()) -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `DiscreteValuationRing.tfae [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsNoetherianRing [`R]) "]")
        (Term.instBinder "[" [] (Term.app `LocalRing [`R]) "]")
        (Term.instBinder "[" [] (Term.app `IsDomain [`R]) "]")
        (Term.explicitBinder "(" [`h] [":" (Init.Core.«term¬_» "¬" (Term.app `IsField [`R]))] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tfae
         [(Init.Core.«term[_,»
           "["
           [(Term.app `DiscreteValuationRing [`R])
            ","
            (Term.app `ValuationRing [`R])
            ","
            (Term.app `IsDedekindDomain [`R])
            ","
            (Init.Logic.«term_∧_»
             (Term.app `IsIntegrallyClosed [`R])
             " ∧ "
             (Init.Logic.«term∃!_,_»
              "∃!"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `P) [(group ":" (Term.app `Ideal [`R]))]))
              ", "
              (Init.Logic.«term_∧_»
               (Init.Logic.«term_≠_» `P " ≠ " (Order.BoundedOrder.«term⊥» "⊥"))
               " ∧ "
               (Term.proj `P "." `IsPrime))))
            ","
            (Term.proj (Term.app `maximalIdeal [`R]) "." `IsPrincipal)
            ","
            (Init.Core.«term_=_»
             (Term.app `FiniteDimensional.finrank [(Term.app `ResidueField [`R]) (Term.app `CotangentSpace [`R])])
             " = "
             (num "1"))
            ","
            (Term.forall
             "∀"
             [(Term.explicitBinder "(" [`I] [] [] ")")
              (Term.explicitBinder
               "("
               [(Term.hole "_")]
               [":" (Init.Logic.«term_≠_» `I " ≠ " (Order.BoundedOrder.«term⊥» "⊥"))]
               []
               ")")]
             []
             ","
             (Init.Logic.«term∃_,_»
              "∃"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) [(group ":" (Init.Data.Nat.Basic.termℕ "ℕ"))]))
              ", "
              (Init.Core.«term_=_» `I " = " (Init.Core.«term_^_» (Term.app `maximalIdeal [`R]) " ^ " `n))))]
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
              [`ne_bot []]
              []
              ":="
              (Term.app `Ring.ne_bot_of_is_maximal_of_not_is_field [(Term.app `maximal_ideal.is_maximal [`R]) `h]))))
           []
           (Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `finrank_eq_one_iff')] "]") [])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group (Tactic.intro "intro" []) []) (group (Tactic.tacticInfer_instance "infer_instance") [])])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "1"))
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group (Tactic.intro "intro" []) [])
                 (group
                  (Std.Tactic.tacticHaveI_
                   "haveI"
                   (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `IsBezout.toGcdDomain [`R]))))
                  [])
                 (group
                  (Std.Tactic.tacticHaveI_
                   "haveI"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec ":" (Term.app `UniqueFactorizationMonoid [`R]))]
                     ":="
                     `ufmOfGcdOfWfDvdMonoid)))
                  [])
                 (group (Tactic.apply "apply" `DiscreteValuationRing.ofUfdOfUniqueIrreducible) [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group
                     (Std.Tactic.obtain
                      "obtain"
                      [(Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
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
                      [":=" [(Term.app `Ring.exists_not_is_unit_of_not_is_field [`h])]])
                     [])
                    (group
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
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp₁)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp₂)])
                            [])]
                          "⟩")])]
                      []
                      [":=" [(Term.app `WfDvdMonoid.exists_irreducible_factor [`hx₂ `hx₁])]])
                     [])
                    (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`p "," `hp₁] "⟩")) [])])
                  [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group (Tactic.exact "exact" `ValuationRing.unique_irreducible) [])])
                  [])])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "4"))
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group (Tactic.intro "intro" [`H]) [])
                 (group
                  (Tactic.exact
                   "exact"
                   (Term.anonymousCtor
                    "⟨"
                    [`inferInstance
                     ","
                     (Term.proj
                      (Term.app
                       (Term.proj (Term.app `DiscreteValuationRing.iff_pid_with_one_nonzero_prime [`R]) "." `mp)
                       [`H])
                      "."
                      (fieldIdx "2"))]
                    "⟩"))
                  [])])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "3"))
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
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₁)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₂)])
                        [])]
                      "⟩"))]
                   [])
                  [])
                 (group
                  (Tactic.exact
                   "exact"
                   (Term.anonymousCtor
                    "⟨"
                    [`inferInstance
                     ","
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`I `hI `hI']
                       []
                       "=>"
                       (Init.Core.«term_▸_»
                        (Term.app
                         `ExistsUnique.unique
                         [`h₂
                          (Term.anonymousCtor "⟨" [`ne_bot "," `inferInstance] "⟩")
                          (Term.anonymousCtor "⟨" [`hI "," `hI'] "⟩")])
                        " ▸ "
                        (Term.app `maximal_ideal.is_maximal [`R]))))
                     ","
                     `h₁]
                    "⟩"))
                  [])])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "5"))
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group (Tactic.intro "intro" [`h]) [])
                 (group (Tactic.exact "exact" (Term.app `maximal_ideal_is_principal_of_is_dedekind_domain [`R])) [])])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "6"))
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
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
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
                     [(Term.typeSpec ":" (Init.Core.«term_∈_» `x " ∈ " (Term.app `maximal_ideal [`R])))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]") [])
                         []
                         (Tactic.exact
                          "exact"
                          (Term.app `Submodule.subset_span [(Term.app `Set.mem_singleton [`x])]))]))))))
                  [])
                 (group
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `x'
                     []
                     [(Term.typeSpec ":" (Term.app `maximal_ideal [`R]))]
                     ":="
                     (Term.anonymousCtor "⟨" [`x "," `this] "⟩"))))
                  [])
                 (group (Mathlib.Tactic.«tacticUse_,,» "use" [(Term.app `Submodule.Quotient.mk [`x'])]) [])
                 (group (Tactic.constructor "constructor") [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group (Tactic.intro "intro" [`e]) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.Quotient.mk_eq_zero)] "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`e] []))])
                     [])
                    (group
                     (Tactic.apply
                      "apply"
                      (Term.app
                       `Ring.ne_bot_of_is_maximal_of_not_is_field
                       [(Term.app `maximal_ideal.is_maximal [`R]) `h]))
                     [])
                    (group
                     (Tactic.apply
                      "apply"
                      (Term.app `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot [(Term.app `maximal_ideal [`R])]))
                     [])
                    (group
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group
                        (Tactic.exact
                         "exact"
                         (Term.anonymousCtor
                          "⟨"
                          [(«term{_}» "{" [`x] "}")
                           ","
                           (Init.Core.«term_▸_»
                            (Term.proj (Term.app `Finset.coe_singleton [`x]) "." `symm)
                            " ▸ "
                            `hx.symm)]
                          "⟩"))
                        [])])
                     [])
                    (group
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group
                        (Mathlib.Tactic.Conv.convLHS
                         "conv_lhs"
                         []
                         []
                         "=>"
                         (Tactic.Conv.convSeq
                          (Tactic.Conv.convSeq1Indented
                           [(Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]"))])))
                        [])
                       (group
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.mem_smul_top_iff)] "]")
                         [(Tactic.location "at" (Tactic.locationHyp [`e] []))])
                        [])
                       (group
                        (tacticRwa__
                         "rwa"
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `Submodule.span_le) "," (Tactic.rwRule [] `Set.singleton_subset_iff)]
                          "]")
                         [])
                        [])])
                     [])
                    (group
                     («tactic___;_»
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(group
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule
                            []
                            (Term.app
                             `LocalRing.jacobson_eq_maximal_ideal
                             [(Term.typeAscription
                               "("
                               (Order.BoundedOrder.«term⊥» "⊥")
                               ":"
                               [(Term.app `Ideal [`R])]
                               ")")
                              `bot_ne_top]))]
                          "]")
                         [])
                        [])
                       (group (Tactic.exact "exact" (Term.app `le_refl [(Term.hole "_")])) [])])
                     [])])
                  [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group
                     (Tactic.refine'
                      "refine'"
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`w]
                        []
                        "=>"
                        (Init.Core.«term_$_»
                         (Term.app `Quotient.inductionOn' [`w])
                         " $ "
                         (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))))))
                     [])
                    (group
                     (Std.Tactic.obtain
                      "obtain"
                      [(Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                            [])]
                          "⟩")])]
                      []
                      [":=" [`y]])
                     [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `hx) "," (Tactic.rwRule [] `Submodule.mem_span_singleton)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                     [])
                    (group
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
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                            [])]
                          "⟩")])]
                      []
                      [":=" [`hy]])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.anonymousCtor "⟨" [(Term.app `Ideal.Quotient.mk [(Term.hole "_") `a]) "," `rfl] "⟩"))
                     [])])
                  [])])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "6") "→" (num "5"))
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
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx')])
                        [])]
                      "⟩"))]
                   [])
                  [])
                 (group (Tactic.induction "induction" [`x] ["using" `Quotient.inductionOn'] [] []) [])
                 (group (Mathlib.Tactic.«tacticUse_,,» "use" [`x]) [])
                 (group (Tactic.apply "apply" `le_antisymm) [])
                 (group (Mathlib.Tactic.tacticSwap "swap") [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Submodule.span_le) "," (Tactic.rwRule [] `Set.singleton_subset_iff)]
                       "]")
                      [])
                     [])
                    (group (Tactic.exact "exact" `x.prop) [])])
                  [])
                 (group
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h₁ []]
                     [(Term.typeSpec
                       ":"
                       (Init.Core.«term_≤_»
                        (Order.Basic.«term_⊔_»
                         (Term.typeAscription
                          "("
                          (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])
                          ":"
                          [(Term.app `Ideal [`R])]
                          ")")
                         " ⊔ "
                         (Term.app `maximal_ideal [`R]))
                        " ≤ "
                        (Order.Basic.«term_⊔_»
                         (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])
                         " ⊔ "
                         (Algebra.Group.Defs.«term_•_»
                          (Term.app `maximal_ideal [`R])
                          " • "
                          (Term.app `maximal_ideal [`R])))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.refine' "refine'" (Term.app `sup_le [`le_sup_left (Term.hole "_")]))
                         []
                         (Std.Tactic.rintro
                          "rintro"
                          [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `m))
                           (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `hm))]
                          [])
                         []
                         (Std.Tactic.obtain
                          "obtain"
                          [(Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                                [])]
                              "⟩")])]
                          []
                          [":="
                           [(Term.app
                             `hx'
                             [(Term.app `Submodule.Quotient.mk [(Term.anonymousCtor "⟨" [`m "," `hm] "⟩")])])]])
                         []
                         (Tactic.induction "induction" [`c] ["using" `Quotient.inductionOn'] [] [])
                         []
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule
                             [(patternIgnore (token.«← » "←"))]
                             (Term.app `sub_sub_cancel [(Init.Core.«term_*_» `c " * " `x) `m]))]
                           "]")
                          [])
                         []
                         (Tactic.apply "apply" (Term.app `sub_mem [(Term.hole "_") (Term.hole "_")]))
                         []
                         («tactic___;_»
                          (cdotTk (patternIgnore (token.«·» "·")))
                          [(group (Tactic.tacticInfer_instance "infer_instance") [])])
                         []
                         («tactic___;_»
                          (cdotTk (patternIgnore (token.«·» "·")))
                          [(group
                            (Tactic.refine'
                             "refine'"
                             (Term.app
                              `Ideal.mem_sup_left
                              [(Term.app `ideal.mem_span_singleton'.mpr [(Term.anonymousCtor "⟨" [`c "," `rfl] "⟩")])]))
                            [])])
                         []
                         («tactic___;_»
                          (cdotTk (patternIgnore (token.«·» "·")))
                          [(group
                            (Tactic.tacticHave_
                             "have"
                             (Term.haveDecl
                              (Term.haveIdDecl
                               []
                               []
                               ":="
                               (Term.app
                                (Term.proj (Term.app `Submodule.Quotient.eq [(Term.hole "_")]) "." `mp)
                                [`hc]))))
                            [])
                           (group
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.mem_smul_top_iff)] "]")
                             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                            [])
                           (group (Tactic.exact "exact" (Term.app `Ideal.mem_sup_right [`this])) [])])]))))))
                  [])
                 (group
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h₂ []]
                     [(Term.typeSpec
                       ":"
                       (Init.Core.«term_≤_»
                        (Term.app `maximal_ideal [`R])
                        " ≤ "
                        (Term.proj
                         (Term.typeAscription "(" (Order.BoundedOrder.«term⊥» "⊥") ":" [(Term.app `Ideal [`R])] ")")
                         "."
                         `jacobson)))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LocalRing.jacobson_eq_maximal_ideal)] "]")
                          [])
                         []
                         (exacts "exacts" "[" [(Term.app `le_refl [(Term.hole "_")]) "," `bot_ne_top] "]")]))))))
                  [])
                 (group
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     []
                     ":="
                     (Term.app
                      `Submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
                      [(Term.app `IsNoetherian.noetherian [(Term.hole "_")]) `h₂ `h₁]))))
                  [])
                 (group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Submodule.bot_smul) "," (Tactic.rwRule [] `sup_bot_eq)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                  [])
                 (group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sup_eq_left) "," (Tactic.rwRule [] `eq_comm)]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `le_sup_left.antisymm
                    [(Init.Core.«term_$_» `h₁.trans " $ " (Term.app `le_of_eq [`this]))]))
                  [])])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "7"))
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group (Tactic.exact "exact" (Term.app `exists_maximal_ideal_pow_eq_of_principal [`R `h])) [])])
               []
               (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "2"))
               []
               («tactic___;_»
                (cdotTk (patternIgnore (token.«·» "·")))
                [(group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ValuationRing.iff_ideal_total)] "]")
                   [])
                  [])
                 (group (Tactic.intro "intro" [`H]) [])
                 (group (Tactic.constructor "constructor") [])
                 (group (Tactic.intro "intro" [`I `J]) [])
                 (group
                  (Classical.«tacticBy_cases_:_»
                   "by_cases"
                   [`hI ":"]
                   (Init.Core.«term_=_» `I " = " (Order.BoundedOrder.«term⊥» "⊥")))
                  [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group (Tactic.subst "subst" [`hI]) [])
                    (group (Mathlib.Tactic.tacticLeft "left") [])
                    (group (Tactic.exact "exact" `bot_le) [])])
                  [])
                 (group
                  (Classical.«tacticBy_cases_:_»
                   "by_cases"
                   [`hJ ":"]
                   (Init.Core.«term_=_» `J " = " (Order.BoundedOrder.«term⊥» "⊥")))
                  [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group (Tactic.subst "subst" [`hJ]) [])
                    (group (Mathlib.Tactic.tacticRight "right") [])
                    (group (Tactic.exact "exact" `bot_le) [])])
                  [])
                 (group
                  (Std.Tactic.obtain
                   "obtain"
                   [(Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                         [])]
                       "⟩")])]
                   []
                   [":=" [(Term.app `H [`I `hI])]])
                  [])
                 (group
                  (Std.Tactic.obtain
                   "obtain"
                   [(Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                         [])]
                       "⟩")])]
                   []
                   [":=" [(Term.app `H [`J `hJ])]])
                  [])
                 (group
                  (Tactic.cases'
                   "cases'"
                   [(Tactic.casesTarget [] (Term.app `le_total [`m `n]))]
                   []
                   ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
                  [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group (Mathlib.Tactic.tacticLeft "left") [])
                    (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
                  [])
                 (group
                  («tactic___;_»
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(group (Mathlib.Tactic.tacticRight "right") [])
                    (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
                  [])])
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`ne_bot []]
             []
             ":="
             (Term.app `Ring.ne_bot_of_is_maximal_of_not_is_field [(Term.app `maximal_ideal.is_maximal [`R]) `h]))))
          []
          (Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `finrank_eq_one_iff')] "]") [])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
              []
              («tactic___;_»
               (cdotTk (patternIgnore (token.«·» "·")))
               [(group (Tactic.intro "intro" []) []) (group (Tactic.tacticInfer_instance "infer_instance") [])])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "1"))
              []
              («tactic___;_»
               (cdotTk (patternIgnore (token.«·» "·")))
               [(group (Tactic.intro "intro" []) [])
                (group
                 (Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `IsBezout.toGcdDomain [`R]))))
                 [])
                (group
                 (Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec ":" (Term.app `UniqueFactorizationMonoid [`R]))]
                    ":="
                    `ufmOfGcdOfWfDvdMonoid)))
                 [])
                (group (Tactic.apply "apply" `DiscreteValuationRing.ofUfdOfUniqueIrreducible) [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group
                    (Std.Tactic.obtain
                     "obtain"
                     [(Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
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
                     [":=" [(Term.app `Ring.exists_not_is_unit_of_not_is_field [`h])]])
                    [])
                   (group
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
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp₁)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp₂)])
                           [])]
                         "⟩")])]
                     []
                     [":=" [(Term.app `WfDvdMonoid.exists_irreducible_factor [`hx₂ `hx₁])]])
                    [])
                   (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`p "," `hp₁] "⟩")) [])])
                 [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Tactic.exact "exact" `ValuationRing.unique_irreducible) [])])
                 [])])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "4"))
              []
              («tactic___;_»
               (cdotTk (patternIgnore (token.«·» "·")))
               [(group (Tactic.intro "intro" [`H]) [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [`inferInstance
                    ","
                    (Term.proj
                     (Term.app
                      (Term.proj (Term.app `DiscreteValuationRing.iff_pid_with_one_nonzero_prime [`R]) "." `mp)
                      [`H])
                     "."
                     (fieldIdx "2"))]
                   "⟩"))
                 [])])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "3"))
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₂)])
                       [])]
                     "⟩"))]
                  [])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [`inferInstance
                    ","
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`I `hI `hI']
                      []
                      "=>"
                      (Init.Core.«term_▸_»
                       (Term.app
                        `ExistsUnique.unique
                        [`h₂
                         (Term.anonymousCtor "⟨" [`ne_bot "," `inferInstance] "⟩")
                         (Term.anonymousCtor "⟨" [`hI "," `hI'] "⟩")])
                       " ▸ "
                       (Term.app `maximal_ideal.is_maximal [`R]))))
                    ","
                    `h₁]
                   "⟩"))
                 [])])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "5"))
              []
              («tactic___;_»
               (cdotTk (patternIgnore (token.«·» "·")))
               [(group (Tactic.intro "intro" [`h]) [])
                (group (Tactic.exact "exact" (Term.app `maximal_ideal_is_principal_of_is_dedekind_domain [`R])) [])])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "6"))
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
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
                    [(Term.typeSpec ":" (Init.Core.«term_∈_» `x " ∈ " (Term.app `maximal_ideal [`R])))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]") [])
                        []
                        (Tactic.exact
                         "exact"
                         (Term.app `Submodule.subset_span [(Term.app `Set.mem_singleton [`x])]))]))))))
                 [])
                (group
                 (Tactic.tacticLet_
                  "let"
                  (Term.letDecl
                   (Term.letIdDecl
                    `x'
                    []
                    [(Term.typeSpec ":" (Term.app `maximal_ideal [`R]))]
                    ":="
                    (Term.anonymousCtor "⟨" [`x "," `this] "⟩"))))
                 [])
                (group (Mathlib.Tactic.«tacticUse_,,» "use" [(Term.app `Submodule.Quotient.mk [`x'])]) [])
                (group (Tactic.constructor "constructor") [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Tactic.intro "intro" [`e]) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.Quotient.mk_eq_zero)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`e] []))])
                    [])
                   (group
                    (Tactic.apply
                     "apply"
                     (Term.app
                      `Ring.ne_bot_of_is_maximal_of_not_is_field
                      [(Term.app `maximal_ideal.is_maximal [`R]) `h]))
                    [])
                   (group
                    (Tactic.apply
                     "apply"
                     (Term.app `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot [(Term.app `maximal_ideal [`R])]))
                    [])
                   (group
                    («tactic___;_»
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(group
                       (Tactic.exact
                        "exact"
                        (Term.anonymousCtor
                         "⟨"
                         [(«term{_}» "{" [`x] "}")
                          ","
                          (Init.Core.«term_▸_»
                           (Term.proj (Term.app `Finset.coe_singleton [`x]) "." `symm)
                           " ▸ "
                           `hx.symm)]
                         "⟩"))
                       [])])
                    [])
                   (group
                    («tactic___;_»
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(group
                       (Mathlib.Tactic.Conv.convLHS
                        "conv_lhs"
                        []
                        []
                        "=>"
                        (Tactic.Conv.convSeq
                         (Tactic.Conv.convSeq1Indented
                          [(Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]"))])))
                       [])
                      (group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.mem_smul_top_iff)] "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`e] []))])
                       [])
                      (group
                       (tacticRwa__
                        "rwa"
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] `Submodule.span_le) "," (Tactic.rwRule [] `Set.singleton_subset_iff)]
                         "]")
                        [])
                       [])])
                    [])
                   (group
                    («tactic___;_»
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule
                           []
                           (Term.app
                            `LocalRing.jacobson_eq_maximal_ideal
                            [(Term.typeAscription "(" (Order.BoundedOrder.«term⊥» "⊥") ":" [(Term.app `Ideal [`R])] ")")
                             `bot_ne_top]))]
                         "]")
                        [])
                       [])
                      (group (Tactic.exact "exact" (Term.app `le_refl [(Term.hole "_")])) [])])
                    [])])
                 [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group
                    (Tactic.refine'
                     "refine'"
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`w]
                       []
                       "=>"
                       (Init.Core.«term_$_»
                        (Term.app `Quotient.inductionOn' [`w])
                        " $ "
                        (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))))))
                    [])
                   (group
                    (Std.Tactic.obtain
                     "obtain"
                     [(Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                           [])]
                         "⟩")])]
                     []
                     [":=" [`y]])
                    [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `hx) "," (Tactic.rwRule [] `Submodule.mem_span_singleton)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                    [])
                   (group
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
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                           [])]
                         "⟩")])]
                     []
                     [":=" [`hy]])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.anonymousCtor "⟨" [(Term.app `Ideal.Quotient.mk [(Term.hole "_") `a]) "," `rfl] "⟩"))
                    [])])
                 [])])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "6") "→" (num "5"))
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx')])
                       [])]
                     "⟩"))]
                  [])
                 [])
                (group (Tactic.induction "induction" [`x] ["using" `Quotient.inductionOn'] [] []) [])
                (group (Mathlib.Tactic.«tacticUse_,,» "use" [`x]) [])
                (group (Tactic.apply "apply" `le_antisymm) [])
                (group (Mathlib.Tactic.tacticSwap "swap") [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `Submodule.span_le) "," (Tactic.rwRule [] `Set.singleton_subset_iff)]
                      "]")
                     [])
                    [])
                   (group (Tactic.exact "exact" `x.prop) [])])
                 [])
                (group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h₁ []]
                    [(Term.typeSpec
                      ":"
                      (Init.Core.«term_≤_»
                       (Order.Basic.«term_⊔_»
                        (Term.typeAscription
                         "("
                         (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])
                         ":"
                         [(Term.app `Ideal [`R])]
                         ")")
                        " ⊔ "
                        (Term.app `maximal_ideal [`R]))
                       " ≤ "
                       (Order.Basic.«term_⊔_»
                        (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])
                        " ⊔ "
                        (Algebra.Group.Defs.«term_•_»
                         (Term.app `maximal_ideal [`R])
                         " • "
                         (Term.app `maximal_ideal [`R])))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.refine' "refine'" (Term.app `sup_le [`le_sup_left (Term.hole "_")]))
                        []
                        (Std.Tactic.rintro
                         "rintro"
                         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `m))
                          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `hm))]
                         [])
                        []
                        (Std.Tactic.obtain
                         "obtain"
                         [(Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.tuple
                             "⟨"
                             [(Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                               [])]
                             "⟩")])]
                         []
                         [":="
                          [(Term.app
                            `hx'
                            [(Term.app `Submodule.Quotient.mk [(Term.anonymousCtor "⟨" [`m "," `hm] "⟩")])])]])
                        []
                        (Tactic.induction "induction" [`c] ["using" `Quotient.inductionOn'] [] [])
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule
                            [(patternIgnore (token.«← » "←"))]
                            (Term.app `sub_sub_cancel [(Init.Core.«term_*_» `c " * " `x) `m]))]
                          "]")
                         [])
                        []
                        (Tactic.apply "apply" (Term.app `sub_mem [(Term.hole "_") (Term.hole "_")]))
                        []
                        («tactic___;_»
                         (cdotTk (patternIgnore (token.«·» "·")))
                         [(group (Tactic.tacticInfer_instance "infer_instance") [])])
                        []
                        («tactic___;_»
                         (cdotTk (patternIgnore (token.«·» "·")))
                         [(group
                           (Tactic.refine'
                            "refine'"
                            (Term.app
                             `Ideal.mem_sup_left
                             [(Term.app `ideal.mem_span_singleton'.mpr [(Term.anonymousCtor "⟨" [`c "," `rfl] "⟩")])]))
                           [])])
                        []
                        («tactic___;_»
                         (cdotTk (patternIgnore (token.«·» "·")))
                         [(group
                           (Tactic.tacticHave_
                            "have"
                            (Term.haveDecl
                             (Term.haveIdDecl
                              []
                              []
                              ":="
                              (Term.app
                               (Term.proj (Term.app `Submodule.Quotient.eq [(Term.hole "_")]) "." `mp)
                               [`hc]))))
                           [])
                          (group
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.mem_smul_top_iff)] "]")
                            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                           [])
                          (group (Tactic.exact "exact" (Term.app `Ideal.mem_sup_right [`this])) [])])]))))))
                 [])
                (group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h₂ []]
                    [(Term.typeSpec
                      ":"
                      (Init.Core.«term_≤_»
                       (Term.app `maximal_ideal [`R])
                       " ≤ "
                       (Term.proj
                        (Term.typeAscription "(" (Order.BoundedOrder.«term⊥» "⊥") ":" [(Term.app `Ideal [`R])] ")")
                        "."
                        `jacobson)))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LocalRing.jacobson_eq_maximal_ideal)] "]")
                         [])
                        []
                        (exacts "exacts" "[" [(Term.app `le_refl [(Term.hole "_")]) "," `bot_ne_top] "]")]))))))
                 [])
                (group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app
                     `Submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
                     [(Term.app `IsNoetherian.noetherian [(Term.hole "_")]) `h₂ `h₁]))))
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.bot_smul) "," (Tactic.rwRule [] `sup_bot_eq)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sup_eq_left) "," (Tactic.rwRule [] `eq_comm)]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.app `le_sup_left.antisymm [(Init.Core.«term_$_» `h₁.trans " $ " (Term.app `le_of_eq [`this]))]))
                 [])])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "7"))
              []
              («tactic___;_»
               (cdotTk (patternIgnore (token.«·» "·")))
               [(group (Tactic.exact "exact" (Term.app `exists_maximal_ideal_pow_eq_of_principal [`R `h])) [])])
              []
              (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "2"))
              []
              («tactic___;_»
               (cdotTk (patternIgnore (token.«·» "·")))
               [(group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ValuationRing.iff_ideal_total)] "]")
                  [])
                 [])
                (group (Tactic.intro "intro" [`H]) [])
                (group (Tactic.constructor "constructor") [])
                (group (Tactic.intro "intro" [`I `J]) [])
                (group
                 (Classical.«tacticBy_cases_:_»
                  "by_cases"
                  [`hI ":"]
                  (Init.Core.«term_=_» `I " = " (Order.BoundedOrder.«term⊥» "⊥")))
                 [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Tactic.subst "subst" [`hI]) [])
                   (group (Mathlib.Tactic.tacticLeft "left") [])
                   (group (Tactic.exact "exact" `bot_le) [])])
                 [])
                (group
                 (Classical.«tacticBy_cases_:_»
                  "by_cases"
                  [`hJ ":"]
                  (Init.Core.«term_=_» `J " = " (Order.BoundedOrder.«term⊥» "⊥")))
                 [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Tactic.subst "subst" [`hJ]) [])
                   (group (Mathlib.Tactic.tacticRight "right") [])
                   (group (Tactic.exact "exact" `bot_le) [])])
                 [])
                (group
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app `H [`I `hI])]])
                 [])
                (group
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app `H [`J `hJ])]])
                 [])
                (group
                 (Tactic.cases'
                  "cases'"
                  [(Tactic.casesTarget [] (Term.app `le_total [`m `n]))]
                  []
                  ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
                 [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Mathlib.Tactic.tacticLeft "left") [])
                   (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
                 [])
                (group
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group (Mathlib.Tactic.tacticRight "right") [])
                   (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
                 [])])
              []
              (Tactic.tfaeFinish "tfae_finish")])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `finrank_eq_one_iff')] "]") [])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.intro "intro" []) []) (group (Tactic.tacticInfer_instance "infer_instance") [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "1"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.intro "intro" []) [])
            (group
             (Std.Tactic.tacticHaveI_
              "haveI"
              (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `IsBezout.toGcdDomain [`R]))))
             [])
            (group
             (Std.Tactic.tacticHaveI_
              "haveI"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `UniqueFactorizationMonoid [`R]))]
                ":="
                `ufmOfGcdOfWfDvdMonoid)))
             [])
            (group (Tactic.apply "apply" `DiscreteValuationRing.ofUfdOfUniqueIrreducible) [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
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
                 [":=" [(Term.app `Ring.exists_not_is_unit_of_not_is_field [`h])]])
                [])
               (group
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp₂)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [(Term.app `WfDvdMonoid.exists_irreducible_factor [`hx₂ `hx₁])]])
                [])
               (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`p "," `hp₁] "⟩")) [])])
             [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group (Tactic.exact "exact" `ValuationRing.unique_irreducible) [])])
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "4"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.intro "intro" [`H]) [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`inferInstance
                ","
                (Term.proj
                 (Term.app
                  (Term.proj (Term.app `DiscreteValuationRing.iff_pid_with_one_nonzero_prime [`R]) "." `mp)
                  [`H])
                 "."
                 (fieldIdx "2"))]
               "⟩"))
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "3"))
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
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h₂)])
                   [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`inferInstance
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`I `hI `hI']
                  []
                  "=>"
                  (Init.Core.«term_▸_»
                   (Term.app
                    `ExistsUnique.unique
                    [`h₂
                     (Term.anonymousCtor "⟨" [`ne_bot "," `inferInstance] "⟩")
                     (Term.anonymousCtor "⟨" [`hI "," `hI'] "⟩")])
                   " ▸ "
                   (Term.app `maximal_ideal.is_maximal [`R]))))
                ","
                `h₁]
               "⟩"))
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "5"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.intro "intro" [`h]) [])
            (group (Tactic.exact "exact" (Term.app `maximal_ideal_is_principal_of_is_dedekind_domain [`R])) [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "6"))
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
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
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
                [(Term.typeSpec ":" (Init.Core.«term_∈_» `x " ∈ " (Term.app `maximal_ideal [`R])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]") [])
                    []
                    (Tactic.exact "exact" (Term.app `Submodule.subset_span [(Term.app `Set.mem_singleton [`x])]))]))))))
             [])
            (group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `x'
                []
                [(Term.typeSpec ":" (Term.app `maximal_ideal [`R]))]
                ":="
                (Term.anonymousCtor "⟨" [`x "," `this] "⟩"))))
             [])
            (group (Mathlib.Tactic.«tacticUse_,,» "use" [(Term.app `Submodule.Quotient.mk [`x'])]) [])
            (group (Tactic.constructor "constructor") [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group (Tactic.intro "intro" [`e]) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.Quotient.mk_eq_zero)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`e] []))])
                [])
               (group
                (Tactic.apply
                 "apply"
                 (Term.app `Ring.ne_bot_of_is_maximal_of_not_is_field [(Term.app `maximal_ideal.is_maximal [`R]) `h]))
                [])
               (group
                (Tactic.apply
                 "apply"
                 (Term.app `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot [(Term.app `maximal_ideal [`R])]))
                [])
               (group
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group
                   (Tactic.exact
                    "exact"
                    (Term.anonymousCtor
                     "⟨"
                     [(«term{_}» "{" [`x] "}")
                      ","
                      (Init.Core.«term_▸_» (Term.proj (Term.app `Finset.coe_singleton [`x]) "." `symm) " ▸ " `hx.symm)]
                     "⟩"))
                   [])])
                [])
               (group
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group
                   (Mathlib.Tactic.Conv.convLHS
                    "conv_lhs"
                    []
                    []
                    "=>"
                    (Tactic.Conv.convSeq
                     (Tactic.Conv.convSeq1Indented
                      [(Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hx)] "]"))])))
                   [])
                  (group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.mem_smul_top_iff)] "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`e] []))])
                   [])
                  (group
                   (tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `Submodule.span_le) "," (Tactic.rwRule [] `Set.singleton_subset_iff)]
                     "]")
                    [])
                   [])])
                [])
               (group
                («tactic___;_»
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       []
                       (Term.app
                        `LocalRing.jacobson_eq_maximal_ideal
                        [(Term.typeAscription "(" (Order.BoundedOrder.«term⊥» "⊥") ":" [(Term.app `Ideal [`R])] ")")
                         `bot_ne_top]))]
                     "]")
                    [])
                   [])
                  (group (Tactic.exact "exact" (Term.app `le_refl [(Term.hole "_")])) [])])
                [])])
             [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`w]
                   []
                   "=>"
                   (Init.Core.«term_$_»
                    (Term.app `Quotient.inductionOn' [`w])
                    " $ "
                    (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))))))
                [])
               (group
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [`y]])
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `hx) "," (Tactic.rwRule [] `Submodule.mem_span_singleton)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                [])
               (group
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [`hy]])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor "⟨" [(Term.app `Ideal.Quotient.mk [(Term.hole "_") `a]) "," `rfl] "⟩"))
                [])])
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "6") "→" (num "5"))
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
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx')])
                   [])]
                 "⟩"))]
              [])
             [])
            (group (Tactic.induction "induction" [`x] ["using" `Quotient.inductionOn'] [] []) [])
            (group (Mathlib.Tactic.«tacticUse_,,» "use" [`x]) [])
            (group (Tactic.apply "apply" `le_antisymm) [])
            (group (Mathlib.Tactic.tacticSwap "swap") [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Submodule.span_le) "," (Tactic.rwRule [] `Set.singleton_subset_iff)]
                  "]")
                 [])
                [])
               (group (Tactic.exact "exact" `x.prop) [])])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h₁ []]
                [(Term.typeSpec
                  ":"
                  (Init.Core.«term_≤_»
                   (Order.Basic.«term_⊔_»
                    (Term.typeAscription
                     "("
                     (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])
                     ":"
                     [(Term.app `Ideal [`R])]
                     ")")
                    " ⊔ "
                    (Term.app `maximal_ideal [`R]))
                   " ≤ "
                   (Order.Basic.«term_⊔_»
                    (Term.app `Ideal.span [(«term{_}» "{" [`x] "}")])
                    " ⊔ "
                    (Algebra.Group.Defs.«term_•_»
                     (Term.app `maximal_ideal [`R])
                     " • "
                     (Term.app `maximal_ideal [`R])))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.refine' "refine'" (Term.app `sup_le [`le_sup_left (Term.hole "_")]))
                    []
                    (Std.Tactic.rintro
                     "rintro"
                     [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `m))
                      (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `hm))]
                     [])
                    []
                    (Std.Tactic.obtain
                     "obtain"
                     [(Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hc)])
                           [])]
                         "⟩")])]
                     []
                     [":="
                      [(Term.app
                        `hx'
                        [(Term.app `Submodule.Quotient.mk [(Term.anonymousCtor "⟨" [`m "," `hm] "⟩")])])]])
                    []
                    (Tactic.induction "induction" [`c] ["using" `Quotient.inductionOn'] [] [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app `sub_sub_cancel [(Init.Core.«term_*_» `c " * " `x) `m]))]
                      "]")
                     [])
                    []
                    (Tactic.apply "apply" (Term.app `sub_mem [(Term.hole "_") (Term.hole "_")]))
                    []
                    («tactic___;_»
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(group (Tactic.tacticInfer_instance "infer_instance") [])])
                    []
                    («tactic___;_»
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(group
                       (Tactic.refine'
                        "refine'"
                        (Term.app
                         `Ideal.mem_sup_left
                         [(Term.app `ideal.mem_span_singleton'.mpr [(Term.anonymousCtor "⟨" [`c "," `rfl] "⟩")])]))
                       [])])
                    []
                    («tactic___;_»
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(group
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          []
                          []
                          ":="
                          (Term.app (Term.proj (Term.app `Submodule.Quotient.eq [(Term.hole "_")]) "." `mp) [`hc]))))
                       [])
                      (group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.mem_smul_top_iff)] "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                       [])
                      (group (Tactic.exact "exact" (Term.app `Ideal.mem_sup_right [`this])) [])])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h₂ []]
                [(Term.typeSpec
                  ":"
                  (Init.Core.«term_≤_»
                   (Term.app `maximal_ideal [`R])
                   " ≤ "
                   (Term.proj
                    (Term.typeAscription "(" (Order.BoundedOrder.«term⊥» "⊥") ":" [(Term.app `Ideal [`R])] ")")
                    "."
                    `jacobson)))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LocalRing.jacobson_eq_maximal_ideal)] "]")
                     [])
                    []
                    (exacts "exacts" "[" [(Term.app `le_refl [(Term.hole "_")]) "," `bot_ne_top] "]")]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app
                 `Submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
                 [(Term.app `IsNoetherian.noetherian [(Term.hole "_")]) `h₂ `h₁]))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.bot_smul) "," (Tactic.rwRule [] `sup_bot_eq)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sup_eq_left) "," (Tactic.rwRule [] `eq_comm)]
               "]")
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app `le_sup_left.antisymm [(Init.Core.«term_$_» `h₁.trans " $ " (Term.app `le_of_eq [`this]))]))
             [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "7"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.exact "exact" (Term.app `exists_maximal_ideal_pow_eq_of_principal [`R `h])) [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "2"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ValuationRing.iff_ideal_total)] "]") [])
             [])
            (group (Tactic.intro "intro" [`H]) [])
            (group (Tactic.constructor "constructor") [])
            (group (Tactic.intro "intro" [`I `J]) [])
            (group
             (Classical.«tacticBy_cases_:_»
              "by_cases"
              [`hI ":"]
              (Init.Core.«term_=_» `I " = " (Order.BoundedOrder.«term⊥» "⊥")))
             [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group (Tactic.subst "subst" [`hI]) [])
               (group (Mathlib.Tactic.tacticLeft "left") [])
               (group (Tactic.exact "exact" `bot_le) [])])
             [])
            (group
             (Classical.«tacticBy_cases_:_»
              "by_cases"
              [`hJ ":"]
              (Init.Core.«term_=_» `J " = " (Order.BoundedOrder.«term⊥» "⊥")))
             [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group (Tactic.subst "subst" [`hJ]) [])
               (group (Mathlib.Tactic.tacticRight "right") [])
               (group (Tactic.exact "exact" `bot_le) [])])
             [])
            (group
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `H [`I `hI])]])
             [])
            (group
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `H [`J `hJ])]])
             [])
            (group
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] (Term.app `le_total [`m `n]))]
              []
              ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
             [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group (Mathlib.Tactic.tacticLeft "left") [])
               (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
             [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group (Mathlib.Tactic.tacticRight "right") [])
               (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
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
         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ValuationRing.iff_ideal_total)] "]") [])
         [])
        (group (Tactic.intro "intro" [`H]) [])
        (group (Tactic.constructor "constructor") [])
        (group (Tactic.intro "intro" [`I `J]) [])
        (group
         (Classical.«tacticBy_cases_:_»
          "by_cases"
          [`hI ":"]
          (Init.Core.«term_=_» `I " = " (Order.BoundedOrder.«term⊥» "⊥")))
         [])
        (group
         («tactic___;_»
          (cdotTk (patternIgnore (token.«·» "·")))
          [(group (Tactic.subst "subst" [`hI]) [])
           (group (Mathlib.Tactic.tacticLeft "left") [])
           (group (Tactic.exact "exact" `bot_le) [])])
         [])
        (group
         (Classical.«tacticBy_cases_:_»
          "by_cases"
          [`hJ ":"]
          (Init.Core.«term_=_» `J " = " (Order.BoundedOrder.«term⊥» "⊥")))
         [])
        (group
         («tactic___;_»
          (cdotTk (patternIgnore (token.«·» "·")))
          [(group (Tactic.subst "subst" [`hJ]) [])
           (group (Mathlib.Tactic.tacticRight "right") [])
           (group (Tactic.exact "exact" `bot_le) [])])
         [])
        (group
         (Std.Tactic.obtain
          "obtain"
          [(Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩")])]
          []
          [":=" [(Term.app `H [`I `hI])]])
         [])
        (group
         (Std.Tactic.obtain
          "obtain"
          [(Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩")])]
          []
          [":=" [(Term.app `H [`J `hJ])]])
         [])
        (group
         (Tactic.cases'
          "cases'"
          [(Tactic.casesTarget [] (Term.app `le_total [`m `n]))]
          []
          ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
         [])
        (group
         («tactic___;_»
          (cdotTk (patternIgnore (token.«·» "·")))
          [(group (Mathlib.Tactic.tacticLeft "left") [])
           (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
         [])
        (group
         («tactic___;_»
          (cdotTk (patternIgnore (token.«·» "·")))
          [(group (Mathlib.Tactic.tacticRight "right") [])
           (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group (Mathlib.Tactic.tacticRight "right") [])
        (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.pow_le_pow [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.pow_le_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Mathlib.Tactic.tacticRight "right")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group (Mathlib.Tactic.tacticLeft "left") [])
        (group (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h'])) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Ideal.pow_le_pow [`h']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.pow_le_pow [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.pow_le_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Mathlib.Tactic.tacticLeft "left")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app `le_total [`m `n]))]
       []
       ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_total [`m `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_total
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m)]) [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `H [`J `hJ])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [`J `hJ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hJ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)]) [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `H [`I `hI])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [`I `hI])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hI
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group (Tactic.subst "subst" [`hJ]) [])
        (group (Mathlib.Tactic.tacticRight "right") [])
        (group (Tactic.exact "exact" `bot_le) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `bot_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bot_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Mathlib.Tactic.tacticRight "right")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
      (Tactic.subst "subst" [`hJ])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hJ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Classical.«tacticBy_cases_:_»
       "by_cases"
       [`hJ ":"]
       (Init.Core.«term_=_» `J " = " (Order.BoundedOrder.«term⊥» "⊥")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_=_» `J " = " (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `J
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group (Tactic.subst "subst" [`hI]) [])
        (group (Mathlib.Tactic.tacticLeft "left") [])
        (group (Tactic.exact "exact" `bot_le) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `bot_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bot_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Mathlib.Tactic.tacticLeft "left")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
      (Tactic.subst "subst" [`hI])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hI
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Classical.«tacticBy_cases_:_»
       "by_cases"
       [`hI ":"]
       (Init.Core.«term_=_» `I " = " (Order.BoundedOrder.«term⊥» "⊥")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Core.«term_=_» `I " = " (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.intro "intro" [`I `J])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
      (Tactic.intro "intro" [`H])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ValuationRing.iff_ideal_total)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ValuationRing.iff_ideal_total
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeHave "tfae_have" [] (num "7") "→" (num "2"))
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
  DiscreteValuationRing.tfae
  [ IsNoetherianRing R ] [ LocalRing R ] [ IsDomain R ] ( h : ¬ IsField R )
    :
      Tfae
        [
          DiscreteValuationRing R
            ,
            ValuationRing R
            ,
            IsDedekindDomain R
            ,
            IsIntegrallyClosed R ∧ ∃! P : Ideal R , P ≠ ⊥ ∧ P . IsPrime
            ,
            maximalIdeal R . IsPrincipal
            ,
            FiniteDimensional.finrank ResidueField R CotangentSpace R = 1
            ,
            ∀ ( I ) ( _ : I ≠ ⊥ ) , ∃ n : ℕ , I = maximalIdeal R ^ n
          ]
  :=
    by
      have ne_bot := Ring.ne_bot_of_is_maximal_of_not_is_field maximal_ideal.is_maximal R h
        classical
          rw [ finrank_eq_one_iff' ]
            tfae_have 1 → 2
            · intro infer_instance
            tfae_have 2 → 1
            ·
              intro
                haveI := IsBezout.toGcdDomain R
                haveI : UniqueFactorizationMonoid R := ufmOfGcdOfWfDvdMonoid
                apply DiscreteValuationRing.ofUfdOfUniqueIrreducible
                ·
                  obtain ⟨ x , hx₁ , hx₂ ⟩ := Ring.exists_not_is_unit_of_not_is_field h
                    obtain ⟨ p , hp₁ , hp₂ ⟩ := WfDvdMonoid.exists_irreducible_factor hx₂ hx₁
                    exact ⟨ p , hp₁ ⟩
                · exact ValuationRing.unique_irreducible
            tfae_have 1 → 4
            · intro H exact ⟨ inferInstance , DiscreteValuationRing.iff_pid_with_one_nonzero_prime R . mp H . 2 ⟩
            tfae_have 4 → 3
            ·
              rintro ⟨ h₁ , h₂ ⟩
                exact
                  ⟨
                    inferInstance
                      ,
                      fun
                        I hI hI'
                          =>
                          ExistsUnique.unique h₂ ⟨ ne_bot , inferInstance ⟩ ⟨ hI , hI' ⟩ ▸ maximal_ideal.is_maximal R
                      ,
                      h₁
                    ⟩
            tfae_have 3 → 5
            · intro h exact maximal_ideal_is_principal_of_is_dedekind_domain R
            tfae_have 5 → 6
            ·
              rintro ⟨ x , hx ⟩
                have : x ∈ maximal_ideal R := by rw [ hx ] exact Submodule.subset_span Set.mem_singleton x
                let x' : maximal_ideal R := ⟨ x , this ⟩
                use Submodule.Quotient.mk x'
                constructor
                ·
                  intro e
                    rw [ Submodule.Quotient.mk_eq_zero ] at e
                    apply Ring.ne_bot_of_is_maximal_of_not_is_field maximal_ideal.is_maximal R h
                    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot maximal_ideal R
                    · exact ⟨ { x } , Finset.coe_singleton x . symm ▸ hx.symm ⟩
                    ·
                      conv_lhs => rw [ hx ]
                        rw [ Submodule.mem_smul_top_iff ] at e
                        rwa [ Submodule.span_le , Set.singleton_subset_iff ]
                    · rw [ LocalRing.jacobson_eq_maximal_ideal ( ⊥ : Ideal R ) bot_ne_top ] exact le_refl _
                ·
                  refine' fun w => Quotient.inductionOn' w $ fun y => _
                    obtain ⟨ y , hy ⟩ := y
                    rw [ hx , Submodule.mem_span_singleton ] at hy
                    obtain ⟨ a , rfl ⟩ := hy
                    exact ⟨ Ideal.Quotient.mk _ a , rfl ⟩
            tfae_have 6 → 5
            ·
              rintro ⟨ x , hx , hx' ⟩
                induction x using Quotient.inductionOn'
                use x
                apply le_antisymm
                swap
                · rw [ Submodule.span_le , Set.singleton_subset_iff ] exact x.prop
                have
                  h₁
                    :
                      ( Ideal.span { x } : Ideal R ) ⊔ maximal_ideal R
                        ≤
                        Ideal.span { x } ⊔ maximal_ideal R • maximal_ideal R
                    :=
                    by
                      refine' sup_le le_sup_left _
                        rintro m hm
                        obtain ⟨ c , hc ⟩ := hx' Submodule.Quotient.mk ⟨ m , hm ⟩
                        induction c using Quotient.inductionOn'
                        rw [ ← sub_sub_cancel c * x m ]
                        apply sub_mem _ _
                        · infer_instance
                        · refine' Ideal.mem_sup_left ideal.mem_span_singleton'.mpr ⟨ c , rfl ⟩
                        ·
                          have := Submodule.Quotient.eq _ . mp hc
                            rw [ Submodule.mem_smul_top_iff ] at this
                            exact Ideal.mem_sup_right this
                have
                  h₂
                    : maximal_ideal R ≤ ( ⊥ : Ideal R ) . jacobson
                    :=
                    by rw [ LocalRing.jacobson_eq_maximal_ideal ] exacts [ le_refl _ , bot_ne_top ]
                have := Submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson IsNoetherian.noetherian _ h₂ h₁
                rw [ Submodule.bot_smul , sup_bot_eq ] at this
                rw [ ← sup_eq_left , eq_comm ]
                exact le_sup_left.antisymm h₁.trans $ le_of_eq this
            tfae_have 5 → 7
            · exact exists_maximal_ideal_pow_eq_of_principal R h
            tfae_have 7 → 2
            ·
              rw [ ValuationRing.iff_ideal_total ]
                intro H
                constructor
                intro I J
                by_cases hI : I = ⊥
                · subst hI left exact bot_le
                by_cases hJ : J = ⊥
                · subst hJ right exact bot_le
                obtain ⟨ n , rfl ⟩ := H I hI
                obtain ⟨ m , rfl ⟩ := H J hJ
                cases' le_total m n with h' h'
                · left exact Ideal.pow_le_pow h'
                · right exact Ideal.pow_le_pow h'
            tfae_finish
#align discrete_valuation_ring.tfae DiscreteValuationRing.tfae

