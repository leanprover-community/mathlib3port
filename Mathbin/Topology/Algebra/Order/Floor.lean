/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.order.floor
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Floor
import Mathbin.Topology.Order.Basic

/-!
# Topological facts about `int.floor`, `int.ceil` and `int.fract`

This file proves statements about limits and continuity of functions involving `floor`, `ceil` and
`fract`.

## Main declarations

* `tendsto_floor_at_top`, `tendsto_floor_at_bot`, `tendsto_ceil_at_top`, `tendsto_ceil_at_bot`:
  `int.floor` and `int.ceil` tend to +-∞ in +-∞.
* `continuous_on_floor`: `int.floor` is continuous on `Ico n (n + 1)`, because constant.
* `continuous_on_ceil`: `int.ceil` is continuous on `Ioc n (n + 1)`, because constant.
* `continuous_on_fract`: `int.fract` is continuous on `Ico n (n + 1)`.
* `continuous_on.comp_fract`: Precomposing a continuous function satisfying `f 0 = f 1` with
  `int.fract` yields another continuous function.
-/


open Filter Function Int Set

open TopologicalSpace

variable {α β γ : Type _} [LinearOrderedRing α] [FloorRing α]

theorem tendsto_floor_at_top : Tendsto (floor : α → ℤ) atTop atTop :=
  floor_mono.tendsto_at_top_at_top fun b =>
    ⟨(b + 1 : ℤ), by
      rw [floor_int_cast]
      exact (lt_add_one _).le⟩
#align tendsto_floor_at_top tendsto_floor_at_top

theorem tendsto_floor_at_bot : Tendsto (floor : α → ℤ) atBot atBot :=
  floor_mono.tendsto_at_bot_at_bot fun b => ⟨b, (floor_int_cast _).le⟩
#align tendsto_floor_at_bot tendsto_floor_at_bot

theorem tendsto_ceil_at_top : Tendsto (ceil : α → ℤ) atTop atTop :=
  ceil_mono.tendsto_at_top_at_top fun b => ⟨b, (ceil_int_cast _).ge⟩
#align tendsto_ceil_at_top tendsto_ceil_at_top

theorem tendsto_ceil_at_bot : Tendsto (ceil : α → ℤ) atBot atBot :=
  ceil_mono.tendsto_at_bot_at_bot fun b =>
    ⟨(b - 1 : ℤ), by
      rw [ceil_int_cast]
      exact (sub_one_lt _).le⟩
#align tendsto_ceil_at_bot tendsto_ceil_at_bot

variable [TopologicalSpace α]

theorem continuous_on_floor (n : ℤ) :
    ContinuousOn (fun x => floor x : α → α) (Ico n (n + 1) : Set α) :=
  (continuous_on_congr <| floor_eq_on_Ico' n).mpr continuous_on_const
#align continuous_on_floor continuous_on_floor

theorem continuous_on_ceil (n : ℤ) :
    ContinuousOn (fun x => ceil x : α → α) (Ioc (n - 1) n : Set α) :=
  (continuous_on_congr <| ceil_eq_on_Ioc' n).mpr continuous_on_const
#align continuous_on_ceil continuous_on_ceil

theorem tendsto_floor_right' [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝 n) :=
  by
  rw [← nhds_within_Ico_eq_nhds_within_Ici (lt_add_one (n : α))]
  simpa only [floor_int_cast] using
    (continuous_on_floor n _ (left_mem_Ico.mpr <| lt_add_one (_ : α))).Tendsto
#align tendsto_floor_right' tendsto_floor_right'

theorem tendsto_ceil_left' [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝 n) :=
  by
  rw [← nhds_within_Ioc_eq_nhds_within_Iic (sub_one_lt (n : α))]
  simpa only [ceil_int_cast] using
    (continuous_on_ceil _ _ (right_mem_Ioc.mpr <| sub_one_lt (_ : α))).Tendsto
#align tendsto_ceil_left' tendsto_ceil_left'

theorem tendsto_floor_right [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝[≥] n) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_floor_right' _)
    (by
      refine' eventually_nhds_within_of_forall fun x (hx : (n : α) ≤ x) => _
      change _ ≤ _
      norm_cast
      convert ← floor_mono hx
      rw [floor_eq_iff]
      exact ⟨le_rfl, lt_add_one _⟩)
#align tendsto_floor_right tendsto_floor_right

theorem tendsto_ceil_left [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝[≤] n) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_ceil_left' _)
    (by
      refine' eventually_nhds_within_of_forall fun x (hx : x ≤ (n : α)) => _
      change _ ≤ _
      norm_cast
      convert ← ceil_mono hx
      rw [ceil_eq_iff]
      exact ⟨sub_one_lt _, le_rfl⟩)
#align tendsto_ceil_left tendsto_ceil_left

theorem tendsto_floor_left [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝[≤] (n - 1)) :=
  by
  rw [← nhds_within_Ico_eq_nhds_within_Iio (sub_one_lt (n : α))]
  convert
      (tendsto_nhds_within_congr fun x hx => (floor_eq_on_Ico' (n - 1) x hx).symm)
        (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
          (eventually_of_forall fun _ => mem_Iic.mpr <| le_rfl)) <;>
    first |norm_cast|infer_instance
  ring
#align tendsto_floor_left tendsto_floor_left

theorem tendsto_ceil_right [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝[≥] (n + 1)) :=
  by
  rw [← nhds_within_Ioc_eq_nhds_within_Ioi (lt_add_one (n : α))]
  convert
      (tendsto_nhds_within_congr fun x hx => (ceil_eq_on_Ioc' (n + 1) x hx).symm)
        (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
          (eventually_of_forall fun _ => mem_Ici.mpr <| le_rfl)) <;>
    first |norm_cast|infer_instance
  ring
#align tendsto_ceil_right tendsto_ceil_right

theorem tendsto_floor_left' [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝 (n - 1)) :=
  by
  rw [← nhds_within_univ]
  exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_floor_left n)
#align tendsto_floor_left' tendsto_floor_left'

theorem tendsto_ceil_right' [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝 (n + 1)) :=
  by
  rw [← nhds_within_univ]
  exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_ceil_right n)
#align tendsto_ceil_right' tendsto_ceil_right'

theorem continuous_on_fract [TopologicalAddGroup α] (n : ℤ) :
    ContinuousOn (fract : α → α) (Ico n (n + 1) : Set α) :=
  continuous_on_id.sub (continuous_on_floor n)
#align continuous_on_fract continuous_on_fract

theorem tendsto_fract_left' [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝 1) := by
  convert (tendsto_nhds_within_of_tendsto_nhds tendsto_id).sub (tendsto_floor_left' n) <;>
    [·
      norm_cast
      ring, infer_instance, infer_instance]
#align tendsto_fract_left' tendsto_fract_left'

theorem tendsto_fract_left [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝[<] 1) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (eventually_of_forall fract_lt_one)
#align tendsto_fract_left tendsto_fract_left

theorem tendsto_fract_right' [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝 0) := by
  convert (tendsto_nhds_within_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n) <;>
    [exact (sub_self _).symm, infer_instance, infer_instance]
#align tendsto_fract_right' tendsto_fract_right'

theorem tendsto_fract_right [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝[≥] 0) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (eventually_of_forall fract_nonneg)
#align tendsto_fract_right tendsto_fract_right

-- mathport name: exprI
local notation "I" => (Icc 0 1 : Set α)

variable [OrderTopology α] [TopologicalAddGroup α] [TopologicalSpace β] [TopologicalSpace γ]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Do not use this, use `continuous_on.comp_fract` instead. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `ContinuousOn.comp_fract' [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f] [":" (Term.arrow `β "→" (Term.arrow `α "→" `γ))] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<|_»
           (Term.app `ContinuousOn [(Term.app `uncurry [`f])])
           "<|"
           (LowerSet.Order.UpperLower.lower_set.prod
            `univ
            " ×ˢ "
            (Topology.Algebra.Order.Floor.termI "I")))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.forall
           "∀"
           [`s]
           []
           ","
           («term_=_» (Term.app `f [`s (num "0")]) "=" (Term.app `f [`s (num "1")])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Continuous
         [(Term.fun
           "fun"
           (Term.basicFun
            [`st]
            [(Term.typeSpec ":" («term_×_» `β "×" `α))]
            "=>"
            («term_<|_»
             (Term.app `f [(Term.proj `st "." (fieldIdx "1"))])
             "<|"
             (Term.app `fract [(Term.proj `st "." (fieldIdx "2"))]))))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.change
            "change"
            (Term.app
             `Continuous
             [(«term_∘_» (Term.app `uncurry [`f]) "∘" (Term.app `Prod.map [`id `fract]))])
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `continuous_iff_continuous_at)] "]")
            [])
           []
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `t)])
                 [])]
               "⟩"))]
            [])
           []
           (Classical.«tacticBy_cases_:_»
            "by_cases"
            [`ht ":"]
            («term_=_» `t "=" (Term.app `floor [`t])))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ht)] "]") [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `continuous_within_at_univ)]
               "]")
              [])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_⊆_»
                   (Term.typeAscription "(" `univ ":" [(Term.app `Set [(«term_×_» `β "×" `α)])] ")")
                   "⊆"
                   («term_∪_»
                    (LowerSet.Order.UpperLower.lower_set.prod
                     `univ
                     " ×ˢ "
                     (Term.app
                      `Iio
                      [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))
                    "∪"
                    (LowerSet.Order.UpperLower.lower_set.prod
                     `univ
                     " ×ˢ "
                     (Term.app
                      `Ici
                      [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))])))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.rintro
                     "rintro"
                     [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `p))
                      (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))]
                     [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `prod_union)]
                      "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.anonymousCtor
                      "⟨"
                      [`trivial
                       ","
                       (Term.app `lt_or_le [(Term.proj `p "." (fieldIdx "2")) (Term.hole "_")])]
                      "⟩"))]))))))
             []
             (Tactic.refine' "refine'" (Term.app `ContinuousWithinAt.mono [(Term.hole "_") `this]))
             []
             (Tactic.refine'
              "refine'"
              (Term.app `ContinuousWithinAt.union [(Term.hole "_") (Term.hole "_")]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `ContinuousWithinAt)
                  ","
                  (Tactic.simpLemma [] [] `fract_int_cast)
                  ","
                  (Tactic.simpLemma [] [] `nhds_within_prod_eq)
                  ","
                  (Tactic.simpLemma [] [] `nhds_within_univ)
                  ","
                  (Tactic.simpLemma [] [] `id.def)
                  ","
                  (Tactic.simpLemma [] [] `comp_app)
                  ","
                  (Tactic.simpLemma [] [] `Prod.map_mk)]
                 "]"]
                [])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.app (Term.app `uncurry [`f]) [(Term.tuple "(" [`s "," [(num "0")]] ")")])
                     "="
                     (Term.app
                      (Term.app `uncurry [`f])
                      [(Term.tuple
                        "("
                        [`s "," [(Term.typeAscription "(" (num "1") ":" [`α] ")")]]
                        ")")])))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["["
                        [(Tactic.simpLemma [] [] `uncurry) "," (Tactic.simpLemma [] [] `hf)]
                        "]"]
                       [])]))))))
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj
                  (Term.proj
                   (Term.app
                    `h
                    [(Term.hole "_")
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor "⟨" [] "⟩")
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.NormCast.tacticExact_mod_cast_
                            "exact_mod_cast"
                            (Term.app
                             (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                             [(Term.app `zero_le_one' [`α])]))])))]
                      "⟩")])
                   "."
                   `Tendsto)
                  "."
                  `comp)
                 [(Term.hole "_")]))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `nhds_within_prod_eq) "," (Tactic.rwRule [] `nhds_within_univ)]
                 "]")
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app `nhds_within_Icc_eq_nhds_within_Iic [(Term.app `zero_lt_one' [`α])]))]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `tendsto_id.prod_map
                 [(«term_<|_»
                   (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
                   "<|"
                   (Term.app `tendsto_fract_left [(Term.hole "_")]))]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `ContinuousWithinAt)
                  ","
                  (Tactic.simpLemma [] [] `fract_int_cast)
                  ","
                  (Tactic.simpLemma [] [] `nhds_within_prod_eq)
                  ","
                  (Tactic.simpLemma [] [] `nhds_within_univ)
                  ","
                  (Tactic.simpLemma [] [] `id.def)
                  ","
                  (Tactic.simpLemma [] [] `comp_app)
                  ","
                  (Tactic.simpLemma [] [] `Prod.map_mk)]
                 "]"]
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj
                  (Term.proj
                   (Term.app
                    `h
                    [(Term.hole "_")
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor "⟨" [] "⟩")
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.NormCast.tacticExact_mod_cast_
                            "exact_mod_cast"
                            (Term.app
                             (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                             [(Term.app `zero_le_one' [`α])]))])))]
                      "⟩")])
                   "."
                   `Tendsto)
                  "."
                  `comp)
                 [(Term.hole "_")]))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `nhds_within_prod_eq)
                  ","
                  (Tactic.rwRule [] `nhds_within_univ)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `nhds_within_Icc_eq_nhds_within_Ici [(Term.app `zero_lt_one' [`α])]))]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `tendsto_id.prod_map
                 [(Term.app `tendsto_fract_right [(Term.hole "_")])]))])])
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
                  («term_∈_»
                   `t
                   "∈"
                   (Term.app
                    `Ioo
                    [(Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
                     («term_+_»
                      (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
                      "+"
                      (num "1"))])))]
                ":="
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `lt_of_le_of_ne [(Term.app `floor_le [`t]) (Term.app `Ne.symm [`ht])])
                  ","
                  (Term.app `lt_floor_add_one [(Term.hole "_")])]
                 "⟩"))))
             []
             (Tactic.apply
              "apply"
              (Term.proj
               (Term.proj
                (Term.app
                 `h
                 [(Term.app (Term.app `Prod.map [(Term.hole "_") `fract]) [(Term.hole "_")])
                  (Term.anonymousCtor
                   "⟨"
                   [`trivial
                    ","
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.app `fract_nonneg [(Term.hole "_")])
                      ","
                      (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
                     "⟩")]
                   "⟩")])
                "."
                `Tendsto)
               "."
               `comp))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `nhds_prod_eq)
                ","
                (Tactic.simpLemma [] [] `nhds_within_prod_eq)
                ","
                (Tactic.simpLemma [] [] `nhds_within_univ)
                ","
                (Tactic.simpLemma [] [] `id.def)
                ","
                (Tactic.simpLemma [] [] `Prod.map_mk)]
               "]"]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `continuous_at_id.tendsto.prod_map
               [(Term.app
                 `tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
                 [(Term.hole "_")
                  (Term.app
                   (Term.proj
                    (Term.app
                     (Term.proj
                      (Term.app
                       `continuous_on_fract
                       [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
                      "."
                      `mono)
                     [`Ioo_subset_Ico_self])
                    "."
                    `ContinuousAt)
                   [(Term.app
                     `Ioo_mem_nhds
                     [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])])
                  (Term.app
                   `eventually_of_forall
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`x]
                      []
                      "=>"
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.app `fract_nonneg [(Term.hole "_")])
                        ","
                        (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
                       "⟩")))])])]))])])))
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
         [(Tactic.change
           "change"
           (Term.app
            `Continuous
            [(«term_∘_» (Term.app `uncurry [`f]) "∘" (Term.app `Prod.map [`id `fract]))])
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `continuous_iff_continuous_at)] "]")
           [])
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `t)])
                [])]
              "⟩"))]
           [])
          []
          (Classical.«tacticBy_cases_:_»
           "by_cases"
           [`ht ":"]
           («term_=_» `t "=" (Term.app `floor [`t])))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ht)] "]") [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `continuous_within_at_univ)]
              "]")
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_⊆_»
                  (Term.typeAscription "(" `univ ":" [(Term.app `Set [(«term_×_» `β "×" `α)])] ")")
                  "⊆"
                  («term_∪_»
                   (LowerSet.Order.UpperLower.lower_set.prod
                    `univ
                    " ×ˢ "
                    (Term.app
                     `Iio
                     [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))
                   "∪"
                   (LowerSet.Order.UpperLower.lower_set.prod
                    `univ
                    " ×ˢ "
                    (Term.app
                     `Ici
                     [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))])))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.rintro
                    "rintro"
                    [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `p))
                     (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))]
                    [])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `prod_union)]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.anonymousCtor
                     "⟨"
                     [`trivial
                      ","
                      (Term.app `lt_or_le [(Term.proj `p "." (fieldIdx "2")) (Term.hole "_")])]
                     "⟩"))]))))))
            []
            (Tactic.refine' "refine'" (Term.app `ContinuousWithinAt.mono [(Term.hole "_") `this]))
            []
            (Tactic.refine'
             "refine'"
             (Term.app `ContinuousWithinAt.union [(Term.hole "_") (Term.hole "_")]))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `ContinuousWithinAt)
                 ","
                 (Tactic.simpLemma [] [] `fract_int_cast)
                 ","
                 (Tactic.simpLemma [] [] `nhds_within_prod_eq)
                 ","
                 (Tactic.simpLemma [] [] `nhds_within_univ)
                 ","
                 (Tactic.simpLemma [] [] `id.def)
                 ","
                 (Tactic.simpLemma [] [] `comp_app)
                 ","
                 (Tactic.simpLemma [] [] `Prod.map_mk)]
                "]"]
               [])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Term.app (Term.app `uncurry [`f]) [(Term.tuple "(" [`s "," [(num "0")]] ")")])
                    "="
                    (Term.app
                     (Term.app `uncurry [`f])
                     [(Term.tuple
                       "("
                       [`s "," [(Term.typeAscription "(" (num "1") ":" [`α] ")")]]
                       ")")])))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [] `uncurry) "," (Tactic.simpLemma [] [] `hf)] "]"]
                      [])]))))))
              []
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.app
                   `h
                   [(Term.hole "_")
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor "⟨" [] "⟩")
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.NormCast.tacticExact_mod_cast_
                           "exact_mod_cast"
                           (Term.app
                            (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                            [(Term.app `zero_le_one' [`α])]))])))]
                     "⟩")])
                  "."
                  `Tendsto)
                 "."
                 `comp)
                [(Term.hole "_")]))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `nhds_within_prod_eq) "," (Tactic.rwRule [] `nhds_within_univ)]
                "]")
               [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.app `nhds_within_Icc_eq_nhds_within_Iic [(Term.app `zero_lt_one' [`α])]))]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `tendsto_id.prod_map
                [(«term_<|_»
                  (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
                  "<|"
                  (Term.app `tendsto_fract_left [(Term.hole "_")]))]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `ContinuousWithinAt)
                 ","
                 (Tactic.simpLemma [] [] `fract_int_cast)
                 ","
                 (Tactic.simpLemma [] [] `nhds_within_prod_eq)
                 ","
                 (Tactic.simpLemma [] [] `nhds_within_univ)
                 ","
                 (Tactic.simpLemma [] [] `id.def)
                 ","
                 (Tactic.simpLemma [] [] `comp_app)
                 ","
                 (Tactic.simpLemma [] [] `Prod.map_mk)]
                "]"]
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj
                 (Term.proj
                  (Term.app
                   `h
                   [(Term.hole "_")
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor "⟨" [] "⟩")
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.NormCast.tacticExact_mod_cast_
                           "exact_mod_cast"
                           (Term.app
                            (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                            [(Term.app `zero_le_one' [`α])]))])))]
                     "⟩")])
                  "."
                  `Tendsto)
                 "."
                 `comp)
                [(Term.hole "_")]))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `nhds_within_prod_eq)
                 ","
                 (Tactic.rwRule [] `nhds_within_univ)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app `nhds_within_Icc_eq_nhds_within_Ici [(Term.app `zero_lt_one' [`α])]))]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `tendsto_id.prod_map
                [(Term.app `tendsto_fract_right [(Term.hole "_")])]))])])
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
                 («term_∈_»
                  `t
                  "∈"
                  (Term.app
                   `Ioo
                   [(Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
                    («term_+_»
                     (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
                     "+"
                     (num "1"))])))]
               ":="
               (Term.anonymousCtor
                "⟨"
                [(Term.app `lt_of_le_of_ne [(Term.app `floor_le [`t]) (Term.app `Ne.symm [`ht])])
                 ","
                 (Term.app `lt_floor_add_one [(Term.hole "_")])]
                "⟩"))))
            []
            (Tactic.apply
             "apply"
             (Term.proj
              (Term.proj
               (Term.app
                `h
                [(Term.app (Term.app `Prod.map [(Term.hole "_") `fract]) [(Term.hole "_")])
                 (Term.anonymousCtor
                  "⟨"
                  [`trivial
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.app `fract_nonneg [(Term.hole "_")])
                     ","
                     (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
                    "⟩")]
                  "⟩")])
               "."
               `Tendsto)
              "."
              `comp))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `nhds_prod_eq)
               ","
               (Tactic.simpLemma [] [] `nhds_within_prod_eq)
               ","
               (Tactic.simpLemma [] [] `nhds_within_univ)
               ","
               (Tactic.simpLemma [] [] `id.def)
               ","
               (Tactic.simpLemma [] [] `Prod.map_mk)]
              "]"]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `continuous_at_id.tendsto.prod_map
              [(Term.app
                `tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
                [(Term.hole "_")
                 (Term.app
                  (Term.proj
                   (Term.app
                    (Term.proj
                     (Term.app
                      `continuous_on_fract
                      [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
                     "."
                     `mono)
                    [`Ioo_subset_Ico_self])
                   "."
                   `ContinuousAt)
                  [(Term.app
                    `Ioo_mem_nhds
                    [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])])
                 (Term.app
                  `eventually_of_forall
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`x]
                     []
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.app `fract_nonneg [(Term.hole "_")])
                       ","
                       (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
                      "⟩")))])])]))])])))
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
             («term_∈_»
              `t
              "∈"
              (Term.app
               `Ioo
               [(Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
                («term_+_»
                 (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
                 "+"
                 (num "1"))])))]
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.app `lt_of_le_of_ne [(Term.app `floor_le [`t]) (Term.app `Ne.symm [`ht])])
             ","
             (Term.app `lt_floor_add_one [(Term.hole "_")])]
            "⟩"))))
        []
        (Tactic.apply
         "apply"
         (Term.proj
          (Term.proj
           (Term.app
            `h
            [(Term.app (Term.app `Prod.map [(Term.hole "_") `fract]) [(Term.hole "_")])
             (Term.anonymousCtor
              "⟨"
              [`trivial
               ","
               (Term.anonymousCtor
                "⟨"
                [(Term.app `fract_nonneg [(Term.hole "_")])
                 ","
                 (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
                "⟩")]
              "⟩")])
           "."
           `Tendsto)
          "."
          `comp))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `nhds_prod_eq)
           ","
           (Tactic.simpLemma [] [] `nhds_within_prod_eq)
           ","
           (Tactic.simpLemma [] [] `nhds_within_univ)
           ","
           (Tactic.simpLemma [] [] `id.def)
           ","
           (Tactic.simpLemma [] [] `Prod.map_mk)]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `continuous_at_id.tendsto.prod_map
          [(Term.app
            `tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
            [(Term.hole "_")
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj
                 (Term.app
                  `continuous_on_fract
                  [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
                 "."
                 `mono)
                [`Ioo_subset_Ico_self])
               "."
               `ContinuousAt)
              [(Term.app
                `Ioo_mem_nhds
                [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])])
             (Term.app
              `eventually_of_forall
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app `fract_nonneg [(Term.hole "_")])
                   ","
                   (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
                  "⟩")))])])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `continuous_at_id.tendsto.prod_map
        [(Term.app
          `tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
          [(Term.hole "_")
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj
               (Term.app
                `continuous_on_fract
                [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
               "."
               `mono)
              [`Ioo_subset_Ico_self])
             "."
             `ContinuousAt)
            [(Term.app
              `Ioo_mem_nhds
              [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])])
           (Term.app
            `eventually_of_forall
            [(Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `fract_nonneg [(Term.hole "_")])
                 ","
                 (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
                "⟩")))])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `continuous_at_id.tendsto.prod_map
       [(Term.app
         `tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
         [(Term.hole "_")
          (Term.app
           (Term.proj
            (Term.app
             (Term.proj
              (Term.app
               `continuous_on_fract
               [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
              "."
              `mono)
             [`Ioo_subset_Ico_self])
            "."
            `ContinuousAt)
           [(Term.app
             `Ioo_mem_nhds
             [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])])
          (Term.app
           `eventually_of_forall
           [(Term.fun
             "fun"
             (Term.basicFun
              [`x]
              []
              "=>"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `fract_nonneg [(Term.hole "_")])
                ","
                (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
               "⟩")))])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
       [(Term.hole "_")
        (Term.app
         (Term.proj
          (Term.app
           (Term.proj
            (Term.app
             `continuous_on_fract
             [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
            "."
            `mono)
           [`Ioo_subset_Ico_self])
          "."
          `ContinuousAt)
         [(Term.app
           `Ioo_mem_nhds
           [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])])
        (Term.app
         `eventually_of_forall
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app `fract_nonneg [(Term.hole "_")])
              ","
              (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
             "⟩")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eventually_of_forall
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.app `fract_nonneg [(Term.hole "_")])
            ","
            (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
           "⟩")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `fract_nonneg [(Term.hole "_")])
          ","
          (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `fract_nonneg [(Term.hole "_")])
        ","
        (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `fract_lt_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fract_lt_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `fract_lt_one [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fract_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fract_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually_of_forall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `eventually_of_forall
      [(Term.fun
        "fun"
        (Term.basicFun
         [`x]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `fract_nonneg [(Term.hole "_")])
           ","
           (Term.proj (Term.paren "(" (Term.app `fract_lt_one [(Term.hole "_")]) ")") "." `le)]
          "⟩")))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj
          (Term.app
           `continuous_on_fract
           [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
          "."
          `mono)
         [`Ioo_subset_Ico_self])
        "."
        `ContinuousAt)
       [(Term.app
         `Ioo_mem_nhds
         [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ioo_mem_nhds
       [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `this "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `this "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ioo_mem_nhds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Ioo_mem_nhds
      [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.app
          `continuous_on_fract
          [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
         "."
         `mono)
        [`Ioo_subset_Ico_self])
       "."
       `ContinuousAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.app
         `continuous_on_fract
         [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
        "."
        `mono)
       [`Ioo_subset_Ico_self])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ioo_subset_Ico_self
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `continuous_on_fract
        [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
       "."
       `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `continuous_on_fract
       [(Term.hole "_") (Term.hole "_") (Term.app `Ioo_subset_Ico_self [`this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ioo_subset_Ico_self [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ioo_subset_Ico_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ioo_subset_Ico_self [`this])
     ")")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_on_fract
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `continuous_on_fract
      [(Term.hole "_")
       (Term.hole "_")
       (Term.paren "(" (Term.app `Ioo_subset_Ico_self [`this]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren
        "("
        (Term.app
         `continuous_on_fract
         [(Term.hole "_")
          (Term.hole "_")
          (Term.paren "(" (Term.app `Ioo_subset_Ico_self [`this]) ")")])
        ")")
       "."
       `mono)
      [`Ioo_subset_Ico_self])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren
        "("
        (Term.app
         (Term.proj
          (Term.paren
           "("
           (Term.app
            `continuous_on_fract
            [(Term.hole "_")
             (Term.hole "_")
             (Term.paren "(" (Term.app `Ioo_subset_Ico_self [`this]) ")")])
           ")")
          "."
          `mono)
         [`Ioo_subset_Ico_self])
        ")")
       "."
       `ContinuousAt)
      [(Term.paren
        "("
        (Term.app
         `Ioo_mem_nhds
         [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
      [(Term.hole "_")
       (Term.paren
        "("
        (Term.app
         (Term.proj
          (Term.paren
           "("
           (Term.app
            (Term.proj
             (Term.paren
              "("
              (Term.app
               `continuous_on_fract
               [(Term.hole "_")
                (Term.hole "_")
                (Term.paren "(" (Term.app `Ioo_subset_Ico_self [`this]) ")")])
              ")")
             "."
             `mono)
            [`Ioo_subset_Ico_self])
           ")")
          "."
          `ContinuousAt)
         [(Term.paren
           "("
           (Term.app
            `Ioo_mem_nhds
            [(Term.proj `this "." (fieldIdx "1")) (Term.proj `this "." (fieldIdx "2"))])
           ")")])
        ")")
       (Term.paren
        "("
        (Term.app
         `eventually_of_forall
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app `fract_nonneg [(Term.hole "_")])
              ","
              (Term.proj (Term.paren "(" (Term.app `fract_lt_one [(Term.hole "_")]) ")") "." `le)]
             "⟩")))])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_at_id.tendsto.prod_map
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
        [(Tactic.simpLemma [] [] `nhds_prod_eq)
         ","
         (Tactic.simpLemma [] [] `nhds_within_prod_eq)
         ","
         (Tactic.simpLemma [] [] `nhds_within_univ)
         ","
         (Tactic.simpLemma [] [] `id.def)
         ","
         (Tactic.simpLemma [] [] `Prod.map_mk)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Prod.map_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `id.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj
        (Term.proj
         (Term.app
          `h
          [(Term.app (Term.app `Prod.map [(Term.hole "_") `fract]) [(Term.hole "_")])
           (Term.anonymousCtor
            "⟨"
            [`trivial
             ","
             (Term.anonymousCtor
              "⟨"
              [(Term.app `fract_nonneg [(Term.hole "_")])
               ","
               (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
              "⟩")]
            "⟩")])
         "."
         `Tendsto)
        "."
        `comp))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.app
         `h
         [(Term.app (Term.app `Prod.map [(Term.hole "_") `fract]) [(Term.hole "_")])
          (Term.anonymousCtor
           "⟨"
           [`trivial
            ","
            (Term.anonymousCtor
             "⟨"
             [(Term.app `fract_nonneg [(Term.hole "_")])
              ","
              (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
             "⟩")]
           "⟩")])
        "."
        `Tendsto)
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `h
        [(Term.app (Term.app `Prod.map [(Term.hole "_") `fract]) [(Term.hole "_")])
         (Term.anonymousCtor
          "⟨"
          [`trivial
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.app `fract_nonneg [(Term.hole "_")])
             ","
             (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
            "⟩")]
          "⟩")])
       "."
       `Tendsto)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `h
       [(Term.app (Term.app `Prod.map [(Term.hole "_") `fract]) [(Term.hole "_")])
        (Term.anonymousCtor
         "⟨"
         [`trivial
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.app `fract_nonneg [(Term.hole "_")])
            ","
            (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
           "⟩")]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`trivial
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.app `fract_nonneg [(Term.hole "_")])
          ","
          (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `fract_nonneg [(Term.hole "_")])
        ","
        (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `fract_lt_one [(Term.hole "_")]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `fract_lt_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fract_lt_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `fract_lt_one [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fract_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fract_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trivial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app (Term.app `Prod.map [(Term.hole "_") `fract]) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `Prod.map [(Term.hole "_") `fract])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fract
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Prod.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Prod.map [(Term.hole "_") `fract])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.paren "(" (Term.app `Prod.map [(Term.hole "_") `fract]) ")") [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `h
      [(Term.paren
        "("
        (Term.app
         (Term.paren "(" (Term.app `Prod.map [(Term.hole "_") `fract]) ")")
         [(Term.hole "_")])
        ")")
       (Term.anonymousCtor
        "⟨"
        [`trivial
         ","
         (Term.anonymousCtor
          "⟨"
          [(Term.app `fract_nonneg [(Term.hole "_")])
           ","
           (Term.proj (Term.paren "(" (Term.app `fract_lt_one [(Term.hole "_")]) ")") "." `le)]
          "⟩")]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
            `t
            "∈"
            (Term.app
             `Ioo
             [(Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
              («term_+_»
               (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
               "+"
               (num "1"))])))]
         ":="
         (Term.anonymousCtor
          "⟨"
          [(Term.app `lt_of_le_of_ne [(Term.app `floor_le [`t]) (Term.app `Ne.symm [`ht])])
           ","
           (Term.app `lt_floor_add_one [(Term.hole "_")])]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `lt_of_le_of_ne [(Term.app `floor_le [`t]) (Term.app `Ne.symm [`ht])])
        ","
        (Term.app `lt_floor_add_one [(Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_floor_add_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_floor_add_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_of_le_of_ne [(Term.app `floor_le [`t]) (Term.app `Ne.symm [`ht])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ne.symm [`ht])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ht
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ne.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Ne.symm [`ht]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `floor_le [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `floor_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `floor_le [`t]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_of_le_of_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `t
       "∈"
       (Term.app
        `Ioo
        [(Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
         («term_+_» (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")") "+" (num "1"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ioo
       [(Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
        («term_+_» (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")") "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")") "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `floor [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `floor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")") "+" (num "1"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (Term.app `floor [`t]) ":" [`α] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `floor [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `floor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ioo
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ht)] "]") [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `continuous_within_at_univ)]
          "]")
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_⊆_»
              (Term.typeAscription "(" `univ ":" [(Term.app `Set [(«term_×_» `β "×" `α)])] ")")
              "⊆"
              («term_∪_»
               (LowerSet.Order.UpperLower.lower_set.prod
                `univ
                " ×ˢ "
                (Term.app `Iio [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))
               "∪"
               (LowerSet.Order.UpperLower.lower_set.prod
                `univ
                " ×ˢ "
                (Term.app
                 `Ici
                 [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))])))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.rintro
                "rintro"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `p))
                 (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))]
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `prod_union)]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [`trivial
                  ","
                  (Term.app `lt_or_le [(Term.proj `p "." (fieldIdx "2")) (Term.hole "_")])]
                 "⟩"))]))))))
        []
        (Tactic.refine' "refine'" (Term.app `ContinuousWithinAt.mono [(Term.hole "_") `this]))
        []
        (Tactic.refine'
         "refine'"
         (Term.app `ContinuousWithinAt.union [(Term.hole "_") (Term.hole "_")]))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `ContinuousWithinAt)
             ","
             (Tactic.simpLemma [] [] `fract_int_cast)
             ","
             (Tactic.simpLemma [] [] `nhds_within_prod_eq)
             ","
             (Tactic.simpLemma [] [] `nhds_within_univ)
             ","
             (Tactic.simpLemma [] [] `id.def)
             ","
             (Tactic.simpLemma [] [] `comp_app)
             ","
             (Tactic.simpLemma [] [] `Prod.map_mk)]
            "]"]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app (Term.app `uncurry [`f]) [(Term.tuple "(" [`s "," [(num "0")]] ")")])
                "="
                (Term.app
                 (Term.app `uncurry [`f])
                 [(Term.tuple
                   "("
                   [`s "," [(Term.typeAscription "(" (num "1") ":" [`α] ")")]]
                   ")")])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [] `uncurry) "," (Tactic.simpLemma [] [] `hf)] "]"]
                  [])]))))))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.proj
              (Term.app
               `h
               [(Term.hole "_")
                (Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor "⟨" [] "⟩")
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.NormCast.tacticExact_mod_cast_
                       "exact_mod_cast"
                       (Term.app
                        (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                        [(Term.app `zero_le_one' [`α])]))])))]
                 "⟩")])
              "."
              `Tendsto)
             "."
             `comp)
            [(Term.hole "_")]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `nhds_within_prod_eq) "," (Tactic.rwRule [] `nhds_within_univ)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app `nhds_within_Icc_eq_nhds_within_Iic [(Term.app `zero_lt_one' [`α])]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `tendsto_id.prod_map
            [(«term_<|_»
              (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
              "<|"
              (Term.app `tendsto_fract_left [(Term.hole "_")]))]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `ContinuousWithinAt)
             ","
             (Tactic.simpLemma [] [] `fract_int_cast)
             ","
             (Tactic.simpLemma [] [] `nhds_within_prod_eq)
             ","
             (Tactic.simpLemma [] [] `nhds_within_univ)
             ","
             (Tactic.simpLemma [] [] `id.def)
             ","
             (Tactic.simpLemma [] [] `comp_app)
             ","
             (Tactic.simpLemma [] [] `Prod.map_mk)]
            "]"]
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.proj
              (Term.app
               `h
               [(Term.hole "_")
                (Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor "⟨" [] "⟩")
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.NormCast.tacticExact_mod_cast_
                       "exact_mod_cast"
                       (Term.app
                        (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                        [(Term.app `zero_le_one' [`α])]))])))]
                 "⟩")])
              "."
              `Tendsto)
             "."
             `comp)
            [(Term.hole "_")]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `nhds_within_prod_eq)
             ","
             (Tactic.rwRule [] `nhds_within_univ)
             ","
             (Tactic.rwRule
              []
              (Term.app `nhds_within_Icc_eq_nhds_within_Ici [(Term.app `zero_lt_one' [`α])]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `tendsto_id.prod_map [(Term.app `tendsto_fract_right [(Term.hole "_")])]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `ContinuousWithinAt)
           ","
           (Tactic.simpLemma [] [] `fract_int_cast)
           ","
           (Tactic.simpLemma [] [] `nhds_within_prod_eq)
           ","
           (Tactic.simpLemma [] [] `nhds_within_univ)
           ","
           (Tactic.simpLemma [] [] `id.def)
           ","
           (Tactic.simpLemma [] [] `comp_app)
           ","
           (Tactic.simpLemma [] [] `Prod.map_mk)]
          "]"]
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app
             `h
             [(Term.hole "_")
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor "⟨" [] "⟩")
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.NormCast.tacticExact_mod_cast_
                     "exact_mod_cast"
                     (Term.app
                      (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                      [(Term.app `zero_le_one' [`α])]))])))]
               "⟩")])
            "."
            `Tendsto)
           "."
           `comp)
          [(Term.hole "_")]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `nhds_within_prod_eq)
           ","
           (Tactic.rwRule [] `nhds_within_univ)
           ","
           (Tactic.rwRule
            []
            (Term.app `nhds_within_Icc_eq_nhds_within_Ici [(Term.app `zero_lt_one' [`α])]))]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app `tendsto_id.prod_map [(Term.app `tendsto_fract_right [(Term.hole "_")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `tendsto_id.prod_map [(Term.app `tendsto_fract_right [(Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto_id.prod_map [(Term.app `tendsto_fract_right [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto_fract_right [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_fract_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tendsto_fract_right [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_id.prod_map
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
        [(Tactic.rwRule [] `nhds_within_prod_eq)
         ","
         (Tactic.rwRule [] `nhds_within_univ)
         ","
         (Tactic.rwRule
          []
          (Term.app `nhds_within_Icc_eq_nhds_within_Ici [(Term.app `zero_lt_one' [`α])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nhds_within_Icc_eq_nhds_within_Ici [(Term.app `zero_lt_one' [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_lt_one' [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_lt_one'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zero_lt_one' [`α]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nhds_within_Icc_eq_nhds_within_Ici
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app
           `h
           [(Term.hole "_")
            (Term.anonymousCtor
             "⟨"
             [(Term.anonymousCtor "⟨" [] "⟩")
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.NormCast.tacticExact_mod_cast_
                   "exact_mod_cast"
                   (Term.app
                    (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                    [(Term.app `zero_le_one' [`α])]))])))]
             "⟩")])
          "."
          `Tendsto)
         "."
         `comp)
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app
          `h
          [(Term.hole "_")
           (Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor "⟨" [] "⟩")
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.NormCast.tacticExact_mod_cast_
                  "exact_mod_cast"
                  (Term.app
                   (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                   [(Term.app `zero_le_one' [`α])]))])))]
            "⟩")])
         "."
         `Tendsto)
        "."
        `comp)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app
         `h
         [(Term.hole "_")
          (Term.anonymousCtor
           "⟨"
           [(Term.anonymousCtor "⟨" [] "⟩")
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.NormCast.tacticExact_mod_cast_
                 "exact_mod_cast"
                 (Term.app
                  (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                  [(Term.app `zero_le_one' [`α])]))])))]
           "⟩")])
        "."
        `Tendsto)
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `h
        [(Term.hole "_")
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor "⟨" [] "⟩")
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.NormCast.tacticExact_mod_cast_
                "exact_mod_cast"
                (Term.app
                 (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                 [(Term.app `zero_le_one' [`α])]))])))]
          "⟩")])
       "."
       `Tendsto)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `h
       [(Term.hole "_")
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor "⟨" [] "⟩")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.NormCast.tacticExact_mod_cast_
               "exact_mod_cast"
               (Term.app
                (Term.proj `left_mem_Icc "." (fieldIdx "2"))
                [(Term.app `zero_le_one' [`α])]))])))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [] "⟩")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.NormCast.tacticExact_mod_cast_
             "exact_mod_cast"
             (Term.app
              (Term.proj `left_mem_Icc "." (fieldIdx "2"))
              [(Term.app `zero_le_one' [`α])]))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           (Term.app
            (Term.proj `left_mem_Icc "." (fieldIdx "2"))
            [(Term.app `zero_le_one' [`α])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_
       "exact_mod_cast"
       (Term.app (Term.proj `left_mem_Icc "." (fieldIdx "2")) [(Term.app `zero_le_one' [`α])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `left_mem_Icc "." (fieldIdx "2")) [(Term.app `zero_le_one' [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_le_one' [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_le_one'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zero_le_one' [`α]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `left_mem_Icc "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `left_mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [] "⟩")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `h
      [(Term.hole "_")
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor "⟨" [] "⟩")
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_
              "exact_mod_cast"
              (Term.app
               (Term.proj `left_mem_Icc "." (fieldIdx "2"))
               [(Term.paren "(" (Term.app `zero_le_one' [`α]) ")")]))])))]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
        [(Tactic.simpLemma [] [] `ContinuousWithinAt)
         ","
         (Tactic.simpLemma [] [] `fract_int_cast)
         ","
         (Tactic.simpLemma [] [] `nhds_within_prod_eq)
         ","
         (Tactic.simpLemma [] [] `nhds_within_univ)
         ","
         (Tactic.simpLemma [] [] `id.def)
         ","
         (Tactic.simpLemma [] [] `comp_app)
         ","
         (Tactic.simpLemma [] [] `Prod.map_mk)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Prod.map_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `id.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fract_int_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ContinuousWithinAt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `ContinuousWithinAt)
           ","
           (Tactic.simpLemma [] [] `fract_int_cast)
           ","
           (Tactic.simpLemma [] [] `nhds_within_prod_eq)
           ","
           (Tactic.simpLemma [] [] `nhds_within_univ)
           ","
           (Tactic.simpLemma [] [] `id.def)
           ","
           (Tactic.simpLemma [] [] `comp_app)
           ","
           (Tactic.simpLemma [] [] `Prod.map_mk)]
          "]"]
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app (Term.app `uncurry [`f]) [(Term.tuple "(" [`s "," [(num "0")]] ")")])
              "="
              (Term.app
               (Term.app `uncurry [`f])
               [(Term.tuple
                 "("
                 [`s "," [(Term.typeAscription "(" (num "1") ":" [`α] ")")]]
                 ")")])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] `uncurry) "," (Tactic.simpLemma [] [] `hf)] "]"]
                [])]))))))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app
             `h
             [(Term.hole "_")
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor "⟨" [] "⟩")
                ","
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.NormCast.tacticExact_mod_cast_
                     "exact_mod_cast"
                     (Term.app
                      (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                      [(Term.app `zero_le_one' [`α])]))])))]
               "⟩")])
            "."
            `Tendsto)
           "."
           `comp)
          [(Term.hole "_")]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `nhds_within_prod_eq) "," (Tactic.rwRule [] `nhds_within_univ)]
          "]")
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app `nhds_within_Icc_eq_nhds_within_Iic [(Term.app `zero_lt_one' [`α])]))]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `tendsto_id.prod_map
          [(«term_<|_»
            (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
            "<|"
            (Term.app `tendsto_fract_left [(Term.hole "_")]))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `tendsto_id.prod_map
        [(«term_<|_»
          (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
          "<|"
          (Term.app `tendsto_fract_left [(Term.hole "_")]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto_id.prod_map
       [(«term_<|_»
         (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
         "<|"
         (Term.app `tendsto_fract_left [(Term.hole "_")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
       "<|"
       (Term.app `tendsto_fract_left [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto_fract_left [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_fract_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Iio_subset_Iic_self
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_nhds_within_mono_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `tendsto_nhds_within_mono_right [`Iio_subset_Iic_self])
      "<|"
      (Term.app `tendsto_fract_left [(Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_id.prod_map
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
        [(Tactic.rwRule
          []
          (Term.app `nhds_within_Icc_eq_nhds_within_Iic [(Term.app `zero_lt_one' [`α])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nhds_within_Icc_eq_nhds_within_Iic [(Term.app `zero_lt_one' [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_lt_one' [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_lt_one'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zero_lt_one' [`α]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nhds_within_Icc_eq_nhds_within_Iic
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
        [(Tactic.rwRule [] `nhds_within_prod_eq) "," (Tactic.rwRule [] `nhds_within_univ)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app
           `h
           [(Term.hole "_")
            (Term.anonymousCtor
             "⟨"
             [(Term.anonymousCtor "⟨" [] "⟩")
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.NormCast.tacticExact_mod_cast_
                   "exact_mod_cast"
                   (Term.app
                    (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                    [(Term.app `zero_le_one' [`α])]))])))]
             "⟩")])
          "."
          `Tendsto)
         "."
         `comp)
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app
          `h
          [(Term.hole "_")
           (Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor "⟨" [] "⟩")
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.NormCast.tacticExact_mod_cast_
                  "exact_mod_cast"
                  (Term.app
                   (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                   [(Term.app `zero_le_one' [`α])]))])))]
            "⟩")])
         "."
         `Tendsto)
        "."
        `comp)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app
         `h
         [(Term.hole "_")
          (Term.anonymousCtor
           "⟨"
           [(Term.anonymousCtor "⟨" [] "⟩")
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.NormCast.tacticExact_mod_cast_
                 "exact_mod_cast"
                 (Term.app
                  (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                  [(Term.app `zero_le_one' [`α])]))])))]
           "⟩")])
        "."
        `Tendsto)
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `h
        [(Term.hole "_")
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor "⟨" [] "⟩")
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.NormCast.tacticExact_mod_cast_
                "exact_mod_cast"
                (Term.app
                 (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                 [(Term.app `zero_le_one' [`α])]))])))]
          "⟩")])
       "."
       `Tendsto)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `h
       [(Term.hole "_")
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor "⟨" [] "⟩")
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.NormCast.tacticExact_mod_cast_
               "exact_mod_cast"
               (Term.app
                (Term.proj `right_mem_Icc "." (fieldIdx "2"))
                [(Term.app `zero_le_one' [`α])]))])))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [] "⟩")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.NormCast.tacticExact_mod_cast_
             "exact_mod_cast"
             (Term.app
              (Term.proj `right_mem_Icc "." (fieldIdx "2"))
              [(Term.app `zero_le_one' [`α])]))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           (Term.app
            (Term.proj `right_mem_Icc "." (fieldIdx "2"))
            [(Term.app `zero_le_one' [`α])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_
       "exact_mod_cast"
       (Term.app (Term.proj `right_mem_Icc "." (fieldIdx "2")) [(Term.app `zero_le_one' [`α])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `right_mem_Icc "." (fieldIdx "2")) [(Term.app `zero_le_one' [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_le_one' [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_le_one'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zero_le_one' [`α]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `right_mem_Icc "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `right_mem_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [] "⟩")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `h
      [(Term.hole "_")
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor "⟨" [] "⟩")
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_
              "exact_mod_cast"
              (Term.app
               (Term.proj `right_mem_Icc "." (fieldIdx "2"))
               [(Term.paren "(" (Term.app `zero_le_one' [`α]) ")")]))])))]
        "⟩")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
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
            (Term.app (Term.app `uncurry [`f]) [(Term.tuple "(" [`s "," [(num "0")]] ")")])
            "="
            (Term.app
             (Term.app `uncurry [`f])
             [(Term.tuple "(" [`s "," [(Term.typeAscription "(" (num "1") ":" [`α] ")")]] ")")])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `uncurry) "," (Tactic.simpLemma [] [] `hf)] "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `uncurry) "," (Tactic.simpLemma [] [] `hf)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `uncurry) "," (Tactic.simpLemma [] [] `hf)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (Term.app `uncurry [`f]) [(Term.tuple "(" [`s "," [(num "0")]] ")")])
       "="
       (Term.app
        (Term.app `uncurry [`f])
        [(Term.tuple "(" [`s "," [(Term.typeAscription "(" (num "1") ":" [`α] ")")]] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `uncurry [`f])
       [(Term.tuple "(" [`s "," [(Term.typeAscription "(" (num "1") ":" [`α] ")")]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`s "," [(Term.typeAscription "(" (num "1") ":" [`α] ")")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [`α] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `uncurry [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `uncurry [`f]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.app `uncurry [`f]) [(Term.tuple "(" [`s "," [(num "0")]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`s "," [(num "0")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `uncurry [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `uncurry [`f]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `ContinuousWithinAt)
         ","
         (Tactic.simpLemma [] [] `fract_int_cast)
         ","
         (Tactic.simpLemma [] [] `nhds_within_prod_eq)
         ","
         (Tactic.simpLemma [] [] `nhds_within_univ)
         ","
         (Tactic.simpLemma [] [] `id.def)
         ","
         (Tactic.simpLemma [] [] `comp_app)
         ","
         (Tactic.simpLemma [] [] `Prod.map_mk)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Prod.map_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `id.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_within_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fract_int_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ContinuousWithinAt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app `ContinuousWithinAt.union [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ContinuousWithinAt.union [(Term.hole "_") (Term.hole "_")])
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
      `ContinuousWithinAt.union
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `ContinuousWithinAt.mono [(Term.hole "_") `this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ContinuousWithinAt.mono [(Term.hole "_") `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousWithinAt.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_⊆_»
            (Term.typeAscription "(" `univ ":" [(Term.app `Set [(«term_×_» `β "×" `α)])] ")")
            "⊆"
            («term_∪_»
             (LowerSet.Order.UpperLower.lower_set.prod
              `univ
              " ×ˢ "
              (Term.app `Iio [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))
             "∪"
             (LowerSet.Order.UpperLower.lower_set.prod
              `univ
              " ×ˢ "
              (Term.app
               `Ici
               [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))])))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `p))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `prod_union)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`trivial
                ","
                (Term.app `lt_or_le [(Term.proj `p "." (fieldIdx "2")) (Term.hole "_")])]
               "⟩"))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `p))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `prod_union)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [`trivial "," (Term.app `lt_or_le [(Term.proj `p "." (fieldIdx "2")) (Term.hole "_")])]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`trivial "," (Term.app `lt_or_le [(Term.proj `p "." (fieldIdx "2")) (Term.hole "_")])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`trivial "," (Term.app `lt_or_le [(Term.proj `p "." (fieldIdx "2")) (Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_or_le [(Term.proj `p "." (fieldIdx "2")) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_or_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trivial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `prod_union)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_union
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `p))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_»
       (Term.typeAscription "(" `univ ":" [(Term.app `Set [(«term_×_» `β "×" `α)])] ")")
       "⊆"
       («term_∪_»
        (LowerSet.Order.UpperLower.lower_set.prod
         `univ
         " ×ˢ "
         (Term.app `Iio [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))
        "∪"
        (LowerSet.Order.UpperLower.lower_set.prod
         `univ
         " ×ˢ "
         (Term.app `Ici [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∪_»
       (LowerSet.Order.UpperLower.lower_set.prod
        `univ
        " ×ˢ "
        (Term.app `Iio [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))
       "∪"
       (LowerSet.Order.UpperLower.lower_set.prod
        `univ
        " ×ˢ "
        (Term.app `Ici [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LowerSet.Order.UpperLower.lower_set.prod
       `univ
       " ×ˢ "
       (Term.app `Ici [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ici [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ici
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 82 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 82, term))
      `univ
[PrettyPrinter.parenthesize] ...precedences are 83 >? 1024, (none, [anonymous]) <=? (some 82, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 82, (some 82, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (LowerSet.Order.UpperLower.lower_set.prod
       `univ
       " ×ˢ "
       (Term.app `Iio [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Iio [(coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" `t "⌋")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Iio
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 82 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 82, term))
      `univ
[PrettyPrinter.parenthesize] ...precedences are 83 >? 1024, (none, [anonymous]) <=? (some 82, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 82, (some 82, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `univ ":" [(Term.app `Set [(«term_×_» `β "×" `α)])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [(«term_×_» `β "×" `α)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» `β "×" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_×_» `β "×" `α) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `continuous_within_at_univ)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_within_at_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ht)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ht
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`ht ":"] («term_=_» `t "=" (Term.app `floor [`t])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `t "=" (Term.app `floor [`t]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `floor [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `floor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `t)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `continuous_iff_continuous_at)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_iff_continuous_at
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.app
        `Continuous
        [(«term_∘_» (Term.app `uncurry [`f]) "∘" (Term.app `Prod.map [`id `fract]))])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Continuous
       [(«term_∘_» (Term.app `uncurry [`f]) "∘" (Term.app `Prod.map [`id `fract]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.app `uncurry [`f]) "∘" (Term.app `Prod.map [`id `fract]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Prod.map [`id `fract])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fract
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `id
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Prod.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.app `uncurry [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `uncurry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1022, (some 1023, term) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_∘_» (Term.app `uncurry [`f]) "∘" (Term.app `Prod.map [`id `fract]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Continuous
       [(Term.fun
         "fun"
         (Term.basicFun
          [`st]
          [(Term.typeSpec ":" («term_×_» `β "×" `α))]
          "=>"
          («term_<|_»
           (Term.app `f [(Term.proj `st "." (fieldIdx "1"))])
           "<|"
           (Term.app `fract [(Term.proj `st "." (fieldIdx "2"))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`st]
        [(Term.typeSpec ":" («term_×_» `β "×" `α))]
        "=>"
        («term_<|_»
         (Term.app `f [(Term.proj `st "." (fieldIdx "1"))])
         "<|"
         (Term.app `fract [(Term.proj `st "." (fieldIdx "2"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `f [(Term.proj `st "." (fieldIdx "1"))])
       "<|"
       (Term.app `fract [(Term.proj `st "." (fieldIdx "2"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fract [(Term.proj `st "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `st "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `st
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fract
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `f [(Term.proj `st "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `st "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `st
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» `β "×" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `st
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`s]
       []
       ","
       («term_=_» (Term.app `f [`s (num "0")]) "=" (Term.app `f [`s (num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `f [`s (num "0")]) "=" (Term.app `f [`s (num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`s (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`s (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `ContinuousOn [(Term.app `uncurry [`f])])
       "<|"
       (LowerSet.Order.UpperLower.lower_set.prod
        `univ
        " ×ˢ "
        (Topology.Algebra.Order.Floor.termI "I")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LowerSet.Order.UpperLower.lower_set.prod
       `univ
       " ×ˢ "
       (Topology.Algebra.Order.Floor.termI "I"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Algebra.Order.Floor.termI "I")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.Order.Floor.termI', expected 'Topology.Algebra.Order.Floor.termI._@.Topology.Algebra.Order.Floor._hyg.6'
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
/-- Do not use this, use `continuous_on.comp_fract` instead. -/
  theorem
    ContinuousOn.comp_fract'
    { f : β → α → γ } ( h : ContinuousOn uncurry f <| univ ×ˢ I ) ( hf : ∀ s , f s 0 = f s 1 )
      : Continuous fun st : β × α => f st . 1 <| fract st . 2
    :=
      by
        change Continuous uncurry f ∘ Prod.map id fract
          rw [ continuous_iff_continuous_at ]
          rintro ⟨ s , t ⟩
          by_cases ht : t = floor t
          ·
            rw [ ht ]
              rw [ ← continuous_within_at_univ ]
              have
                : ( univ : Set β × α ) ⊆ univ ×ˢ Iio ↑ ⌊ t ⌋ ∪ univ ×ˢ Ici ↑ ⌊ t ⌋
                  :=
                  by rintro p - rw [ ← prod_union ] exact ⟨ trivial , lt_or_le p . 2 _ ⟩
              refine' ContinuousWithinAt.mono _ this
              refine' ContinuousWithinAt.union _ _
              ·
                simp
                    only
                    [
                      ContinuousWithinAt
                        ,
                        fract_int_cast
                        ,
                        nhds_within_prod_eq
                        ,
                        nhds_within_univ
                        ,
                        id.def
                        ,
                        comp_app
                        ,
                        Prod.map_mk
                      ]
                  have
                    : uncurry f ( s , 0 ) = uncurry f ( s , ( 1 : α ) ) := by simp [ uncurry , hf ]
                  rw [ this ]
                  refine'
                    h _ ⟨ ⟨ ⟩ , by exact_mod_cast right_mem_Icc . 2 zero_le_one' α ⟩ . Tendsto
                        .
                        comp
                      _
                  rw [ nhds_within_prod_eq , nhds_within_univ ]
                  rw [ nhds_within_Icc_eq_nhds_within_Iic zero_lt_one' α ]
                  exact
                    tendsto_id.prod_map
                      tendsto_nhds_within_mono_right Iio_subset_Iic_self <| tendsto_fract_left _
              ·
                simp
                    only
                    [
                      ContinuousWithinAt
                        ,
                        fract_int_cast
                        ,
                        nhds_within_prod_eq
                        ,
                        nhds_within_univ
                        ,
                        id.def
                        ,
                        comp_app
                        ,
                        Prod.map_mk
                      ]
                  refine'
                    h _ ⟨ ⟨ ⟩ , by exact_mod_cast left_mem_Icc . 2 zero_le_one' α ⟩ . Tendsto . comp
                      _
                  rw
                    [
                      nhds_within_prod_eq
                        ,
                        nhds_within_univ
                        ,
                        nhds_within_Icc_eq_nhds_within_Ici zero_lt_one' α
                      ]
                  exact tendsto_id.prod_map tendsto_fract_right _
          ·
            have
                : t ∈ Ioo ( floor t : α ) ( floor t : α ) + 1
                  :=
                  ⟨ lt_of_le_of_ne floor_le t Ne.symm ht , lt_floor_add_one _ ⟩
              apply
                h Prod.map _ fract _ ⟨ trivial , ⟨ fract_nonneg _ , fract_lt_one _ . le ⟩ ⟩
                    .
                    Tendsto
                  .
                  comp
              simp
                only
                [ nhds_prod_eq , nhds_within_prod_eq , nhds_within_univ , id.def , Prod.map_mk ]
              exact
                continuous_at_id.tendsto.prod_map
                  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
                    _
                      continuous_on_fract _ _ Ioo_subset_Ico_self this . mono Ioo_subset_Ico_self
                          .
                          ContinuousAt
                        Ioo_mem_nhds this . 1 this . 2
                      eventually_of_forall fun x => ⟨ fract_nonneg _ , fract_lt_one _ . le ⟩
#align continuous_on.comp_fract' ContinuousOn.comp_fract'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ContinuousOn.comp_fract {s : β → α} {f : β → α → γ}
    (h : ContinuousOn (uncurry f) <| univ ×ˢ Icc 0 1) (hs : Continuous s)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun x : β => f x <| Int.fract (s x) :=
  (h.comp_fract' hf).comp (continuous_id.prod_mk hs)
#align continuous_on.comp_fract ContinuousOn.comp_fract

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "A special case of `continuous_on.comp_fract`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `ContinuousOn.comp_fract'' [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f] [":" (Term.arrow `α "→" `β)] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" (Term.app `ContinuousOn [`f (Topology.Algebra.Order.Floor.termI "I")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hf]
         [":" («term_=_» (Term.app `f [(num "0")]) "=" (Term.app `f [(num "1")]))]
         []
         ")")]
       (Term.typeSpec ":" (Term.app `Continuous [(«term_∘_» `f "∘" `fract)])))
      (Command.declValSimple
       ":="
       (Term.app
        `ContinuousOn.comp_fract
        [(Term.app
          (Term.app (Term.proj `h "." `comp) [`continuous_on_snd])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x `hx]
             []
             "=>"
             (Term.proj (Term.app (Term.proj `mem_prod "." `mp) [`hx]) "." (fieldIdx "2"))))])
         `continuous_id
         (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `hf))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ContinuousOn.comp_fract
       [(Term.app
         (Term.app (Term.proj `h "." `comp) [`continuous_on_snd])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x `hx]
            []
            "=>"
            (Term.proj (Term.app (Term.proj `mem_prod "." `mp) [`hx]) "." (fieldIdx "2"))))])
        `continuous_id
        (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `hf))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `hf))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `continuous_id
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.app (Term.proj `h "." `comp) [`continuous_on_snd])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x `hx]
          []
          "=>"
          (Term.proj (Term.app (Term.proj `mem_prod "." `mp) [`hx]) "." (fieldIdx "2"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `hx]
        []
        "=>"
        (Term.proj (Term.app (Term.proj `mem_prod "." `mp) [`hx]) "." (fieldIdx "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app (Term.proj `mem_prod "." `mp) [`hx]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `mem_prod "." `mp) [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `mem_prod "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `mem_prod "." `mp) [`hx])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app (Term.proj `h "." `comp) [`continuous_on_snd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_on_snd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `h "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `h "." `comp) [`continuous_on_snd])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.paren "(" (Term.app (Term.proj `h "." `comp) [`continuous_on_snd]) ")")
      [(Term.fun
        "fun"
        (Term.basicFun
         [`x `hx]
         []
         "=>"
         (Term.proj
          (Term.paren "(" (Term.app (Term.proj `mem_prod "." `mp) [`hx]) ")")
          "."
          (fieldIdx "2"))))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousOn.comp_fract
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Continuous [(«term_∘_» `f "∘" `fract)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `f "∘" `fract)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fract
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `f "∘" `fract) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Continuous
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `f [(num "0")]) "=" (Term.app `f [(num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
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
      (Term.app `ContinuousOn [`f (Topology.Algebra.Order.Floor.termI "I")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.Order.Floor.termI', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.Order.Floor.termI', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Algebra.Order.Floor.termI "I")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.Order.Floor.termI', expected 'Topology.Algebra.Order.Floor.termI._@.Topology.Algebra.Order.Floor._hyg.6'
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
/-- A special case of `continuous_on.comp_fract`. -/
  theorem
    ContinuousOn.comp_fract''
    { f : α → β } ( h : ContinuousOn f I ) ( hf : f 0 = f 1 ) : Continuous f ∘ fract
    :=
      ContinuousOn.comp_fract
        h . comp continuous_on_snd fun x hx => mem_prod . mp hx . 2 continuous_id fun _ => hf
#align continuous_on.comp_fract'' ContinuousOn.comp_fract''

