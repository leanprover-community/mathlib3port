/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module set_theory.ordinal.principal
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.FixedPoint

/-!
### Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

### Main definitions and results
* `principal`: A principal or indecomposable ordinal under some binary operation. We include 0 and
  any other typically excluded edge cases for simplicity.
* `unbounded_principal`: Principal ordinals are unbounded.
* `principal_add_iff_zero_or_omega_opow`: The main characterization theorem for additive principal
  ordinals.
* `principal_mul_iff_le_two_or_omega_opow_opow`: The main characterization theorem for
  multiplicative principal ordinals.

### Todo
* Prove that exponential principal ordinals are 0, 1, 2, ω, or epsilon numbers, i.e. fixed points
  of `λ x, ω ^ x`.
-/


universe u

noncomputable section

open Order

namespace Ordinal

-- mathport name: ordinal.pow
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

/-! ### Principal ordinals -/


/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def Principal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o
#align ordinal.principal Ordinal.Principal

theorem principal_iff_principal_swap {op : Ordinal → Ordinal → Ordinal} {o : Ordinal} :
    Principal op o ↔ Principal (Function.swap op) o := by
  constructor <;> exact fun h a b ha hb => h hb ha
#align ordinal.principal_iff_principal_swap Ordinal.principal_iff_principal_swap

theorem principal_zero {op : Ordinal → Ordinal → Ordinal} : Principal op 0 := fun a _ h =>
  (Ordinal.not_lt_zero a h).elim
#align ordinal.principal_zero Ordinal.principal_zero

@[simp]
theorem principal_one_iff {op : Ordinal → Ordinal → Ordinal} : Principal op 1 ↔ op 0 0 = 0 :=
  by
  refine' ⟨fun h => _, fun h a b ha hb => _⟩
  · rwa [← lt_one_iff_zero]
    exact h zero_lt_one zero_lt_one
  · rwa [lt_one_iff_zero, ha, hb] at *
#align ordinal.principal_one_iff Ordinal.principal_one_iff

theorem Principal.iterate_lt {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal} (hao : a < o)
    (ho : Principal op o) (n : ℕ) : (op a^[n]) a < o :=
  by
  induction' n with n hn
  · rwa [Function.iterate_zero]
  · rw [Function.iterate_succ']
    exact ho hao hn
#align ordinal.principal.iterate_lt Ordinal.Principal.iterate_lt

theorem op_eq_self_of_principal {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal.{u}} (hao : a < o)
    (H : IsNormal (op a)) (ho : Principal op o) (ho' : IsLimit o) : op a o = o :=
  by
  refine' le_antisymm _ (H.self_le _)
  rw [← IsNormal.bsup_eq.{u, u} H ho', bsup_le_iff]
  exact fun b hbo => (ho hao hbo).le
#align ordinal.op_eq_self_of_principal Ordinal.op_eq_self_of_principal

theorem nfp_le_of_principal {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal} (hao : a < o)
    (ho : Principal op o) : nfp (op a) a ≤ o :=
  nfp_le fun n => (ho.iterate_lt hao n).le
#align ordinal.nfp_le_of_principal Ordinal.nfp_le_of_principal

/-! ### Principal ordinals are unbounded -/


/-- The least strict upper bound of `op` applied to all pairs of ordinals less than `o`. This is
essentially a two-argument version of `ordinal.blsub`. -/
def blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  lsub fun x : o.out.α × o.out.α => op (typein (· < ·) x.1) (typein (· < ·) x.2)
#align ordinal.blsub₂ Ordinal.blsub₂

theorem lt_blsub₂ (op : Ordinal → Ordinal → Ordinal) {o : Ordinal} {a b : Ordinal} (ha : a < o)
    (hb : b < o) : op a b < blsub₂ op o :=
  by
  convert
    lt_lsub _ (Prod.mk (enum (· < ·) a (by rwa [type_lt])) (enum (· < ·) b (by rwa [type_lt])))
  simp only [typein_enum]
#align ordinal.lt_blsub₂ Ordinal.lt_blsub₂

theorem principal_nfp_blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (blsub₂.{u, u} op) o) := fun a b ha hb =>
  by
  rw [lt_nfp] at *
  cases' ha with m hm
  cases' hb with n hn
  cases' le_total ((blsub₂.{u, u} op^[m]) o) ((blsub₂.{u, u} op^[n]) o) with h h
  · use n + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ op (hm.trans_le h) hn
  · use m + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ op hm (hn.trans_le h)
#align ordinal.principal_nfp_blsub₂ Ordinal.principal_nfp_blsub₂

theorem unbounded_principal (op : Ordinal → Ordinal → Ordinal) :
    Set.Unbounded (· < ·) { o | Principal op o } := fun o =>
  ⟨_, principal_nfp_blsub₂ op o, (le_nfp _ o).not_lt⟩
#align ordinal.unbounded_principal Ordinal.unbounded_principal

/-! #### Additive principal ordinals -/


theorem principal_add_one : Principal (· + ·) 1 :=
  principal_one_iff.2 <| zero_add 0
#align ordinal.principal_add_one Ordinal.principal_add_one

theorem principal_add_of_le_one {o : Ordinal} (ho : o ≤ 1) : Principal (· + ·) o :=
  by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact principal_zero
  · exact principal_add_one
#align ordinal.principal_add_of_le_one Ordinal.principal_add_of_le_one

theorem principal_add_is_limit {o : Ordinal} (ho₁ : 1 < o) (ho : Principal (· + ·) o) : o.IsLimit :=
  by
  refine' ⟨fun ho₀ => _, fun a hao => _⟩
  · rw [ho₀] at ho₁
    exact not_lt_of_gt zero_lt_one ho₁
  · cases' eq_or_ne a 0 with ha ha
    · rw [ha, succ_zero]
      exact ho₁
    · refine' lt_of_le_of_lt _ (ho hao hao)
      rwa [← add_one_eq_succ, add_le_add_iff_left, one_le_iff_ne_zero]
#align ordinal.principal_add_is_limit Ordinal.principal_add_is_limit

theorem principal_add_iff_add_left_eq_self {o : Ordinal} :
    Principal (· + ·) o ↔ ∀ a < o, a + o = o :=
  by
  refine' ⟨fun ho a hao => _, fun h a b hao hbo => _⟩
  · cases' lt_or_le 1 o with ho₁ ho₁
    · exact op_eq_self_of_principal hao (add_is_normal a) ho (principal_add_is_limit ho₁ ho)
    · rcases le_one_iff.1 ho₁ with (rfl | rfl)
      · exact (Ordinal.not_lt_zero a hao).elim
      · rw [lt_one_iff_zero] at hao
        rw [hao, zero_add]
  · rw [← h a hao]
    exact (add_is_normal a).StrictMono hbo
#align ordinal.principal_add_iff_add_left_eq_self Ordinal.principal_add_iff_add_left_eq_self

theorem exists_lt_add_of_not_principal_add {a} (ha : ¬Principal (· + ·) a) :
    ∃ (b c : _)(hb : b < a)(hc : c < a), b + c = a :=
  by
  unfold principal at ha
  push_neg  at ha
  rcases ha with ⟨b, c, hb, hc, H⟩
  refine'
    ⟨b, _, hb, lt_of_le_of_ne (sub_le_self a b) fun hab => _, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le, hab] at H
  exact H.not_lt hc
#align ordinal.exists_lt_add_of_not_principal_add Ordinal.exists_lt_add_of_not_principal_add

theorem principal_add_iff_add_lt_ne_self {a} :
    Principal (· + ·) a ↔ ∀ ⦃b c⦄, b < a → c < a → b + c ≠ a :=
  ⟨fun ha b c hb hc => (ha hb hc).Ne, fun H =>
    by
    by_contra' ha
    rcases exists_lt_add_of_not_principal_add ha with ⟨b, c, hb, hc, rfl⟩
    exact (H hb hc).irrefl⟩
#align ordinal.principal_add_iff_add_lt_ne_self Ordinal.principal_add_iff_add_lt_ne_self

theorem add_omega {a : Ordinal} (h : a < omega) : a + omega = omega :=
  by
  rcases lt_omega.1 h with ⟨n, rfl⟩
  clear h; induction' n with n IH
  · rw [Nat.cast_zero, zero_add]
  · rwa [Nat.cast_succ, add_assoc, one_add_of_omega_le (le_refl _)]
#align ordinal.add_omega Ordinal.add_omega

theorem principal_add_omega : Principal (· + ·) omega :=
  principal_add_iff_add_left_eq_self.2 fun a => add_omega
#align ordinal.principal_add_omega Ordinal.principal_add_omega

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_omega_opow [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" `Ordinal] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_<_» `a "<" (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_» `a "+" (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))
         "="
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `le_antisymm
             [(Term.hole "_") (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])]))
           []
           (Tactic.revert "revert" [`h])
           ";"
           (Tactic.refine'
            "refine'"
            (Term.app
             `limit_rec_on
             [`b
              (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
              (Term.fun "fun" (Term.basicFun [`b (Term.hole "_") `h] [] "=>" (Term.hole "_")))
              (Term.fun "fun" (Term.basicFun [`b `l `IH `h] [] "=>" (Term.hole "_")))]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `opow_zero)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `succ_zero)
                ","
                (Tactic.rwRule [] `lt_succ_iff)
                ","
                (Tactic.rwRule [] `Ordinal.le_zero)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `zero_add)] "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj (Term.app `lt_mul_of_limit [`omega_is_limit]) "." (fieldIdx "1"))
                 [`h]))]
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
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xo)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `le_trans
               [(Term.app `add_le_add_right [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
                (Term.hole "_")]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `opow_succ)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_add)
                ","
                (Tactic.rwRule [] (Term.app `add_omega [`xo]))]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj (Term.app `lt_opow_of_limit [`omega_ne_zero `l]) "." (fieldIdx "1"))
                 [`h]))]
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
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xb)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj
                  (Term.app
                   (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
                   [(Term.app `opow_is_normal [`one_lt_omega])])
                  "."
                  `limit_le)
                 [`l])
                "."
                (fieldIdx "2"))
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`y `yb]
                  []
                  "=>"
                  (Term.app
                   (Term.proj
                    (Term.app
                     `add_le_add_left
                     [(Term.app
                       `opow_le_opow_right
                       [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
                      (Term.hole "_")])
                    "."
                    `trans)
                   [(Term.app
                     `le_trans
                     [(Term.app
                       `IH
                       [(Term.hole "_")
                        (Term.app `max_lt [`xb `yb])
                        («term_<|_»
                         `ax.trans_le
                         "<|"
                         (Term.app
                          `opow_le_opow_right
                          [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
                      («term_<|_»
                       (Term.app `opow_le_opow_right [`omega_pos])
                       "<|"
                       («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))])])))]))])])))
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            `le_antisymm
            [(Term.hole "_") (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])]))
          []
          (Tactic.revert "revert" [`h])
          ";"
          (Tactic.refine'
           "refine'"
           (Term.app
            `limit_rec_on
            [`b
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
             (Term.fun "fun" (Term.basicFun [`b (Term.hole "_") `h] [] "=>" (Term.hole "_")))
             (Term.fun "fun" (Term.basicFun [`b `l `IH `h] [] "=>" (Term.hole "_")))]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `opow_zero)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `succ_zero)
               ","
               (Tactic.rwRule [] `lt_succ_iff)
               ","
               (Tactic.rwRule [] `Ordinal.le_zero)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `zero_add)] "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj (Term.app `lt_mul_of_limit [`omega_is_limit]) "." (fieldIdx "1"))
                [`h]))]
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
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xo)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `le_trans
              [(Term.app `add_le_add_right [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
               (Term.hole "_")]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `opow_succ)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_add)
               ","
               (Tactic.rwRule [] (Term.app `add_omega [`xo]))]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj (Term.app `lt_opow_of_limit [`omega_ne_zero `l]) "." (fieldIdx "1"))
                [`h]))]
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
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xb)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
                  [(Term.app `opow_is_normal [`one_lt_omega])])
                 "."
                 `limit_le)
                [`l])
               "."
               (fieldIdx "2"))
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`y `yb]
                 []
                 "=>"
                 (Term.app
                  (Term.proj
                   (Term.app
                    `add_le_add_left
                    [(Term.app
                      `opow_le_opow_right
                      [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
                     (Term.hole "_")])
                   "."
                   `trans)
                  [(Term.app
                    `le_trans
                    [(Term.app
                      `IH
                      [(Term.hole "_")
                       (Term.app `max_lt [`xb `yb])
                       («term_<|_»
                        `ax.trans_le
                        "<|"
                        (Term.app
                         `opow_le_opow_right
                         [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
                     («term_<|_»
                      (Term.app `opow_le_opow_right [`omega_pos])
                      "<|"
                      («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))])])))]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj (Term.app `lt_opow_of_limit [`omega_ne_zero `l]) "." (fieldIdx "1"))
            [`h]))]
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
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xb)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
              [(Term.app `opow_is_normal [`one_lt_omega])])
             "."
             `limit_le)
            [`l])
           "."
           (fieldIdx "2"))
          [(Term.fun
            "fun"
            (Term.basicFun
             [`y `yb]
             []
             "=>"
             (Term.app
              (Term.proj
               (Term.app
                `add_le_add_left
                [(Term.app
                  `opow_le_opow_right
                  [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
                 (Term.hole "_")])
               "."
               `trans)
              [(Term.app
                `le_trans
                [(Term.app
                  `IH
                  [(Term.hole "_")
                   (Term.app `max_lt [`xb `yb])
                   («term_<|_»
                    `ax.trans_le
                    "<|"
                    (Term.app
                     `opow_le_opow_right
                     [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
                 («term_<|_»
                  (Term.app `opow_le_opow_right [`omega_pos])
                  "<|"
                  («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))])])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
            [(Term.app `opow_is_normal [`one_lt_omega])])
           "."
           `limit_le)
          [`l])
         "."
         (fieldIdx "2"))
        [(Term.fun
          "fun"
          (Term.basicFun
           [`y `yb]
           []
           "=>"
           (Term.app
            (Term.proj
             (Term.app
              `add_le_add_left
              [(Term.app
                `opow_le_opow_right
                [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
               (Term.hole "_")])
             "."
             `trans)
            [(Term.app
              `le_trans
              [(Term.app
                `IH
                [(Term.hole "_")
                 (Term.app `max_lt [`xb `yb])
                 («term_<|_»
                  `ax.trans_le
                  "<|"
                  (Term.app
                   `opow_le_opow_right
                   [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
               («term_<|_»
                (Term.app `opow_le_opow_right [`omega_pos])
                "<|"
                («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj
          (Term.app
           (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
           [(Term.app `opow_is_normal [`one_lt_omega])])
          "."
          `limit_le)
         [`l])
        "."
        (fieldIdx "2"))
       [(Term.fun
         "fun"
         (Term.basicFun
          [`y `yb]
          []
          "=>"
          (Term.app
           (Term.proj
            (Term.app
             `add_le_add_left
             [(Term.app
               `opow_le_opow_right
               [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
              (Term.hole "_")])
            "."
            `trans)
           [(Term.app
             `le_trans
             [(Term.app
               `IH
               [(Term.hole "_")
                (Term.app `max_lt [`xb `yb])
                («term_<|_»
                 `ax.trans_le
                 "<|"
                 (Term.app
                  `opow_le_opow_right
                  [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
              («term_<|_»
               (Term.app `opow_le_opow_right [`omega_pos])
               "<|"
               («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y `yb]
        []
        "=>"
        (Term.app
         (Term.proj
          (Term.app
           `add_le_add_left
           [(Term.app
             `opow_le_opow_right
             [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
            (Term.hole "_")])
          "."
          `trans)
         [(Term.app
           `le_trans
           [(Term.app
             `IH
             [(Term.hole "_")
              (Term.app `max_lt [`xb `yb])
              («term_<|_»
               `ax.trans_le
               "<|"
               (Term.app
                `opow_le_opow_right
                [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
            («term_<|_»
             (Term.app `opow_le_opow_right [`omega_pos])
             "<|"
             («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `add_le_add_left
         [(Term.app
           `opow_le_opow_right
           [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
          (Term.hole "_")])
        "."
        `trans)
       [(Term.app
         `le_trans
         [(Term.app
           `IH
           [(Term.hole "_")
            (Term.app `max_lt [`xb `yb])
            («term_<|_»
             `ax.trans_le
             "<|"
             (Term.app
              `opow_le_opow_right
              [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
          («term_<|_»
           (Term.app `opow_le_opow_right [`omega_pos])
           "<|"
           («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_trans
       [(Term.app
         `IH
         [(Term.hole "_")
          (Term.app `max_lt [`xb `yb])
          («term_<|_»
           `ax.trans_le
           "<|"
           (Term.app
            `opow_le_opow_right
            [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
        («term_<|_»
         (Term.app `opow_le_opow_right [`omega_pos])
         "<|"
         («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `opow_le_opow_right [`omega_pos])
       "<|"
       («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `max_lt [`xb `yb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `yb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `opow_le_opow_right [`omega_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `omega_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_le_opow_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `opow_le_opow_right [`omega_pos])
      "<|"
      («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `IH
       [(Term.hole "_")
        (Term.app `max_lt [`xb `yb])
        («term_<|_»
         `ax.trans_le
         "<|"
         (Term.app
          `opow_le_opow_right
          [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `ax.trans_le
       "<|"
       (Term.app
        `opow_le_opow_right
        [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `opow_le_opow_right
       [`omega_pos (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])
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
      `le_max_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `omega_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_le_opow_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `ax.trans_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      `ax.trans_le
      "<|"
      (Term.app
       `opow_le_opow_right
       [`omega_pos (Term.paren "(" (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")]) ")")]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `max_lt [`xb `yb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `yb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `max_lt [`xb `yb]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `IH
      [(Term.hole "_")
       (Term.paren "(" (Term.app `max_lt [`xb `yb]) ")")
       (Term.paren
        "("
        («term_<|_»
         `ax.trans_le
         "<|"
         (Term.app
          `opow_le_opow_right
          [`omega_pos
           (Term.paren "(" (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")]) ")")]))
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_trans
      [(Term.paren
        "("
        (Term.app
         `IH
         [(Term.hole "_")
          (Term.paren "(" (Term.app `max_lt [`xb `yb]) ")")
          (Term.paren
           "("
           («term_<|_»
            `ax.trans_le
            "<|"
            (Term.app
             `opow_le_opow_right
             [`omega_pos
              (Term.paren "(" (Term.app `le_max_left [(Term.hole "_") (Term.hole "_")]) ")")]))
           ")")])
        ")")
       (Term.paren
        "("
        («term_<|_»
         (Term.app `opow_le_opow_right [`omega_pos])
         "<|"
         («term_<|_» `le_of_lt "<|" (Term.app `max_lt [`xb `yb])))
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `add_le_add_left
        [(Term.app
          `opow_le_opow_right
          [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
         (Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `add_le_add_left
       [(Term.app
         `opow_le_opow_right
         [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       `opow_le_opow_right
       [`omega_pos (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])
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
      `le_max_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `omega_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_le_opow_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `opow_le_opow_right
      [`omega_pos (Term.paren "(" (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `add_le_add_left
      [(Term.paren
        "("
        (Term.app
         `opow_le_opow_right
         [`omega_pos
          (Term.paren "(" (Term.app `le_max_right [(Term.hole "_") (Term.hole "_")]) ")")])
        ")")
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `yb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
          [(Term.app `opow_is_normal [`one_lt_omega])])
         "."
         `limit_le)
        [`l])
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
         [(Term.app `opow_is_normal [`one_lt_omega])])
        "."
        `limit_le)
       [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
        [(Term.app `opow_is_normal [`one_lt_omega])])
       "."
       `limit_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
       [(Term.app `opow_is_normal [`one_lt_omega])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opow_is_normal [`one_lt_omega])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_lt_omega
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_is_normal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opow_is_normal [`one_lt_omega])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `add_is_normal [`a]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `add_is_normal [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_is_normal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `add_is_normal [`a]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `add_is_normal [`a]) ")") "." `trans)
      [(Term.paren "(" (Term.app `opow_is_normal [`one_lt_omega]) ")")])
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
         (Term.proj (Term.paren "(" (Term.app `add_is_normal [`a]) ")") "." `trans)
         [(Term.paren "(" (Term.app `opow_is_normal [`one_lt_omega]) ")")])
        ")")
       "."
       `limit_le)
      [`l])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj (Term.app `lt_opow_of_limit [`omega_ne_zero `l]) "." (fieldIdx "1"))
          [`h]))]
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
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xb)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `lt_opow_of_limit [`omega_ne_zero `l]) "." (fieldIdx "1"))
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `lt_opow_of_limit [`omega_ne_zero `l]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lt_opow_of_limit [`omega_ne_zero `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `omega_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_opow_of_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lt_opow_of_limit [`omega_ne_zero `l])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj (Term.app `lt_mul_of_limit [`omega_is_limit]) "." (fieldIdx "1"))
            [`h]))]
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
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xo)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `le_trans
          [(Term.app `add_le_add_right [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
           (Term.hole "_")]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `opow_succ)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_add)
           ","
           (Tactic.rwRule [] (Term.app `add_omega [`xo]))]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `opow_succ)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_add)
         ","
         (Tactic.rwRule [] (Term.app `add_omega [`xo]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_omega [`xo])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xo
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_omega
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `le_trans
        [(Term.app `add_le_add_right [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_trans
       [(Term.app `add_le_add_right [(Term.app `le_of_lt [`ax]) (Term.hole "_")]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `add_le_add_right [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `le_of_lt [`ax])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ax
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_of_lt [`ax]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_le_add_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `add_le_add_right [(Term.paren "(" (Term.app `le_of_lt [`ax]) ")") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj (Term.app `lt_mul_of_limit [`omega_is_limit]) "." (fieldIdx "1"))
          [`h]))]
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
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xo)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `lt_mul_of_limit [`omega_is_limit]) "." (fieldIdx "1")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `lt_mul_of_limit [`omega_is_limit]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lt_mul_of_limit [`omega_is_limit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `omega_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_mul_of_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lt_mul_of_limit [`omega_is_limit])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `opow_zero)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `succ_zero)
           ","
           (Tactic.rwRule [] `lt_succ_iff)
           ","
           (Tactic.rwRule [] `Ordinal.le_zero)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `zero_add)] "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `zero_add)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `opow_zero)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `succ_zero)
         ","
         (Tactic.rwRule [] `lt_succ_iff)
         ","
         (Tactic.rwRule [] `Ordinal.le_zero)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ordinal.le_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_succ_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `succ_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `limit_rec_on
        [`b
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
         (Term.fun "fun" (Term.basicFun [`b (Term.hole "_") `h] [] "=>" (Term.hole "_")))
         (Term.fun "fun" (Term.basicFun [`b `l `IH `h] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `limit_rec_on
       [`b
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
        (Term.fun "fun" (Term.basicFun [`b (Term.hole "_") `h] [] "=>" (Term.hole "_")))
        (Term.fun "fun" (Term.basicFun [`b `l `IH `h] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`b `l `IH `h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`b (Term.hole "_") `h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`b (Term.hole "_") `h] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `limit_rec_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.revert "revert" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `le_antisymm
        [(Term.hole "_") (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_antisymm
       [(Term.hole "_") (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])
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
      `le_add_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_+_» `a "+" (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))
       "="
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  add_omega_opow
  { a b : Ordinal } ( h : a < omega ^ b ) : a + omega ^ b = omega ^ b
  :=
    by
      refine' le_antisymm _ le_add_left _ _
        revert h
        ;
        refine' limit_rec_on b fun h => _ fun b _ h => _ fun b l IH h => _
        · rw [ opow_zero , ← succ_zero , lt_succ_iff , Ordinal.le_zero ] at h rw [ h , zero_add ]
        ·
          rw [ opow_succ ] at h
            rcases lt_mul_of_limit omega_is_limit . 1 h with ⟨ x , xo , ax ⟩
            refine' le_trans add_le_add_right le_of_lt ax _ _
            rw [ opow_succ , ← mul_add , add_omega xo ]
        ·
          rcases lt_opow_of_limit omega_ne_zero l . 1 h with ⟨ x , xb , ax ⟩
            exact
              add_is_normal a . trans opow_is_normal one_lt_omega . limit_le l . 2
                fun
                  y yb
                    =>
                    add_le_add_left opow_le_opow_right omega_pos le_max_right _ _ _ . trans
                      le_trans
                        IH
                            _
                              max_lt xb yb
                              ax.trans_le <| opow_le_opow_right omega_pos le_max_left _ _
                          opow_le_opow_right omega_pos <| le_of_lt <| max_lt xb yb
#align ordinal.add_omega_opow Ordinal.add_omega_opow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `principal_add_omega_opow [])
      (Command.declSig
       [(Term.explicitBinder "(" [`o] [":" `Ordinal] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Principal
         [(Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")")
          (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `o)])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `principal_add_iff_add_left_eq_self "." (fieldIdx "2"))
        [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `add_omega_opow))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `principal_add_iff_add_left_eq_self "." (fieldIdx "2"))
       [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `add_omega_opow))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `add_omega_opow))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_omega_opow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `principal_add_iff_add_left_eq_self "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `principal_add_iff_add_left_eq_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Principal
       [(Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")")
        (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `o)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  principal_add_omega_opow
  ( o : Ordinal ) : Principal ( · + · ) omega ^ o
  := principal_add_iff_add_left_eq_self . 2 fun a => add_omega_opow
#align ordinal.principal_add_omega_opow Ordinal.principal_add_omega_opow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The main characterization theorem for additive principal ordinals. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `principal_add_iff_zero_or_omega_opow [])
      (Command.declSig
       [(Term.implicitBinder "{" [`o] [":" `Ordinal] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.app
          `Principal
          [(Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")") `o])
         "↔"
         («term_∨_»
          («term_=_» `o "=" (num "0"))
          "∨"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
           ","
           («term_=_» `o "=" (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `a)))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `eq_or_ne [`o (num "0")]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `rfl)
                    "|"
                    (Std.Tactic.RCases.rcasesPat.one `ho)])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `principal_zero) "," (Tactic.simpLemma [] [] `Or.inl)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `principal_add_iff_add_left_eq_self)] "]")
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `ho) "," (Tactic.simpLemma [] [] `false_or_iff)] "]"]
              [])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`H]
                  []
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.hole "_")
                    ","
                    (Term.proj
                     (Term.app
                      (Term.proj
                       (Term.app
                        `lt_or_eq_of_le
                        [(Term.app `opow_log_le_self [(Term.hole "_") `ho])])
                       "."
                       `resolve_left)
                      [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))])
                     "."
                     `symm)]
                   "⟩")))
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`b "," `e] "⟩")]
                  []
                  "=>"
                  (Term.subst
                   (Term.proj `e "." `symm)
                   "▸"
                   [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `add_omega_opow))])))]
               "⟩"))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `H [(Term.hole "_") `h]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl [] [] ":=" (Term.app `lt_opow_succ_log_self [`one_lt_omega `o]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `opow_succ)
                ","
                (Tactic.rwRule [] (Term.app `lt_mul_of_limit [`omega_is_limit]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `this)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ao)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h')])
                     [])]
                   "⟩")])
                [])])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`ao]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.clear "clear" [`ao])
             []
             (Tactic.revert "revert" [`h'])
             []
             (Tactic.apply "apply" `not_lt_of_le)
             []
             (Mathlib.Tactic.tacticSuffices_
              "suffices"
              [`e []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_+_»
                  («term_*_»
                   (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                    `omega
                    "^"
                    (Term.app `log [`omega `o]))
                   "*"
                   (coeNotation "↑" `n))
                  "+"
                  `o)
                 "="
                 `o))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `e)] "]")]
                 ["using"
                  (Term.app
                   `le_add_right
                   [(«term_*_»
                     (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                      `omega
                      "^"
                      (Term.app `log [`omega `o]))
                     "*"
                     (coeNotation "↑" `n))
                    `o])]))])
             []
             (Tactic.induction'
              "induction'"
              [(Tactic.casesTarget [] `n)]
              []
              ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Nat.cast_zero)
                  ","
                  (Tactic.simpLemma [] [] `mul_zero)
                  ","
                  (Tactic.simpLemma [] [] `zero_add)]
                 "]"]
                [])])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Nat.cast_succ)
                ","
                (Tactic.simpLemma [] [] `mul_add_one)
                ","
                (Tactic.simpLemma [] [] `add_assoc)
                ","
                (Tactic.simpLemma [] [] `this)
                ","
                (Tactic.simpLemma [] [] `IH)]
               "]"]
              [])])])))
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `eq_or_ne [`o (num "0")]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `rfl)
                   "|"
                   (Std.Tactic.RCases.rcasesPat.one `ho)])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `principal_zero) "," (Tactic.simpLemma [] [] `Or.inl)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `principal_add_iff_add_left_eq_self)] "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `ho) "," (Tactic.simpLemma [] [] `false_or_iff)] "]"]
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`H]
                 []
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.hole "_")
                   ","
                   (Term.proj
                    (Term.app
                     (Term.proj
                      (Term.app
                       `lt_or_eq_of_le
                       [(Term.app `opow_log_le_self [(Term.hole "_") `ho])])
                      "."
                      `resolve_left)
                     [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))])
                    "."
                    `symm)]
                  "⟩")))
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`b "," `e] "⟩")]
                 []
                 "=>"
                 (Term.subst
                  (Term.proj `e "." `symm)
                  "▸"
                  [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `add_omega_opow))])))]
              "⟩"))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `H [(Term.hole "_") `h]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl [] [] ":=" (Term.app `lt_opow_succ_log_self [`one_lt_omega `o]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `opow_succ)
               ","
               (Tactic.rwRule [] (Term.app `lt_mul_of_limit [`omega_is_limit]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `this)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ao)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h')])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`ao]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.clear "clear" [`ao])
            []
            (Tactic.revert "revert" [`h'])
            []
            (Tactic.apply "apply" `not_lt_of_le)
            []
            (Mathlib.Tactic.tacticSuffices_
             "suffices"
             [`e []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_+_»
                 («term_*_»
                  (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                   `omega
                   "^"
                   (Term.app `log [`omega `o]))
                  "*"
                  (coeNotation "↑" `n))
                 "+"
                 `o)
                "="
                `o))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                ["only"]
                [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `e)] "]")]
                ["using"
                 (Term.app
                  `le_add_right
                  [(«term_*_»
                    (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                     `omega
                     "^"
                     (Term.app `log [`omega `o]))
                    "*"
                    (coeNotation "↑" `n))
                   `o])]))])
            []
            (Tactic.induction'
             "induction'"
             [(Tactic.casesTarget [] `n)]
             []
             ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
             [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Nat.cast_zero)
                 ","
                 (Tactic.simpLemma [] [] `mul_zero)
                 ","
                 (Tactic.simpLemma [] [] `zero_add)]
                "]"]
               [])])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Nat.cast_succ)
               ","
               (Tactic.simpLemma [] [] `mul_add_one)
               ","
               (Tactic.simpLemma [] [] `add_assoc)
               ","
               (Tactic.simpLemma [] [] `this)
               ","
               (Tactic.simpLemma [] [] `IH)]
              "]"]
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `principal_add_iff_add_left_eq_self)] "]")
         [])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `ho) "," (Tactic.simpLemma [] [] `false_or_iff)] "]"]
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`H]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.hole "_")
               ","
               (Term.proj
                (Term.app
                 (Term.proj
                  (Term.app `lt_or_eq_of_le [(Term.app `opow_log_le_self [(Term.hole "_") `ho])])
                  "."
                  `resolve_left)
                 [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))])
                "."
                `symm)]
              "⟩")))
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`b "," `e] "⟩")]
             []
             "=>"
             (Term.subst
              (Term.proj `e "." `symm)
              "▸"
              [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `add_omega_opow))])))]
          "⟩"))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `H [(Term.hole "_") `h]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl [] [] ":=" (Term.app `lt_opow_succ_log_self [`one_lt_omega `o]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `opow_succ)
           ","
           (Tactic.rwRule [] (Term.app `lt_mul_of_limit [`omega_is_limit]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `this)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ao)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h')])
                [])]
              "⟩")])
           [])])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`ao]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.clear "clear" [`ao])
        []
        (Tactic.revert "revert" [`h'])
        []
        (Tactic.apply "apply" `not_lt_of_le)
        []
        (Mathlib.Tactic.tacticSuffices_
         "suffices"
         [`e []]
         [(Term.typeSpec
           ":"
           («term_=_»
            («term_+_»
             («term_*_»
              (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
               `omega
               "^"
               (Term.app `log [`omega `o]))
              "*"
              (coeNotation "↑" `n))
             "+"
             `o)
            "="
            `o))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `e)] "]")]
            ["using"
             (Term.app
              `le_add_right
              [(«term_*_»
                (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                 `omega
                 "^"
                 (Term.app `log [`omega `o]))
                "*"
                (coeNotation "↑" `n))
               `o])]))])
        []
        (Tactic.induction'
         "induction'"
         [(Tactic.casesTarget [] `n)]
         []
         ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
         [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Nat.cast_zero)
             ","
             (Tactic.simpLemma [] [] `mul_zero)
             ","
             (Tactic.simpLemma [] [] `zero_add)]
            "]"]
           [])])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Nat.cast_succ)
           ","
           (Tactic.simpLemma [] [] `mul_add_one)
           ","
           (Tactic.simpLemma [] [] `add_assoc)
           ","
           (Tactic.simpLemma [] [] `this)
           ","
           (Tactic.simpLemma [] [] `IH)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Nat.cast_succ)
         ","
         (Tactic.simpLemma [] [] `mul_add_one)
         ","
         (Tactic.simpLemma [] [] `add_assoc)
         ","
         (Tactic.simpLemma [] [] `this)
         ","
         (Tactic.simpLemma [] [] `IH)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
          [(Tactic.simpLemma [] [] `Nat.cast_zero)
           ","
           (Tactic.simpLemma [] [] `mul_zero)
           ","
           (Tactic.simpLemma [] [] `zero_add)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Nat.cast_zero)
         ","
         (Tactic.simpLemma [] [] `mul_zero)
         ","
         (Tactic.simpLemma [] [] `zero_add)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `n)]
       []
       ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          ["only"]
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `e)] "]")]
          ["using"
           (Term.app
            `le_add_right
            [(«term_*_»
              (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
               `omega
               "^"
               (Term.app `log [`omega `o]))
              "*"
              (coeNotation "↑" `n))
             `o])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `e)] "]")]
        ["using"
         (Term.app
          `le_add_right
          [(«term_*_»
            (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" (Term.app `log [`omega `o]))
            "*"
            (coeNotation "↑" `n))
           `o])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_add_right
       [(«term_*_»
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" (Term.app `log [`omega `o]))
         "*"
         (coeNotation "↑" `n))
        `o])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_»
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" (Term.app `log [`omega `o]))
       "*"
       (coeNotation "↑" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" (Term.app `log [`omega `o]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The main characterization theorem for additive principal ordinals. -/
  theorem
    principal_add_iff_zero_or_omega_opow
    { o : Ordinal } : Principal ( · + · ) o ↔ o = 0 ∨ ∃ a , o = omega ^ a
    :=
      by
        rcases eq_or_ne o 0 with ( rfl | ho )
          · simp only [ principal_zero , Or.inl ]
          ·
            rw [ principal_add_iff_add_left_eq_self ]
              simp only [ ho , false_or_iff ]
              refine'
                ⟨
                  fun
                      H
                        =>
                        ⟨
                          _ , lt_or_eq_of_le opow_log_le_self _ ho . resolve_left fun h => _ . symm
                          ⟩
                    ,
                    fun ⟨ b , e ⟩ => e . symm ▸ fun a => add_omega_opow
                  ⟩
              have := H _ h
              have := lt_opow_succ_log_self one_lt_omega o
              rw [ opow_succ , lt_mul_of_limit omega_is_limit ] at this
              rcases this with ⟨ a , ao , h' ⟩
              rcases lt_omega . 1 ao with ⟨ n , rfl ⟩
              clear ao
              revert h'
              apply not_lt_of_le
              suffices e : omega ^ log omega o * ↑ n + o = o
              · simpa only [ e ] using le_add_right omega ^ log omega o * ↑ n o
              induction' n with n IH
              · simp only [ Nat.cast_zero , mul_zero , zero_add ]
              simp only [ Nat.cast_succ , mul_add_one , add_assoc , this , IH ]
#align ordinal.principal_add_iff_zero_or_omega_opow Ordinal.principal_add_iff_zero_or_omega_opow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `opow_principal_add_of_principal_add [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [] "}")
        (Term.explicitBinder
         "("
         [`ha]
         [":"
          (Term.app
           `Principal
           [(Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")") `a])]
         []
         ")")
        (Term.explicitBinder "(" [`b] [":" `Ordinal] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Principal
         [(Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")")
          (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `a "^" `b)])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              (Term.app
               (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
               [`ha]))]
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `eq_or_ne [`b (num "0")]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.paren
                   "("
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.one `rfl)
                      "|"
                      (Std.Tactic.RCases.rcasesPat.one `hb)])
                    [])
                   ")")])
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]") [])
               []
               (Tactic.exact "exact" `principal_add_one)])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_opow [`hb]))] "]")
                [])])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_mul)]
               "]")
              [])
             []
             (Tactic.exact "exact" (Term.app `principal_add_omega_opow [(Term.hole "_")]))])])))
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1")) [`ha]))]
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
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                      [])]
                    "⟩")])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `eq_or_ne [`b (num "0")]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `rfl)
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `hb)])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]") [])
              []
              (Tactic.exact "exact" `principal_add_one)])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_opow [`hb]))] "]")
               [])])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_mul)]
              "]")
             [])
            []
            (Tactic.exact "exact" (Term.app `principal_add_omega_opow [(Term.hole "_")]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_mul)] "]")
         [])
        []
        (Tactic.exact "exact" (Term.app `principal_add_omega_opow [(Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `principal_add_omega_opow [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `principal_add_omega_opow [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `principal_add_omega_opow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_mul)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `eq_or_ne [`b (num "0")]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.paren
              "("
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.one `rfl) "|" (Std.Tactic.RCases.rcasesPat.one `hb)])
               [])
              ")")])
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]") [])
          []
          (Tactic.exact "exact" `principal_add_one)])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_opow [`hb]))] "]")
           [])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_opow [`hb]))] "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `zero_opow [`hb]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_opow [`hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_opow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]") [])
        []
        (Tactic.exact "exact" `principal_add_one)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `principal_add_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `principal_add_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `eq_or_ne [`b (num "0")]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `rfl) "|" (Std.Tactic.RCases.rcasesPat.one `hb)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_or_ne [`b (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_or_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1")) [`ha]))]
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1")) [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `principal_add_iff_zero_or_omega_opow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Principal
       [(Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")")
        (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `a "^" `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `a "^" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  opow_principal_add_of_principal_add
  { a } ( ha : Principal ( · + · ) a ) ( b : Ordinal ) : Principal ( · + · ) a ^ b
  :=
    by
      rcases principal_add_iff_zero_or_omega_opow . 1 ha with ( rfl | ⟨ c , rfl ⟩ )
        ·
          rcases eq_or_ne b 0 with ( rfl | hb )
            · rw [ opow_zero ] exact principal_add_one
            · rwa [ zero_opow hb ]
        · rw [ ← opow_mul ] exact principal_add_omega_opow _
#align ordinal.opow_principal_add_of_principal_add Ordinal.opow_principal_add_of_principal_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_absorp [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" `Ordinal] "}")
        (Term.explicitBinder
         "("
         [`h₁]
         [":" («term_<_» `a "<" (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h₂]
         [":" («term_≤_» (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b) "≤" `c)]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» («term_+_» `a "+" `c) "=" `c)))
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
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `Ordinal.add_sub_cancel_of_le [`h₂]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
              ","
              (Tactic.rwRule [] (Term.app `add_omega_opow [`h₁]))]
             "]")
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `Ordinal.add_sub_cancel_of_le [`h₂]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
             ","
             (Tactic.rwRule [] (Term.app `add_omega_opow [`h₁]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `Ordinal.add_sub_cancel_of_le [`h₂]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
         ","
         (Tactic.rwRule [] (Term.app `add_omega_opow [`h₁]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_omega_opow [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_omega_opow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ordinal.add_sub_cancel_of_le [`h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ordinal.add_sub_cancel_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» («term_+_» `a "+" `c) "=" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_» `a "+" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b) "≤" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
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
  add_absorp
  { a b c : Ordinal } ( h₁ : a < omega ^ b ) ( h₂ : omega ^ b ≤ c ) : a + c = c
  := by rw [ ← Ordinal.add_sub_cancel_of_le h₂ , ← add_assoc , add_omega_opow h₁ ]
#align ordinal.add_absorp Ordinal.add_absorp

theorem mul_principal_add_is_principal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b ≠ 1)
    (hb : Principal (· + ·) b) : Principal (· + ·) (a * b) :=
  by
  rcases eq_zero_or_pos a with (rfl | ha)
  · rw [zero_mul]
    exact principal_zero
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact principal_zero
    · rw [← succ_le_iff, succ_zero] at hb₁'
      intro c d hc hd
      rw [lt_mul_of_limit (principal_add_is_limit (lt_of_le_of_ne hb₁' hb₁.symm) hb)] at *
      · rcases hc with ⟨x, hx, hx'⟩
        rcases hd with ⟨y, hy, hy'⟩
        use x + y, hb hx hy
        rw [mul_add]
        exact Left.add_lt_add hx' hy'
      assumption'
#align ordinal.mul_principal_add_is_principal_add Ordinal.mul_principal_add_is_principal_add

/-! #### Multiplicative principal ordinals -/


theorem principal_mul_one : Principal (· * ·) 1 :=
  by
  rw [principal_one_iff]
  exact zero_mul _
#align ordinal.principal_mul_one Ordinal.principal_mul_one

theorem principal_mul_two : Principal (· * ·) 2 := fun a b ha hb =>
  by
  have h₂ : succ (1 : Ordinal) = 2 := rfl
  rw [← h₂, lt_succ_iff] at *
  convert mul_le_mul' ha hb
  exact (mul_one 1).symm
#align ordinal.principal_mul_two Ordinal.principal_mul_two

theorem principal_mul_of_le_two {o : Ordinal} (ho : o ≤ 2) : Principal (· * ·) o :=
  by
  rcases lt_or_eq_of_le ho with (ho | rfl)
  · have h₂ : succ (1 : Ordinal) = 2 := rfl
    rw [← h₂, lt_succ_iff] at ho
    rcases lt_or_eq_of_le ho with (ho | rfl)
    · rw [lt_one_iff_zero.1 ho]
      exact principal_zero
    · exact principal_mul_one
  · exact principal_mul_two
#align ordinal.principal_mul_of_le_two Ordinal.principal_mul_of_le_two

theorem principal_add_of_principal_mul {o : Ordinal} (ho : Principal (· * ·) o) (ho₂ : o ≠ 2) :
    Principal (· + ·) o := by
  cases' lt_or_gt_of_ne ho₂ with ho₁ ho₂
  · change o < succ 1 at ho₁
    rw [lt_succ_iff] at ho₁
    exact principal_add_of_le_one ho₁
  · refine' fun a b hao hbo => lt_of_le_of_lt _ (ho (max_lt hao hbo) ho₂)
    rw [mul_two]
    exact add_le_add (le_max_left a b) (le_max_right a b)
#align ordinal.principal_add_of_principal_mul Ordinal.principal_add_of_principal_mul

theorem principal_mul_is_limit {o : Ordinal.{u}} (ho₂ : 2 < o) (ho : Principal (· * ·) o) :
    o.IsLimit :=
  principal_add_is_limit ((lt_succ 1).trans ho₂) (principal_add_of_principal_mul ho (ne_of_gt ho₂))
#align ordinal.principal_mul_is_limit Ordinal.principal_mul_is_limit

theorem principal_mul_iff_mul_left_eq {o : Ordinal} :
    Principal (· * ·) o ↔ ∀ a, 0 < a → a < o → a * o = o :=
  by
  refine' ⟨fun h a ha₀ hao => _, fun h a b hao hbo => _⟩
  · cases' le_or_gt o 2 with ho ho
    · convert one_mul o
      apply le_antisymm
      · have : a < succ 1 := hao.trans_le ho
        rwa [lt_succ_iff] at this
      · rwa [← succ_le_iff, succ_zero] at ha₀
    · exact op_eq_self_of_principal hao (mul_is_normal ha₀) h (principal_mul_is_limit ho h)
  · rcases eq_or_ne a 0 with (rfl | ha)
    · rwa [zero_mul]
    rw [← Ordinal.pos_iff_ne_zero] at ha
    rw [← h a ha hao]
    exact (mul_is_normal ha).StrictMono hbo
#align ordinal.principal_mul_iff_mul_left_eq Ordinal.principal_mul_iff_mul_left_eq

theorem principal_mul_omega : Principal (· * ·) omega := fun a b ha hb =>
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← nat_cast_mul]
    apply nat_lt_omega
#align ordinal.principal_mul_omega Ordinal.principal_mul_omega

theorem mul_omega {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : a * omega = omega :=
  principal_mul_iff_mul_left_eq.1 principal_mul_omega a a0 ha
#align ordinal.mul_omega Ordinal.mul_omega

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_lt_omega_opow [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" `Ordinal] "}")
        (Term.explicitBinder "(" [`c0] [":" («term_<_» (num "0") "<" `c)] [] ")")
        (Term.explicitBinder
         "("
         [`ha]
         [":" («term_<_» `a "<" (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `c))]
         []
         ")")
        (Term.explicitBinder "(" [`hb] [":" («term_<_» `b "<" `omega)] [] ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         («term_*_» `a "*" `b)
         "<"
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `c))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `zero_or_succ_or_limit [`c]))]
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
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.one `l)])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app (Term.proj (Term.app `lt_irrefl [(Term.hole "_")]) "." `elim) [`c0]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj
                  (Term.app
                   (Term.proj
                    («term_<|_»
                     `mul_is_normal
                     "<|"
                     (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
                    "."
                    `limit_lt)
                   [`omega_is_limit])
                  "."
                  (fieldIdx "1"))
                 [`ha]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `an)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.apply
              "apply"
              (Term.proj
               (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`an]) (Term.hole "_")])
               "."
               `trans_lt))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `opow_succ)
                ","
                (Tactic.rwRule [] `mul_assoc)
                ","
                (Tactic.rwRule
                 []
                 (Term.app
                  `mul_lt_mul_iff_left
                  [(Term.app `opow_pos [(Term.hole "_") `omega_pos])]))]
               "]")
              [])
             []
             (Tactic.exact "exact" (Term.app `principal_mul_omega [`hn `hb]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj
                  (Term.app
                   (Term.proj (Term.app `opow_is_normal [`one_lt_omega]) "." `limit_lt)
                   [`l])
                  "."
                  (fieldIdx "1"))
                 [`ha]))]
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
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.app `mul_le_mul' [(Term.app `le_of_lt [`ax]) (Term.app `le_of_lt [`hb])])
                "."
                `trans_lt)
               [(Term.hole "_")]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_succ)
                ","
                (Tactic.rwRule [] (Term.app `opow_lt_opow_iff_right [`one_lt_omega]))]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app (Term.proj `l "." (fieldIdx "2")) [(Term.hole "_") `hx]))])])))
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `zero_or_succ_or_limit [`c]))]
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
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.one `l)])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app (Term.proj (Term.app `lt_irrefl [(Term.hole "_")]) "." `elim) [`c0]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj
                   («term_<|_»
                    `mul_is_normal
                    "<|"
                    (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
                   "."
                   `limit_lt)
                  [`omega_is_limit])
                 "."
                 (fieldIdx "1"))
                [`ha]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `an)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.apply
             "apply"
             (Term.proj
              (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`an]) (Term.hole "_")])
              "."
              `trans_lt))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `opow_succ)
               ","
               (Tactic.rwRule [] `mul_assoc)
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `mul_lt_mul_iff_left
                 [(Term.app `opow_pos [(Term.hole "_") `omega_pos])]))]
              "]")
             [])
            []
            (Tactic.exact "exact" (Term.app `principal_mul_omega [`hn `hb]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj (Term.app `opow_is_normal [`one_lt_omega]) "." `limit_lt)
                  [`l])
                 "."
                 (fieldIdx "1"))
                [`ha]))]
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
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.app `mul_le_mul' [(Term.app `le_of_lt [`ax]) (Term.app `le_of_lt [`hb])])
               "."
               `trans_lt)
              [(Term.hole "_")]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_succ)
               ","
               (Tactic.rwRule [] (Term.app `opow_lt_opow_iff_right [`one_lt_omega]))]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app (Term.proj `l "." (fieldIdx "2")) [(Term.hole "_") `hx]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj
             (Term.app (Term.proj (Term.app `opow_is_normal [`one_lt_omega]) "." `limit_lt) [`l])
             "."
             (fieldIdx "1"))
            [`ha]))]
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
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.app `mul_le_mul' [(Term.app `le_of_lt [`ax]) (Term.app `le_of_lt [`hb])])
           "."
           `trans_lt)
          [(Term.hole "_")]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_succ)
           ","
           (Tactic.rwRule [] (Term.app `opow_lt_opow_iff_right [`one_lt_omega]))]
          "]")
         [])
        []
        (Tactic.exact "exact" (Term.app (Term.proj `l "." (fieldIdx "2")) [(Term.hole "_") `hx]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app (Term.proj `l "." (fieldIdx "2")) [(Term.hole "_") `hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `l "." (fieldIdx "2")) [(Term.hole "_") `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `l "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_succ)
         ","
         (Tactic.rwRule [] (Term.app `opow_lt_opow_iff_right [`one_lt_omega]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opow_lt_opow_iff_right [`one_lt_omega])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_lt_omega
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_lt_opow_iff_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app `mul_le_mul' [(Term.app `le_of_lt [`ax]) (Term.app `le_of_lt [`hb])])
         "."
         `trans_lt)
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `mul_le_mul' [(Term.app `le_of_lt [`ax]) (Term.app `le_of_lt [`hb])])
        "."
        `trans_lt)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `mul_le_mul' [(Term.app `le_of_lt [`ax]) (Term.app `le_of_lt [`hb])])
       "."
       `trans_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mul_le_mul' [(Term.app `le_of_lt [`ax]) (Term.app `le_of_lt [`hb])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_lt [`hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_of_lt [`hb]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_of_lt [`ax])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ax
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_of_lt [`ax]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mul_le_mul'
      [(Term.paren "(" (Term.app `le_of_lt [`ax]) ")")
       (Term.paren "(" (Term.app `le_of_lt [`hb]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj
           (Term.app (Term.proj (Term.app `opow_is_normal [`one_lt_omega]) "." `limit_lt) [`l])
           "."
           (fieldIdx "1"))
          [`ha]))]
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
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app (Term.proj (Term.app `opow_is_normal [`one_lt_omega]) "." `limit_lt) [`l])
        "."
        (fieldIdx "1"))
       [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app (Term.proj (Term.app `opow_is_normal [`one_lt_omega]) "." `limit_lt) [`l])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `opow_is_normal [`one_lt_omega]) "." `limit_lt) [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `opow_is_normal [`one_lt_omega]) "." `limit_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opow_is_normal [`one_lt_omega])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_lt_omega
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_is_normal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opow_is_normal [`one_lt_omega])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `opow_is_normal [`one_lt_omega]) ")") "." `limit_lt)
      [`l])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj
               («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
               "."
               `limit_lt)
              [`omega_is_limit])
             "."
             (fieldIdx "1"))
            [`ha]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `an)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.apply
         "apply"
         (Term.proj
          (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`an]) (Term.hole "_")])
          "."
          `trans_lt))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `opow_succ)
           ","
           (Tactic.rwRule [] `mul_assoc)
           ","
           (Tactic.rwRule
            []
            (Term.app `mul_lt_mul_iff_left [(Term.app `opow_pos [(Term.hole "_") `omega_pos])]))]
          "]")
         [])
        []
        (Tactic.exact "exact" (Term.app `principal_mul_omega [`hn `hb]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `principal_mul_omega [`hn `hb]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `principal_mul_omega [`hn `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `principal_mul_omega
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
        [(Tactic.rwRule [] `opow_succ)
         ","
         (Tactic.rwRule [] `mul_assoc)
         ","
         (Tactic.rwRule
          []
          (Term.app `mul_lt_mul_iff_left [(Term.app `opow_pos [(Term.hole "_") `omega_pos])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_lt_mul_iff_left [(Term.app `opow_pos [(Term.hole "_") `omega_pos])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opow_pos [(Term.hole "_") `omega_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `omega_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opow_pos [(Term.hole "_") `omega_pos])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_lt_mul_iff_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj
        (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`an]) (Term.hole "_")])
        "."
        `trans_lt))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`an]) (Term.hole "_")])
       "."
       `trans_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`an]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `le_of_lt [`an])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `an
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_of_lt [`an]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_right'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_le_mul_right' [(Term.paren "(" (Term.app `le_of_lt [`an]) ")") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj
             («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
             "."
             `limit_lt)
            [`omega_is_limit])
           "."
           (fieldIdx "1"))
          [`ha]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hn)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `an)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj
          («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
          "."
          `limit_lt)
         [`omega_is_limit])
        "."
        (fieldIdx "1"))
       [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj
         («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
         "."
         `limit_lt)
        [`omega_is_limit])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
        "."
        `limit_lt)
       [`omega_is_limit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `omega_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
       "."
       `limit_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opow_pos [(Term.hole "_") `omega_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `omega_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `mul_is_normal
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
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
        («term_<|_» `mul_is_normal "<|" (Term.app `opow_pos [(Term.hole "_") `omega_pos]))
        ")")
       "."
       `limit_lt)
      [`omega_is_limit])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app (Term.proj (Term.app `lt_irrefl [(Term.hole "_")]) "." `elim) [`c0]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app (Term.proj (Term.app `lt_irrefl [(Term.hole "_")]) "." `elim) [`c0]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `lt_irrefl [(Term.hole "_")]) "." `elim) [`c0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `lt_irrefl [(Term.hole "_")]) "." `elim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lt_irrefl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_irrefl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lt_irrefl [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `zero_or_succ_or_limit [`c]))]
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")
               "|"
               (Std.Tactic.RCases.rcasesPat.one `l)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_or_succ_or_limit [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_or_succ_or_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       («term_*_» `a "*" `b)
       "<"
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mul_lt_omega_opow
  { a b c : Ordinal } ( c0 : 0 < c ) ( ha : a < omega ^ c ) ( hb : b < omega ) : a * b < omega ^ c
  :=
    by
      rcases zero_or_succ_or_limit c with ( rfl | ⟨ c , rfl ⟩ | l )
        · exact lt_irrefl _ . elim c0
        ·
          rw [ opow_succ ] at ha
            rcases
              mul_is_normal <| opow_pos _ omega_pos . limit_lt omega_is_limit . 1 ha
              with ⟨ n , hn , an ⟩
            apply mul_le_mul_right' le_of_lt an _ . trans_lt
            rw [ opow_succ , mul_assoc , mul_lt_mul_iff_left opow_pos _ omega_pos ]
            exact principal_mul_omega hn hb
        ·
          rcases opow_is_normal one_lt_omega . limit_lt l . 1 ha with ⟨ x , hx , ax ⟩
            refine' mul_le_mul' le_of_lt ax le_of_lt hb . trans_lt _
            rw [ ← opow_succ , opow_lt_opow_iff_right one_lt_omega ]
            exact l . 2 _ hx
#align ordinal.mul_lt_omega_opow Ordinal.mul_lt_omega_opow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_omega_opow_opow [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" `Ordinal] "}")
        (Term.explicitBinder "(" [`a0] [":" («term_<_» (num "0") "<" `a)] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           `a
           "<"
           (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
            `omega
            "^"
            (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_*_»
          `a
          "*"
          (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
           `omega
           "^"
           (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b)))
         "="
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
          `omega
          "^"
          (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Classical.«tacticBy_cases_:_» "by_cases" [`b0 ":"] («term_=_» `b "=" (num "0")))
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `b0)
                ","
                (Tactic.rwRule [] `opow_zero)
                ","
                (Tactic.rwRule [] `opow_one)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
             []
             (Tactic.exact "exact" (Term.app `mul_omega [`a0 `h]))])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `le_antisymm
             [(Term.hole "_")
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
                    [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
                    ["using"
                     (Term.app
                      `mul_le_mul_right'
                      [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`a0])
                       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                        `omega
                        "^"
                        (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))])]))])))]))
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              (Term.app
               (Term.proj
                (Term.app
                 `lt_opow_of_limit
                 [`omega_ne_zero (Term.app `opow_is_limit_left [`omega_is_limit `b0])])
                "."
                (fieldIdx "1"))
               [`h]))]
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
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xb)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.apply
            "apply"
            (Term.proj
             (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
             "."
             `trans))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_add)
              ","
              (Tactic.rwRule [] (Term.app `add_omega_opow [`xb]))]
             "]")
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
         [(Classical.«tacticBy_cases_:_» "by_cases" [`b0 ":"] («term_=_» `b "=" (num "0")))
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `b0)
               ","
               (Tactic.rwRule [] `opow_zero)
               ","
               (Tactic.rwRule [] `opow_one)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
            []
            (Tactic.exact "exact" (Term.app `mul_omega [`a0 `h]))])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `le_antisymm
            [(Term.hole "_")
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
                   [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
                   ["using"
                    (Term.app
                     `mul_le_mul_right'
                     [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`a0])
                      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                       `omega
                       "^"
                       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))])]))])))]))
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              (Term.proj
               (Term.app
                `lt_opow_of_limit
                [`omega_ne_zero (Term.app `opow_is_limit_left [`omega_is_limit `b0])])
               "."
               (fieldIdx "1"))
              [`h]))]
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xb)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.apply
           "apply"
           (Term.proj
            (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
            "."
            `trans))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_add)
             ","
             (Tactic.rwRule [] (Term.app `add_omega_opow [`xb]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_add)
         ","
         (Tactic.rwRule [] (Term.app `add_omega_opow [`xb]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_omega_opow [`xb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_omega_opow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj
        (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
        "."
        `trans))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mul_le_mul_right' [(Term.app `le_of_lt [`ax]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `le_of_lt [`ax])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ax
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_of_lt [`ax]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_right'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_le_mul_right' [(Term.paren "(" (Term.app `le_of_lt [`ax]) ")") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj
           (Term.app
            `lt_opow_of_limit
            [`omega_ne_zero (Term.app `opow_is_limit_left [`omega_is_limit `b0])])
           "."
           (fieldIdx "1"))
          [`h]))]
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
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xb)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ax)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `lt_opow_of_limit
         [`omega_ne_zero (Term.app `opow_is_limit_left [`omega_is_limit `b0])])
        "."
        (fieldIdx "1"))
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `lt_opow_of_limit
        [`omega_ne_zero (Term.app `opow_is_limit_left [`omega_is_limit `b0])])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `lt_opow_of_limit
       [`omega_ne_zero (Term.app `opow_is_limit_left [`omega_is_limit `b0])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opow_is_limit_left [`omega_is_limit `b0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `omega_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_is_limit_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opow_is_limit_left [`omega_is_limit `b0])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `omega_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_opow_of_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `lt_opow_of_limit
      [`omega_ne_zero (Term.paren "(" (Term.app `opow_is_limit_left [`omega_is_limit `b0]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `le_antisymm
        [(Term.hole "_")
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
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
               ["using"
                (Term.app
                 `mul_le_mul_right'
                 [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`a0])
                  (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                   `omega
                   "^"
                   (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))])]))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_antisymm
       [(Term.hole "_")
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
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
              ["using"
               (Term.app
                `mul_le_mul_right'
                [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`a0])
                 (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                  `omega
                  "^"
                  (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))])]))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
            ["using"
             (Term.app
              `mul_le_mul_right'
              [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`a0])
               (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
                `omega
                "^"
                (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))])]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `one_mul)] "]")]
        ["using"
         (Term.app
          `mul_le_mul_right'
          [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`a0])
           (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
            `omega
            "^"
            (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_le_mul_right'
       [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`a0])
        (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
         `omega
         "^"
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
       `omega
       "^"
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `b))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
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
  mul_omega_opow_opow
  { a b : Ordinal } ( a0 : 0 < a ) ( h : a < omega ^ omega ^ b )
    : a * omega ^ omega ^ b = omega ^ omega ^ b
  :=
    by
      by_cases b0 : b = 0
        ;
        · rw [ b0 , opow_zero , opow_one ] at h ⊢ exact mul_omega a0 h
        refine'
          le_antisymm
            _
              by
                simpa
                  only [ one_mul ] using mul_le_mul_right' one_le_iff_pos . 2 a0 omega ^ omega ^ b
        rcases
          lt_opow_of_limit omega_ne_zero opow_is_limit_left omega_is_limit b0 . 1 h
          with ⟨ x , xb , ax ⟩
        apply mul_le_mul_right' le_of_lt ax _ . trans
        rw [ ← opow_add , add_omega_opow xb ]
#align ordinal.mul_omega_opow_opow Ordinal.mul_omega_opow_opow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `principal_mul_omega_opow_opow [])
      (Command.declSig
       [(Term.explicitBinder "(" [`o] [":" `Ordinal] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Principal
         [(Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")")
          (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
           `omega
           "^"
           (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `o))])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `principal_mul_iff_mul_left_eq "." (fieldIdx "2"))
        [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_omega_opow_opow))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `principal_mul_iff_mul_left_eq "." (fieldIdx "2"))
       [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_omega_opow_opow))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_omega_opow_opow))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_omega_opow_opow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `principal_mul_iff_mul_left_eq "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `principal_mul_iff_mul_left_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Principal
       [(Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")")
        (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
         `omega
         "^"
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `o))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
       `omega
       "^"
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `o))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  principal_mul_omega_opow_opow
  ( o : Ordinal ) : Principal ( · * · ) omega ^ omega ^ o
  := principal_mul_iff_mul_left_eq . 2 fun a => mul_omega_opow_opow
#align ordinal.principal_mul_omega_opow_opow Ordinal.principal_mul_omega_opow_opow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `principal_add_of_principal_mul_opow [])
      (Command.declSig
       [(Term.implicitBinder "{" [`o `b] [":" `Ordinal] "}")
        (Term.explicitBinder "(" [`hb] [":" («term_<_» (num "1") "<" `b)] [] ")")
        (Term.explicitBinder
         "("
         [`ho]
         [":"
          (Term.app
           `Principal
           [(Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")")
            (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" `o)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Principal
         [(Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")") `o])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x `y `hx `hy]
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
                []
                ":="
                (Term.app
                 `ho
                 [(Term.app
                   (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
                   [`hx])
                  (Term.app
                   (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
                   [`hy])]))))
             []
             (Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_add)
                ","
                (Tactic.rwRule [] (Term.app `opow_lt_opow_iff_right [`hb]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y `hx `hy]
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
               []
               ":="
               (Term.app
                `ho
                [(Term.app
                  (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
                  [`hx])
                 (Term.app
                  (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
                  [`hy])]))))
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_add)
               ","
               (Tactic.rwRule [] (Term.app `opow_lt_opow_iff_right [`hb]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
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
             []
             ":="
             (Term.app
              `ho
              [(Term.app
                (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
                [`hx])
               (Term.app
                (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
                [`hy])]))))
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_add)
             ","
             (Tactic.rwRule [] (Term.app `opow_lt_opow_iff_right [`hb]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_add)
         ","
         (Tactic.rwRule [] (Term.app `opow_lt_opow_iff_right [`hb]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opow_lt_opow_iff_right [`hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_lt_opow_iff_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          `ho
          [(Term.app (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2")) [`hx])
           (Term.app
            (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
            [`hy])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ho
       [(Term.app (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2")) [`hx])
        (Term.app (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2")) [`hy])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2")) [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opow_lt_opow_iff_right [`hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_lt_opow_iff_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opow_lt_opow_iff_right [`hb])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `opow_lt_opow_iff_right [`hb]) ")") "." (fieldIdx "2"))
      [`hy])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2")) [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `opow_lt_opow_iff_right [`hb]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opow_lt_opow_iff_right [`hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_lt_opow_iff_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opow_lt_opow_iff_right [`hb])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `opow_lt_opow_iff_right [`hb]) ")") "." (fieldIdx "2"))
      [`hx])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ho
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Principal
       [(Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")") `o])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.paren "(" («term_+_» (Term.cdot "·") "+" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.cdot "·") "+" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Principal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Principal
       [(Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")")
        (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" `o)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
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
  principal_add_of_principal_mul_opow
  { o b : Ordinal } ( hb : 1 < b ) ( ho : Principal ( · * · ) b ^ o ) : Principal ( · + · ) o
  :=
    fun
      x y hx hy
        =>
        by
          have := ho opow_lt_opow_iff_right hb . 2 hx opow_lt_opow_iff_right hb . 2 hy
            rwa [ ← opow_add , opow_lt_opow_iff_right hb ] at this
#align ordinal.principal_add_of_principal_mul_opow Ordinal.principal_add_of_principal_mul_opow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The main characterization theorem for multiplicative principal ordinals. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `principal_mul_iff_le_two_or_omega_opow_opow [])
      (Command.declSig
       [(Term.implicitBinder "{" [`o] [":" `Ordinal] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.app
          `Principal
          [(Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")") `o])
         "↔"
         («term_∨_»
          («term_≤_» `o "≤" (num "2"))
          "∨"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
           ","
           («term_=_»
            `o
            "="
            (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
             `omega
             "^"
             (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `a))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun "fun" (Term.basicFun [`ho] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] (Term.app `le_or_lt [`o (num "2")]))]
              []
              ["with" [(Lean.binderIdent `ho₂) (Lean.binderIdent `ho₂)]])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `Or.inl [`ho₂]))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
                 [(Term.app `principal_add_of_principal_mul [`ho `ho₂.ne'])]))]
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
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                         [])]
                       "⟩")])
                    [])
                   ")")])
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.proj (Term.app `Ordinal.not_lt_zero [(num "2") `ho₂]) "." `elim))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
                 [(Term.app `principal_add_of_principal_mul_opow [`one_lt_omega `ho])]))]
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
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                         [])]
                       "⟩")])
                    [])
                   ")")])
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`ho₂] []))])
               []
               (Tactic.exact
                "exact"
                (Term.proj
                 (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `not_le) [`ho₂.le])
                 "."
                 `elim))])
             []
             (Tactic.exact
              "exact"
              (Term.app `Or.inr [(Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `ho₂)
                    "|"
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])
                  [])
                 ")"))]
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `principal_mul_of_le_two [`ho₂]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `principal_mul_omega_opow_opow [`a]))])])])))
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
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`ho] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] (Term.app `le_or_lt [`o (num "2")]))]
             []
             ["with" [(Lean.binderIdent `ho₂) (Lean.binderIdent `ho₂)]])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `Or.inl [`ho₂]))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
                [(Term.app `principal_add_of_principal_mul [`ho `ho₂.ne'])]))]
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
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.proj (Term.app `Ordinal.not_lt_zero [(num "2") `ho₂]) "." `elim))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
                [(Term.app `principal_add_of_principal_mul_opow [`one_lt_omega `ho])]))]
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
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`ho₂] []))])
              []
              (Tactic.exact
               "exact"
               (Term.proj
                (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `not_le) [`ho₂.le])
                "."
                `elim))])
            []
            (Tactic.exact "exact" (Term.app `Or.inr [(Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `ho₂)
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                      [])]
                    "⟩")])
                 [])
                ")"))]
             [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `principal_mul_of_le_two [`ho₂]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `principal_mul_omega_opow_opow [`a]))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `ho₂)
               "|"
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])
            ")"))]
         [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `principal_mul_of_le_two [`ho₂]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `principal_mul_omega_opow_opow [`a]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `principal_mul_omega_opow_opow [`a]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `principal_mul_omega_opow_opow [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `principal_mul_omega_opow_opow [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `principal_mul_omega_opow_opow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `principal_mul_of_le_two [`ho₂]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `principal_mul_of_le_two [`ho₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `principal_mul_of_le_two [`ho₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ho₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `principal_mul_of_le_two
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.paren
          "("
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.one `ho₂)
             "|"
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩")])
           [])
          ")"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] (Term.app `le_or_lt [`o (num "2")]))]
         []
         ["with" [(Lean.binderIdent `ho₂) (Lean.binderIdent `ho₂)]])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `Or.inl [`ho₂]))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
            [(Term.app `principal_add_of_principal_mul [`ho `ho₂.ne'])]))]
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
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])
               [])
              ")")])
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.proj (Term.app `Ordinal.not_lt_zero [(num "2") `ho₂]) "." `elim))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
            [(Term.app `principal_add_of_principal_mul_opow [`one_lt_omega `ho])]))]
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
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])
               [])
              ")")])
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`ho₂] []))])
          []
          (Tactic.exact
           "exact"
           (Term.proj
            (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `not_le) [`ho₂.le])
            "."
            `elim))])
        []
        (Tactic.exact "exact" (Term.app `Or.inr [(Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Or.inr [(Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inr [(Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`ho₂] []))])
        []
        (Tactic.exact
         "exact"
         (Term.proj
          (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `not_le) [`ho₂.le])
          "."
          `elim))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `not_le) [`ho₂.le])
        "."
        `elim))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `not_le) [`ho₂.le])
       "."
       `elim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `not_le) [`ho₂.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ho₂.le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `lt_succ [(num "1")]) "." `not_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lt_succ [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `lt_succ [(num "1")]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `lt_succ [(num "1")]) ")") "." `not_le)
      [`ho₂.le])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_zero)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`ho₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ho₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
          [(Term.app `principal_add_of_principal_mul_opow [`one_lt_omega `ho])]))]
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
       [(Term.app `principal_add_of_principal_mul_opow [`one_lt_omega `ho])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `principal_add_of_principal_mul_opow [`one_lt_omega `ho])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ho
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `one_lt_omega
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `principal_add_of_principal_mul_opow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `principal_add_of_principal_mul_opow [`one_lt_omega `ho])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `principal_add_iff_zero_or_omega_opow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.proj (Term.app `Ordinal.not_lt_zero [(num "2") `ho₂]) "." `elim))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.app `Ordinal.not_lt_zero [(num "2") `ho₂]) "." `elim))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Ordinal.not_lt_zero [(num "2") `ho₂]) "." `elim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ordinal.not_lt_zero [(num "2") `ho₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ho₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ordinal.not_lt_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ordinal.not_lt_zero [(num "2") `ho₂])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
          [(Term.app `principal_add_of_principal_mul [`ho `ho₂.ne'])]))]
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
       [(Term.app `principal_add_of_principal_mul [`ho `ho₂.ne'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `principal_add_of_principal_mul [`ho `ho₂.ne'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ho₂.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ho
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `principal_add_of_principal_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `principal_add_of_principal_mul [`ho `ho₂.ne'])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `principal_add_iff_zero_or_omega_opow "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `principal_add_iff_zero_or_omega_opow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `Or.inl [`ho₂]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Or.inl [`ho₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inl [`ho₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ho₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app `le_or_lt [`o (num "2")]))]
       []
       ["with" [(Lean.binderIdent `ho₂) (Lean.binderIdent `ho₂)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_or_lt [`o (num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `o
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_or_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`ho] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`ho] [] "=>" (Term.hole "_"))) "," (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`ho] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ho
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (Term.app
        `Principal
        [(Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")") `o])
       "↔"
       («term_∨_»
        («term_≤_» `o "≤" (num "2"))
        "∨"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
         ","
         («term_=_»
          `o
          "="
          (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
           `omega
           "^"
           (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `a))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       («term_≤_» `o "≤" (num "2"))
       "∨"
       («term∃_,_»
        "∃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
        ","
        («term_=_»
         `o
         "="
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
          `omega
          "^"
          (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `a)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
       ","
       («term_=_»
        `o
        "="
        (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
         `omega
         "^"
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `a))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       `o
       "="
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
        `omega
        "^"
        (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
       `omega
       "^"
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `omega "^" `a))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The main characterization theorem for multiplicative principal ordinals. -/
  theorem
    principal_mul_iff_le_two_or_omega_opow_opow
    { o : Ordinal } : Principal ( · * · ) o ↔ o ≤ 2 ∨ ∃ a , o = omega ^ omega ^ a
    :=
      by
        refine' ⟨ fun ho => _ , _ ⟩
          ·
            cases' le_or_lt o 2 with ho₂ ho₂
              · exact Or.inl ho₂
              rcases
                principal_add_iff_zero_or_omega_opow . 1 principal_add_of_principal_mul ho ho₂.ne'
                with ( rfl | ⟨ a , rfl ⟩ )
              · exact Ordinal.not_lt_zero 2 ho₂ . elim
              rcases
                principal_add_iff_zero_or_omega_opow . 1
                  principal_add_of_principal_mul_opow one_lt_omega ho
                with ( rfl | ⟨ b , rfl ⟩ )
              · rw [ opow_zero ] at ho₂ exact lt_succ 1 . not_le ho₂.le . elim
              exact Or.inr ⟨ b , rfl ⟩
          ·
            rintro ( ho₂ | ⟨ a , rfl ⟩ )
              · exact principal_mul_of_le_two ho₂
              · exact principal_mul_omega_opow_opow a
#align
  ordinal.principal_mul_iff_le_two_or_omega_opow_opow Ordinal.principal_mul_iff_le_two_or_omega_opow_opow

theorem mul_omega_dvd {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : ∀ {b}, omega ∣ b → a * b = b
  | _, ⟨b, rfl⟩ => by rw [← mul_assoc, mul_omega a0 ha]
#align ordinal.mul_omega_dvd Ordinal.mul_omega_dvd

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_eq_opow_log_succ [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Term.explicitUniv `Ordinal ".{" [`u] "}")] "}")
        (Term.explicitBinder "(" [`ha] [":" («term_≠_» `a "≠" (num "0"))] [] ")")
        (Term.explicitBinder
         "("
         [`hb]
         [":"
          (Term.app
           `Principal
           [(Term.paren "(" («term_*_» (Term.cdot "·") "*" (Term.cdot "·")) ")") `b])]
         []
         ")")
        (Term.explicitBinder "(" [`hb₂] [":" («term_<_» (num "2") "<" `b)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_*_» `a "*" `b)
         "="
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow
          `b
          "^"
          (Term.app `succ [(Term.app `log [`b `a])])))))
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
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl [`hbl []] [] ":=" (Term.app `principal_mul_is_limit [`hb₂ `hb]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  (Term.explicitUniv `IsNormal.bsup_eq ".{" [`u "," `u] "}")
                  [(Term.app
                    `mul_is_normal
                    [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`ha])])
                   `hbl]))
                ","
                (Tactic.rwRule [] `bsup_le_iff)]
               "]")
              [])
             []
             (Tactic.intro "intro" [`c `hcb])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hb₁ []]
                [(Term.typeSpec ":" («term_<_» (num "1") "<" `b))]
                ":="
                (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `trans) [`hb₂]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hbo₀ []]
                [(Term.typeSpec
                  ":"
                  («term_≠_»
                   (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" (Term.app `b.log [`a]))
                   "≠"
                   (num "0")))]
                ":="
                (Term.app
                 (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "1"))
                 [(Term.app `opow_pos [(Term.hole "_") (Term.app `zero_lt_one.trans [`hb₁])])]))))
             []
             (Tactic.apply
              "apply"
              (Term.app
               `le_trans
               [(Term.app
                 `mul_le_mul_right'
                 [(Term.app `le_of_lt [(Term.app `lt_mul_succ_div [`a `hbo₀])]) `c])]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `opow_succ)]
               "]")
              [])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `mul_le_mul_left'
               [(Term.app
                 `le_of_lt
                 [(Term.app
                   `hb
                   [(Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
                    `hcb])])
                (Term.hole "_")]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `div_lt [`hbo₀]))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_succ)]
               "]")
              [])
             []
             (Tactic.exact "exact" (Term.app `lt_opow_succ_log_self [`hb₁ (Term.hole "_")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]") [])
             []
             (Tactic.exact
              "exact"
              (Term.app `mul_le_mul_right' [(Term.app `opow_log_le_self [`b `ha]) `b]))])])))
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
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl [`hbl []] [] ":=" (Term.app `principal_mul_is_limit [`hb₂ `hb]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.explicitUniv `IsNormal.bsup_eq ".{" [`u "," `u] "}")
                 [(Term.app
                   `mul_is_normal
                   [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`ha])])
                  `hbl]))
               ","
               (Tactic.rwRule [] `bsup_le_iff)]
              "]")
             [])
            []
            (Tactic.intro "intro" [`c `hcb])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hb₁ []]
               [(Term.typeSpec ":" («term_<_» (num "1") "<" `b))]
               ":="
               (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `trans) [`hb₂]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hbo₀ []]
               [(Term.typeSpec
                 ":"
                 («term_≠_»
                  (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" (Term.app `b.log [`a]))
                  "≠"
                  (num "0")))]
               ":="
               (Term.app
                (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "1"))
                [(Term.app `opow_pos [(Term.hole "_") (Term.app `zero_lt_one.trans [`hb₁])])]))))
            []
            (Tactic.apply
             "apply"
             (Term.app
              `le_trans
              [(Term.app
                `mul_le_mul_right'
                [(Term.app `le_of_lt [(Term.app `lt_mul_succ_div [`a `hbo₀])]) `c])]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `opow_succ)]
              "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `mul_le_mul_left'
              [(Term.app
                `le_of_lt
                [(Term.app
                  `hb
                  [(Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
                   `hcb])])
               (Term.hole "_")]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `div_lt [`hbo₀]))
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_succ)]
              "]")
             [])
            []
            (Tactic.exact "exact" (Term.app `lt_opow_succ_log_self [`hb₁ (Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]") [])
            []
            (Tactic.exact
             "exact"
             (Term.app `mul_le_mul_right' [(Term.app `opow_log_le_self [`b `ha]) `b]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]") [])
        []
        (Tactic.exact
         "exact"
         (Term.app `mul_le_mul_right' [(Term.app `opow_log_le_self [`b `ha]) `b]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `mul_le_mul_right' [(Term.app `opow_log_le_self [`b `ha]) `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_le_mul_right' [(Term.app `opow_log_le_self [`b `ha]) `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opow_log_le_self [`b `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_log_le_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opow_log_le_self [`b `ha])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_right'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opow_succ)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl [`hbl []] [] ":=" (Term.app `principal_mul_is_limit [`hb₂ `hb]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app
             (Term.explicitUniv `IsNormal.bsup_eq ".{" [`u "," `u] "}")
             [(Term.app
               `mul_is_normal
               [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`ha])])
              `hbl]))
           ","
           (Tactic.rwRule [] `bsup_le_iff)]
          "]")
         [])
        []
        (Tactic.intro "intro" [`c `hcb])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hb₁ []]
           [(Term.typeSpec ":" («term_<_» (num "1") "<" `b))]
           ":="
           (Term.app (Term.proj (Term.app `lt_succ [(num "1")]) "." `trans) [`hb₂]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hbo₀ []]
           [(Term.typeSpec
             ":"
             («term_≠_»
              (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" (Term.app `b.log [`a]))
              "≠"
              (num "0")))]
           ":="
           (Term.app
            (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "1"))
            [(Term.app `opow_pos [(Term.hole "_") (Term.app `zero_lt_one.trans [`hb₁])])]))))
        []
        (Tactic.apply
         "apply"
         (Term.app
          `le_trans
          [(Term.app
            `mul_le_mul_right'
            [(Term.app `le_of_lt [(Term.app `lt_mul_succ_div [`a `hbo₀])]) `c])]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `opow_succ)]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `mul_le_mul_left'
          [(Term.app
            `le_of_lt
            [(Term.app
              `hb
              [(Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
               `hcb])])
           (Term.hole "_")]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `div_lt [`hbo₀]))
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_succ)]
          "]")
         [])
        []
        (Tactic.exact "exact" (Term.app `lt_opow_succ_log_self [`hb₁ (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `lt_opow_succ_log_self [`hb₁ (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_opow_succ_log_self [`hb₁ (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hb₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_opow_succ_log_self
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
        [(Tactic.rwRule [] (Term.app `div_lt [`hbo₀]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `opow_succ)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `div_lt [`hbo₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hbo₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `mul_le_mul_left'
        [(Term.app
          `le_of_lt
          [(Term.app
            `hb
            [(Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
             `hcb])])
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_le_mul_left'
       [(Term.app
         `le_of_lt
         [(Term.app
           `hb
           [(Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
            `hcb])])
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       `le_of_lt
       [(Term.app
         `hb
         [(Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")]) `hcb])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hb
       [(Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")]) `hcb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hcb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
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
      (Term.proj `hbl "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hbl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `hb
      [(Term.paren
        "("
        (Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
        ")")
       `hcb])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_of_lt
      [(Term.paren
        "("
        (Term.app
         `hb
         [(Term.paren
           "("
           (Term.app (Term.proj `hbl "." (fieldIdx "2")) [(Term.hole "_") (Term.hole "_")])
           ")")
          `hcb])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_left'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `opow_succ)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opow_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `le_trans
        [(Term.app
          `mul_le_mul_right'
          [(Term.app `le_of_lt [(Term.app `lt_mul_succ_div [`a `hbo₀])]) `c])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_trans
       [(Term.app
         `mul_le_mul_right'
         [(Term.app `le_of_lt [(Term.app `lt_mul_succ_div [`a `hbo₀])]) `c])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_le_mul_right'
       [(Term.app `le_of_lt [(Term.app `lt_mul_succ_div [`a `hbo₀])]) `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_of_lt [(Term.app `lt_mul_succ_div [`a `hbo₀])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_mul_succ_div [`a `hbo₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hbo₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_mul_succ_div
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lt_mul_succ_div [`a `hbo₀])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_of_lt [(Term.paren "(" (Term.app `lt_mul_succ_div [`a `hbo₀]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_right'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mul_le_mul_right'
      [(Term.paren
        "("
        (Term.app `le_of_lt [(Term.paren "(" (Term.app `lt_mul_succ_div [`a `hbo₀]) ")")])
        ")")
       `c])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hbo₀ []]
         [(Term.typeSpec
           ":"
           («term_≠_»
            (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" (Term.app `b.log [`a]))
            "≠"
            (num "0")))]
         ":="
         (Term.app
          (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "1"))
          [(Term.app `opow_pos [(Term.hole "_") (Term.app `zero_lt_one.trans [`hb₁])])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "1"))
       [(Term.app `opow_pos [(Term.hole "_") (Term.app `zero_lt_one.trans [`hb₁])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opow_pos [(Term.hole "_") (Term.app `zero_lt_one.trans [`hb₁])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_lt_one.trans [`hb₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_lt_one.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zero_lt_one.trans [`hb₁])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `opow_pos
      [(Term.hole "_") (Term.paren "(" (Term.app `zero_lt_one.trans [`hb₁]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ordinal.pos_iff_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" (Term.app `b.log [`a]))
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `b "^" (Term.app `b.log [`a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
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
theorem
  mul_eq_opow_log_succ
  { a b : Ordinal .{ u } } ( ha : a ≠ 0 ) ( hb : Principal ( · * · ) b ) ( hb₂ : 2 < b )
    : a * b = b ^ succ log b a
  :=
    by
      apply le_antisymm
        ·
          have hbl := principal_mul_is_limit hb₂ hb
            rw
              [
                ← IsNormal.bsup_eq .{ u , u } mul_is_normal Ordinal.pos_iff_ne_zero . 2 ha hbl
                  ,
                  bsup_le_iff
                ]
            intro c hcb
            have hb₁ : 1 < b := lt_succ 1 . trans hb₂
            have
              hbo₀ : b ^ b.log a ≠ 0 := Ordinal.pos_iff_ne_zero . 1 opow_pos _ zero_lt_one.trans hb₁
            apply le_trans mul_le_mul_right' le_of_lt lt_mul_succ_div a hbo₀ c
            rw [ mul_assoc , opow_succ ]
            refine' mul_le_mul_left' le_of_lt hb hbl . 2 _ _ hcb _
            rw [ div_lt hbo₀ , ← opow_succ ]
            exact lt_opow_succ_log_self hb₁ _
        · rw [ opow_succ ] exact mul_le_mul_right' opow_log_le_self b ha b
#align ordinal.mul_eq_opow_log_succ Ordinal.mul_eq_opow_log_succ

/-! #### Exponential principal ordinals -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `principal_opow_omega [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Principal
         [(Term.paren
           "("
           (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow (Term.cdot "·") "^" (Term.cdot "·"))
           ")")
          `omega])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`a `b `ha `hb]
         []
         "=>"
         (Term.match
          "match"
          []
          []
          [(Term.matchDiscr [] `a)
           ","
           (Term.matchDiscr [] `b)
           ","
           (Term.matchDiscr [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`ha]))
           ","
           (Term.matchDiscr [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`hb]))]
          "with"
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[(Term.hole "_")
               ","
               (Term.hole "_")
               ","
               (Term.anonymousCtor "⟨" [`m "," `rfl] "⟩")
               ","
               (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nat_cast_opow)]
                   "]")
                  [])
                 []
                 (Tactic.apply "apply" `nat_lt_omega)]))))]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b `ha `hb]
        []
        "=>"
        (Term.match
         "match"
         []
         []
         [(Term.matchDiscr [] `a)
          ","
          (Term.matchDiscr [] `b)
          ","
          (Term.matchDiscr [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`ha]))
          ","
          (Term.matchDiscr [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`hb]))]
         "with"
         (Term.matchAlts
          [(Term.matchAlt
            "|"
            [[(Term.hole "_")
              ","
              (Term.hole "_")
              ","
              (Term.anonymousCtor "⟨" [`m "," `rfl] "⟩")
              ","
              (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Mathlib.Tactic.tacticSimp_rw__
                 "simp_rw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nat_cast_opow)]
                  "]")
                 [])
                []
                (Tactic.apply "apply" `nat_lt_omega)]))))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `a)
        ","
        (Term.matchDiscr [] `b)
        ","
        (Term.matchDiscr [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`ha]))
        ","
        (Term.matchDiscr [] (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`hb]))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.hole "_")
            ","
            (Term.hole "_")
            ","
            (Term.anonymousCtor "⟨" [`m "," `rfl] "⟩")
            ","
            (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")]]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Mathlib.Tactic.tacticSimp_rw__
               "simp_rw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nat_cast_opow)]
                "]")
               [])
              []
              (Tactic.apply "apply" `nat_lt_omega)]))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nat_cast_opow)]
            "]")
           [])
          []
          (Tactic.apply "apply" `nat_lt_omega)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `nat_lt_omega)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nat_lt_omega
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nat_cast_opow)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nat_cast_opow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`n "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`m "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `lt_omega "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `lt_omega
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `lt_omega "." (fieldIdx "1")) [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `lt_omega "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `lt_omega
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Principal
       [(Term.paren
         "("
         (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow (Term.cdot "·") "^" (Term.cdot "·"))
         ")")
        `omega])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `omega
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.paren
       "("
       (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow (Term.cdot "·") "^" (Term.cdot "·"))
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow (Term.cdot "·") "^" (Term.cdot "·"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  principal_opow_omega
  : Principal ( · ^ · ) omega
  :=
    fun
      a b ha hb
        =>
        match
          a , b , lt_omega . 1 ha , lt_omega . 1 hb
          with
          | _ , _ , ⟨ m , rfl ⟩ , ⟨ n , rfl ⟩ => by simp_rw [ ← nat_cast_opow ] apply nat_lt_omega
#align ordinal.principal_opow_omega Ordinal.principal_opow_omega

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `opow_omega [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `Ordinal] "}")
        (Term.explicitBinder "(" [`a1] [":" («term_<_» (num "1") "<" `a)] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_<_» `a "<" `omega)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_» (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `a "^" `omega) "=" `omega)))
      (Command.declValSimple
       ":="
       (Term.app
        `le_antisymm
        [(Term.app
          (Term.proj
           (Term.app
            `opow_le_of_limit
            [(«term_<|_»
              (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
              "<|"
              (Term.app `le_of_lt [`a1]))
             `omega_is_limit])
           "."
           (fieldIdx "2"))
          [(Term.fun
            "fun"
            (Term.basicFun
             [`b `hb]
             []
             "=>"
             (Term.proj (Term.app `principal_opow_omega [`h `hb]) "." `le)))])
         (Term.app `right_le_opow [(Term.hole "_") `a1])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_antisymm
       [(Term.app
         (Term.proj
          (Term.app
           `opow_le_of_limit
           [(«term_<|_»
             (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
             "<|"
             (Term.app `le_of_lt [`a1]))
            `omega_is_limit])
          "."
          (fieldIdx "2"))
         [(Term.fun
           "fun"
           (Term.basicFun
            [`b `hb]
            []
            "=>"
            (Term.proj (Term.app `principal_opow_omega [`h `hb]) "." `le)))])
        (Term.app `right_le_opow [(Term.hole "_") `a1])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `right_le_opow [(Term.hole "_") `a1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `right_le_opow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `right_le_opow [(Term.hole "_") `a1])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.app
         `opow_le_of_limit
         [(«term_<|_»
           (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
           "<|"
           (Term.app `le_of_lt [`a1]))
          `omega_is_limit])
        "."
        (fieldIdx "2"))
       [(Term.fun
         "fun"
         (Term.basicFun
          [`b `hb]
          []
          "=>"
          (Term.proj (Term.app `principal_opow_omega [`h `hb]) "." `le)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b `hb]
        []
        "=>"
        (Term.proj (Term.app `principal_opow_omega [`h `hb]) "." `le)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `principal_opow_omega [`h `hb]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `principal_opow_omega [`h `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `principal_opow_omega
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `principal_opow_omega [`h `hb])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `opow_le_of_limit
        [(«term_<|_»
          (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
          "<|"
          (Term.app `le_of_lt [`a1]))
         `omega_is_limit])
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `opow_le_of_limit
       [(«term_<|_»
         (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
         "<|"
         (Term.app `le_of_lt [`a1]))
        `omega_is_limit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `omega_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
       "<|"
       (Term.app `le_of_lt [`a1]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_lt [`a1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `one_le_iff_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1")) "<|" (Term.app `le_of_lt [`a1]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opow_le_of_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `opow_le_of_limit
      [(Term.paren
        "("
        («term_<|_»
         (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
         "<|"
         (Term.app `le_of_lt [`a1]))
        ")")
       `omega_is_limit])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren
        "("
        (Term.app
         `opow_le_of_limit
         [(Term.paren
           "("
           («term_<|_»
            (Term.proj `one_le_iff_ne_zero "." (fieldIdx "1"))
            "<|"
            (Term.app `le_of_lt [`a1]))
           ")")
          `omega_is_limit])
        ")")
       "."
       (fieldIdx "2"))
      [(Term.fun
        "fun"
        (Term.basicFun
         [`b `hb]
         []
         "=>"
         (Term.proj (Term.paren "(" (Term.app `principal_opow_omega [`h `hb]) ")") "." `le)))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `a "^" `omega) "=" `omega)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `omega
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Ordinal.SetTheory.Ordinal.Principal.ordinal.pow `a "^" `omega)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow', expected 'Ordinal.SetTheory.Ordinal.Principal.ordinal.pow._@.SetTheory.Ordinal.Principal._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  opow_omega
  { a : Ordinal } ( a1 : 1 < a ) ( h : a < omega ) : a ^ omega = omega
  :=
    le_antisymm
      opow_le_of_limit one_le_iff_ne_zero . 1 <| le_of_lt a1 omega_is_limit . 2
          fun b hb => principal_opow_omega h hb . le
        right_le_opow _ a1
#align ordinal.opow_omega Ordinal.opow_omega

end Ordinal

