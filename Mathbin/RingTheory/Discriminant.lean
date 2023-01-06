/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module ring_theory.discriminant
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Trace
import Mathbin.RingTheory.Norm
import Mathbin.NumberTheory.NumberField.Basic

/-!
# Discriminant of a family of vectors

Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define the
*discriminant* of `b` as the determinant of the matrix whose `(i j)`-th element is the trace of
`b i * b j`.

## Main definition

* `algebra.discr A b` : the discriminant of `b : ι → B`.

## Main results

* `algebra.discr_zero_of_not_linear_independent` : if `b` is not linear independent, then
  `algebra.discr A b = 0`.
* `algebra.discr_of_matrix_vec_mul` and `discr_of_matrix_mul_vec` : formulas relating
  `algebra.discr A ι b` with `algebra.discr A ((P.map (algebra_map A B)).vec_mul b)` and
  `algebra.discr A ((P.map (algebra_map A B)).mul_vec b)`.
* `algebra.discr_not_zero_of_basis` : over a field, if `b` is a basis, then
  `algebra.discr K b ≠ 0`.
* `algebra.discr_eq_det_embeddings_matrix_reindex_pow_two` : if `L/K` is a field extension and
  `b : ι → L`, then `discr K b` is the square of the determinant of the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the embedding in an algebraically closed
  field `E` corresponding to `j : ι` via a bijection `e : ι ≃ (L →ₐ[K] E)`.
* `algebra.discr_of_power_basis_eq_prod` : the discriminant of a power basis.
* `discr_is_integral` : if `K` and `L` are fields and `is_scalar_tower R K L`, is `b : ι → L`
  satisfies ` ∀ i, is_integral R (b i)`, then `is_integral R (discr K b)`.
* `discr_mul_is_integral_mem_adjoin` : let `K` be the fraction field of an integrally closed domain
  `R` and let `L` be a finite separable extension of `K`. Let `B : power_basis K L` be such that
  `is_integral R B.gen`. Then for all, `z : L` we have
  `(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`.

## Implementation details

Our definition works for any `A`-algebra `B`, but note that if `B` is not free as an `A`-module,
then `trace A B = 0` by definition, so `discr A b = 0` for any `b`.
-/


universe u v w z

open Matrix BigOperators

open Matrix FiniteDimensional Fintype Polynomial Finset IntermediateField

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z) {ι : Type w}

variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

section Discr

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discr A ι b` as the determinant of `trace_matrix A ι b`. -/
noncomputable def discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] (b : ι → B) := by classical exact (trace_matrix A b).det
#align algebra.discr Algebra.discr

theorem discr_def [DecidableEq ι] [Fintype ι] (b : ι → B) : discr A b = (traceMatrix A b).det := by
  convert rfl
#align algebra.discr_def Algebra.discr_def

variable {ι' : Type _} [Fintype ι'] [Fintype ι]

section Basic

@[simp]
theorem discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : discr A (b ∘ ⇑f.symm) = discr A b := by
  classical rw [← Basis.coe_reindex, discr_def, trace_matrix_reindex, det_reindex_self, ← discr_def]
#align algebra.discr_reindex Algebra.discr_reindex

/-- If `b` is not linear independent, then `algebra.discr A b = 0`. -/
theorem discr_zero_of_not_linear_independent [IsDomain A] {b : ι → B}
    (hli : ¬LinearIndependent A b) : discr A b = 0 := by
  classical
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linear_independent_iff.1 hli
    have : (trace_matrix A b).mulVec g = 0 := by
      ext i
      have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) :=
        by
        intro j
        simp [mul_comm]
      simp only [mul_vec, dot_product, trace_matrix, Pi.zero_apply, trace_form_apply, fun j =>
        this j, ← LinearMap.map_sum, ← sum_mul, hg, zero_mul, LinearMap.map_zero]
    by_contra h
    rw [discr_def] at h
    simpa [Matrix.eq_zero_of_mul_vec_eq_zero h this] using hi
#align algebra.discr_zero_of_not_linear_independent Algebra.discr_zero_of_not_linear_independent

variable {A}

/-- Relation between `algebra.discr A ι b` and
`algebra.discr A ((P.map (algebra_map A B)).vec_mul b)`. -/
theorem discr_of_matrix_vec_mul [DecidableEq ι] (b : ι → B) (P : Matrix ι ι A) :
    discr A ((P.map (algebraMap A B)).vecMul b) = P.det ^ 2 * discr A b := by
  rw [discr_def, trace_matrix_of_matrix_vec_mul, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]
#align algebra.discr_of_matrix_vec_mul Algebra.discr_of_matrix_vec_mul

/-- Relation between `algebra.discr A ι b` and
`algebra.discr A ((P.map (algebra_map A B)).mul_vec b)`. -/
theorem discr_of_matrix_mul_vec [DecidableEq ι] (b : ι → B) (P : Matrix ι ι A) :
    discr A ((P.map (algebraMap A B)).mulVec b) = P.det ^ 2 * discr A b := by
  rw [discr_def, trace_matrix_of_matrix_mul_vec, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]
#align algebra.discr_of_matrix_mul_vec Algebra.discr_of_matrix_mul_vec

end Basic

section Field

variable (K : Type u) {L : Type v} (E : Type z) [Field K] [Field L] [Field E]

variable [Algebra K L] [Algebra K E]

variable [Module.Finite K L] [IsAlgClosed E]

/-- Over a field, if `b` is a basis, then `algebra.discr K b ≠ 0`. -/
theorem discr_not_zero_of_basis [IsSeparable K L] (b : Basis ι K L) : discr K b ≠ 0 :=
  by
  cases isEmpty_or_nonempty ι
  · simp [discr]
  · have :=
      span_eq_top_of_linear_independent_of_card_eq_finrank b.linear_independent
        (finrank_eq_card_basis b).symm
    rw [discr_def, trace_matrix_def]
    simp_rw [← Basis.mk_apply b.linear_independent this.ge]
    rw [← trace_matrix_def, trace_matrix_of_basis, ← BilinForm.nondegenerate_iff_det_ne_zero]
    exact traceFormNondegenerate _ _
#align algebra.discr_not_zero_of_basis Algebra.discr_not_zero_of_basis

/-- Over a field, if `b` is a basis, then `algebra.discr K b` is a unit. -/
theorem discr_is_unit_of_basis [IsSeparable K L] (b : Basis ι K L) : IsUnit (discr K b) :=
  IsUnit.mk0 _ (discr_not_zero_of_basis _ _)
#align algebra.discr_is_unit_of_basis Algebra.discr_is_unit_of_basis

variable (b : ι → L) (pb : PowerBasis K L)

/-- If `L/K` is a field extension and `b : ι → L`, then `discr K b` is the square of the
determinant of the matrix whose `(i, j)` coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the
embedding in an algebraically closed field `E` corresponding to `j : ι` via a bijection
`e : ι ≃ (L →ₐ[K] E)`. -/
theorem discr_eq_det_embeddings_matrix_reindex_pow_two [DecidableEq ι] [IsSeparable K L]
    (e : ι ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K b) = (embeddingsMatrixReindex K E b e).det ^ 2 := by
  rw [discr_def, RingHom.map_det, RingHom.map_matrix_apply,
    trace_matrix_eq_embeddings_matrix_reindex_mul_trans, det_mul, det_transpose, pow_two]
#align
  algebra.discr_eq_det_embeddings_matrix_reindex_pow_two Algebra.discr_eq_det_embeddings_matrix_reindex_pow_two

/-- The discriminant of a power basis. -/
theorem discr_power_basis_eq_prod (e : Fin pb.dim ≃ (L →ₐ[K] E)) [IsSeparable K L] :
    algebraMap K E (discr K pb.Basis) =
      ∏ i : Fin pb.dim, ∏ j in ioi i, (e j pb.gen - e i pb.gen) ^ 2 :=
  by
  rw [discr_eq_det_embeddings_matrix_reindex_pow_two K E pb.basis e,
    embeddings_matrix_reindex_eq_vandermonde, det_transpose, det_vandermonde, ← prod_pow]
  congr ; ext i
  rw [← prod_pow]
#align algebra.discr_power_basis_eq_prod Algebra.discr_power_basis_eq_prod

/-- A variation of `of_power_basis_eq_prod`. -/
theorem discr_power_basis_eq_prod' [IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.Basis) =
      ∏ i : Fin pb.dim, ∏ j in ioi i, -((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)) :=
  by
  rw [discr_power_basis_eq_prod _ _ _ e]
  congr ; ext i; congr ; ext j
  ring
#align algebra.discr_power_basis_eq_prod' Algebra.discr_power_basis_eq_prod'

-- mathport name: exprn
local notation "n" => finrank K L

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "A variation of `of_power_basis_eq_prod`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `discr_power_basis_eq_prod'' [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsSeparable [`K `L]) "]")
        (Term.explicitBinder
         "("
         [`e]
         [":"
          (Logic.Equiv.Defs.«term_≃_»
           (Term.app `Fin [(Term.proj `pb "." `dim)])
           " ≃ "
           (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `algebraMap [`K `E (Term.app `discr [`K (Term.proj `pb "." `Basis)])])
         "="
         («term_*_»
          («term_^_»
           («term-_» "-" (num "1"))
           "^"
           («term_/_»
            («term_*_»
             (Algebra.RingTheory.Discriminant.termn "n")
             "*"
             («term_-_» (Algebra.RingTheory.Discriminant.termn "n") "-" (num "1")))
            "/"
            (num "2")))
          "*"
          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
           "∏"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `i)
             [(group ":" (Term.app `Fin [(Term.proj `pb "." `dim)]))]))
           ", "
           (BigOperators.Algebra.BigOperators.Basic.finset.prod
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
            " in "
            (Term.app `ioi [`i])
            ", "
            («term_*_»
             («term_-_»
              (Term.app `e [`j (Term.proj `pb "." `gen)])
              "-"
              (Term.app `e [`i (Term.proj `pb "." `gen)]))
             "*"
             («term_-_»
              (Term.app `e [`i (Term.proj `pb "." `gen)])
              "-"
              (Term.app `e [`j (Term.proj `pb "." `gen)])))))))))
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
               []
               (Term.app
                `discr_power_basis_eq_prod'
                [(Term.hole "_") (Term.hole "_") (Term.hole "_") `e]))]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.fun
                "fun"
                (Term.basicFun
                 [`i `j]
                 []
                 "=>"
                 (Term.app
                  `neg_eq_neg_one_mul
                  [(«term_*_»
                    («term_-_» (Term.app `e [`j `pb.gen]) "-" (Term.app `e [`i `pb.gen]))
                    "*"
                    («term_-_» (Term.app `e [`i `pb.gen]) "-" (Term.app `e [`j `pb.gen])))]))))
              ","
              (Tactic.rwRule [] `prod_mul_distrib)]
             "]")
            [])
           []
           (Tactic.congr "congr" [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `prod_pow_eq_pow_sum)
              ","
              (Tactic.simpLemma [] [] `prod_const)]
             "]"]
            [])
           []
           (Tactic.congr "congr" [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app (Term.explicit "@" `Nat.cast_inj) [(Data.Rat.Init.termℚ "ℚ")]))
              ","
              (Tactic.rwRule [] `Nat.cast_sum)]
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
                (Term.forall
                 "∀"
                 [`x]
                 [(Term.typeSpec ":" (Term.app `Fin [`pb.dim]))]
                 ","
                 («term_≤_» («term_+_» (coeNotation "↑" `x) "+" (num "1")) "≤" `pb.dim)))]
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
                    [(Tactic.simpLemma [] [] `Nat.succ_le_iff)
                     ","
                     (Tactic.simpLemma [] [] `Fin.is_lt)]
                    "]"]
                   [])]))))))
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Fin.card_Ioi)
              ","
              (Tactic.rwRule [] `Nat.sub_sub)
              ","
              (Tactic.rwRule [] (Term.app `add_comm [(num "1")]))]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Nat.cast_sub)
              ","
              (Tactic.simpLemma [] [] `this)
              ","
              (Tactic.simpLemma [] [] `Finset.card_fin)
              ","
              (Tactic.simpLemma [] [] `nsmul_eq_mul)
              ","
              (Tactic.simpLemma [] [] `sum_const)
              ","
              (Tactic.simpLemma [] [] `sum_sub_distrib)
              ","
              (Tactic.simpLemma [] [] `Nat.cast_add)
              ","
              (Tactic.simpLemma [] [] `Nat.cast_one)
              ","
              (Tactic.simpLemma [] [] `sum_add_distrib)
              ","
              (Tactic.simpLemma [] [] `mul_one)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.cast_sum)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `Finset.sum_range)
                [(termℕ "ℕ")
                 (Term.hole "_")
                 `pb.dim
                 (Term.fun "fun" (Term.basicFun [`i] [] "=>" `i))]))
              ","
              (Tactic.rwRule [] `sum_range_id)]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hn []]
              [(Term.typeSpec
                ":"
                («term_=_» (Algebra.RingTheory.Discriminant.termn "n") "=" `pb.dim))]
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
                      (Term.app `AlgHom.card [`K `L `E]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `Fintype.card_fin [`pb.dim]))]
                    "]")
                   [])
                  []
                  (Tactic.exact "exact" (Term.app `card_congr [(Term.app `Equiv.symm [`e])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₂ []]
              [(Term.typeSpec
                ":"
                («term_∣_»
                 (num "2")
                 "∣"
                 («term_*_» `pb.dim "*" («term_-_» `pb.dim "-" (num "1")))))]
              ":="
              (Term.app
               (Term.proj `even_iff_two_dvd "." (fieldIdx "1"))
               [(Term.app `Nat.even_mul_self_pred [(Term.hole "_")])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hne []]
              [(Term.typeSpec
                ":"
                («term_≠_»
                 (Term.typeAscription
                  "("
                  (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
                  ":"
                  [(Data.Rat.Init.termℚ "ℚ")]
                  ")")
                 "≠"
                 (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hle []]
              [(Term.typeSpec ":" («term_≤_» (num "1") "≤" `pb.dim))]
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hn)
                     ","
                     (Tactic.rwRule [] `Nat.one_le_iff_ne_zero)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zero_lt_iff)
                     ","
                     (Tactic.rwRule [] `FiniteDimensional.finrank_pos_iff)]
                    "]")
                   [])
                  []
                  (Tactic.tacticInfer_instance "infer_instance")]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `hn)
              ","
              (Tactic.rwRule [] (Term.app `Nat.cast_div [`h₂ `hne]))
              ","
              (Tactic.rwRule [] `Nat.cast_mul)
              ","
              (Tactic.rwRule [] (Term.app `Nat.cast_sub [`hle]))]
             "]")
            [])
           []
           (Tactic.fieldSimp "field_simp" [] [] [] [] [])
           []
           (Mathlib.Tactic.RingNF.ring "ring")])))
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
              []
              (Term.app
               `discr_power_basis_eq_prod'
               [(Term.hole "_") (Term.hole "_") (Term.hole "_") `e]))]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.fun
               "fun"
               (Term.basicFun
                [`i `j]
                []
                "=>"
                (Term.app
                 `neg_eq_neg_one_mul
                 [(«term_*_»
                   («term_-_» (Term.app `e [`j `pb.gen]) "-" (Term.app `e [`i `pb.gen]))
                   "*"
                   («term_-_» (Term.app `e [`i `pb.gen]) "-" (Term.app `e [`j `pb.gen])))]))))
             ","
             (Tactic.rwRule [] `prod_mul_distrib)]
            "]")
           [])
          []
          (Tactic.congr "congr" [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `prod_pow_eq_pow_sum) "," (Tactic.simpLemma [] [] `prod_const)]
            "]"]
           [])
          []
          (Tactic.congr "congr" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app (Term.explicit "@" `Nat.cast_inj) [(Data.Rat.Init.termℚ "ℚ")]))
             ","
             (Tactic.rwRule [] `Nat.cast_sum)]
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
               (Term.forall
                "∀"
                [`x]
                [(Term.typeSpec ":" (Term.app `Fin [`pb.dim]))]
                ","
                («term_≤_» («term_+_» (coeNotation "↑" `x) "+" (num "1")) "≤" `pb.dim)))]
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
                   [(Tactic.simpLemma [] [] `Nat.succ_le_iff)
                    ","
                    (Tactic.simpLemma [] [] `Fin.is_lt)]
                   "]"]
                  [])]))))))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Fin.card_Ioi)
             ","
             (Tactic.rwRule [] `Nat.sub_sub)
             ","
             (Tactic.rwRule [] (Term.app `add_comm [(num "1")]))]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Nat.cast_sub)
             ","
             (Tactic.simpLemma [] [] `this)
             ","
             (Tactic.simpLemma [] [] `Finset.card_fin)
             ","
             (Tactic.simpLemma [] [] `nsmul_eq_mul)
             ","
             (Tactic.simpLemma [] [] `sum_const)
             ","
             (Tactic.simpLemma [] [] `sum_sub_distrib)
             ","
             (Tactic.simpLemma [] [] `Nat.cast_add)
             ","
             (Tactic.simpLemma [] [] `Nat.cast_one)
             ","
             (Tactic.simpLemma [] [] `sum_add_distrib)
             ","
             (Tactic.simpLemma [] [] `mul_one)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.cast_sum)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               (Term.explicit "@" `Finset.sum_range)
               [(termℕ "ℕ")
                (Term.hole "_")
                `pb.dim
                (Term.fun "fun" (Term.basicFun [`i] [] "=>" `i))]))
             ","
             (Tactic.rwRule [] `sum_range_id)]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hn []]
             [(Term.typeSpec
               ":"
               («term_=_» (Algebra.RingTheory.Discriminant.termn "n") "=" `pb.dim))]
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
                     (Term.app `AlgHom.card [`K `L `E]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `Fintype.card_fin [`pb.dim]))]
                   "]")
                  [])
                 []
                 (Tactic.exact "exact" (Term.app `card_congr [(Term.app `Equiv.symm [`e])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             [(Term.typeSpec
               ":"
               («term_∣_» (num "2") "∣" («term_*_» `pb.dim "*" («term_-_» `pb.dim "-" (num "1")))))]
             ":="
             (Term.app
              (Term.proj `even_iff_two_dvd "." (fieldIdx "1"))
              [(Term.app `Nat.even_mul_self_pred [(Term.hole "_")])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hne []]
             [(Term.typeSpec
               ":"
               («term_≠_»
                (Term.typeAscription
                 "("
                 (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
                 ":"
                 [(Data.Rat.Init.termℚ "ℚ")]
                 ")")
                "≠"
                (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hle []]
             [(Term.typeSpec ":" («term_≤_» (num "1") "≤" `pb.dim))]
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hn)
                    ","
                    (Tactic.rwRule [] `Nat.one_le_iff_ne_zero)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zero_lt_iff)
                    ","
                    (Tactic.rwRule [] `FiniteDimensional.finrank_pos_iff)]
                   "]")
                  [])
                 []
                 (Tactic.tacticInfer_instance "infer_instance")]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `hn)
             ","
             (Tactic.rwRule [] (Term.app `Nat.cast_div [`h₂ `hne]))
             ","
             (Tactic.rwRule [] `Nat.cast_mul)
             ","
             (Tactic.rwRule [] (Term.app `Nat.cast_sub [`hle]))]
            "]")
           [])
          []
          (Tactic.fieldSimp "field_simp" [] [] [] [] [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp "field_simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `hn)
         ","
         (Tactic.rwRule [] (Term.app `Nat.cast_div [`h₂ `hne]))
         ","
         (Tactic.rwRule [] `Nat.cast_mul)
         ","
         (Tactic.rwRule [] (Term.app `Nat.cast_sub [`hle]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.cast_sub [`hle])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hle
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.cast_sub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.cast_div [`h₂ `hne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.cast_div
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hle []]
         [(Term.typeSpec ":" («term_≤_» (num "1") "≤" `pb.dim))]
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hn)
                ","
                (Tactic.rwRule [] `Nat.one_le_iff_ne_zero)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zero_lt_iff)
                ","
                (Tactic.rwRule [] `FiniteDimensional.finrank_pos_iff)]
               "]")
              [])
             []
             (Tactic.tacticInfer_instance "infer_instance")]))))))
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hn)
             ","
             (Tactic.rwRule [] `Nat.one_le_iff_ne_zero)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zero_lt_iff)
             ","
             (Tactic.rwRule [] `FiniteDimensional.finrank_pos_iff)]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hn)
         ","
         (Tactic.rwRule [] `Nat.one_le_iff_ne_zero)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `zero_lt_iff)
         ","
         (Tactic.rwRule [] `FiniteDimensional.finrank_pos_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `FiniteDimensional.finrank_pos_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_lt_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.one_le_iff_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (num "1") "≤" `pb.dim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.dim
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hne []]
         [(Term.typeSpec
           ":"
           («term_≠_»
            (Term.typeAscription
             "("
             (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
             ":"
             [(Data.Rat.Init.termℚ "ℚ")]
             ")")
            "≠"
            (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       (Term.typeAscription
        "("
        (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
        ":"
        [(Data.Rat.Init.termℚ "ℚ")]
        ")")
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
       ":"
       [(Data.Rat.Init.termℚ "ℚ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "2") ":" [(termℕ "ℕ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₂ []]
         [(Term.typeSpec
           ":"
           («term_∣_» (num "2") "∣" («term_*_» `pb.dim "*" («term_-_» `pb.dim "-" (num "1")))))]
         ":="
         (Term.app
          (Term.proj `even_iff_two_dvd "." (fieldIdx "1"))
          [(Term.app `Nat.even_mul_self_pred [(Term.hole "_")])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `even_iff_two_dvd "." (fieldIdx "1"))
       [(Term.app `Nat.even_mul_self_pred [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.even_mul_self_pred [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.even_mul_self_pred
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Nat.even_mul_self_pred [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `even_iff_two_dvd "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `even_iff_two_dvd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∣_» (num "2") "∣" («term_*_» `pb.dim "*" («term_-_» `pb.dim "-" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `pb.dim "*" («term_-_» `pb.dim "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `pb.dim "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `pb.dim
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `pb.dim "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `pb.dim
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hn []]
         [(Term.typeSpec ":" («term_=_» (Algebra.RingTheory.Discriminant.termn "n") "=" `pb.dim))]
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
                 (Term.app `AlgHom.card [`K `L `E]))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `Fintype.card_fin [`pb.dim]))]
               "]")
              [])
             []
             (Tactic.exact "exact" (Term.app `card_congr [(Term.app `Equiv.symm [`e])]))]))))))
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `AlgHom.card [`K `L `E]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `Fintype.card_fin [`pb.dim]))]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `card_congr [(Term.app `Equiv.symm [`e])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `card_congr [(Term.app `Equiv.symm [`e])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `card_congr [(Term.app `Equiv.symm [`e])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.symm [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Equiv.symm [`e]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `card_congr
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `AlgHom.card [`K `L `E]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Fintype.card_fin [`pb.dim]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fintype.card_fin [`pb.dim])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.dim
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card_fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `AlgHom.card [`K `L `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AlgHom.card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Algebra.RingTheory.Discriminant.termn "n") "=" `pb.dim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.dim
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.RingTheory.Discriminant.termn "n")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.RingTheory.Discriminant.termn', expected 'Algebra.RingTheory.Discriminant.termn._@.RingTheory.Discriminant._hyg.11'
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
/-- A variation of `of_power_basis_eq_prod`. -/
  theorem
    discr_power_basis_eq_prod''
    [ IsSeparable K L ] ( e : Fin pb . dim ≃ L →ₐ[ K ] E )
      :
        algebraMap K E discr K pb . Basis
          =
          - 1 ^ n * n - 1 / 2
            *
            ∏
              i : Fin pb . dim
              ,
              ∏ j in ioi i , e j pb . gen - e i pb . gen * e i pb . gen - e j pb . gen
    :=
      by
        rw [ discr_power_basis_eq_prod' _ _ _ e ]
          simp_rw
            [
              fun i j => neg_eq_neg_one_mul e j pb.gen - e i pb.gen * e i pb.gen - e j pb.gen
                ,
                prod_mul_distrib
              ]
          congr
          simp only [ prod_pow_eq_pow_sum , prod_const ]
          congr
          rw [ ← @ Nat.cast_inj ℚ , Nat.cast_sum ]
          have : ∀ x : Fin pb.dim , ↑ x + 1 ≤ pb.dim := by simp [ Nat.succ_le_iff , Fin.is_lt ]
          simp_rw [ Fin.card_Ioi , Nat.sub_sub , add_comm 1 ]
          simp
            only
            [
              Nat.cast_sub
                ,
                this
                ,
                Finset.card_fin
                ,
                nsmul_eq_mul
                ,
                sum_const
                ,
                sum_sub_distrib
                ,
                Nat.cast_add
                ,
                Nat.cast_one
                ,
                sum_add_distrib
                ,
                mul_one
              ]
          rw [ ← Nat.cast_sum , ← @ Finset.sum_range ℕ _ pb.dim fun i => i , sum_range_id ]
          have
            hn
              : n = pb.dim
              :=
              by
                rw [ ← AlgHom.card K L E , ← Fintype.card_fin pb.dim ] exact card_congr Equiv.symm e
          have h₂ : 2 ∣ pb.dim * pb.dim - 1 := even_iff_two_dvd . 1 Nat.even_mul_self_pred _
          have hne : ( ( 2 : ℕ ) : ℚ ) ≠ 0 := by simp
          have
            hle
              : 1 ≤ pb.dim
              :=
              by
                rw
                    [
                      ← hn
                        ,
                        Nat.one_le_iff_ne_zero
                        ,
                        ← zero_lt_iff
                        ,
                        FiniteDimensional.finrank_pos_iff
                      ]
                  infer_instance
          rw [ hn , Nat.cast_div h₂ hne , Nat.cast_mul , Nat.cast_sub hle ]
          field_simp
          ring
#align algebra.discr_power_basis_eq_prod'' Algebra.discr_power_basis_eq_prod''

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Formula for the discriminant of a power basis using the norm of the field extension. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `discr_power_basis_eq_norm [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsSeparable [`K `L]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `discr [`K (Term.proj `pb "." `Basis)])
         "="
         («term_*_»
          («term_^_»
           («term-_» "-" (num "1"))
           "^"
           («term_/_»
            («term_*_»
             (Algebra.RingTheory.Discriminant.termn "n")
             "*"
             («term_-_» (Algebra.RingTheory.Discriminant.termn "n") "-" (num "1")))
            "/"
            (num "2")))
          "*"
          (Term.app
           `norm
           [`K
            (Term.app
             `aeval
             [(Term.proj `pb "." `gen)
              (Term.proj (Term.app `minpoly [`K (Term.proj `pb "." `gen)]) "." `derivative)])])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `E [] [] ":=" (Term.app `AlgebraicClosure [`L]))))
           []
           (Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`a `b]
                [(Term.typeSpec ":" `E)]
                "=>"
                (Term.app `Classical.propDecidable [(Term.app `Eq [`a `b])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`e []]
              [(Term.typeSpec
                ":"
                (Logic.Equiv.Defs.«term_≃_»
                 (Term.app `Fin [`pb.dim])
                 " ≃ "
                 (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E)))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine' "refine'" (Term.app `equiv_of_card_eq [(Term.hole "_")]))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Fintype.card_fin) "," (Tactic.rwRule [] `AlgHom.card)]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.proj (Term.app `PowerBasis.finrank [`pb]) "." `symm))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hnodup []]
              [(Term.typeSpec
                ":"
                (Term.proj
                 (Term.proj
                  (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
                  "."
                  `roots)
                 "."
                 `Nodup))]
              ":="
              (Term.app
               `nodup_roots
               [(Term.app `separable.map [(Term.app `IsSeparable.separable [`K `pb.gen])])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hroots []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`σ]
                 [(Term.typeSpec ":" (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E))]
                 ","
                 («term_∈_»
                  (Term.app `σ [`pb.gen])
                  "∈"
                  (Term.proj
                   (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
                   "."
                   `roots))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`σ])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `mem_roots)
                     ","
                     (Tactic.rwRule [] `is_root.def)
                     ","
                     (Tactic.rwRule [] `eval_map)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)
                     ","
                     (Tactic.rwRule [] `aeval_alg_hom_apply)]
                    "]")
                   [])
                  []
                  (Std.Tactic.tacticRepeat'_
                   "repeat'"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["["
                        [(Tactic.simpLemma
                          []
                          []
                          (Term.app
                           `minpoly.ne_zero
                           [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
                        "]"]
                       [])])))]))))))
           []
           (Tactic.apply "apply" (Term.proj (Term.app `algebraMap [`K `E]) "." `Injective))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `RingHom.map_mul)
              ","
              (Tactic.rwRule [] `RingHom.map_pow)
              ","
              (Tactic.rwRule [] `RingHom.map_neg)
              ","
              (Tactic.rwRule [] `RingHom.map_one)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `discr_power_basis_eq_prod''
                [(Term.hole "_") (Term.hole "_") (Term.hole "_") `e]))]
             "]")
            [])
           []
           (Tactic.congr "congr" [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `norm_eq_prod_embeddings)
              ","
              (Tactic.rwRule [] `prod_prod_Ioi_mul_eq_prod_prod_off_diag)]
             "]")
            [])
           []
           (Mathlib.Tactic.Conv.convRHS
            "conv_rhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(Tactic.Conv.congr "congr")
               []
               (Tactic.Conv.skip "skip")
               []
               (Tactic.Conv.ext "ext" [])
               []
               (Tactic.Conv.convRw__
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_alg_hom_apply)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `aeval_root_derivative_of_splits
                    [(Term.app `minpoly.monic [(Term.app `IsSeparable.is_integral [`K `pb.gen])])
                     (Term.app `IsAlgClosed.splits_codomain [(Term.hole "_")])
                     (Term.app `hroots [`σ])]))
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    `Finset.prod_mk
                    [(Term.hole "_") (Term.app `hnodup.erase [(Term.hole "_")])]))]
                 "]"))])))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `prod_sigma') "," (Tactic.rwRule [] `prod_sigma')]
             "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `prod_bij
             [(Term.fun
               "fun"
               (Term.basicFun
                [`i `hi]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `e [(Term.proj `i "." (fieldIdx "2"))])
                  ","
                  (Term.app `e [(Term.proj `i "." (fieldIdx "1")) `pb.gen])]
                 "⟩")))
              (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))
              (Term.fun
               "fun"
               (Term.basicFun
                [`i `hi]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     []
                     []
                     [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])])))))
              (Term.fun "fun" (Term.basicFun [`i `j `hi `hj `hij] [] "=>" (Term.hole "_")))
              (Term.fun "fun" (Term.basicFun [`σ `hσ] [] "=>" (Term.hole "_")))]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `true_and_iff)
                ","
                (Tactic.simpLemma [] [] `Finset.mem_mk)
                ","
                (Tactic.simpLemma [] [] `mem_univ)
                ","
                (Tactic.simpLemma [] [] `mem_sigma)]
               "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  `Multiset.mem_erase_of_ne
                  [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]))]
               "]")
              [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `hroots [(Term.hole "_")]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `true_and_iff)
                  ","
                  (Tactic.simpLemma [] [] `mem_univ)
                  ","
                  (Tactic.simpLemma [] [] `Ne.def)
                  ","
                  (Tactic.simpLemma [] [] `mem_sigma)
                  ","
                  (Tactic.simpLemma [] [] `mem_compl)
                  ","
                  (Tactic.simpLemma [] [] `mem_singleton)]
                 "]"]
                [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `PowerBasis.lift_equiv_apply_coe)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `PowerBasis.lift_equiv_apply_coe)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `hi
                 [(«term_<|_»
                   `e.injective
                   "<|"
                   («term_<|_»
                    `pb.lift_equiv.injective
                    "<|"
                    (Term.app `Subtype.eq [`h.symm])))]))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Equiv.apply_eq_iff_eq)
                ","
                (Tactic.simpLemma [] [] `heq_iff_eq)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`hij] []))])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.proj `hij "." (fieldIdx "2")))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `Sigma.eq
               [(Term.app
                 `Equiv.injective
                 [`e (Term.app `Equiv.injective [(Term.hole "_") (Term.app `Subtype.eq [`h])])])
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["[" [(Tactic.simpLemma [] [] (Term.proj `hij "." (fieldIdx "1")))] "]"]
                     [])])))]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `true_and_iff)
                ","
                (Tactic.simpLemma [] [] `Finset.mem_mk)
                ","
                (Tactic.simpLemma [] [] `mem_univ)
                ","
                (Tactic.simpLemma [] [] `mem_sigma)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`hσ] [(patternIgnore (token.«⊢» "⊢"))]))])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Sigma.exists)
                ","
                (Tactic.simpLemma [] [] `exists_prop)
                ","
                (Tactic.simpLemma [] [] `mem_compl)
                ","
                (Tactic.simpLemma [] [] `mem_singleton)
                ","
                (Tactic.simpLemma [] [] `Ne.def)]
               "]"]
              [])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.app
                 `e.symm
                 [(Term.app
                   `PowerBasis.lift
                   [`pb (Term.proj `σ "." (fieldIdx "2")) (Term.hole "_")])])
                ","
                (Term.app `e.symm [(Term.proj `σ "." (fieldIdx "1"))])
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
                  ","
                  (Term.app `Sigma.eq [(Term.hole "_") (Term.hole "_")])]
                 "⟩")]
               "⟩"))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `aeval_def)
                  ","
                  (Tactic.rwRule [] `eval₂_eq_eval_map)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_roots)]
                 "]")
                [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact
                  "exact"
                  (Term.app `Multiset.erase_subset [(Term.hole "_") (Term.hole "_") `hσ]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.app
                      `minpoly.ne_zero
                      [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
                   "]"]
                  [])])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Mathlib.Tactic.tacticReplace_
                "replace"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h []]
                  []
                  ":="
                  (Term.app
                   `AlgHom.congr_fun
                   [(Term.app `Equiv.injective [(Term.hole "_") `h]) `pb.gen]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `PowerBasis.lift_gen)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hσ] []))])
               []
               (Tactic.exact "exact" (Term.app `hnodup.not_mem_erase [`hσ]))])
             []
             (Tactic.allGoals
              "all_goals"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])])))
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
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `E [] [] ":=" (Term.app `AlgebraicClosure [`L]))))
          []
          (Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`a `b]
               [(Term.typeSpec ":" `E)]
               "=>"
               (Term.app `Classical.propDecidable [(Term.app `Eq [`a `b])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`e []]
             [(Term.typeSpec
               ":"
               (Logic.Equiv.Defs.«term_≃_»
                (Term.app `Fin [`pb.dim])
                " ≃ "
                (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine' "refine'" (Term.app `equiv_of_card_eq [(Term.hole "_")]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Fintype.card_fin) "," (Tactic.rwRule [] `AlgHom.card)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.proj (Term.app `PowerBasis.finrank [`pb]) "." `symm))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hnodup []]
             [(Term.typeSpec
               ":"
               (Term.proj
                (Term.proj
                 (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
                 "."
                 `roots)
                "."
                `Nodup))]
             ":="
             (Term.app
              `nodup_roots
              [(Term.app `separable.map [(Term.app `IsSeparable.separable [`K `pb.gen])])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hroots []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`σ]
                [(Term.typeSpec ":" (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E))]
                ","
                («term_∈_»
                 (Term.app `σ [`pb.gen])
                 "∈"
                 (Term.proj
                  (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
                  "."
                  `roots))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`σ])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `mem_roots)
                    ","
                    (Tactic.rwRule [] `is_root.def)
                    ","
                    (Tactic.rwRule [] `eval_map)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)
                    ","
                    (Tactic.rwRule [] `aeval_alg_hom_apply)]
                   "]")
                  [])
                 []
                 (Std.Tactic.tacticRepeat'_
                  "repeat'"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["["
                       [(Tactic.simpLemma
                         []
                         []
                         (Term.app
                          `minpoly.ne_zero
                          [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
                       "]"]
                      [])])))]))))))
          []
          (Tactic.apply "apply" (Term.proj (Term.app `algebraMap [`K `E]) "." `Injective))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `RingHom.map_mul)
             ","
             (Tactic.rwRule [] `RingHom.map_pow)
             ","
             (Tactic.rwRule [] `RingHom.map_neg)
             ","
             (Tactic.rwRule [] `RingHom.map_one)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `discr_power_basis_eq_prod''
               [(Term.hole "_") (Term.hole "_") (Term.hole "_") `e]))]
            "]")
           [])
          []
          (Tactic.congr "congr" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `norm_eq_prod_embeddings)
             ","
             (Tactic.rwRule [] `prod_prod_Ioi_mul_eq_prod_prod_off_diag)]
            "]")
           [])
          []
          (Mathlib.Tactic.Conv.convRHS
           "conv_rhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.congr "congr")
              []
              (Tactic.Conv.skip "skip")
              []
              (Tactic.Conv.ext "ext" [])
              []
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_alg_hom_apply)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app
                   `aeval_root_derivative_of_splits
                   [(Term.app `minpoly.monic [(Term.app `IsSeparable.is_integral [`K `pb.gen])])
                    (Term.app `IsAlgClosed.splits_codomain [(Term.hole "_")])
                    (Term.app `hroots [`σ])]))
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app
                   `Finset.prod_mk
                   [(Term.hole "_") (Term.app `hnodup.erase [(Term.hole "_")])]))]
                "]"))])))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `prod_sigma') "," (Tactic.rwRule [] `prod_sigma')]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `prod_bij
            [(Term.fun
              "fun"
              (Term.basicFun
               [`i `hi]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `e [(Term.proj `i "." (fieldIdx "2"))])
                 ","
                 (Term.app `e [(Term.proj `i "." (fieldIdx "1")) `pb.gen])]
                "⟩")))
             (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))
             (Term.fun
              "fun"
              (Term.basicFun
               [`i `hi]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    []
                    [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])])))))
             (Term.fun "fun" (Term.basicFun [`i `j `hi `hj `hij] [] "=>" (Term.hole "_")))
             (Term.fun "fun" (Term.basicFun [`σ `hσ] [] "=>" (Term.hole "_")))]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `true_and_iff)
               ","
               (Tactic.simpLemma [] [] `Finset.mem_mk)
               ","
               (Tactic.simpLemma [] [] `mem_univ)
               ","
               (Tactic.simpLemma [] [] `mem_sigma)]
              "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `Multiset.mem_erase_of_ne
                 [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]))]
              "]")
             [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `hroots [(Term.hole "_")]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `true_and_iff)
                 ","
                 (Tactic.simpLemma [] [] `mem_univ)
                 ","
                 (Tactic.simpLemma [] [] `Ne.def)
                 ","
                 (Tactic.simpLemma [] [] `mem_sigma)
                 ","
                 (Tactic.simpLemma [] [] `mem_compl)
                 ","
                 (Tactic.simpLemma [] [] `mem_singleton)]
                "]"]
               [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  `PowerBasis.lift_equiv_apply_coe)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `hi
                [(«term_<|_»
                  `e.injective
                  "<|"
                  («term_<|_»
                   `pb.lift_equiv.injective
                   "<|"
                   (Term.app `Subtype.eq [`h.symm])))]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Equiv.apply_eq_iff_eq)
               ","
               (Tactic.simpLemma [] [] `heq_iff_eq)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`hij] []))])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.proj `hij "." (fieldIdx "2")))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `Sigma.eq
              [(Term.app
                `Equiv.injective
                [`e (Term.app `Equiv.injective [(Term.hole "_") (Term.app `Subtype.eq [`h])])])
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpLemma [] [] (Term.proj `hij "." (fieldIdx "1")))] "]"]
                    [])])))]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `true_and_iff)
               ","
               (Tactic.simpLemma [] [] `Finset.mem_mk)
               ","
               (Tactic.simpLemma [] [] `mem_univ)
               ","
               (Tactic.simpLemma [] [] `mem_sigma)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`hσ] [(patternIgnore (token.«⊢» "⊢"))]))])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Sigma.exists)
               ","
               (Tactic.simpLemma [] [] `exists_prop)
               ","
               (Tactic.simpLemma [] [] `mem_compl)
               ","
               (Tactic.simpLemma [] [] `mem_singleton)
               ","
               (Tactic.simpLemma [] [] `Ne.def)]
              "]"]
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.app
                `e.symm
                [(Term.app
                  `PowerBasis.lift
                  [`pb (Term.proj `σ "." (fieldIdx "2")) (Term.hole "_")])])
               ","
               (Term.app `e.symm [(Term.proj `σ "." (fieldIdx "1"))])
               ","
               (Term.anonymousCtor
                "⟨"
                [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
                 ","
                 (Term.app `Sigma.eq [(Term.hole "_") (Term.hole "_")])]
                "⟩")]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `aeval_def)
                 ","
                 (Tactic.rwRule [] `eval₂_eq_eval_map)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_roots)]
                "]")
               [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact
                 "exact"
                 (Term.app `Multiset.erase_subset [(Term.hole "_") (Term.hole "_") `hσ]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.simp
                 "simp"
                 []
                 []
                 []
                 ["["
                  [(Tactic.simpLemma
                    []
                    []
                    (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
                  "]"]
                 [])])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Mathlib.Tactic.tacticReplace_
               "replace"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h []]
                 []
                 ":="
                 (Term.app
                  `AlgHom.congr_fun
                  [(Term.app `Equiv.injective [(Term.hole "_") `h]) `pb.gen]))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `PowerBasis.lift_gen)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`hσ] []))])
              []
              (Tactic.exact "exact" (Term.app `hnodup.not_mem_erase [`hσ]))])
            []
            (Tactic.allGoals
             "all_goals"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `true_and_iff)
           ","
           (Tactic.simpLemma [] [] `Finset.mem_mk)
           ","
           (Tactic.simpLemma [] [] `mem_univ)
           ","
           (Tactic.simpLemma [] [] `mem_sigma)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`hσ] [(patternIgnore (token.«⊢» "⊢"))]))])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Sigma.exists)
           ","
           (Tactic.simpLemma [] [] `exists_prop)
           ","
           (Tactic.simpLemma [] [] `mem_compl)
           ","
           (Tactic.simpLemma [] [] `mem_singleton)
           ","
           (Tactic.simpLemma [] [] `Ne.def)]
          "]"]
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.app
            `e.symm
            [(Term.app `PowerBasis.lift [`pb (Term.proj `σ "." (fieldIdx "2")) (Term.hole "_")])])
           ","
           (Term.app `e.symm [(Term.proj `σ "." (fieldIdx "1"))])
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
             ","
             (Term.app `Sigma.eq [(Term.hole "_") (Term.hole "_")])]
            "⟩")]
          "⟩"))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `aeval_def)
             ","
             (Tactic.rwRule [] `eval₂_eq_eval_map)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_roots)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app `Multiset.erase_subset [(Term.hole "_") (Term.hole "_") `hσ]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma
                []
                []
                (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
              "]"]
             [])])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             []
             ":="
             (Term.app
              `AlgHom.congr_fun
              [(Term.app `Equiv.injective [(Term.hole "_") `h]) `pb.gen]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `PowerBasis.lift_gen)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hσ] []))])
          []
          (Tactic.exact "exact" (Term.app `hnodup.not_mem_erase [`hσ]))])
        []
        (Tactic.allGoals
         "all_goals"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.allGoals
       "all_goals"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticReplace_
         "replace"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h []]
           []
           ":="
           (Term.app
            `AlgHom.congr_fun
            [(Term.app `Equiv.injective [(Term.hole "_") `h]) `pb.gen]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `PowerBasis.lift_gen)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hσ] []))])
        []
        (Tactic.exact "exact" (Term.app `hnodup.not_mem_erase [`hσ]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hnodup.not_mem_erase [`hσ]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hnodup.not_mem_erase [`hσ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hσ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hnodup.not_mem_erase
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hσ] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hσ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
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
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `PowerBasis.lift_gen)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PowerBasis.lift_gen
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h []]
         []
         ":="
         (Term.app `AlgHom.congr_fun [(Term.app `Equiv.injective [(Term.hole "_") `h]) `pb.gen]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `AlgHom.congr_fun [(Term.app `Equiv.injective [(Term.hole "_") `h]) `pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Equiv.injective [(Term.hole "_") `h])
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
      `Equiv.injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Equiv.injective [(Term.hole "_") `h])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AlgHom.congr_fun
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
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `aeval_def)
           ","
           (Tactic.rwRule [] `eval₂_eq_eval_map)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_roots)]
          "]")
         [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.app `Multiset.erase_subset [(Term.hole "_") (Term.hole "_") `hσ]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma
              []
              []
              (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
            "]"]
           [])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         []
         ["["
          [(Tactic.simpLemma
            []
            []
            (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          []
          (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsSeparable.is_integral [`K `pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsSeparable.is_integral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsSeparable.is_integral [`K `pb.gen])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `minpoly.ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app `Multiset.erase_subset [(Term.hole "_") (Term.hole "_") `hσ]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Multiset.erase_subset [(Term.hole "_") (Term.hole "_") `hσ]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Multiset.erase_subset [(Term.hole "_") (Term.hole "_") `hσ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hσ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      `Multiset.erase_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `aeval_def)
         ","
         (Tactic.rwRule [] `eval₂_eq_eval_map)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mem_roots)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_roots
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_root.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval₂_eq_eval_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `e.symm
          [(Term.app `PowerBasis.lift [`pb (Term.proj `σ "." (fieldIdx "2")) (Term.hole "_")])])
         ","
         (Term.app `e.symm [(Term.proj `σ "." (fieldIdx "1"))])
         ","
         (Term.anonymousCtor
          "⟨"
          [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
           ","
           (Term.app `Sigma.eq [(Term.hole "_") (Term.hole "_")])]
          "⟩")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `e.symm
         [(Term.app `PowerBasis.lift [`pb (Term.proj `σ "." (fieldIdx "2")) (Term.hole "_")])])
        ","
        (Term.app `e.symm [(Term.proj `σ "." (fieldIdx "1"))])
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
          ","
          (Term.app `Sigma.eq [(Term.hole "_") (Term.hole "_")])]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
        ","
        (Term.app `Sigma.eq [(Term.hole "_") (Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Sigma.eq [(Term.hole "_") (Term.hole "_")])
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
      `Sigma.eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e.symm [(Term.proj `σ "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `σ "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `e.symm
       [(Term.app `PowerBasis.lift [`pb (Term.proj `σ "." (fieldIdx "2")) (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `PowerBasis.lift [`pb (Term.proj `σ "." (fieldIdx "2")) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.proj `σ "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PowerBasis.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `PowerBasis.lift [`pb (Term.proj `σ "." (fieldIdx "2")) (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Sigma.exists)
         ","
         (Tactic.simpLemma [] [] `exists_prop)
         ","
         (Tactic.simpLemma [] [] `mem_compl)
         ","
         (Tactic.simpLemma [] [] `mem_singleton)
         ","
         (Tactic.simpLemma [] [] `Ne.def)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_compl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `exists_prop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Sigma.exists
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `true_and_iff)
         ","
         (Tactic.simpLemma [] [] `Finset.mem_mk)
         ","
         (Tactic.simpLemma [] [] `mem_univ)
         ","
         (Tactic.simpLemma [] [] `mem_sigma)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`hσ] [(patternIgnore (token.«⊢» "⊢"))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hσ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_sigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.mem_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_and_iff
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
          [(Tactic.simpLemma [] [] `Equiv.apply_eq_iff_eq) "," (Tactic.simpLemma [] [] `heq_iff_eq)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`hij] []))])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.proj `hij "." (fieldIdx "2")))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `Sigma.eq
          [(Term.app
            `Equiv.injective
            [`e (Term.app `Equiv.injective [(Term.hole "_") (Term.app `Subtype.eq [`h])])])
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] (Term.proj `hij "." (fieldIdx "1")))] "]"]
                [])])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Sigma.eq
        [(Term.app
          `Equiv.injective
          [`e (Term.app `Equiv.injective [(Term.hole "_") (Term.app `Subtype.eq [`h])])])
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] (Term.proj `hij "." (fieldIdx "1")))] "]"]
              [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Sigma.eq
       [(Term.app
         `Equiv.injective
         [`e (Term.app `Equiv.injective [(Term.hole "_") (Term.app `Subtype.eq [`h])])])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] (Term.proj `hij "." (fieldIdx "1")))] "]"]
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
           ["[" [(Tactic.simpLemma [] [] (Term.proj `hij "." (fieldIdx "1")))] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.proj `hij "." (fieldIdx "1")))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hij "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hij
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.simp
          "simp"
          []
          []
          []
          ["[" [(Tactic.simpLemma [] [] (Term.proj `hij "." (fieldIdx "1")))] "]"]
          [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Equiv.injective
       [`e (Term.app `Equiv.injective [(Term.hole "_") (Term.app `Subtype.eq [`h])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.injective [(Term.hole "_") (Term.app `Subtype.eq [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subtype.eq [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Subtype.eq [`h]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Equiv.injective [(Term.hole "_") (Term.paren "(" (Term.app `Subtype.eq [`h]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Equiv.injective
      [`e
       (Term.paren
        "("
        (Term.app
         `Equiv.injective
         [(Term.hole "_") (Term.paren "(" (Term.app `Subtype.eq [`h]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Sigma.eq
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PowerBasis.lift_equiv_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PowerBasis.lift_equiv_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.proj `hij "." (fieldIdx "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hij "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hij
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Equiv.apply_eq_iff_eq) "," (Tactic.simpLemma [] [] `heq_iff_eq)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`hij] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hij
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `heq_iff_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.apply_eq_iff_eq
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
          [(Tactic.simpLemma [] [] `true_and_iff)
           ","
           (Tactic.simpLemma [] [] `Finset.mem_mk)
           ","
           (Tactic.simpLemma [] [] `mem_univ)
           ","
           (Tactic.simpLemma [] [] `mem_sigma)]
          "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `Multiset.mem_erase_of_ne
             [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]))]
          "]")
         [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `hroots [(Term.hole "_")]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `true_and_iff)
             ","
             (Tactic.simpLemma [] [] `mem_univ)
             ","
             (Tactic.simpLemma [] [] `Ne.def)
             ","
             (Tactic.simpLemma [] [] `mem_sigma)
             ","
             (Tactic.simpLemma [] [] `mem_compl)
             ","
             (Tactic.simpLemma [] [] `mem_singleton)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `hi
            [(«term_<|_»
              `e.injective
              "<|"
              («term_<|_» `pb.lift_equiv.injective "<|" (Term.app `Subtype.eq [`h.symm])))]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `true_and_iff)
           ","
           (Tactic.simpLemma [] [] `mem_univ)
           ","
           (Tactic.simpLemma [] [] `Ne.def)
           ","
           (Tactic.simpLemma [] [] `mem_sigma)
           ","
           (Tactic.simpLemma [] [] `mem_compl)
           ","
           (Tactic.simpLemma [] [] `mem_singleton)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `hi
          [(«term_<|_»
            `e.injective
            "<|"
            («term_<|_» `pb.lift_equiv.injective "<|" (Term.app `Subtype.eq [`h.symm])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `hi
        [(«term_<|_»
          `e.injective
          "<|"
          («term_<|_» `pb.lift_equiv.injective "<|" (Term.app `Subtype.eq [`h.symm])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hi
       [(«term_<|_»
         `e.injective
         "<|"
         («term_<|_» `pb.lift_equiv.injective "<|" (Term.app `Subtype.eq [`h.symm])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `e.injective
       "<|"
       («term_<|_» `pb.lift_equiv.injective "<|" (Term.app `Subtype.eq [`h.symm])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `pb.lift_equiv.injective "<|" (Term.app `Subtype.eq [`h.symm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subtype.eq [`h.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `pb.lift_equiv.injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `e.injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      `e.injective
      "<|"
      («term_<|_» `pb.lift_equiv.injective "<|" (Term.app `Subtype.eq [`h.symm])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hi
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PowerBasis.lift_equiv_apply_coe)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PowerBasis.lift_equiv_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PowerBasis.lift_equiv_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `true_and_iff)
         ","
         (Tactic.simpLemma [] [] `mem_univ)
         ","
         (Tactic.simpLemma [] [] `Ne.def)
         ","
         (Tactic.simpLemma [] [] `mem_sigma)
         ","
         (Tactic.simpLemma [] [] `mem_compl)
         ","
         (Tactic.simpLemma [] [] `mem_singleton)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_compl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_sigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ne.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `hroots [(Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hroots [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hroots [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hroots
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `Multiset.mem_erase_of_ne
           [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Multiset.mem_erase_of_ne
       [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiset.mem_erase_of_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `true_and_iff)
         ","
         (Tactic.simpLemma [] [] `Finset.mem_mk)
         ","
         (Tactic.simpLemma [] [] `mem_univ)
         ","
         (Tactic.simpLemma [] [] `mem_sigma)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_sigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.mem_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `prod_bij
        [(Term.fun
          "fun"
          (Term.basicFun
           [`i `hi]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.app `e [(Term.proj `i "." (fieldIdx "2"))])
             ","
             (Term.app `e [(Term.proj `i "." (fieldIdx "1")) `pb.gen])]
            "⟩")))
         (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))
         (Term.fun
          "fun"
          (Term.basicFun
           [`i `hi]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                []
                [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])])))))
         (Term.fun "fun" (Term.basicFun [`i `j `hi `hj `hij] [] "=>" (Term.hole "_")))
         (Term.fun "fun" (Term.basicFun [`σ `hσ] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `prod_bij
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i `hi]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.app `e [(Term.proj `i "." (fieldIdx "2"))])
            ","
            (Term.app `e [(Term.proj `i "." (fieldIdx "1")) `pb.gen])]
           "⟩")))
        (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))
        (Term.fun
         "fun"
         (Term.basicFun
          [`i `hi]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               []
               []
               [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])])))))
        (Term.fun "fun" (Term.basicFun [`i `j `hi `hj `hij] [] "=>" (Term.hole "_")))
        (Term.fun "fun" (Term.basicFun [`σ `hσ] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`σ `hσ] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hσ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`i `j `hi `hj `hij] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hij
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`i `j `hi `hj `hij] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `hi]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             []
             [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])])))))
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
           []
           [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`i `hi]
       []
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            []
            [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])])))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `hi]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `e [(Term.proj `i "." (fieldIdx "2"))])
          ","
          (Term.app `e [(Term.proj `i "." (fieldIdx "1")) `pb.gen])]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `e [(Term.proj `i "." (fieldIdx "2"))])
        ","
        (Term.app `e [(Term.proj `i "." (fieldIdx "1")) `pb.gen])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [(Term.proj `i "." (fieldIdx "1")) `pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `i "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [(Term.proj `i "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `i "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`i `hi]
       []
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `e [(Term.proj `i "." (fieldIdx "2"))])
         ","
         (Term.app `e [(Term.proj `i "." (fieldIdx "1")) `pb.gen])]
        "⟩")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `prod_bij
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `prod_sigma') "," (Tactic.rwRule [] `prod_sigma')]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_sigma'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_sigma'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convRHS
       "conv_rhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.congr "congr")
          []
          (Tactic.Conv.skip "skip")
          []
          (Tactic.Conv.ext "ext" [])
          []
          (Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_alg_hom_apply)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `aeval_root_derivative_of_splits
               [(Term.app `minpoly.monic [(Term.app `IsSeparable.is_integral [`K `pb.gen])])
                (Term.app `IsAlgClosed.splits_codomain [(Term.hole "_")])
                (Term.app `hroots [`σ])]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `Finset.prod_mk
               [(Term.hole "_") (Term.app `hnodup.erase [(Term.hole "_")])]))]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Finset.prod_mk [(Term.hole "_") (Term.app `hnodup.erase [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hnodup.erase [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hnodup.erase
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hnodup.erase [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.prod_mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `aeval_root_derivative_of_splits
       [(Term.app `minpoly.monic [(Term.app `IsSeparable.is_integral [`K `pb.gen])])
        (Term.app `IsAlgClosed.splits_codomain [(Term.hole "_")])
        (Term.app `hroots [`σ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hroots [`σ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hroots
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hroots [`σ]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsAlgClosed.splits_codomain [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsAlgClosed.splits_codomain
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsAlgClosed.splits_codomain [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `minpoly.monic [(Term.app `IsSeparable.is_integral [`K `pb.gen])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsSeparable.is_integral [`K `pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsSeparable.is_integral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsSeparable.is_integral [`K `pb.gen])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `minpoly.monic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `minpoly.monic
      [(Term.paren "(" (Term.app `IsSeparable.is_integral [`K `pb.gen]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval_root_derivative_of_splits
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_alg_hom_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `norm_eq_prod_embeddings)
         ","
         (Tactic.rwRule [] `prod_prod_Ioi_mul_eq_prod_prod_off_diag)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_prod_Ioi_mul_eq_prod_prod_off_diag
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_prod_embeddings
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `RingHom.map_mul)
         ","
         (Tactic.rwRule [] `RingHom.map_pow)
         ","
         (Tactic.rwRule [] `RingHom.map_neg)
         ","
         (Tactic.rwRule [] `RingHom.map_one)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `discr_power_basis_eq_prod''
           [(Term.hole "_") (Term.hole "_") (Term.hole "_") `e]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `discr_power_basis_eq_prod'' [(Term.hole "_") (Term.hole "_") (Term.hole "_") `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      `discr_power_basis_eq_prod''
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.proj (Term.app `algebraMap [`K `E]) "." `Injective))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `algebraMap [`K `E]) "." `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `algebraMap [`K `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`K `E]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hroots []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`σ]
            [(Term.typeSpec ":" (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E))]
            ","
            («term_∈_»
             (Term.app `σ [`pb.gen])
             "∈"
             (Term.proj
              (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
              "."
              `roots))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`σ])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mem_roots)
                ","
                (Tactic.rwRule [] `is_root.def)
                ","
                (Tactic.rwRule [] `eval_map)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)
                ","
                (Tactic.rwRule [] `aeval_alg_hom_apply)]
               "]")
              [])
             []
             (Std.Tactic.tacticRepeat'_
              "repeat'"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.app
                      `minpoly.ne_zero
                      [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
                   "]"]
                  [])])))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`σ])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mem_roots)
             ","
             (Tactic.rwRule [] `is_root.def)
             ","
             (Tactic.rwRule [] `eval_map)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)
             ","
             (Tactic.rwRule [] `aeval_alg_hom_apply)]
            "]")
           [])
          []
          (Std.Tactic.tacticRepeat'_
           "repeat'"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma
                  []
                  []
                  (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
                "]"]
               [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRepeat'_
       "repeat'"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma
              []
              []
              (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          []
          (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `minpoly.ne_zero [(Term.app `IsSeparable.is_integral [`K `pb.gen])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsSeparable.is_integral [`K `pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsSeparable.is_integral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsSeparable.is_integral [`K `pb.gen])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `minpoly.ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mem_roots)
         ","
         (Tactic.rwRule [] `is_root.def)
         ","
         (Tactic.rwRule [] `eval_map)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)
         ","
         (Tactic.rwRule [] `aeval_alg_hom_apply)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_alg_hom_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_root.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_roots
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`σ])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`σ]
       [(Term.typeSpec ":" (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E))]
       ","
       («term_∈_»
        (Term.app `σ [`pb.gen])
        "∈"
        (Term.proj
         (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
         "."
         `roots)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.app `σ [`pb.gen])
       "∈"
       (Term.proj
        (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
        "."
        `roots))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
       "."
       `roots)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `minpoly [`K `pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `minpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `minpoly [`K `pb.gen]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `algebraMap [`K `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`K `E]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `map
      [(Term.paren "(" (Term.app `algebraMap [`K `E]) ")")
       (Term.paren "(" (Term.app `minpoly [`K `pb.gen]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `σ [`pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `L
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hnodup []]
         [(Term.typeSpec
           ":"
           (Term.proj
            (Term.proj
             (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
             "."
             `roots)
            "."
            `Nodup))]
         ":="
         (Term.app
          `nodup_roots
          [(Term.app `separable.map [(Term.app `IsSeparable.separable [`K `pb.gen])])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nodup_roots
       [(Term.app `separable.map [(Term.app `IsSeparable.separable [`K `pb.gen])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `separable.map [(Term.app `IsSeparable.separable [`K `pb.gen])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsSeparable.separable [`K `pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsSeparable.separable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsSeparable.separable [`K `pb.gen])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `separable.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `separable.map [(Term.paren "(" (Term.app `IsSeparable.separable [`K `pb.gen]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nodup_roots
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
        "."
        `roots)
       "."
       `Nodup)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
       "."
       `roots)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `map [(Term.app `algebraMap [`K `E]) (Term.app `minpoly [`K `pb.gen])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `minpoly [`K `pb.gen])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.gen
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `minpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `minpoly [`K `pb.gen]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `algebraMap [`K `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`K `E]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `map
      [(Term.paren "(" (Term.app `algebraMap [`K `E]) ")")
       (Term.paren "(" (Term.app `minpoly [`K `pb.gen]) ")")])
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
         [`e []]
         [(Term.typeSpec
           ":"
           (Logic.Equiv.Defs.«term_≃_»
            (Term.app `Fin [`pb.dim])
            " ≃ "
            (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E)))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine' "refine'" (Term.app `equiv_of_card_eq [(Term.hole "_")]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Fintype.card_fin) "," (Tactic.rwRule [] `AlgHom.card)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.proj (Term.app `PowerBasis.finrank [`pb]) "." `symm))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine' "refine'" (Term.app `equiv_of_card_eq [(Term.hole "_")]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Fintype.card_fin) "," (Tactic.rwRule [] `AlgHom.card)]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.proj (Term.app `PowerBasis.finrank [`pb]) "." `symm))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.app `PowerBasis.finrank [`pb]) "." `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `PowerBasis.finrank [`pb]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `PowerBasis.finrank [`pb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PowerBasis.finrank
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `PowerBasis.finrank [`pb])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Fintype.card_fin) "," (Tactic.rwRule [] `AlgHom.card)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.card
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.card_fin
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `equiv_of_card_eq [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `equiv_of_card_eq [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `equiv_of_card_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Logic.Equiv.Defs.«term_≃_»
       (Term.app `Fin [`pb.dim])
       " ≃ "
       (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `L
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 26 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Algebra.Hom.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `Fin [`pb.dim])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pb.dim
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`a `b]
           [(Term.typeSpec ":" `E)]
           "=>"
           (Term.app `Classical.propDecidable [(Term.app `Eq [`a `b])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b]
        [(Term.typeSpec ":" `E)]
        "=>"
        (Term.app `Classical.propDecidable [(Term.app `Eq [`a `b])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Classical.propDecidable [(Term.app `Eq [`a `b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq [`a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Eq [`a `b]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.propDecidable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl (Term.letIdDecl `E [] [] ":=" (Term.app `AlgebraicClosure [`L]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `AlgebraicClosure [`L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `AlgebraicClosure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `discr [`K (Term.proj `pb "." `Basis)])
       "="
       («term_*_»
        («term_^_»
         («term-_» "-" (num "1"))
         "^"
         («term_/_»
          («term_*_»
           (Algebra.RingTheory.Discriminant.termn "n")
           "*"
           («term_-_» (Algebra.RingTheory.Discriminant.termn "n") "-" (num "1")))
          "/"
          (num "2")))
        "*"
        (Term.app
         `norm
         [`K
          (Term.app
           `aeval
           [(Term.proj `pb "." `gen)
            (Term.proj (Term.app `minpoly [`K (Term.proj `pb "." `gen)]) "." `derivative)])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_»
        («term-_» "-" (num "1"))
        "^"
        («term_/_»
         («term_*_»
          (Algebra.RingTheory.Discriminant.termn "n")
          "*"
          («term_-_» (Algebra.RingTheory.Discriminant.termn "n") "-" (num "1")))
         "/"
         (num "2")))
       "*"
       (Term.app
        `norm
        [`K
         (Term.app
          `aeval
          [(Term.proj `pb "." `gen)
           (Term.proj (Term.app `minpoly [`K (Term.proj `pb "." `gen)]) "." `derivative)])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `norm
       [`K
        (Term.app
         `aeval
         [(Term.proj `pb "." `gen)
          (Term.proj (Term.app `minpoly [`K (Term.proj `pb "." `gen)]) "." `derivative)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `aeval
       [(Term.proj `pb "." `gen)
        (Term.proj (Term.app `minpoly [`K (Term.proj `pb "." `gen)]) "." `derivative)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `minpoly [`K (Term.proj `pb "." `gen)]) "." `derivative)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `minpoly [`K (Term.proj `pb "." `gen)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `pb "." `gen)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `minpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `minpoly [`K (Term.proj `pb "." `gen)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `pb "." `gen)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `aeval
      [(Term.proj `pb "." `gen)
       (Term.proj
        (Term.paren "(" (Term.app `minpoly [`K (Term.proj `pb "." `gen)]) ")")
        "."
        `derivative)])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_»
       («term-_» "-" (num "1"))
       "^"
       («term_/_»
        («term_*_»
         (Algebra.RingTheory.Discriminant.termn "n")
         "*"
         («term_-_» (Algebra.RingTheory.Discriminant.termn "n") "-" (num "1")))
        "/"
        (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       («term_*_»
        (Algebra.RingTheory.Discriminant.termn "n")
        "*"
        («term_-_» (Algebra.RingTheory.Discriminant.termn "n") "-" (num "1")))
       "/"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       (Algebra.RingTheory.Discriminant.termn "n")
       "*"
       («term_-_» (Algebra.RingTheory.Discriminant.termn "n") "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Algebra.RingTheory.Discriminant.termn "n") "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Algebra.RingTheory.Discriminant.termn "n")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.RingTheory.Discriminant.termn', expected 'Algebra.RingTheory.Discriminant.termn._@.RingTheory.Discriminant._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Formula for the discriminant of a power basis using the norm of the field extension. -/
  theorem
    discr_power_basis_eq_norm
    [ IsSeparable K L ]
      :
        discr K pb . Basis
          =
          - 1 ^ n * n - 1 / 2 * norm K aeval pb . gen minpoly K pb . gen . derivative
    :=
      by
        let E := AlgebraicClosure L
          letI := fun a b : E => Classical.propDecidable Eq a b
          have
            e
              : Fin pb.dim ≃ L →ₐ[ K ] E
              :=
              by
                refine' equiv_of_card_eq _
                  rw [ Fintype.card_fin , AlgHom.card ]
                  exact PowerBasis.finrank pb . symm
          have
            hnodup
              : map algebraMap K E minpoly K pb.gen . roots . Nodup
              :=
              nodup_roots separable.map IsSeparable.separable K pb.gen
          have
            hroots
              : ∀ σ : L →ₐ[ K ] E , σ pb.gen ∈ map algebraMap K E minpoly K pb.gen . roots
              :=
              by
                intro σ
                  rw [ mem_roots , is_root.def , eval_map , ← aeval_def , aeval_alg_hom_apply ]
                  repeat' simp [ minpoly.ne_zero IsSeparable.is_integral K pb.gen ]
          apply algebraMap K E . Injective
          rw
            [
              RingHom.map_mul
                ,
                RingHom.map_pow
                ,
                RingHom.map_neg
                ,
                RingHom.map_one
                ,
                discr_power_basis_eq_prod'' _ _ _ e
              ]
          congr
          rw [ norm_eq_prod_embeddings , prod_prod_Ioi_mul_eq_prod_prod_off_diag ]
          conv_rhs
            =>
            congr
              skip
              ext
              rw
                [
                  ← aeval_alg_hom_apply
                    ,
                    aeval_root_derivative_of_splits
                      minpoly.monic IsSeparable.is_integral K pb.gen
                        IsAlgClosed.splits_codomain _
                        hroots σ
                    ,
                    ← Finset.prod_mk _ hnodup.erase _
                  ]
          rw [ prod_sigma' , prod_sigma' ]
          refine'
            prod_bij
              fun i hi => ⟨ e i . 2 , e i . 1 pb.gen ⟩
                fun i hi => _
                fun i hi => by simp at hi
                fun i j hi hj hij => _
                fun σ hσ => _
          ·
            simp only [ true_and_iff , Finset.mem_mk , mem_univ , mem_sigma ]
              rw [ Multiset.mem_erase_of_ne fun h => _ ]
              · exact hroots _
              ·
                simp
                    only
                    [ true_and_iff , mem_univ , Ne.def , mem_sigma , mem_compl , mem_singleton ]
                    at hi
                  rw [ ← PowerBasis.lift_equiv_apply_coe , ← PowerBasis.lift_equiv_apply_coe ] at h
                  exact hi e.injective <| pb.lift_equiv.injective <| Subtype.eq h.symm
          ·
            simp only [ Equiv.apply_eq_iff_eq , heq_iff_eq ] at hij
              have h := hij . 2
              rw [ ← PowerBasis.lift_equiv_apply_coe , ← PowerBasis.lift_equiv_apply_coe ] at h
              refine' Sigma.eq Equiv.injective e Equiv.injective _ Subtype.eq h by simp [ hij . 1 ]
          ·
            simp only [ true_and_iff , Finset.mem_mk , mem_univ , mem_sigma ] at hσ ⊢
              simp only [ Sigma.exists , exists_prop , mem_compl , mem_singleton , Ne.def ]
              refine'
                ⟨ e.symm PowerBasis.lift pb σ . 2 _ , e.symm σ . 1 , ⟨ fun h => _ , Sigma.eq _ _ ⟩ ⟩
              ·
                rw [ aeval_def , eval₂_eq_eval_map , ← is_root.def , ← mem_roots ]
                  · exact Multiset.erase_subset _ _ hσ
                  · simp [ minpoly.ne_zero IsSeparable.is_integral K pb.gen ]
              ·
                replace h := AlgHom.congr_fun Equiv.injective _ h pb.gen
                  rw [ PowerBasis.lift_gen ] at h
                  rw [ ← h ] at hσ
                  exact hnodup.not_mem_erase hσ
              all_goals simp
#align algebra.discr_power_basis_eq_norm Algebra.discr_power_basis_eq_norm

section Integral

variable {R : Type z} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]

-- mathport name: expris_integral
local notation "is_integral" => IsIntegral

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `K` and `L` are fields and `is_scalar_tower R K L`, and `b : ι → L` satisfies\n` ∀ i, is_integral R (b i)`, then `is_integral R (discr K b)`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `discr_is_integral [])
      (Command.declSig
       [(Term.implicitBinder "{" [`b] [":" (Term.arrow `ι "→" `L)] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [`i]
           []
           ","
           (Term.app
            (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
            [`R (Term.app `b [`i])]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
         [`R (Term.app `discr [`K `b])])))
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
              [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `discr_def)] "]") [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `IsIntegral.det
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`i `j]
                    []
                    "=>"
                    (Term.app
                     `is_integral_trace
                     [(Term.app
                       `is_integral_mul
                       [(Term.app `h [`i]) (Term.app `h [`j])])])))]))])))])))
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
             [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `discr_def)] "]") [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `IsIntegral.det
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`i `j]
                   []
                   "=>"
                   (Term.app
                    `is_integral_trace
                    [(Term.app
                      `is_integral_mul
                      [(Term.app `h [`i]) (Term.app `h [`j])])])))]))])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `discr_def)] "]") [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `IsIntegral.det
            [(Term.fun
              "fun"
              (Term.basicFun
               [`i `j]
               []
               "=>"
               (Term.app
                `is_integral_trace
                [(Term.app `is_integral_mul [(Term.app `h [`i]) (Term.app `h [`j])])])))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `IsIntegral.det
        [(Term.fun
          "fun"
          (Term.basicFun
           [`i `j]
           []
           "=>"
           (Term.app
            `is_integral_trace
            [(Term.app `is_integral_mul [(Term.app `h [`i]) (Term.app `h [`j])])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsIntegral.det
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i `j]
          []
          "=>"
          (Term.app
           `is_integral_trace
           [(Term.app `is_integral_mul [(Term.app `h [`i]) (Term.app `h [`j])])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `j]
        []
        "=>"
        (Term.app
         `is_integral_trace
         [(Term.app `is_integral_mul [(Term.app `h [`i]) (Term.app `h [`j])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_integral_trace
       [(Term.app `is_integral_mul [(Term.app `h [`i]) (Term.app `h [`j])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_integral_mul [(Term.app `h [`i]) (Term.app `h [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`j]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `h [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_integral_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `is_integral_mul
      [(Term.paren "(" (Term.app `h [`i]) ")") (Term.paren "(" (Term.app `h [`j]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_integral_trace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIntegral.det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `discr_def)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `discr_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
       [`R (Term.app `discr [`K `b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `discr [`K `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `discr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `discr [`K `b]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.RingTheory.Discriminant.termis_integral', expected 'Algebra.RingTheory.Discriminant.termis_integral._@.RingTheory.Discriminant._hyg.596'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `K` and `L` are fields and `is_scalar_tower R K L`, and `b : ι → L` satisfies
    ` ∀ i, is_integral R (b i)`, then `is_integral R (discr K b)`. -/
  theorem
    discr_is_integral
    { b : ι → L } ( h : ∀ i , is_integral R b i ) : is_integral R discr K b
    :=
      by
        classical
          rw [ discr_def ] exact IsIntegral.det fun i j => is_integral_trace is_integral_mul h i h j
#align algebra.discr_is_integral Algebra.discr_is_integral

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `b` and `b'` are `ℚ`-bases of a number field `K` such that\n`∀ i j, is_integral ℤ (b.to_matrix b' i j)` and `∀ i j, is_integral ℤ (b'.to_matrix b i j)` then\n`discr ℚ b = discr ℚ b'`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `discr_eq_discr_of_to_matrix_coeff_is_integral [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `NumberField [`K]) "]")
        (Term.implicitBinder "{" [`b] [":" (Term.app `Basis [`ι (Data.Rat.Init.termℚ "ℚ") `K])] "}")
        (Term.implicitBinder
         "{"
         [`b']
         [":" (Term.app `Basis [`ι' (Data.Rat.Init.termℚ "ℚ") `K])]
         "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [`i `j]
           []
           ","
           (Term.app
            (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
            [(termℤ "ℤ") (Term.app (Term.proj `b "." `toMatrix) [`b' `i `j])]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h']
         [":"
          (Term.forall
           "∀"
           [`i `j]
           []
           ","
           (Term.app
            (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
            [(termℤ "ℤ") (Term.app (Term.proj `b' "." `toMatrix) [`b `i `j])]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `discr [(Data.Rat.Init.termℚ "ℚ") `b])
         "="
         (Term.app `discr [(Data.Rat.Init.termℚ "ℚ") `b']))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.replace'
            "replace"
            [`h' []]
            [(Term.typeSpec
              ":"
              (Term.forall
               "∀"
               [`i `j]
               []
               ","
               (Term.app
                (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                [(termℤ "ℤ")
                 (Term.app
                  `b'.to_matrix
                  [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])]) `i `j])])))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`i `j])
             []
             (convert
              "convert"
              []
              (Term.app
               `h'
               [`i (Term.app (Term.proj (Term.app `b.index_equiv [`b']) "." `symm) [`j])])
              [])
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
           []
           (Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    (Term.proj
                     (Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])
                     "."
                     `to_matrix_map_vec_mul)
                    [`b']))
                  ","
                  (Tactic.rwRule [] `discr_of_matrix_vec_mul)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `one_mul [(Term.app `discr [(Data.Rat.Init.termℚ "ℚ") `b])]))
                  ","
                  (Tactic.rwRule [] `Basis.coe_reindex)
                  ","
                  (Tactic.rwRule [] `discr_reindex)]
                 "]")
                [])
               []
               (Tactic.congr "congr" [])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hint []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                     [(termℤ "ℤ")
                      (Term.proj
                       (Term.app
                        (Term.proj
                         (Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])
                         "."
                         `toMatrix)
                        [`b'])
                       "."
                       `det)]))]
                  ":="
                  (Term.app
                   `IsIntegral.det
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`i `j]
                      []
                      "=>"
                      (Term.app `h [(Term.hole "_") (Term.hole "_")])))]))))
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                      [])]
                    "⟩")])]
                []
                [":="
                 [(Term.app
                   (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                   [`hint])]])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hunit []]
                  [(Term.typeSpec ":" (Term.app `IsUnit [`r]))]
                  ":="
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
                           (Term.app
                            (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                            [(termℤ "ℤ")
                             (Term.proj
                              (Term.app
                               `b'.to_matrix
                               [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
                              "."
                              `det)]))]
                         ":="
                         (Term.app
                          `IsIntegral.det
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`i `j]
                             []
                             "=>"
                             (Term.app `h' [(Term.hole "_") (Term.hole "_")])))]))))
                      []
                      (Std.Tactic.obtain
                       "obtain"
                       [(Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `r')])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `hr')])
                             [])]
                           "⟩")])]
                       []
                       [":="
                        [(Term.app
                          (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                          [`this])]])
                      []
                      (Tactic.refine'
                       "refine'"
                       (Term.app
                        (Term.proj `isUnit_iff_exists_inv "." (fieldIdx "2"))
                        [(Term.anonymousCtor "⟨" [`r' "," (Term.hole "_")] "⟩")]))
                      []
                      (Tactic.tacticSuffices_
                       "suffices"
                       (Term.sufficesDecl
                        []
                        («term_=_»
                         (Term.app
                          `algebraMap
                          [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ") («term_*_» `r "*" `r')])
                         "="
                         (num "1"))
                        (Term.byTactic'
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
                                (Term.app
                                 `RingHom.map_one
                                 [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))]
                              "]")
                             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                            []
                            (Tactic.exact
                             "exact"
                             (Term.app
                              (Term.app
                               `IsFractionRing.injective
                               [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
                              [`this]))])))))
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `RingHom.map_mul)
                         ","
                         (Tactic.rwRule [] `hr)
                         ","
                         (Tactic.rwRule [] `hr')
                         ","
                         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_mul)
                         ","
                         (Tactic.rwRule [] `Basis.to_matrix_mul_to_matrix_flip)
                         ","
                         (Tactic.rwRule [] `det_one)]
                        "]")
                       [])]))))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    `RingHom.map_one
                    [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)]
                 "]")
                [])
               []
               (Tactic.cases'
                "cases'"
                [(Tactic.casesTarget
                  []
                  (Term.app (Term.proj `Int.isUnit_iff "." (fieldIdx "1")) [`hunit]))]
                []
                ["with" [(Lean.binderIdent `hp) (Lean.binderIdent `hm)]])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hp)] "]"] [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hm)] "]"] [])])])))])))
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
         [(Mathlib.Tactic.replace'
           "replace"
           [`h' []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`i `j]
              []
              ","
              (Term.app
               (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
               [(termℤ "ℤ")
                (Term.app
                 `b'.to_matrix
                 [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])]) `i `j])])))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`i `j])
            []
            (convert
             "convert"
             []
             (Term.app
              `h'
              [`i (Term.app (Term.proj (Term.app `b.index_equiv [`b']) "." `symm) [`j])])
             [])
            []
            (Std.Tactic.Simpa.simpa "simpa" [] [] (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] []))])
          []
          (Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app
                   (Term.proj
                    (Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])
                    "."
                    `to_matrix_map_vec_mul)
                   [`b']))
                 ","
                 (Tactic.rwRule [] `discr_of_matrix_vec_mul)
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `one_mul [(Term.app `discr [(Data.Rat.Init.termℚ "ℚ") `b])]))
                 ","
                 (Tactic.rwRule [] `Basis.coe_reindex)
                 ","
                 (Tactic.rwRule [] `discr_reindex)]
                "]")
               [])
              []
              (Tactic.congr "congr" [])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hint []]
                 [(Term.typeSpec
                   ":"
                   (Term.app
                    (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                    [(termℤ "ℤ")
                     (Term.proj
                      (Term.app
                       (Term.proj
                        (Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])
                        "."
                        `toMatrix)
                       [`b'])
                      "."
                      `det)]))]
                 ":="
                 (Term.app
                  `IsIntegral.det
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`i `j]
                     []
                     "=>"
                     (Term.app `h [(Term.hole "_") (Term.hole "_")])))]))))
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                     [])]
                   "⟩")])]
               []
               [":="
                [(Term.app
                  (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                  [`hint])]])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hunit []]
                 [(Term.typeSpec ":" (Term.app `IsUnit [`r]))]
                 ":="
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
                          (Term.app
                           (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                           [(termℤ "ℤ")
                            (Term.proj
                             (Term.app
                              `b'.to_matrix
                              [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
                             "."
                             `det)]))]
                        ":="
                        (Term.app
                         `IsIntegral.det
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`i `j]
                            []
                            "=>"
                            (Term.app `h' [(Term.hole "_") (Term.hole "_")])))]))))
                     []
                     (Std.Tactic.obtain
                      "obtain"
                      [(Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r')])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `hr')])
                            [])]
                          "⟩")])]
                      []
                      [":="
                       [(Term.app
                         (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                         [`this])]])
                     []
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       (Term.proj `isUnit_iff_exists_inv "." (fieldIdx "2"))
                       [(Term.anonymousCtor "⟨" [`r' "," (Term.hole "_")] "⟩")]))
                     []
                     (Tactic.tacticSuffices_
                      "suffices"
                      (Term.sufficesDecl
                       []
                       («term_=_»
                        (Term.app
                         `algebraMap
                         [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ") («term_*_» `r "*" `r')])
                        "="
                        (num "1"))
                       (Term.byTactic'
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
                               (Term.app
                                `RingHom.map_one
                                [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))]
                             "]")
                            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                           []
                           (Tactic.exact
                            "exact"
                            (Term.app
                             (Term.app
                              `IsFractionRing.injective
                              [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
                             [`this]))])))))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `RingHom.map_mul)
                        ","
                        (Tactic.rwRule [] `hr)
                        ","
                        (Tactic.rwRule [] `hr')
                        ","
                        (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_mul)
                        ","
                        (Tactic.rwRule [] `Basis.to_matrix_mul_to_matrix_flip)
                        ","
                        (Tactic.rwRule [] `det_one)]
                       "]")
                      [])]))))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app
                   `RingHom.map_one
                   [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)]
                "]")
               [])
              []
              (Tactic.cases'
               "cases'"
               [(Tactic.casesTarget
                 []
                 (Term.app (Term.proj `Int.isUnit_iff "." (fieldIdx "1")) [`hunit]))]
               []
               ["with" [(Lean.binderIdent `hp) (Lean.binderIdent `hm)]])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hp)] "]"] [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hm)] "]"] [])])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               (Term.proj
                (Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])
                "."
                `to_matrix_map_vec_mul)
               [`b']))
             ","
             (Tactic.rwRule [] `discr_of_matrix_vec_mul)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `one_mul [(Term.app `discr [(Data.Rat.Init.termℚ "ℚ") `b])]))
             ","
             (Tactic.rwRule [] `Basis.coe_reindex)
             ","
             (Tactic.rwRule [] `discr_reindex)]
            "]")
           [])
          []
          (Tactic.congr "congr" [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hint []]
             [(Term.typeSpec
               ":"
               (Term.app
                (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                [(termℤ "ℤ")
                 (Term.proj
                  (Term.app
                   (Term.proj (Term.app `b.reindex [(Term.app `b.index_equiv [`b'])]) "." `toMatrix)
                   [`b'])
                  "."
                  `det)]))]
             ":="
             (Term.app
              `IsIntegral.det
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i `j]
                 []
                 "=>"
                 (Term.app `h [(Term.hole "_") (Term.hole "_")])))]))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
              [`hint])]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hunit []]
             [(Term.typeSpec ":" (Term.app `IsUnit [`r]))]
             ":="
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
                      (Term.app
                       (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                       [(termℤ "ℤ")
                        (Term.proj
                         (Term.app
                          `b'.to_matrix
                          [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
                         "."
                         `det)]))]
                    ":="
                    (Term.app
                     `IsIntegral.det
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`i `j]
                        []
                        "=>"
                        (Term.app `h' [(Term.hole "_") (Term.hole "_")])))]))))
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r')])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr')])
                        [])]
                      "⟩")])]
                  []
                  [":="
                   [(Term.app
                     (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                     [`this])]])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.proj `isUnit_iff_exists_inv "." (fieldIdx "2"))
                   [(Term.anonymousCtor "⟨" [`r' "," (Term.hole "_")] "⟩")]))
                 []
                 (Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   («term_=_»
                    (Term.app
                     `algebraMap
                     [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ") («term_*_» `r "*" `r')])
                    "="
                    (num "1"))
                   (Term.byTactic'
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
                           (Term.app
                            `RingHom.map_one
                            [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))]
                         "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                       []
                       (Tactic.exact
                        "exact"
                        (Term.app
                         (Term.app
                          `IsFractionRing.injective
                          [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
                         [`this]))])))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `RingHom.map_mul)
                    ","
                    (Tactic.rwRule [] `hr)
                    ","
                    (Tactic.rwRule [] `hr')
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_mul)
                    ","
                    (Tactic.rwRule [] `Basis.to_matrix_mul_to_matrix_flip)
                    ","
                    (Tactic.rwRule [] `det_one)]
                   "]")
                  [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `RingHom.map_one
               [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)]
            "]")
           [])
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget
             []
             (Term.app (Term.proj `Int.isUnit_iff "." (fieldIdx "1")) [`hunit]))]
           []
           ["with" [(Lean.binderIdent `hp) (Lean.binderIdent `hm)]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hp)] "]"] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hm)] "]"] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hm)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hm)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hp)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hp)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app (Term.proj `Int.isUnit_iff "." (fieldIdx "1")) [`hunit]))]
       []
       ["with" [(Lean.binderIdent `hp) (Lean.binderIdent `hm)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Int.isUnit_iff "." (fieldIdx "1")) [`hunit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hunit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Int.isUnit_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Int.isUnit_iff
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
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `RingHom.map_one
           [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `RingHom.map_one [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Rat.Init.termℚ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Rat.Init.termℚ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.map_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hunit []]
         [(Term.typeSpec ":" (Term.app `IsUnit [`r]))]
         ":="
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
                  (Term.app
                   (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                   [(termℤ "ℤ")
                    (Term.proj
                     (Term.app
                      `b'.to_matrix
                      [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
                     "."
                     `det)]))]
                ":="
                (Term.app
                 `IsIntegral.det
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`i `j]
                    []
                    "=>"
                    (Term.app `h' [(Term.hole "_") (Term.hole "_")])))]))))
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r')])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr')])
                    [])]
                  "⟩")])]
              []
              [":="
               [(Term.app
                 (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                 [`this])]])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj `isUnit_iff_exists_inv "." (fieldIdx "2"))
               [(Term.anonymousCtor "⟨" [`r' "," (Term.hole "_")] "⟩")]))
             []
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_=_»
                (Term.app
                 `algebraMap
                 [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ") («term_*_» `r "*" `r')])
                "="
                (num "1"))
               (Term.byTactic'
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
                       (Term.app
                        `RingHom.map_one
                        [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     (Term.app `IsFractionRing.injective [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
                     [`this]))])))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `RingHom.map_mul)
                ","
                (Tactic.rwRule [] `hr)
                ","
                (Tactic.rwRule [] `hr')
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_mul)
                ","
                (Tactic.rwRule [] `Basis.to_matrix_mul_to_matrix_flip)
                ","
                (Tactic.rwRule [] `det_one)]
               "]")
              [])]))))))
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
               (Term.app
                (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
                [(termℤ "ℤ")
                 (Term.proj
                  (Term.app `b'.to_matrix [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
                  "."
                  `det)]))]
             ":="
             (Term.app
              `IsIntegral.det
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i `j]
                 []
                 "=>"
                 (Term.app `h' [(Term.hole "_") (Term.hole "_")])))]))))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r')])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr')])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
              [`this])]])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj `isUnit_iff_exists_inv "." (fieldIdx "2"))
            [(Term.anonymousCtor "⟨" [`r' "," (Term.hole "_")] "⟩")]))
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            («term_=_»
             (Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ") («term_*_» `r "*" `r')])
             "="
             (num "1"))
            (Term.byTactic'
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
                    (Term.app
                     `RingHom.map_one
                     [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.app `IsFractionRing.injective [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
                  [`this]))])))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `RingHom.map_mul)
             ","
             (Tactic.rwRule [] `hr)
             ","
             (Tactic.rwRule [] `hr')
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_mul)
             ","
             (Tactic.rwRule [] `Basis.to_matrix_mul_to_matrix_flip)
             ","
             (Tactic.rwRule [] `det_one)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `RingHom.map_mul)
         ","
         (Tactic.rwRule [] `hr)
         ","
         (Tactic.rwRule [] `hr')
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `det_mul)
         ","
         (Tactic.rwRule [] `Basis.to_matrix_mul_to_matrix_flip)
         ","
         (Tactic.rwRule [] `det_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Basis.to_matrix_mul_to_matrix_flip
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_=_»
         (Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ") («term_*_» `r "*" `r')])
         "="
         (num "1"))
        (Term.byTactic'
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
                (Term.app
                 `RingHom.map_one
                 [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.app `IsFractionRing.injective [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
              [`this]))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.app `IsFractionRing.injective [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
        [`this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `IsFractionRing.injective [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
       [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `IsFractionRing.injective [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Rat.Init.termℚ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Rat.Init.termℚ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsFractionRing.injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsFractionRing.injective [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `RingHom.map_one
           [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `RingHom.map_one [(Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Rat.Init.termℚ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Rat.Init.termℚ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.map_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ") («term_*_» `r "*" `r')])
       "="
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `algebraMap [(termℤ "ℤ") (Data.Rat.Init.termℚ "ℚ") («term_*_» `r "*" `r')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `r "*" `r')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `r "*" `r') ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Rat.Init.termℚ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Rat.Init.termℚ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Rat.Init.termℚ "ℚ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj `isUnit_iff_exists_inv "." (fieldIdx "2"))
        [(Term.anonymousCtor "⟨" [`r' "," (Term.hole "_")] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `isUnit_iff_exists_inv "." (fieldIdx "2"))
       [(Term.anonymousCtor "⟨" [`r' "," (Term.hole "_")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`r' "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `isUnit_iff_exists_inv "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `isUnit_iff_exists_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r')])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr')])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1")) [`this])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1")) [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IsIntegrallyClosed.is_integral_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
           (Term.app
            (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
            [(termℤ "ℤ")
             (Term.proj
              (Term.app `b'.to_matrix [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
              "."
              `det)]))]
         ":="
         (Term.app
          `IsIntegral.det
          [(Term.fun
            "fun"
            (Term.basicFun [`i `j] [] "=>" (Term.app `h' [(Term.hole "_") (Term.hole "_")])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsIntegral.det
       [(Term.fun
         "fun"
         (Term.basicFun [`i `j] [] "=>" (Term.app `h' [(Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`i `j] [] "=>" (Term.app `h' [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h' [(Term.hole "_") (Term.hole "_")])
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
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIntegral.det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
       [(termℤ "ℤ")
        (Term.proj
         (Term.app `b'.to_matrix [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
         "."
         `det)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `b'.to_matrix [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
       "."
       `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `b'.to_matrix [(Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b.reindex [(Term.app `b.index_equiv [`b'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b.index_equiv [`b'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.index_equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `b.index_equiv [`b']) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.reindex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `b.reindex [(Term.paren "(" (Term.app `b.index_equiv [`b']) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b'.to_matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `b'.to_matrix
      [(Term.paren
        "("
        (Term.app `b.reindex [(Term.paren "(" (Term.app `b.index_equiv [`b']) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.RingTheory.Discriminant.termis_integral', expected 'Algebra.RingTheory.Discriminant.termis_integral._@.RingTheory.Discriminant._hyg.596'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
/--
    If `b` and `b'` are `ℚ`-bases of a number field `K` such that
    `∀ i j, is_integral ℤ (b.to_matrix b' i j)` and `∀ i j, is_integral ℤ (b'.to_matrix b i j)` then
    `discr ℚ b = discr ℚ b'`. -/
  theorem
    discr_eq_discr_of_to_matrix_coeff_is_integral
    [ NumberField K ]
        { b : Basis ι ℚ K }
        { b' : Basis ι' ℚ K }
        ( h : ∀ i j , is_integral ℤ b . toMatrix b' i j )
        ( h' : ∀ i j , is_integral ℤ b' . toMatrix b i j )
      : discr ℚ b = discr ℚ b'
    :=
      by
        replace h' : ∀ i j , is_integral ℤ b'.to_matrix b.reindex b.index_equiv b' i j
          · intro i j convert h' i b.index_equiv b' . symm j simpa
          classical
            rw
                [
                  ← b.reindex b.index_equiv b' . to_matrix_map_vec_mul b'
                    ,
                    discr_of_matrix_vec_mul
                    ,
                    ← one_mul discr ℚ b
                    ,
                    Basis.coe_reindex
                    ,
                    discr_reindex
                  ]
              congr
              have
                hint
                  : is_integral ℤ b.reindex b.index_equiv b' . toMatrix b' . det
                  :=
                  IsIntegral.det fun i j => h _ _
              obtain ⟨ r , hr ⟩ := IsIntegrallyClosed.is_integral_iff . 1 hint
              have
                hunit
                  : IsUnit r
                  :=
                  by
                    have
                        : is_integral ℤ b'.to_matrix b.reindex b.index_equiv b' . det
                          :=
                          IsIntegral.det fun i j => h' _ _
                      obtain ⟨ r' , hr' ⟩ := IsIntegrallyClosed.is_integral_iff . 1 this
                      refine' isUnit_iff_exists_inv . 2 ⟨ r' , _ ⟩
                      suffices
                        algebraMap ℤ ℚ r * r' = 1
                          by
                            rw [ ← RingHom.map_one algebraMap ℤ ℚ ] at this
                              exact IsFractionRing.injective ℤ ℚ this
                      rw
                        [
                          RingHom.map_mul
                            ,
                            hr
                            ,
                            hr'
                            ,
                            ← det_mul
                            ,
                            Basis.to_matrix_mul_to_matrix_flip
                            ,
                            det_one
                          ]
              rw [ ← RingHom.map_one algebraMap ℤ ℚ , ← hr ]
              cases' Int.isUnit_iff . 1 hunit with hp hm
              · simp [ hp ]
              · simp [ hm ]
#align
  algebra.discr_eq_discr_of_to_matrix_coeff_is_integral Algebra.discr_eq_discr_of_to_matrix_coeff_is_integral

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Let `K` be the fraction field of an integrally closed domain `R` and let `L` be a finite\nseparable extension of `K`. Let `B : power_basis K L` be such that `is_integral R B.gen`.\nThen for all, `z : L` that are integral over `R`, we have\n`(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `discr_mul_is_integral_mem_adjoin [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`R]) "]")
        (Term.instBinder "[" [] (Term.app `IsSeparable [`K `L]) "]")
        (Term.instBinder "[" [] (Term.app `IsIntegrallyClosed [`R]) "]")
        (Term.instBinder "[" [] (Term.app `IsFractionRing [`R `K]) "]")
        (Term.implicitBinder "{" [`B] [":" (Term.app `PowerBasis [`K `L])] "}")
        (Term.explicitBinder
         "("
         [`hint]
         [":"
          (Term.app
           (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
           [`R (Term.proj `B "." `gen)])]
         []
         ")")
        (Term.implicitBinder "{" [`z] [":" `L] "}")
        (Term.explicitBinder
         "("
         [`hz]
         [":" (Term.app (Algebra.RingTheory.Discriminant.termis_integral "is_integral") [`R `z])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_»
         (Algebra.Group.Defs.«term_•_» (Term.app `discr [`K (Term.proj `B "." `Basis)]) " • " `z)
         "∈"
         (Term.app
          `adjoin
          [`R
           (Term.typeAscription
            "("
            («term{_}» "{" [(Term.proj `B "." `gen)] "}")
            ":"
            [(Term.app `Set [`L])]
            ")")]))))
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
              [`hinv []]
              [(Term.typeSpec
                ":"
                (Term.app `IsUnit [(Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)]))]
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
                    []
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `discr_def)]
                      "]")]
                    ["using" (Term.app `discr_is_unit_of_basis [(Term.hole "_") `B.basis])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`H []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Algebra.Group.Defs.«term_•_»
                  (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
                  " • "
                  (Term.app
                   (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `mulVec)
                   [(Term.app `B.basis.equiv_fun [`z])]))
                 "="
                 (Algebra.Group.Defs.«term_•_»
                  (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
                  " • "
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`i]
                    []
                    "=>"
                    (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))]))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.congr "congr" [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `trace_matrix_of_basis_mul_vec
                    [(Term.hole "_") (Term.hole "_")]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`cramer []]
              []
              ":="
              (Term.app
               `mul_vec_cramer
               [(Term.app `trace_matrix [`K `B.basis])
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`i]
                  []
                  "=>"
                  (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])))]))))
           []
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             (Term.forall
              "∀"
              [`i]
              []
              ","
              («term_∈_»
               (Term.app
                (Algebra.Group.Defs.«term_•_»
                 (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
                 " • "
                 (Term.app `B.basis.equiv_fun [`z]))
                [`i])
               "∈"
               (Term.typeAscription
                "("
                (Order.BoundedOrder.«term⊥» "⊥")
                ":"
                [(Term.app `Subalgebra [`R `K])]
                ")")))
             (Term.byTactic'
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
                     (Term.app `B.basis.sum_repr [`z]))
                    ","
                    (Tactic.rwRule [] `Finset.smul_sum)]
                   "]")
                  [])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `Subalgebra.sum_mem
                   [(Term.hole "_")
                    (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
                 []
                 (Mathlib.Tactic.tacticReplace_
                  "replace"
                  (Term.haveDecl (Term.haveIdDecl [`this []] [] ":=" (Term.app `this [`i]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `discr_def)
                    ","
                    (Tactic.rwRule [] `Pi.smul_apply)
                    ","
                    (Tactic.rwRule [] `mem_bot)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [`this]])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Basis.equiv_fun_apply)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_assoc)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)
                    ","
                    (Tactic.rwRule [] `algebra_map_smul)]
                   "]")
                  [])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app `Subalgebra.smul_mem [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `B.basis_eq_pow [`i]))] "]")
                  [])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `Subalgebra.pow_mem
                   [(Term.hole "_")
                    (Term.app `subset_adjoin [(Term.app `Set.mem_singleton [(Term.hole "_")])])
                    (Term.hole "_")]))])))))
           []
           (Tactic.intro "intro" [`i])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_vec_smul)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`cramer] []))])
           []
           (Mathlib.Tactic.tacticReplace_
            "replace"
            (Term.haveDecl
             (Term.haveIdDecl
              [`cramer []]
              []
              ":="
              (Term.app
               `congr_arg
               [(Term.app `mul_vec [(«term_⁻¹» (Term.app `trace_matrix [`K `B.basis]) "⁻¹")])
                `cramer]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `mul_vec_mul_vec)
              ","
              (Tactic.rwRule [] (Term.app `nonsing_inv_mul [(Term.hole "_") `hinv]))
              ","
              (Tactic.rwRule [] `mul_vec_mul_vec)
              ","
              (Tactic.rwRule [] (Term.app `nonsing_inv_mul [(Term.hole "_") `hinv]))
              ","
              (Tactic.rwRule [] `one_mul_vec)
              ","
              (Tactic.rwRule [] `one_mul_vec)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`cramer] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `congr_fun [`cramer `i]))
              ","
              (Tactic.rwRule [] `cramer_apply)
              ","
              (Tactic.rwRule [] `det_apply)]
             "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `Subalgebra.sum_mem
             [(Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [`σ (Term.hole "_")]
                []
                "=>"
                (Term.app
                 `Subalgebra.zsmul_mem
                 [(Term.hole "_")
                  (Term.app
                   `Subalgebra.prod_mem
                   [(Term.hole "_")
                    (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))])
                  (Term.hole "_")])))]))
           []
           (Classical.«tacticBy_cases_:_» "by_cases" [`hji ":"] («term_=_» `j "=" `i))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `update_column_apply)
                ","
                (Tactic.simpLemma [] [] `hji)
                ","
                (Tactic.simpLemma [] [] `eq_self_iff_true)
                ","
                (Tactic.simpLemma [] [] `PowerBasis.coe_basis)]
               "]"]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj `mem_bot "." (fieldIdx "2"))
               [(«term_<|_»
                 (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                 "<|"
                 («term_<|_»
                  `is_integral_trace
                  "<|"
                  («term_<|_»
                   (Term.app `is_integral_mul [`hz])
                   "<|"
                   (Term.app `IsIntegral.pow [`hint (Term.hole "_")]))))]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `update_column_apply)
                ","
                (Tactic.simpLemma [] [] `hji)
                ","
                (Tactic.simpLemma [] [] `PowerBasis.coe_basis)]
               "]"]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj `mem_bot "." (fieldIdx "2"))
               [(«term_<|_»
                 (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                 "<|"
                 («term_<|_»
                  `is_integral_trace
                  "<|"
                  (Term.app
                   `is_integral_mul
                   [(Term.app `IsIntegral.pow [`hint (Term.hole "_")])
                    (Term.app `IsIntegral.pow [`hint (Term.hole "_")])])))]))])])))
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
             [`hinv []]
             [(Term.typeSpec
               ":"
               (Term.app `IsUnit [(Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)]))]
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
                   []
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `discr_def)]
                     "]")]
                   ["using" (Term.app `discr_is_unit_of_basis [(Term.hole "_") `B.basis])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`H []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Algebra.Group.Defs.«term_•_»
                 (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
                 " • "
                 (Term.app
                  (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `mulVec)
                  [(Term.app `B.basis.equiv_fun [`z])]))
                "="
                (Algebra.Group.Defs.«term_•_»
                 (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
                 " • "
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`i]
                   []
                   "=>"
                   (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))]))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.congr "congr" [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `trace_matrix_of_basis_mul_vec
                   [(Term.hole "_") (Term.hole "_")]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`cramer []]
             []
             ":="
             (Term.app
              `mul_vec_cramer
              [(Term.app `trace_matrix [`K `B.basis])
               (Term.fun
                "fun"
                (Term.basicFun
                 [`i]
                 []
                 "=>"
                 (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])))]))))
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            (Term.forall
             "∀"
             [`i]
             []
             ","
             («term_∈_»
              (Term.app
               (Algebra.Group.Defs.«term_•_»
                (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
                " • "
                (Term.app `B.basis.equiv_fun [`z]))
               [`i])
              "∈"
              (Term.typeAscription
               "("
               (Order.BoundedOrder.«term⊥» "⊥")
               ":"
               [(Term.app `Subalgebra [`R `K])]
               ")")))
            (Term.byTactic'
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
                    (Term.app `B.basis.sum_repr [`z]))
                   ","
                   (Tactic.rwRule [] `Finset.smul_sum)]
                  "]")
                 [])
                []
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `Subalgebra.sum_mem
                  [(Term.hole "_")
                   (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
                []
                (Mathlib.Tactic.tacticReplace_
                 "replace"
                 (Term.haveDecl (Term.haveIdDecl [`this []] [] ":=" (Term.app `this [`i]))))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `discr_def)
                   ","
                   (Tactic.rwRule [] `Pi.smul_apply)
                   ","
                   (Tactic.rwRule [] `mem_bot)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [`this]])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Basis.equiv_fun_apply)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_assoc)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)
                   ","
                   (Tactic.rwRule [] `algebra_map_smul)]
                  "]")
                 [])
                []
                (Tactic.refine'
                 "refine'"
                 (Term.app `Subalgebra.smul_mem [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `B.basis_eq_pow [`i]))] "]")
                 [])
                []
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `Subalgebra.pow_mem
                  [(Term.hole "_")
                   (Term.app `subset_adjoin [(Term.app `Set.mem_singleton [(Term.hole "_")])])
                   (Term.hole "_")]))])))))
          []
          (Tactic.intro "intro" [`i])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_vec_smul)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`cramer] []))])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`cramer []]
             []
             ":="
             (Term.app
              `congr_arg
              [(Term.app `mul_vec [(«term_⁻¹» (Term.app `trace_matrix [`K `B.basis]) "⁻¹")])
               `cramer]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mul_vec_mul_vec)
             ","
             (Tactic.rwRule [] (Term.app `nonsing_inv_mul [(Term.hole "_") `hinv]))
             ","
             (Tactic.rwRule [] `mul_vec_mul_vec)
             ","
             (Tactic.rwRule [] (Term.app `nonsing_inv_mul [(Term.hole "_") `hinv]))
             ","
             (Tactic.rwRule [] `one_mul_vec)
             ","
             (Tactic.rwRule [] `one_mul_vec)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`cramer] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `congr_fun [`cramer `i]))
             ","
             (Tactic.rwRule [] `cramer_apply)
             ","
             (Tactic.rwRule [] `det_apply)]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `Subalgebra.sum_mem
            [(Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [`σ (Term.hole "_")]
               []
               "=>"
               (Term.app
                `Subalgebra.zsmul_mem
                [(Term.hole "_")
                 (Term.app
                  `Subalgebra.prod_mem
                  [(Term.hole "_")
                   (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))])
                 (Term.hole "_")])))]))
          []
          (Classical.«tacticBy_cases_:_» "by_cases" [`hji ":"] («term_=_» `j "=" `i))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `update_column_apply)
               ","
               (Tactic.simpLemma [] [] `hji)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `PowerBasis.coe_basis)]
              "]"]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj `mem_bot "." (fieldIdx "2"))
              [(«term_<|_»
                (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                "<|"
                («term_<|_»
                 `is_integral_trace
                 "<|"
                 («term_<|_»
                  (Term.app `is_integral_mul [`hz])
                  "<|"
                  (Term.app `IsIntegral.pow [`hint (Term.hole "_")]))))]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `update_column_apply)
               ","
               (Tactic.simpLemma [] [] `hji)
               ","
               (Tactic.simpLemma [] [] `PowerBasis.coe_basis)]
              "]"]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj `mem_bot "." (fieldIdx "2"))
              [(«term_<|_»
                (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
                "<|"
                («term_<|_»
                 `is_integral_trace
                 "<|"
                 (Term.app
                  `is_integral_mul
                  [(Term.app `IsIntegral.pow [`hint (Term.hole "_")])
                   (Term.app `IsIntegral.pow [`hint (Term.hole "_")])])))]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `update_column_apply)
           ","
           (Tactic.simpLemma [] [] `hji)
           ","
           (Tactic.simpLemma [] [] `PowerBasis.coe_basis)]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj `mem_bot "." (fieldIdx "2"))
          [(«term_<|_»
            (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
            "<|"
            («term_<|_»
             `is_integral_trace
             "<|"
             (Term.app
              `is_integral_mul
              [(Term.app `IsIntegral.pow [`hint (Term.hole "_")])
               (Term.app `IsIntegral.pow [`hint (Term.hole "_")])])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj `mem_bot "." (fieldIdx "2"))
        [(«term_<|_»
          (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
          "<|"
          («term_<|_»
           `is_integral_trace
           "<|"
           (Term.app
            `is_integral_mul
            [(Term.app `IsIntegral.pow [`hint (Term.hole "_")])
             (Term.app `IsIntegral.pow [`hint (Term.hole "_")])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `mem_bot "." (fieldIdx "2"))
       [(«term_<|_»
         (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
         "<|"
         («term_<|_»
          `is_integral_trace
          "<|"
          (Term.app
           `is_integral_mul
           [(Term.app `IsIntegral.pow [`hint (Term.hole "_")])
            (Term.app `IsIntegral.pow [`hint (Term.hole "_")])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
       "<|"
       («term_<|_»
        `is_integral_trace
        "<|"
        (Term.app
         `is_integral_mul
         [(Term.app `IsIntegral.pow [`hint (Term.hole "_")])
          (Term.app `IsIntegral.pow [`hint (Term.hole "_")])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `is_integral_trace
       "<|"
       (Term.app
        `is_integral_mul
        [(Term.app `IsIntegral.pow [`hint (Term.hole "_")])
         (Term.app `IsIntegral.pow [`hint (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_integral_mul
       [(Term.app `IsIntegral.pow [`hint (Term.hole "_")])
        (Term.app `IsIntegral.pow [`hint (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsIntegral.pow [`hint (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hint
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIntegral.pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsIntegral.pow [`hint (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsIntegral.pow [`hint (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hint
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIntegral.pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IsIntegral.pow [`hint (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_integral_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `is_integral_trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IsIntegrallyClosed.is_integral_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
      "<|"
      («term_<|_»
       `is_integral_trace
       "<|"
       (Term.app
        `is_integral_mul
        [(Term.paren "(" (Term.app `IsIntegral.pow [`hint (Term.hole "_")]) ")")
         (Term.paren "(" (Term.app `IsIntegral.pow [`hint (Term.hole "_")]) ")")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `mem_bot "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_bot
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
        [(Tactic.simpLemma [] [] `update_column_apply)
         ","
         (Tactic.simpLemma [] [] `hji)
         ","
         (Tactic.simpLemma [] [] `PowerBasis.coe_basis)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PowerBasis.coe_basis
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hji
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `update_column_apply
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
          [(Tactic.simpLemma [] [] `update_column_apply)
           ","
           (Tactic.simpLemma [] [] `hji)
           ","
           (Tactic.simpLemma [] [] `eq_self_iff_true)
           ","
           (Tactic.simpLemma [] [] `PowerBasis.coe_basis)]
          "]"]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj `mem_bot "." (fieldIdx "2"))
          [(«term_<|_»
            (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
            "<|"
            («term_<|_»
             `is_integral_trace
             "<|"
             («term_<|_»
              (Term.app `is_integral_mul [`hz])
              "<|"
              (Term.app `IsIntegral.pow [`hint (Term.hole "_")]))))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj `mem_bot "." (fieldIdx "2"))
        [(«term_<|_»
          (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
          "<|"
          («term_<|_»
           `is_integral_trace
           "<|"
           («term_<|_»
            (Term.app `is_integral_mul [`hz])
            "<|"
            (Term.app `IsIntegral.pow [`hint (Term.hole "_")]))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `mem_bot "." (fieldIdx "2"))
       [(«term_<|_»
         (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
         "<|"
         («term_<|_»
          `is_integral_trace
          "<|"
          («term_<|_»
           (Term.app `is_integral_mul [`hz])
           "<|"
           (Term.app `IsIntegral.pow [`hint (Term.hole "_")]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
       "<|"
       («term_<|_»
        `is_integral_trace
        "<|"
        («term_<|_»
         (Term.app `is_integral_mul [`hz])
         "<|"
         (Term.app `IsIntegral.pow [`hint (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `is_integral_trace
       "<|"
       («term_<|_»
        (Term.app `is_integral_mul [`hz])
        "<|"
        (Term.app `IsIntegral.pow [`hint (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `is_integral_mul [`hz])
       "<|"
       (Term.app `IsIntegral.pow [`hint (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsIntegral.pow [`hint (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hint
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIntegral.pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `is_integral_mul [`hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_integral_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `is_integral_trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IsIntegrallyClosed.is_integral_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.proj `IsIntegrallyClosed.is_integral_iff "." (fieldIdx "1"))
      "<|"
      («term_<|_»
       `is_integral_trace
       "<|"
       («term_<|_»
        (Term.app `is_integral_mul [`hz])
        "<|"
        (Term.app `IsIntegral.pow [`hint (Term.hole "_")]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `mem_bot "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_bot
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
        [(Tactic.simpLemma [] [] `update_column_apply)
         ","
         (Tactic.simpLemma [] [] `hji)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `PowerBasis.coe_basis)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PowerBasis.coe_basis
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hji
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `update_column_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`hji ":"] («term_=_» `j "=" `i))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `j "=" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Subalgebra.sum_mem
        [(Term.hole "_")
         (Term.fun
          "fun"
          (Term.basicFun
           [`σ (Term.hole "_")]
           []
           "=>"
           (Term.app
            `Subalgebra.zsmul_mem
            [(Term.hole "_")
             (Term.app
              `Subalgebra.prod_mem
              [(Term.hole "_")
               (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))])
             (Term.hole "_")])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subalgebra.sum_mem
       [(Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [`σ (Term.hole "_")]
          []
          "=>"
          (Term.app
           `Subalgebra.zsmul_mem
           [(Term.hole "_")
            (Term.app
             `Subalgebra.prod_mem
             [(Term.hole "_")
              (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))])
            (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`σ (Term.hole "_")]
        []
        "=>"
        (Term.app
         `Subalgebra.zsmul_mem
         [(Term.hole "_")
          (Term.app
           `Subalgebra.prod_mem
           [(Term.hole "_")
            (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))])
          (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subalgebra.zsmul_mem
       [(Term.hole "_")
        (Term.app
         `Subalgebra.prod_mem
         [(Term.hole "_")
          (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))])
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
       `Subalgebra.prod_mem
       [(Term.hole "_")
        (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra.prod_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Subalgebra.prod_mem
      [(Term.hole "_")
       (Term.fun "fun" (Term.basicFun [`j (Term.hole "_")] [] "=>" (Term.hole "_")))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra.zsmul_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra.sum_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `congr_fun [`cramer `i]))
         ","
         (Tactic.rwRule [] `cramer_apply)
         ","
         (Tactic.rwRule [] `det_apply)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cramer_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_fun [`cramer `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cramer
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_fun
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
        [(Tactic.rwRule [] `mul_vec_mul_vec)
         ","
         (Tactic.rwRule [] (Term.app `nonsing_inv_mul [(Term.hole "_") `hinv]))
         ","
         (Tactic.rwRule [] `mul_vec_mul_vec)
         ","
         (Tactic.rwRule [] (Term.app `nonsing_inv_mul [(Term.hole "_") `hinv]))
         ","
         (Tactic.rwRule [] `one_mul_vec)
         ","
         (Tactic.rwRule [] `one_mul_vec)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`cramer] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cramer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul_vec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul_vec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nonsing_inv_mul [(Term.hole "_") `hinv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hinv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nonsing_inv_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_vec_mul_vec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nonsing_inv_mul [(Term.hole "_") `hinv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hinv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nonsing_inv_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_vec_mul_vec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl
         [`cramer []]
         []
         ":="
         (Term.app
          `congr_arg
          [(Term.app `mul_vec [(«term_⁻¹» (Term.app `trace_matrix [`K `B.basis]) "⁻¹")])
           `cramer]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.app `mul_vec [(«term_⁻¹» (Term.app `trace_matrix [`K `B.basis]) "⁻¹")]) `cramer])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cramer
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mul_vec [(«term_⁻¹» (Term.app `trace_matrix [`K `B.basis]) "⁻¹")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (Term.app `trace_matrix [`K `B.basis]) "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `trace_matrix [`K `B.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace_matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `trace_matrix [`K `B.basis])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_vec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `mul_vec
      [(«term_⁻¹» (Term.paren "(" (Term.app `trace_matrix [`K `B.basis]) ")") "⁻¹")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `H)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_vec_smul)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`cramer] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cramer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_vec_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (Term.forall
         "∀"
         [`i]
         []
         ","
         («term_∈_»
          (Term.app
           (Algebra.Group.Defs.«term_•_»
            (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
            " • "
            (Term.app `B.basis.equiv_fun [`z]))
           [`i])
          "∈"
          (Term.typeAscription
           "("
           (Order.BoundedOrder.«term⊥» "⊥")
           ":"
           [(Term.app `Subalgebra [`R `K])]
           ")")))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `B.basis.sum_repr [`z]))
               ","
               (Tactic.rwRule [] `Finset.smul_sum)]
              "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `Subalgebra.sum_mem
              [(Term.hole "_") (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
            []
            (Mathlib.Tactic.tacticReplace_
             "replace"
             (Term.haveDecl (Term.haveIdDecl [`this []] [] ":=" (Term.app `this [`i]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `discr_def)
               ","
               (Tactic.rwRule [] `Pi.smul_apply)
               ","
               (Tactic.rwRule [] `mem_bot)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                   [])]
                 "⟩")])]
             []
             [":=" [`this]])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Basis.equiv_fun_apply)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_assoc)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)
               ","
               (Tactic.rwRule [] `algebra_map_smul)]
              "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app `Subalgebra.smul_mem [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `B.basis_eq_pow [`i]))] "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `Subalgebra.pow_mem
              [(Term.hole "_")
               (Term.app `subset_adjoin [(Term.app `Set.mem_singleton [(Term.hole "_")])])
               (Term.hole "_")]))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Subalgebra.pow_mem
        [(Term.hole "_")
         (Term.app `subset_adjoin [(Term.app `Set.mem_singleton [(Term.hole "_")])])
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subalgebra.pow_mem
       [(Term.hole "_")
        (Term.app `subset_adjoin [(Term.app `Set.mem_singleton [(Term.hole "_")])])
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
      (Term.app `subset_adjoin [(Term.app `Set.mem_singleton [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.mem_singleton [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.mem_singleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Set.mem_singleton [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `subset_adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `subset_adjoin
      [(Term.paren "(" (Term.app `Set.mem_singleton [(Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra.pow_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `B.basis_eq_pow [`i]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `B.basis_eq_pow [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `B.basis_eq_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app `Subalgebra.smul_mem [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subalgebra.smul_mem [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra.smul_mem
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)
         ","
         (Tactic.rwRule [] `algebra_map_smul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `algebra_map_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Basis.equiv_fun_apply)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Basis.equiv_fun_apply
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
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `discr_def)
         ","
         (Tactic.rwRule [] `Pi.smul_apply)
         ","
         (Tactic.rwRule [] `mem_bot)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_bot
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `discr_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl (Term.haveIdDecl [`this []] [] ":=" (Term.app `this [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Subalgebra.sum_mem
        [(Term.hole "_") (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subalgebra.sum_mem
       [(Term.hole "_") (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i `hi] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra.sum_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `B.basis.sum_repr [`z]))
         ","
         (Tactic.rwRule [] `Finset.smul_sum)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.smul_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `B.basis.sum_repr [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `B.basis.sum_repr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`i]
       []
       ","
       («term_∈_»
        (Term.app
         (Algebra.Group.Defs.«term_•_»
          (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
          " • "
          (Term.app `B.basis.equiv_fun [`z]))
         [`i])
        "∈"
        (Term.typeAscription
         "("
         (Order.BoundedOrder.«term⊥» "⊥")
         ":"
         [(Term.app `Subalgebra [`R `K])]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.app
        (Algebra.Group.Defs.«term_•_»
         (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
         " • "
         (Term.app `B.basis.equiv_fun [`z]))
        [`i])
       "∈"
       (Term.typeAscription
        "("
        (Order.BoundedOrder.«term⊥» "⊥")
        ":"
        [(Term.app `Subalgebra [`R `K])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Order.BoundedOrder.«term⊥» "⊥")
       ":"
       [(Term.app `Subalgebra [`R `K])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subalgebra [`R `K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subalgebra
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Algebra.Group.Defs.«term_•_»
        (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
        " • "
        (Term.app `B.basis.equiv_fun [`z]))
       [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Group.Defs.«term_•_»
       (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
       " • "
       (Term.app `B.basis.equiv_fun [`z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `B.basis.equiv_fun [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `B.basis.equiv_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `trace_matrix [`K `B.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace_matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `trace_matrix [`K `B.basis])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 73, (some 73, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_»
      (Term.proj (Term.paren "(" (Term.app `trace_matrix [`K `B.basis]) ")") "." `det)
      " • "
      (Term.app `B.basis.equiv_fun [`z]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`cramer []]
         []
         ":="
         (Term.app
          `mul_vec_cramer
          [(Term.app `trace_matrix [`K `B.basis])
           (Term.fun
            "fun"
            (Term.basicFun
             [`i]
             []
             "=>"
             (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_vec_cramer
       [(Term.app `trace_matrix [`K `B.basis])
        (Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `z "*" (Term.app `B.basis [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `B.basis [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» `z "*" (Term.app `B.basis [`i]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `trace_matrix [`K `B.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace_matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `trace_matrix [`K `B.basis])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_vec_cramer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`H []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Algebra.Group.Defs.«term_•_»
             (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
             " • "
             (Term.app
              (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `mulVec)
              [(Term.app `B.basis.equiv_fun [`z])]))
            "="
            (Algebra.Group.Defs.«term_•_»
             (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
             " • "
             (Term.fun
              "fun"
              (Term.basicFun
               [`i]
               []
               "=>"
               (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))]))))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.congr "congr" [])
             []
             (Tactic.exact
              "exact"
              (Term.app `trace_matrix_of_basis_mul_vec [(Term.hole "_") (Term.hole "_")]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.congr "congr" [])
          []
          (Tactic.exact
           "exact"
           (Term.app `trace_matrix_of_basis_mul_vec [(Term.hole "_") (Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `trace_matrix_of_basis_mul_vec [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `trace_matrix_of_basis_mul_vec [(Term.hole "_") (Term.hole "_")])
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
      `trace_matrix_of_basis_mul_vec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Algebra.Group.Defs.«term_•_»
        (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
        " • "
        (Term.app
         (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `mulVec)
         [(Term.app `B.basis.equiv_fun [`z])]))
       "="
       (Algebra.Group.Defs.«term_•_»
        (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
        " • "
        (Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
       " • "
       (Term.fun
        "fun"
        (Term.basicFun
         [`i]
         []
         "=>"
         (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `trace [`K `L («term_*_» `z "*" (Term.app `B.basis [`i]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `z "*" (Term.app `B.basis [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `B.basis [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» `z "*" (Term.app `B.basis [`i]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `trace_matrix [`K `B.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace_matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `trace_matrix [`K `B.basis])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_•_»
       (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
       " • "
       (Term.app
        (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `mulVec)
        [(Term.app `B.basis.equiv_fun [`z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `mulVec)
       [(Term.app `B.basis.equiv_fun [`z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `B.basis.equiv_fun [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `B.basis.equiv_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `B.basis.equiv_fun [`z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `mulVec)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `trace_matrix [`K `B.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace_matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `trace_matrix [`K `B.basis])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `trace_matrix [`K `B.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace_matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `trace_matrix [`K `B.basis])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hinv []]
         [(Term.typeSpec
           ":"
           (Term.app `IsUnit [(Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)]))]
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
               []
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `discr_def)]
                 "]")]
               ["using" (Term.app `discr_is_unit_of_basis [(Term.hole "_") `B.basis])]))]))))))
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
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `discr_def)]
              "]")]
            ["using" (Term.app `discr_is_unit_of_basis [(Term.hole "_") `B.basis])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `discr_def)]
          "]")]
        ["using" (Term.app `discr_is_unit_of_basis [(Term.hole "_") `B.basis])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `discr_is_unit_of_basis [(Term.hole "_") `B.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `discr_is_unit_of_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `discr_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsUnit [(Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `trace_matrix [`K `B.basis]) "." `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `trace_matrix [`K `B.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace_matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `trace_matrix [`K `B.basis])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_»
       (Algebra.Group.Defs.«term_•_» (Term.app `discr [`K (Term.proj `B "." `Basis)]) " • " `z)
       "∈"
       (Term.app
        `adjoin
        [`R
         (Term.typeAscription
          "("
          («term{_}» "{" [(Term.proj `B "." `gen)] "}")
          ":"
          [(Term.app `Set [`L])]
          ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `adjoin
       [`R
        (Term.typeAscription
         "("
         («term{_}» "{" [(Term.proj `B "." `gen)] "}")
         ":"
         [(Term.app `Set [`L])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term{_}» "{" [(Term.proj `B "." `gen)] "}")
       ":"
       [(Term.app `Set [`L])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [`L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [(Term.proj `B "." `gen)] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `B "." `gen)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_•_» (Term.app `discr [`K (Term.proj `B "." `Basis)]) " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.app `discr [`K (Term.proj `B "." `Basis)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `B "." `Basis)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `discr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Algebra.RingTheory.Discriminant.termis_integral "is_integral") [`R `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.RingTheory.Discriminant.termis_integral "is_integral")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.RingTheory.Discriminant.termis_integral', expected 'Algebra.RingTheory.Discriminant.termis_integral._@.RingTheory.Discriminant._hyg.596'
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
/--
    Let `K` be the fraction field of an integrally closed domain `R` and let `L` be a finite
    separable extension of `K`. Let `B : power_basis K L` be such that `is_integral R B.gen`.
    Then for all, `z : L` that are integral over `R`, we have
    `(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`. -/
  theorem
    discr_mul_is_integral_mem_adjoin
    [ IsDomain R ]
        [ IsSeparable K L ]
        [ IsIntegrallyClosed R ]
        [ IsFractionRing R K ]
        { B : PowerBasis K L }
        ( hint : is_integral R B . gen )
        { z : L }
        ( hz : is_integral R z )
      : discr K B . Basis • z ∈ adjoin R ( { B . gen } : Set L )
    :=
      by
        have
            hinv
              : IsUnit trace_matrix K B.basis . det
              :=
              by simpa [ ← discr_def ] using discr_is_unit_of_basis _ B.basis
          have
            H
              :
                trace_matrix K B.basis . det • trace_matrix K B.basis . mulVec B.basis.equiv_fun z
                  =
                  trace_matrix K B.basis . det • fun i => trace K L z * B.basis i
              :=
              by congr exact trace_matrix_of_basis_mul_vec _ _
          have cramer := mul_vec_cramer trace_matrix K B.basis fun i => trace K L z * B.basis i
          suffices
            ∀ i , trace_matrix K B.basis . det • B.basis.equiv_fun z i ∈ ( ⊥ : Subalgebra R K )
              by
                rw [ ← B.basis.sum_repr z , Finset.smul_sum ]
                  refine' Subalgebra.sum_mem _ fun i hi => _
                  replace this := this i
                  rw [ ← discr_def , Pi.smul_apply , mem_bot ] at this
                  obtain ⟨ r , hr ⟩ := this
                  rw [ Basis.equiv_fun_apply ] at hr
                  rw [ ← smul_assoc , ← hr , algebra_map_smul ]
                  refine' Subalgebra.smul_mem _ _ _
                  rw [ B.basis_eq_pow i ]
                  refine' Subalgebra.pow_mem _ subset_adjoin Set.mem_singleton _ _
          intro i
          rw [ ← H , ← mul_vec_smul ] at cramer
          replace cramer := congr_arg mul_vec trace_matrix K B.basis ⁻¹ cramer
          rw
            [
              mul_vec_mul_vec
                ,
                nonsing_inv_mul _ hinv
                ,
                mul_vec_mul_vec
                ,
                nonsing_inv_mul _ hinv
                ,
                one_mul_vec
                ,
                one_mul_vec
              ]
            at cramer
          rw [ ← congr_fun cramer i , cramer_apply , det_apply ]
          refine'
            Subalgebra.sum_mem
              _ fun σ _ => Subalgebra.zsmul_mem _ Subalgebra.prod_mem _ fun j _ => _ _
          by_cases hji : j = i
          ·
            simp only [ update_column_apply , hji , eq_self_iff_true , PowerBasis.coe_basis ]
              exact
                mem_bot . 2
                  IsIntegrallyClosed.is_integral_iff . 1
                    <|
                    is_integral_trace <| is_integral_mul hz <| IsIntegral.pow hint _
          ·
            simp only [ update_column_apply , hji , PowerBasis.coe_basis ]
              exact
                mem_bot . 2
                  IsIntegrallyClosed.is_integral_iff . 1
                    <|
                    is_integral_trace <| is_integral_mul IsIntegral.pow hint _ IsIntegral.pow hint _
#align algebra.discr_mul_is_integral_mem_adjoin Algebra.discr_mul_is_integral_mem_adjoin

end Integral

end Field

end Discr

end Algebra

