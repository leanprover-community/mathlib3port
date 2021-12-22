import Mathbin.Data.Polynomial.Derivative
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.RingTheory.Polynomial.Pochhammer
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.LinearAlgebra.LinearIndependent
import Mathbin.Data.MvPolynomial.Pderiv

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernstein_polynomial (R : Type*) [comm_ring R] (n ν : ℕ) : polynomial R :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(finset.range (n + 1)).sum (λ ν, bernstein_polynomial R n ν) = 1`
* `(finset.range (n + 1)).sum (λ ν, ν • bernstein_polynomial R n ν) = n • X`
* `(finset.range (n + 1)).sum (λ ν, (ν * (ν-1)) • bernstein_polynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `analysis.special_functions.bernstein`, which defines the Bernstein approximations
of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly to `f`.
-/


noncomputable section

open nat (choose)

open polynomial (x)

variable (R : Type _) [CommRingₓ R]

/-- 
`bernstein_polynomial R n ν` is `(choose n ν) * X^ν * (1 - X)^(n - ν)`.

Although the coefficients are integers, it is convenient to work over an arbitrary commutative ring.
-/
def bernsteinPolynomial (n ν : ℕ) : Polynomial R :=
  (choose n ν*X^ν)*1 - X^n - ν

example : bernsteinPolynomial ℤ 3 2 = (3*X^2) - 3*X^3 := by
  norm_num [bernsteinPolynomial, choose]
  ring

namespace bernsteinPolynomial

theorem eq_zero_of_lt {n ν : ℕ} (h : n < ν) : bernsteinPolynomial R n ν = 0 := by
  simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]

section

variable {R} {S : Type _} [CommRingₓ S]

@[simp]
theorem map (f : R →+* S) (n ν : ℕ) : (bernsteinPolynomial R n ν).map f = bernsteinPolynomial S n ν := by
  simp [bernsteinPolynomial]

end

theorem flip (n ν : ℕ) (h : ν ≤ n) : (bernsteinPolynomial R n ν).comp (1 - X) = bernsteinPolynomial R n (n - ν) := by
  dsimp [bernsteinPolynomial]
  simp [h, tsub_tsub_assoc, mul_right_commₓ]

theorem flip' (n ν : ℕ) (h : ν ≤ n) : bernsteinPolynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X) := by
  rw [← flip _ _ _ h, Polynomial.comp_assoc]
  simp

theorem eval_at_0 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0 := by
  dsimp [bernsteinPolynomial]
  split_ifs
  ·
    subst h
    simp
  ·
    simp [zero_pow (Nat.pos_of_ne_zeroₓ h)]

theorem eval_at_1 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0 := by
  dsimp [bernsteinPolynomial]
  split_ifs
  ·
    subst h
    simp
  ·
    obtain w | w := (n - ν).eq_zero_or_pos
    ·
      simp [Nat.choose_eq_zero_of_lt ((tsub_eq_zero_iff_le.mp w).lt_of_ne (Ne.symm h))]
    ·
      simp [zero_pow w]

theorem derivative_succ_aux (n ν : ℕ) :
    (bernsteinPolynomial R (n+1) (ν+1)).derivative = (n+1)*bernsteinPolynomial R n ν - bernsteinPolynomial R n (ν+1) :=
  by
  dsimp [bernsteinPolynomial]
  suffices
    ((((↑(n+1).choose (ν+1))*((↑ν)+1)*X^ν)*1 - X^n - ν) - ((↑(n+1).choose (ν+1))*X^ν+1)*(↑(n - ν))*1 - X^n - ν - 1) =
      ((↑n)+1)*(((↑n.choose ν)*X^ν)*1 - X^n - ν) - ((↑n.choose (ν+1))*X^ν+1)*1 - X^n - ν+1by
    simpa [Polynomial.derivative_pow, ← sub_eq_add_neg]
  conv_rhs => rw [mul_sub]
  refine' congr (congr_argₓ Sub.sub _) _
  ·
    simp only [← mul_assocₓ]
    refine' congr (congr_argₓ (·*·) (congr (congr_argₓ (·*·) _) rfl)) rfl
    exact_mod_cast congr_argₓ (fun m : ℕ => (m : Polynomial R)) (Nat.succ_mul_choose_eq n ν).symm
  ·
    rw [← tsub_add_eq_tsub_tsub, ← mul_assocₓ, ← mul_assocₓ]
    congr 1
    rw [mul_commₓ]
    rw [← mul_assocₓ, ← mul_assocₓ]
    congr 1
    norm_cast
    congr 1
    convert (Nat.choose_mul_succ_eq n (ν+1)).symm using 1
    ·
      convert mul_commₓ _ _ using 2
      simp
    ·
      apply mul_commₓ

theorem derivative_succ (n ν : ℕ) :
    (bernsteinPolynomial R n (ν+1)).derivative =
      n*bernsteinPolynomial R (n - 1) ν - bernsteinPolynomial R (n - 1) (ν+1) :=
  by
  cases n
  ·
    simp [bernsteinPolynomial]
  ·
    apply derivative_succ_aux

theorem derivative_zero (n : ℕ) : (bernsteinPolynomial R n 0).derivative = (-n)*bernsteinPolynomial R (n - 1) 0 := by
  dsimp [bernsteinPolynomial]
  simp [Polynomial.derivative_pow]

theorem iterate_derivative_at_0_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < ν → ((Polynomial.derivative^[k]) (bernsteinPolynomial R n ν)).eval 0 = 0 := by
  cases ν
  ·
    rintro ⟨⟩
  ·
    rw [Nat.lt_succ_iffₓ]
    induction' k with k ih generalizing n ν
    ·
      simp [eval_at_0]
    ·
      simp only [derivative_succ, Int.coe_nat_eq_zero, Int.nat_cast_eq_coe_nat, mul_eq_zero, Function.comp_app,
        Function.iterate_succ, Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_cast_nat_mul,
        Polynomial.eval_mul, Polynomial.eval_nat_cast, Polynomial.eval_sub]
      intro h
      apply mul_eq_zero_of_right
      rw [ih _ _ (Nat.le_of_succ_leₓ h), sub_zero]
      convert ih _ _ (Nat.pred_le_predₓ h)
      exact (Nat.succ_pred_eq_of_posₓ (k.succ_pos.trans_le h)).symm

@[simp]
theorem iterate_derivative_succ_at_0_eq_zero (n ν : ℕ) :
    ((Polynomial.derivative^[ν]) (bernsteinPolynomial R n (ν+1))).eval 0 = 0 :=
  iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

open Polynomial

@[simp]
theorem iterate_derivative_at_0 (n ν : ℕ) :
    ((Polynomial.derivative^[ν]) (bernsteinPolynomial R n ν)).eval 0 = (pochhammer R ν).eval (n - (ν - 1) : ℕ) := by
  by_cases' h : ν ≤ n
  ·
    induction' ν with ν ih generalizing n h
    ·
      simp [eval_at_0]
    ·
      have h' : ν ≤ n - 1 := le_tsub_of_add_le_right h
      simp only [derivative_succ, ih (n - 1) h', iterate_derivative_succ_at_0_eq_zero, Nat.succ_sub_succ_eq_sub,
        tsub_zero, sub_zero, iterate_derivative_sub, iterate_derivative_cast_nat_mul, eval_one, eval_mul, eval_add,
        eval_sub, eval_X, eval_comp, eval_nat_cast, Function.comp_app, Function.iterate_succ, pochhammer_succ_left]
      obtain rfl | h'' := ν.eq_zero_or_pos
      ·
        simp
      ·
        have : n - 1 - (ν - 1) = n - ν := by
          rw [← Nat.succ_le_iff] at h''
          rw [← tsub_add_eq_tsub_tsub, add_commₓ, tsub_add_cancel_of_le h'']
        rw [this, pochhammer_eval_succ]
        rw_mod_cast [tsub_add_cancel_of_le (h'.trans n.pred_le)]
  ·
    simp only [not_leₓ] at h
    rw [tsub_eq_zero_iff_le.mpr (Nat.le_pred_of_lt h), eq_zero_of_lt R h]
    simp [pos_iff_ne_zero.mp (pos_of_gt h)]

theorem iterate_derivative_at_0_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    ((Polynomial.derivative^[ν]) (bernsteinPolynomial R n ν)).eval 0 ≠ 0 := by
  simp only [Int.coe_nat_eq_zero, bernsteinPolynomial.iterate_derivative_at_0, Ne.def, Nat.cast_eq_zero]
  simp only [← pochhammer_eval_cast]
  norm_cast
  apply ne_of_gtₓ
  obtain rfl | h' := Nat.eq_zero_or_posₓ ν
  ·
    simp
  ·
    rw [← Nat.succ_pred_eq_of_posₓ h'] at h
    exact pochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_leₓ h))

/-!
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/


theorem iterate_derivative_at_1_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < n - ν → ((Polynomial.derivative^[k]) (bernsteinPolynomial R n ν)).eval 1 = 0 := by
  intro w
  rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
  simp [Polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w]

@[simp]
theorem iterate_derivative_at_1 (n ν : ℕ) (h : ν ≤ n) :
    ((Polynomial.derivative^[n - ν]) (bernsteinPolynomial R n ν)).eval 1 =
      (-1^n - ν)*(pochhammer R (n - ν)).eval (ν+1) :=
  by
  rw [flip' _ _ _ h]
  simp [Polynomial.eval_comp, h]
  obtain rfl | h' := h.eq_or_lt
  ·
    simp
  ·
    congr
    norm_cast
    rw [← tsub_add_eq_tsub_tsub, tsub_tsub_cancel_of_le (nat.succ_le_iff.mpr h')]

theorem iterate_derivative_at_1_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    ((Polynomial.derivative^[n - ν]) (bernsteinPolynomial R n ν)).eval 1 ≠ 0 := by
  rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h, Ne.def, neg_one_pow_mul_eq_zero_iff, ← Nat.cast_succ, ←
    pochhammer_eval_cast, ← Nat.cast_zero, Nat.cast_inj]
  exact (pochhammer_pos _ _ (Nat.succ_posₓ ν)).ne'

open Submodule

theorem linear_independent_aux (n k : ℕ) (h : k ≤ n+1) :
    LinearIndependent ℚ fun ν : Finₓ k => bernsteinPolynomial ℚ n ν := by
  induction' k with k ih
  ·
    apply linear_independent_empty_type
  ·
    apply linear_independent_fin_succ'.mpr
    fconstructor
    ·
      exact ih (le_of_ltₓ h)
    ·
      clear ih
      simp only [Nat.succ_eq_add_one, add_le_add_iff_right] at h
      simp only [Finₓ.coe_last, Finₓ.init_def]
      dsimp
      apply not_mem_span_of_apply_not_mem_span_image (Polynomial.derivativeLhom ℚ^n - k)
      simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image]
      intro p m
      apply_fun Polynomial.eval (1 : ℚ)
      simp only [Polynomial.derivative_lhom_coe, LinearMap.pow_apply]
      suffices ((Polynomial.derivative^[n - k]) p).eval 1 = 0 by
        rw [this]
        exact (iterate_derivative_at_1_ne_zero ℚ n k h).symm
      apply span_induction m
      ·
        simp
        rintro ⟨a, w⟩
        simp only [Finₓ.coe_mk]
        rw [iterate_derivative_at_1_eq_zero_of_lt ℚ n ((tsub_lt_tsub_iff_left_of_le h).mpr w)]
      ·
        simp
      ·
        intro x y hx hy
        simp [hx, hy]
      ·
        intro a x h
        simp [h]

/-- 
The Bernstein polynomials are linearly independent.

We prove by induction that the collection of `bernstein_polynomial n ν` for `ν = 0, ..., k`
are linearly independent.
The inductive step relies on the observation that the `(n-k)`-th derivative, evaluated at 1,
annihilates `bernstein_polynomial n ν` for `ν < k`, but has a nonzero value at `ν = k`.
-/
theorem LinearIndependent (n : ℕ) : LinearIndependent ℚ fun ν : Finₓ (n+1) => bernsteinPolynomial ℚ n ν :=
  linear_independent_aux n (n+1) (le_reflₓ _)

theorem Sum (n : ℕ) : ((Finset.range (n+1)).Sum fun ν => bernsteinPolynomial R n ν) = 1 := by
  conv => congr congr skip ext dsimp [bernsteinPolynomial]rw [mul_assocₓ, mul_commₓ]
  rw [← add_pow]
  simp

open Polynomial

open MvPolynomial

-- failed to format: format: uncaught backtrack exception
theorem
  sum_smul
  ( n : ℕ ) : ( ( Finset.range ( n + 1 ) ) . Sum fun ν => ν • bernsteinPolynomial R n ν ) = n • X
  :=
    by
      let x : MvPolynomial Bool R := MvPolynomial.x tt
        let y : MvPolynomial Bool R := MvPolynomial.x ff
        have pderiv_tt_x : pderiv tt x = 1 := by simp [ x ]
        have pderiv_tt_y : pderiv tt y = 0 := by simp [ pderiv_X , y ]
        let e : Bool → Polynomial R := fun i => cond i X ( 1 - X )
        have h : ( ( x + y ) ^ n ) = ( ( x + y ) ^ n ) := rfl
        apply_fun pderiv tt at h
        apply_fun aeval e at h
        apply_fun fun p => p * X at h
        have
          w
            :
              ∀
                k : ℕ
                ,
                ( ( ( ( ( ↑ k ) * Polynomial.x ^ k - 1 ) * 1 - Polynomial.x ^ n - k ) * ↑ n.choose k ) * Polynomial.x )
                  =
                  k • bernsteinPolynomial R n k
            :=
            by
              rintro ( _ | k )
                · simp
                ·
                  dsimp [ bernsteinPolynomial ]
                    simp only [ ← nat_cast_mul , Nat.succ_eq_add_one , Nat.add_succ_sub_one , add_zeroₓ , pow_succₓ ]
                    push_cast
                    ring
        conv
          at h
          =>
          lhs
            rw [ add_pow , ( pderiv tt ) . map_sum , ( MvPolynomial.aeval e ) . map_sum , Finset.sum_mul ]
            apply_congr
            skip
            simp [ pderiv_mul , pderiv_tt_x , pderiv_tt_y , e , w ]
        conv at h => rhs rw [ pderiv_pow , ( pderiv tt ) . map_add , pderiv_tt_x , pderiv_tt_y ] simp [ e ]
        simpa using h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_mul_smul [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      (Term.proj (Term.app `Finset.range [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." `Sum)
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`ν] [])]
         "=>"
         (Algebra.Group.Defs.«term_•_»
          (Finset.Data.Finset.Fold.«term_*_» `ν "*" («term_-_» `ν "-" (numLit "1")))
          " • "
          (Term.app `bernsteinPolynomial [`R `n `ν]))))])
     "="
     (Algebra.Group.Defs.«term_•_»
      (Finset.Data.Finset.Fold.«term_*_» `n "*" («term_-_» `n "-" (numLit "1")))
      " • "
      (Cardinal.SetTheory.Cardinal.«term_^_» `X "^" (numLit "2"))))))
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
           `x
           [(Term.typeSpec ":" (Term.app `MvPolynomial [`Bool `R]))]
           ":="
           (Term.app `MvPolynomial.x [`tt]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `y
           [(Term.typeSpec ":" (Term.app `MvPolynomial [`Bool `R]))]
           ":="
           (Term.app `MvPolynomial.x [`ff]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`pderiv_tt_x []]
           [(Term.typeSpec ":" («term_=_» (Term.app `pderiv [`tt `x]) "=" (numLit "1")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `x)] "]"] []) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`pderiv_tt_y []]
           [(Term.typeSpec ":" («term_=_» (Term.app `pderiv [`tt `y]) "=" (numLit "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["[" [(Tactic.simpLemma [] [] `pderiv_X) "," (Tactic.simpLemma [] [] `y)] "]"]
                 [])
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `e
           [(Term.typeSpec ":" (Term.arrow `Bool "→" (Term.app `Polynomial [`R])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`i] [])]
             "=>"
             (Term.app `cond [`i `X («term_-_» (numLit "1") "-" `X)]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_+_» `x "+" `y) "^" `n)
              "="
              (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_+_» `x "+" `y) "^" `n)))]
           ":="
           `rfl)))
        [])
       (group
        (Tactic.applyFun "apply_fun" (Term.app `pderiv [`tt]) [(Tactic.location "at" (Tactic.locationHyp [`h] []))] [])
        [])
       (group
        (Tactic.applyFun "apply_fun" (Term.app `pderiv [`tt]) [(Tactic.location "at" (Tactic.locationHyp [`h] []))] [])
        [])
       (group
        (Tactic.applyFun "apply_fun" (Term.app `aeval [`e]) [(Tactic.location "at" (Tactic.locationHyp [`h] []))] [])
        [])
       (group
        (Tactic.applyFun
         "apply_fun"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`p] [])]
           "=>"
           (Finset.Data.Finset.Fold.«term_*_» `p "*" (Cardinal.SetTheory.Cardinal.«term_^_» `X "^" (numLit "2")))))
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))]
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`w []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
              ","
              («term_=_»
               (Finset.Data.Finset.Fold.«term_*_»
                (Finset.Data.Finset.Fold.«term_*_»
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Init.Coe.«term↑_» "↑" `k)
                   "*"
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Init.Coe.«term↑_» "↑" («term_-_» `k "-" (numLit "1")))
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     `Polynomial.x
                     "^"
                     («term_-_» («term_-_» `k "-" (numLit "1")) "-" (numLit "1")))))
                  "*"
                  (Cardinal.SetTheory.Cardinal.«term_^_»
                   («term_-_» (numLit "1") "-" `Polynomial.x)
                   "^"
                   («term_-_» `n "-" `k)))
                 "*"
                 (Init.Coe.«term↑_» "↑" (Term.app `n.choose [`k])))
                "*"
                (Cardinal.SetTheory.Cardinal.«term_^_» `Polynomial.x "^" (numLit "2")))
               "="
               (Algebra.Group.Defs.«term_•_»
                (Finset.Data.Finset.Fold.«term_*_» `k "*" («term_-_» `k "-" (numLit "1")))
                " • "
                (Term.app `bernsteinPolynomial [`R `n `k])))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one
                   (Tactic.rcasesPat.paren
                    "("
                    (Tactic.rcasesPatLo
                     (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_") "|" (Tactic.rcasesPat.one `k)])
                     [])
                    ")"))]
                 [])
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] `k)]
                      ["with"
                       (Tactic.rcasesPat.paren
                        "("
                        (Tactic.rcasesPatLo
                         (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_") "|" (Tactic.rcasesPat.one `k)])
                         [])
                        ")")])
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `bernsteinPolynomial)] "]"] [] [])
                          [])
                         (group
                          (Tactic.simp
                           "simp"
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] ["←"] `nat_cast_mul)
                             ","
                             (Tactic.simpLemma [] [] `Nat.succ_eq_add_one)
                             ","
                             (Tactic.simpLemma [] [] `Nat.add_succ_sub_one)
                             ","
                             (Tactic.simpLemma [] [] `add_zeroₓ)
                             ","
                             (Tactic.simpLemma [] [] `pow_succₓ)]
                            "]"]
                           [])
                          [])
                         (group (Tactic.pushCast "push_cast" [] []) [])
                         (group (Tactic.Ring.tacticRing "ring") [])])))
                     [])])))
                [])]))))))
        [])
       (group
        (Tactic.Conv.conv
         "conv"
         ["at" `h]
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group (Tactic.Conv.lhs "lhs") [])
            (group
             (Tactic.Conv.convRw__
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `add_pow)
                ","
                (Tactic.rwRule [] (Term.proj (Term.app `pderiv [`tt]) "." `map_sum))
                ","
                (Tactic.rwRule [] (Term.proj (Term.app `pderiv [`tt]) "." `map_sum))
                ","
                (Tactic.rwRule [] (Term.proj (Term.app `MvPolynomial.aeval [`e]) "." `map_sum))
                ","
                (Tactic.rwRule [] `Finset.sum_mul)]
               "]"))
             [])
            (group (Tactic.Conv.applyCongr "apply_congr" []) [])
            (group (Tactic.Conv.convSkip "skip") [])
            (group
             (Tactic.Conv.simp
              "simp"
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `pderiv_mul)
                ","
                (Tactic.simpLemma [] [] `pderiv_tt_x)
                ","
                (Tactic.simpLemma [] [] `pderiv_tt_y)
                ","
                (Tactic.simpLemma [] [] `e)
                ","
                (Tactic.simpLemma [] [] `w)]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.Conv.conv
         "conv"
         ["at" `h]
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group (Tactic.Conv.rhs "rhs") [])
            (group
             (Tactic.Conv.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `pderiv_one)
                ","
                (Tactic.simpLemma [] [] `pderiv_mul)
                ","
                (Tactic.simpLemma [] [] `pderiv_pow)
                ","
                (Tactic.simpLemma [] [] `pderiv_nat_cast)
                ","
                (Tactic.simpLemma [] [] (Term.proj (Term.app `pderiv [`tt]) "." `map_add))
                ","
                (Tactic.simpLemma [] [] `pderiv_tt_x)
                ","
                (Tactic.simpLemma [] [] `pderiv_tt_y)]
               "]"]
              [])
             [])
            (group
             (Tactic.Conv.simp
              "simp"
              []
              []
              ["[" [(Tactic.simpLemma [] [] `e) "," (Tactic.simpLemma [] [] `smul_smul)] "]"]
              [])
             [])])))
        [])
       (group (Tactic.simpa "simpa" [] [] [] [] ["using" `h]) [])])))
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
         (Term.letIdDecl
          `x
          [(Term.typeSpec ":" (Term.app `MvPolynomial [`Bool `R]))]
          ":="
          (Term.app `MvPolynomial.x [`tt]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `y
          [(Term.typeSpec ":" (Term.app `MvPolynomial [`Bool `R]))]
          ":="
          (Term.app `MvPolynomial.x [`ff]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`pderiv_tt_x []]
          [(Term.typeSpec ":" («term_=_» (Term.app `pderiv [`tt `x]) "=" (numLit "1")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `x)] "]"] []) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`pderiv_tt_y []]
          [(Term.typeSpec ":" («term_=_» (Term.app `pderiv [`tt `y]) "=" (numLit "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                []
                ["[" [(Tactic.simpLemma [] [] `pderiv_X) "," (Tactic.simpLemma [] [] `y)] "]"]
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `e
          [(Term.typeSpec ":" (Term.arrow `Bool "→" (Term.app `Polynomial [`R])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [])]
            "=>"
            (Term.app `cond [`i `X («term_-_» (numLit "1") "-" `X)]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_+_» `x "+" `y) "^" `n)
             "="
             (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_+_» `x "+" `y) "^" `n)))]
          ":="
          `rfl)))
       [])
      (group
       (Tactic.applyFun "apply_fun" (Term.app `pderiv [`tt]) [(Tactic.location "at" (Tactic.locationHyp [`h] []))] [])
       [])
      (group
       (Tactic.applyFun "apply_fun" (Term.app `pderiv [`tt]) [(Tactic.location "at" (Tactic.locationHyp [`h] []))] [])
       [])
      (group
       (Tactic.applyFun "apply_fun" (Term.app `aeval [`e]) [(Tactic.location "at" (Tactic.locationHyp [`h] []))] [])
       [])
      (group
       (Tactic.applyFun
        "apply_fun"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`p] [])]
          "=>"
          (Finset.Data.Finset.Fold.«term_*_» `p "*" (Cardinal.SetTheory.Cardinal.«term_^_» `X "^" (numLit "2")))))
        [(Tactic.location "at" (Tactic.locationHyp [`h] []))]
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`w []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
             ","
             («term_=_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Finset.Data.Finset.Fold.«term_*_»
                (Finset.Data.Finset.Fold.«term_*_»
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Init.Coe.«term↑_» "↑" `k)
                  "*"
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Init.Coe.«term↑_» "↑" («term_-_» `k "-" (numLit "1")))
                   "*"
                   (Cardinal.SetTheory.Cardinal.«term_^_»
                    `Polynomial.x
                    "^"
                    («term_-_» («term_-_» `k "-" (numLit "1")) "-" (numLit "1")))))
                 "*"
                 (Cardinal.SetTheory.Cardinal.«term_^_»
                  («term_-_» (numLit "1") "-" `Polynomial.x)
                  "^"
                  («term_-_» `n "-" `k)))
                "*"
                (Init.Coe.«term↑_» "↑" (Term.app `n.choose [`k])))
               "*"
               (Cardinal.SetTheory.Cardinal.«term_^_» `Polynomial.x "^" (numLit "2")))
              "="
              (Algebra.Group.Defs.«term_•_»
               (Finset.Data.Finset.Fold.«term_*_» `k "*" («term_-_» `k "-" (numLit "1")))
               " • "
               (Term.app `bernsteinPolynomial [`R `n `k])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one
                  (Tactic.rcasesPat.paren
                   "("
                   (Tactic.rcasesPatLo
                    (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_") "|" (Tactic.rcasesPat.one `k)])
                    [])
                   ")"))]
                [])
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] `k)]
                     ["with"
                      (Tactic.rcasesPat.paren
                       "("
                       (Tactic.rcasesPatLo
                        (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_") "|" (Tactic.rcasesPat.one `k)])
                        [])
                       ")")])
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.dsimp "dsimp" [] [] ["[" [(Tactic.simpLemma [] [] `bernsteinPolynomial)] "]"] [] [])
                         [])
                        (group
                         (Tactic.simp
                          "simp"
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] ["←"] `nat_cast_mul)
                            ","
                            (Tactic.simpLemma [] [] `Nat.succ_eq_add_one)
                            ","
                            (Tactic.simpLemma [] [] `Nat.add_succ_sub_one)
                            ","
                            (Tactic.simpLemma [] [] `add_zeroₓ)
                            ","
                            (Tactic.simpLemma [] [] `pow_succₓ)]
                           "]"]
                          [])
                         [])
                        (group (Tactic.pushCast "push_cast" [] []) [])
                        (group (Tactic.Ring.tacticRing "ring") [])])))
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.Conv.conv
        "conv"
        ["at" `h]
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.lhs "lhs") [])
           (group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `add_pow)
               ","
               (Tactic.rwRule [] (Term.proj (Term.app `pderiv [`tt]) "." `map_sum))
               ","
               (Tactic.rwRule [] (Term.proj (Term.app `pderiv [`tt]) "." `map_sum))
               ","
               (Tactic.rwRule [] (Term.proj (Term.app `MvPolynomial.aeval [`e]) "." `map_sum))
               ","
               (Tactic.rwRule [] `Finset.sum_mul)]
              "]"))
            [])
           (group (Tactic.Conv.applyCongr "apply_congr" []) [])
           (group (Tactic.Conv.convSkip "skip") [])
           (group
            (Tactic.Conv.simp
             "simp"
             []
             []
             ["["
              [(Tactic.simpLemma [] [] `pderiv_mul)
               ","
               (Tactic.simpLemma [] [] `pderiv_tt_x)
               ","
               (Tactic.simpLemma [] [] `pderiv_tt_y)
               ","
               (Tactic.simpLemma [] [] `e)
               ","
               (Tactic.simpLemma [] [] `w)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.Conv.conv
        "conv"
        ["at" `h]
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.rhs "rhs") [])
           (group
            (Tactic.Conv.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `pderiv_one)
               ","
               (Tactic.simpLemma [] [] `pderiv_mul)
               ","
               (Tactic.simpLemma [] [] `pderiv_pow)
               ","
               (Tactic.simpLemma [] [] `pderiv_nat_cast)
               ","
               (Tactic.simpLemma [] [] (Term.proj (Term.app `pderiv [`tt]) "." `map_add))
               ","
               (Tactic.simpLemma [] [] `pderiv_tt_x)
               ","
               (Tactic.simpLemma [] [] `pderiv_tt_y)]
              "]"]
             [])
            [])
           (group
            (Tactic.Conv.simp
             "simp"
             []
             []
             ["[" [(Tactic.simpLemma [] [] `e) "," (Tactic.simpLemma [] [] `smul_smul)] "]"]
             [])
            [])])))
       [])
      (group (Tactic.simpa "simpa" [] [] [] [] ["using" `h]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.Conv.conv
   "conv"
   ["at" `h]
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.rhs "rhs") [])
      (group
       (Tactic.Conv.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `pderiv_one)
          ","
          (Tactic.simpLemma [] [] `pderiv_mul)
          ","
          (Tactic.simpLemma [] [] `pderiv_pow)
          ","
          (Tactic.simpLemma [] [] `pderiv_nat_cast)
          ","
          (Tactic.simpLemma [] [] (Term.proj (Term.app `pderiv [`tt]) "." `map_add))
          ","
          (Tactic.simpLemma [] [] `pderiv_tt_x)
          ","
          (Tactic.simpLemma [] [] `pderiv_tt_y)]
         "]"]
        [])
       [])
      (group
       (Tactic.Conv.simp
        "simp"
        []
        []
        ["[" [(Tactic.simpLemma [] [] `e) "," (Tactic.simpLemma [] [] `smul_smul)] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.conv', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
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
theorem
  sum_mul_smul
  ( n : ℕ ) : Finset.range n + 1 . Sum fun ν => ν * ν - 1 • bernsteinPolynomial R n ν = n * n - 1 • X ^ 2
  :=
    by
      let x : MvPolynomial Bool R := MvPolynomial.x tt
        let y : MvPolynomial Bool R := MvPolynomial.x ff
        have pderiv_tt_x : pderiv tt x = 1 := by simp [ x ]
        have pderiv_tt_y : pderiv tt y = 0 := by simp [ pderiv_X , y ]
        let e : Bool → Polynomial R := fun i => cond i X 1 - X
        have h : x + y ^ n = x + y ^ n := rfl
        apply_fun pderiv tt at h
        apply_fun pderiv tt at h
        apply_fun aeval e at h
        apply_fun fun p => p * X ^ 2 at h
        have
          w
            :
              ∀
                k : ℕ
                ,
                ↑ k * ↑ k - 1 * Polynomial.x ^ k - 1 - 1 * 1 - Polynomial.x ^ n - k * ↑ n.choose k * Polynomial.x ^ 2
                  =
                  k * k - 1 • bernsteinPolynomial R n k
            :=
            by
              rintro ( _ | k )
                · simp
                ·
                  rcases k with ( _ | k )
                    · simp
                    ·
                      dsimp [ bernsteinPolynomial ]
                        simp
                          only
                          [ ← nat_cast_mul , Nat.succ_eq_add_one , Nat.add_succ_sub_one , add_zeroₓ , pow_succₓ ]
                        push_cast
                        ring
        conv
          at h
          =>
          lhs
            rw [ add_pow , pderiv tt . map_sum , pderiv tt . map_sum , MvPolynomial.aeval e . map_sum , Finset.sum_mul ]
            apply_congr
            skip
            simp [ pderiv_mul , pderiv_tt_x , pderiv_tt_y , e , w ]
        conv
          at h
          =>
          rhs
            simp
              only
              [
                pderiv_one , pderiv_mul , pderiv_pow , pderiv_nat_cast , pderiv tt . map_add , pderiv_tt_x , pderiv_tt_y
                ]
            simp [ e , smul_smul ]
        simpa using h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nA certain linear combination of the previous three identities,\nwhich we'll want later.\n-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `variance [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      (Term.proj (Term.app `Finset.range [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." `Sum)
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`ν] [])]
         "=>"
         (Finset.Data.Finset.Fold.«term_*_»
          (Cardinal.SetTheory.Cardinal.«term_^_»
           («term_-_» (Algebra.Group.Defs.«term_•_» `n " • " `Polynomial.x) "-" `ν)
           "^"
           (numLit "2"))
          "*"
          (Term.app `bernsteinPolynomial [`R `n `ν]))))])
     "="
     (Finset.Data.Finset.Fold.«term_*_»
      (Algebra.Group.Defs.«term_•_» `n " • " `Polynomial.x)
      "*"
      («term_-_» (numLit "1") "-" `Polynomial.x)))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`p []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Init.Logic.«term_+_»
               (Init.Logic.«term_+_»
                (Term.app
                 (Term.proj (Term.app `Finset.range [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." `Sum)
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`ν] [])]
                    "=>"
                    (Algebra.Group.Defs.«term_•_»
                     (Finset.Data.Finset.Fold.«term_*_» `ν "*" («term_-_» `ν "-" (numLit "1")))
                     " • "
                     (Term.app `bernsteinPolynomial [`R `n `ν]))))])
                "+"
                (Finset.Data.Finset.Fold.«term_*_»
                 («term_-_»
                  (numLit "1")
                  "-"
                  (Algebra.Group.Defs.«term_•_»
                   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                   " • "
                   `Polynomial.x))
                 "*"
                 (Term.app
                  (Term.proj (Term.app `Finset.range [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." `Sum)
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`ν] [])]
                     "=>"
                     (Algebra.Group.Defs.«term_•_» `ν " • " (Term.app `bernsteinPolynomial [`R `n `ν]))))])))
               "+"
               (Finset.Data.Finset.Fold.«term_*_»
                (Algebra.Group.Defs.«term_•_»
                 (Cardinal.SetTheory.Cardinal.«term_^_» `n "^" (numLit "2"))
                 " • "
                 (Cardinal.SetTheory.Cardinal.«term_^_» `X "^" (numLit "2")))
                "*"
                (Term.app
                 (Term.proj (Term.app `Finset.range [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." `Sum)
                 [(Term.fun
                   "fun"
                   (Term.basicFun [(Term.simpleBinder [`ν] [])] "=>" (Term.app `bernsteinPolynomial [`R `n `ν])))])))
              "="
              (Term.hole "_")))]
           ":="
           `rfl)))
        [])
       (group
        (Tactic.Conv.conv
         "conv"
         ["at" `p]
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group (Tactic.Conv.lhs "lhs") [])
            (group
             (Tactic.Conv.convRw__
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Finset.mul_sum)
                ","
                (Tactic.rwRule [] `Finset.mul_sum)
                ","
                (Tactic.rwRule ["←"] `Finset.sum_add_distrib)
                ","
                (Tactic.rwRule ["←"] `Finset.sum_add_distrib)]
               "]"))
             [])
            (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"] []) [])
            (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] []) [])
            (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `add_mulₓ)] "]"] []) [])])))
        [])
       (group
        (Tactic.Conv.conv
         "conv"
         ["at" `p]
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group (Tactic.Conv.rhs "rhs") [])
            (group
             (Tactic.Conv.convRw__
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Sum)
                ","
                (Tactic.rwRule [] `sum_smul)
                ","
                (Tactic.rwRule [] `sum_mul_smul)
                ","
                (Tactic.rwRule ["←"] `nat_cast_mul)]
               "]"))
             [])])))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_» (Term.hole "_") "=" (Term.hole "_"))
           ":="
           (Term.app
            `Finset.sum_congr
            [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `m] [])] "=>" (Term.hole "_")))]))
          (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" `p)
          (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" (Term.hole "_"))])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.congr "congr" [(numLit "1")] []) [])
            (group
             (Tactic.simp'
              "simp'"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"]
              ["with" [`push_cast]]
              [])
             [])
            (group
             (Tactic.«tactic_<;>_»
              (Tactic.cases "cases" [(Tactic.casesTarget [] `k)] [] [])
              "<;>"
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])]))))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp'
              "simp'"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"]
              ["with" [`push_cast]]
              [])
             [])
            (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])])))
             [])])))
        [])])))
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`p []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Init.Logic.«term_+_»
              (Init.Logic.«term_+_»
               (Term.app
                (Term.proj (Term.app `Finset.range [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." `Sum)
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`ν] [])]
                   "=>"
                   (Algebra.Group.Defs.«term_•_»
                    (Finset.Data.Finset.Fold.«term_*_» `ν "*" («term_-_» `ν "-" (numLit "1")))
                    " • "
                    (Term.app `bernsteinPolynomial [`R `n `ν]))))])
               "+"
               (Finset.Data.Finset.Fold.«term_*_»
                («term_-_»
                 (numLit "1")
                 "-"
                 (Algebra.Group.Defs.«term_•_»
                  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `n)
                  " • "
                  `Polynomial.x))
                "*"
                (Term.app
                 (Term.proj (Term.app `Finset.range [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." `Sum)
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`ν] [])]
                    "=>"
                    (Algebra.Group.Defs.«term_•_» `ν " • " (Term.app `bernsteinPolynomial [`R `n `ν]))))])))
              "+"
              (Finset.Data.Finset.Fold.«term_*_»
               (Algebra.Group.Defs.«term_•_»
                (Cardinal.SetTheory.Cardinal.«term_^_» `n "^" (numLit "2"))
                " • "
                (Cardinal.SetTheory.Cardinal.«term_^_» `X "^" (numLit "2")))
               "*"
               (Term.app
                (Term.proj (Term.app `Finset.range [(Init.Logic.«term_+_» `n "+" (numLit "1"))]) "." `Sum)
                [(Term.fun
                  "fun"
                  (Term.basicFun [(Term.simpleBinder [`ν] [])] "=>" (Term.app `bernsteinPolynomial [`R `n `ν])))])))
             "="
             (Term.hole "_")))]
          ":="
          `rfl)))
       [])
      (group
       (Tactic.Conv.conv
        "conv"
        ["at" `p]
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.lhs "lhs") [])
           (group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Finset.mul_sum)
               ","
               (Tactic.rwRule [] `Finset.mul_sum)
               ","
               (Tactic.rwRule ["←"] `Finset.sum_add_distrib)
               ","
               (Tactic.rwRule ["←"] `Finset.sum_add_distrib)]
              "]"))
            [])
           (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"] []) [])
           (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] []) [])
           (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `add_mulₓ)] "]"] []) [])])))
       [])
      (group
       (Tactic.Conv.conv
        "conv"
        ["at" `p]
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group (Tactic.Conv.rhs "rhs") [])
           (group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Sum)
               ","
               (Tactic.rwRule [] `sum_smul)
               ","
               (Tactic.rwRule [] `sum_mul_smul)
               ","
               (Tactic.rwRule ["←"] `nat_cast_mul)]
              "]"))
            [])])))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_» (Term.hole "_") "=" (Term.hole "_"))
          ":="
          (Term.app
           `Finset.sum_congr
           [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `m] [])] "=>" (Term.hole "_")))]))
         (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" `p)
         (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" (Term.hole "_"))])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.congr "congr" [(numLit "1")] []) [])
           (group
            (Tactic.simp'
             "simp'"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"]
             ["with" [`push_cast]]
             [])
            [])
           (group
            (Tactic.«tactic_<;>_»
             (Tactic.cases "cases" [(Tactic.casesTarget [] `k)] [] [])
             "<;>"
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])]))))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp'
             "simp'"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"]
             ["with" [`push_cast]]
             [])
            [])
           (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])])))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp'
        "simp'"
        []
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"]
        ["with" [`push_cast]]
        [])
       [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.Ring.tacticRing "ring")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Ring.tacticRing', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp' "simp'" [] [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"] ["with" [`push_cast]] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nat_cast_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.congr "congr" [(numLit "1")] []) [])
      (group
       (Tactic.simp'
        "simp'"
        []
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"]
        ["with" [`push_cast]]
        [])
       [])
      (group
       (Tactic.«tactic_<;>_»
        (Tactic.cases "cases" [(Tactic.casesTarget [] `k)] [] [])
        "<;>"
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])]))))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.cases "cases" [(Tactic.casesTarget [] `k)] [] [])
   "<;>"
   (Tactic.«tactic·._»
    "·"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.simp "simp" [] [] [] []) []) (group (Tactic.Ring.tacticRing "ring") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.Ring.tacticRing "ring")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Ring.tacticRing', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `k)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp' "simp'" [] [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"] ["with" [`push_cast]] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nat_cast_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [(numLit "1")] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_» (Term.hole "_") "=" (Term.hole "_"))
     ":="
     (Term.app
      `Finset.sum_congr
      [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `m] [])] "=>" (Term.hole "_")))]))
    (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" `p)
    (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" (Term.hole "_"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (Term.hole "_"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (Term.hole "_"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   `Finset.sum_congr
   [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `m] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `m] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (Term.hole "_"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.Conv.conv
   "conv"
   ["at" `p]
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.rhs "rhs") [])
      (group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Sum)
          ","
          (Tactic.rwRule [] `sum_smul)
          ","
          (Tactic.rwRule [] `sum_mul_smul)
          ","
          (Tactic.rwRule ["←"] `nat_cast_mul)]
         "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.conv', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nat_cast_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_mul_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.rhs', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.Conv.conv
   "conv"
   ["at" `p]
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group (Tactic.Conv.lhs "lhs") [])
      (group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Finset.mul_sum)
          ","
          (Tactic.rwRule [] `Finset.mul_sum)
          ","
          (Tactic.rwRule ["←"] `Finset.sum_add_distrib)
          ","
          (Tactic.rwRule ["←"] `Finset.sum_add_distrib)]
         "]"))
       [])
      (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `nat_cast_mul)] "]"] []) [])
      (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] []) [])
      (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `add_mulₓ)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.conv', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
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
    A certain linear combination of the previous three identities,
    which we'll want later.
    -/
  theorem
    variance
    ( n : ℕ )
      :
        Finset.range n + 1 . Sum fun ν => n • Polynomial.x - ν ^ 2 * bernsteinPolynomial R n ν
          =
          n • Polynomial.x * 1 - Polynomial.x
    :=
      by
        have
            p
              :
                Finset.range n + 1 . Sum fun ν => ν * ν - 1 • bernsteinPolynomial R n ν
                      +
                      1 - 2 * n • Polynomial.x * Finset.range n + 1 . Sum fun ν => ν • bernsteinPolynomial R n ν
                    +
                    n ^ 2 • X ^ 2 * Finset.range n + 1 . Sum fun ν => bernsteinPolynomial R n ν
                  =
                  _
              :=
              rfl
          conv
            at p
            =>
            lhs
              rw [ Finset.mul_sum , Finset.mul_sum , ← Finset.sum_add_distrib , ← Finset.sum_add_distrib ]
              simp only [ ← nat_cast_mul ]
              simp only [ ← mul_assocₓ ]
              simp only [ ← add_mulₓ ]
          conv at p => rhs rw [ Sum , sum_smul , sum_mul_smul , ← nat_cast_mul ]
          calc _ = _ := Finset.sum_congr rfl fun k m => _ _ = _ := p _ = _ := _
          · congr 1 simp' only [ ← nat_cast_mul ] with push_cast cases k <;> · simp ring
          · simp' only [ ← nat_cast_mul ] with push_cast cases n · simp · simp ring

end bernsteinPolynomial

