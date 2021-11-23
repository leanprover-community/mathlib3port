import Mathbin.NumberTheory.Padics.PadicIntegers 
import Mathbin.Topology.MetricSpace.CauSeqFilter 
import Mathbin.Analysis.SpecificLimits 
import Mathbin.Data.Polynomial.Identities 
import Mathbin.Topology.Algebra.Polynomial

/-!
# Hensel's lemma on ℤ_p

This file proves Hensel's lemma on ℤ_p, roughly following Keith Conrad's writeup:
<http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>

Hensel's lemma gives a simple condition for the existence of a root of a polynomial.

The proof and motivation are described in the paper
[R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019].

## References

* <http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/Hensel%27s_lemma>

## Tags

p-adic, p adic, padic, p-adic integer
-/


noncomputable theory

open_locale Classical TopologicalSpace

theorem padic_polynomial_dist {p : ℕ} [Fact p.prime] (F : Polynomial ℤ_[p]) (x y : ℤ_[p]) :
  ∥F.eval x - F.eval y∥ ≤ ∥x - y∥ :=
  let ⟨z, hz⟩ := F.eval_sub_factor x y 
  calc ∥F.eval x - F.eval y∥ = ∥z∥*∥x - y∥ :=
    by 
      simp [hz]
    _ ≤ 1*∥x - y∥ := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
    _ = ∥x - y∥ :=
    by 
      simp 
    

open Filter Metric

private theorem comp_tendsto_lim {p : ℕ} [Fact p.prime] {F : Polynomial ℤ_[p]} (ncs : CauSeq ℤ_[p] norm) :
  tendsto (fun i => F.eval (ncs i)) at_top (𝓝 (F.eval ncs.lim)) :=
  F.continuous_at.tendsto.comp ncs.tendsto_limit

section 

parameter
  {p :
    ℕ}[Fact
      p.prime]{ncs :
    CauSeq ℤ_[p]
      norm}{F : Polynomial ℤ_[p]}{a : ℤ_[p]}(ncs_der_val : ∀ n, ∥F.derivative.eval (ncs n)∥ = ∥F.derivative.eval a∥)

include ncs_der_val

private theorem ncs_tendsto_const : tendsto (fun i => ∥F.derivative.eval (ncs i)∥) at_top (𝓝 ∥F.derivative.eval a∥) :=
  by 
    convert tendsto_const_nhds <;> ext <;> rw [ncs_der_val]

private theorem ncs_tendsto_lim :
  tendsto (fun i => ∥F.derivative.eval (ncs i)∥) at_top (𝓝 ∥F.derivative.eval ncs.lim∥) :=
  tendsto.comp (continuous_iff_continuous_at.1 continuous_norm _) (comp_tendsto_lim _)

private theorem norm_deriv_eq : ∥F.derivative.eval ncs.lim∥ = ∥F.derivative.eval a∥ :=
  tendsto_nhds_unique ncs_tendsto_lim ncs_tendsto_const

end 

section 

parameter
  {p :
    ℕ}[Fact
      p.prime]{ncs : CauSeq ℤ_[p] norm}{F : Polynomial ℤ_[p]}(hnorm : tendsto (fun i => ∥F.eval (ncs i)∥) at_top (𝓝 0))

include hnorm

private theorem tendsto_zero_of_norm_tendsto_zero : tendsto (fun i => F.eval (ncs i)) at_top (𝓝 0) :=
  tendsto_iff_norm_tendsto_zero.2
    (by 
      simpa using hnorm)

theorem limit_zero_of_norm_tendsto_zero : F.eval ncs.lim = 0 :=
  tendsto_nhds_unique (comp_tendsto_lim _) tendsto_zero_of_norm_tendsto_zero

end 

section Hensel

open Nat

parameter
  {p :
    ℕ}[Fact
      p.prime]{F : Polynomial ℤ_[p]}{a : ℤ_[p]}(hnorm : ∥F.eval a∥ < (∥F.derivative.eval a∥^2))(hnsol : F.eval a ≠ 0)

include hnorm

/-- `T` is an auxiliary value that is used to control the behavior of the polynomial `F`. -/
private def T : ℝ :=
  ∥(F.eval a / (F.derivative.eval a^2) : ℚ_[p])∥

private theorem deriv_sq_norm_pos : 0 < (∥F.derivative.eval a∥^2) :=
  lt_of_le_of_ltₓ (norm_nonneg _) hnorm

private theorem deriv_sq_norm_ne_zero : (∥F.derivative.eval a∥^2) ≠ 0 :=
  ne_of_gtₓ deriv_sq_norm_pos

private theorem deriv_norm_ne_zero : ∥F.derivative.eval a∥ ≠ 0 :=
  fun h =>
    deriv_sq_norm_ne_zero
      (by 
        simp [sq])

private theorem deriv_norm_pos : 0 < ∥F.derivative.eval a∥ :=
  lt_of_le_of_neₓ (norm_nonneg _) (Ne.symm deriv_norm_ne_zero)

private theorem deriv_ne_zero : F.derivative.eval a ≠ 0 :=
  mt norm_eq_zero.2 deriv_norm_ne_zero

private theorem T_def : T = ∥F.eval a∥ / (∥F.derivative.eval a∥^2) :=
  calc T = ∥F.eval a∥ / ∥(F.derivative.eval a^2 : ℚ_[p])∥ := NormedField.norm_div _ _ 
    _ = ∥F.eval a∥ / ∥F.derivative.eval a^2∥ :=
    by 
      simp [norm, PadicInt.norm_def]
    _ = ∥F.eval a∥ / (∥F.derivative.eval a∥^2) :=
    by 
      simp 
    

private theorem T_lt_one : T < 1 :=
  let h := (div_lt_one deriv_sq_norm_pos).2 hnorm 
  by 
    rw [T_def] <;> apply h

private theorem T_pow {n : ℕ} (hn : n > 0) : (T^n) < 1 :=
  have  : (T^n) ≤ (T^1) := pow_le_pow_of_le_one (norm_nonneg _) (le_of_ltₓ T_lt_one) (succ_le_of_lt hn)
  lt_of_le_of_ltₓ
    (by 
      simpa)
    T_lt_one

private theorem T_pow' (n : ℕ) : (T^2^n) < 1 :=
  T_pow
    (pow_pos
      (by 
        normNum)
      _)

private theorem T_pow_nonneg (n : ℕ) : 0 ≤ (T^n) :=
  pow_nonneg (norm_nonneg _) _

/-- We will construct a sequence of elements of ℤ_p satisfying successive values of `ih`. -/
private def ih (n : ℕ) (z : ℤ_[p]) : Prop :=
  ∥F.derivative.eval z∥ = ∥F.derivative.eval a∥ ∧ ∥F.eval z∥ ≤ (∥F.derivative.eval a∥^2)*T^2^n

private theorem ih_0 : ih 0 a :=
  ⟨rfl,
    by 
      simp [T_def, mul_div_cancel' _ (ne_of_gtₓ (deriv_sq_norm_pos hnorm))]⟩

private theorem calc_norm_le_one {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
  ∥(«expr↑ » (F.eval z) : ℚ_[p]) / «expr↑ » (F.derivative.eval z)∥ ≤ 1 :=
  calc
    ∥(«expr↑ » (F.eval z) : ℚ_[p]) / «expr↑ » (F.derivative.eval z)∥ =
      ∥(«expr↑ » (F.eval z) : ℚ_[p])∥ / ∥(«expr↑ » (F.derivative.eval z) : ℚ_[p])∥ :=
    NormedField.norm_div _ _ 
    _ = ∥F.eval z∥ / ∥F.derivative.eval a∥ :=
    by 
      simp [hz.1]
    _ ≤ ((∥F.derivative.eval a∥^2)*T^2^n) / ∥F.derivative.eval a∥ := (div_le_div_right deriv_norm_pos).2 hz.2
    _ = ∥F.derivative.eval a∥*T^2^n := div_sq_cancel (ne_of_gtₓ deriv_norm_pos) _ 
    _ ≤ 1 := mul_le_one (PadicInt.norm_le_one _) (T_pow_nonneg _) (le_of_ltₓ (T_pow' _))
    

private theorem calc_deriv_dist {z z' z1 : ℤ_[p]} (hz' : z' = z - z1) (hz1 : ∥z1∥ = ∥F.eval z∥ / ∥F.derivative.eval a∥)
  {n} (hz : ih n z) : ∥F.derivative.eval z' - F.derivative.eval z∥ < ∥F.derivative.eval a∥ :=
  calc ∥F.derivative.eval z' - F.derivative.eval z∥ ≤ ∥z' - z∥ := padic_polynomial_dist _ _ _ 
    _ = ∥z1∥ :=
    by 
      simp only [sub_eq_add_neg, add_assocₓ, hz', add_add_neg_cancel'_right, norm_neg]
    _ = ∥F.eval z∥ / ∥F.derivative.eval a∥ := hz1 
    _ ≤ ((∥F.derivative.eval a∥^2)*T^2^n) / ∥F.derivative.eval a∥ := (div_le_div_right deriv_norm_pos).2 hz.2
    _ = ∥F.derivative.eval a∥*T^2^n := div_sq_cancel deriv_norm_ne_zero _ 
    _ < ∥F.derivative.eval a∥ :=
    (mul_lt_iff_lt_one_right deriv_norm_pos).2
      (T_pow
        (pow_pos
          (by 
            normNum)
          _))
    

private def calc_eval_z' {z z' z1 : ℤ_[p]} (hz' : z' = z - z1) {n} (hz : ih n z)
  (h1 : ∥(«expr↑ » (F.eval z) : ℚ_[p]) / «expr↑ » (F.derivative.eval z)∥ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
  { q : ℤ_[p] // F.eval z' = q*z1^2 } :=
  have hdzne' : («expr↑ » (F.derivative.eval z) : ℚ_[p]) ≠ 0 :=
    have hdzne : F.derivative.eval z ≠ 0 :=
      mt norm_eq_zero.2
        (by 
          rw [hz.1] <;> apply deriv_norm_ne_zero <;> assumption)
    fun h => hdzne$ Subtype.ext_iff_val.2 h 
  let ⟨q, hq⟩ := F.binom_expansion z (-z1)
  have  : ∥(«expr↑ » (F.derivative.eval z)*«expr↑ » (F.eval z) / «expr↑ » (F.derivative.eval z) : ℚ_[p])∥ ≤ 1 :=
    by 
      rw [padicNormE.mul]
      exact mul_le_one (PadicInt.norm_le_one _) (norm_nonneg _) h1 
  have  : (F.derivative.eval z*-z1) = -F.eval z :=
    calc (F.derivative.eval z*-z1) = F.derivative.eval z*-⟨«expr↑ » (F.eval z) / «expr↑ » (F.derivative.eval z), h1⟩ :=
      by 
        rw [hzeq]
      _ = -F.derivative.eval z*⟨«expr↑ » (F.eval z) / «expr↑ » (F.derivative.eval z), h1⟩ :=
      by 
        simp [Subtype.ext_iff_val]
      _ = -⟨«expr↑ » (F.derivative.eval z)*«expr↑ » (F.eval z) / «expr↑ » (F.derivative.eval z), this⟩ :=
      Subtype.ext$
        by 
          simp 
      _ = -F.eval z :=
      by 
        simp [mul_div_cancel' _ hdzne']
      
  have heq : F.eval z' = q*z1^2 :=
    by 
      simpa [sub_eq_add_neg, this, hz'] using hq
  ⟨q, HEq⟩

private def calc_eval_z'_norm {z z' z1 : ℤ_[p]} {n} (hz : ih n z) {q} (heq : F.eval z' = q*z1^2)
  (h1 : ∥(«expr↑ » (F.eval z) : ℚ_[p]) / «expr↑ » (F.derivative.eval z)∥ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
  ∥F.eval z'∥ ≤ (∥F.derivative.eval a∥^2)*T^2^n+1 :=
  calc ∥F.eval z'∥ = ∥q∥*∥z1∥^2 :=
    by 
      simp [HEq]
    _ ≤ 1*∥z1∥^2 := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (pow_nonneg (norm_nonneg _) _)
    _ = (∥F.eval z∥^2) / (∥F.derivative.eval a∥^2) :=
    by 
      simp [hzeq, hz.1, div_pow]
    _ ≤ (((∥F.derivative.eval a∥^2)*T^2^n)^2) / (∥F.derivative.eval a∥^2) :=
    (div_le_div_right deriv_sq_norm_pos).2 (pow_le_pow_of_le_left (norm_nonneg _) hz.2 _)
    _ = (((∥F.derivative.eval a∥^2)^2)*(T^2^n)^2) / (∥F.derivative.eval a∥^2) :=
    by 
      simp only [mul_powₓ]
    _ = (∥F.derivative.eval a∥^2)*(T^2^n)^2 := div_sq_cancel deriv_sq_norm_ne_zero _ 
    _ = (∥F.derivative.eval a∥^2)*T^2^n+1 :=
    by 
      rw [←pow_mulₓ, pow_succ'ₓ 2]
    

set_option eqn_compiler.zeta true

-- error in NumberTheory.Padics.Hensel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given `z : ℤ_[p]` satisfying `ih n z`, construct `z' : ℤ_[p]` satisfying `ih (n+1) z'`. We need
the hypothesis `ih n z`, since otherwise `z'` is not necessarily an integer. -/
private
def ih_n {n : exprℕ()} {z : «exprℤ_[ ]»(p)} (hz : ih n z) : {z' : «exprℤ_[ ]»(p) // ih «expr + »(n, 1) z'} :=
have h1 : «expr ≤ »(«expr∥ ∥»(«expr / »((«expr↑ »(F.eval z) : «exprℚ_[ ]»(p)), «expr↑ »(F.derivative.eval z))), 1), from calc_norm_le_one hz,
let z1 : «exprℤ_[ ]»(p) := ⟨_, h1⟩, z' : «exprℤ_[ ]»(p) := «expr - »(z, z1) in
⟨z', have hdist : «expr < »(«expr∥ ∥»(«expr - »(F.derivative.eval z', F.derivative.eval z)), «expr∥ ∥»(F.derivative.eval a)), from calc_deriv_dist rfl (by simp [] [] [] ["[", expr z1, ",", expr hz.1, "]"] [] []) hz,
 have hfeq : «expr = »(«expr∥ ∥»(F.derivative.eval z'), «expr∥ ∥»(F.derivative.eval a)), begin
   rw ["[", expr sub_eq_add_neg, ",", "<-", expr hz.1, ",", "<-", expr norm_neg (F.derivative.eval z), "]"] ["at", ident hdist],
   have [] [] [":=", expr padic_int.norm_eq_of_norm_add_lt_right hdist],
   rwa ["[", expr norm_neg, ",", expr hz.1, "]"] ["at", ident this]
 end,
 let ⟨q, heq⟩ := calc_eval_z' rfl hz h1 rfl in
 have hnle : «expr ≤ »(«expr∥ ∥»(F.eval z'), «expr * »(«expr ^ »(«expr∥ ∥»(F.derivative.eval a), 2), «expr ^ »(T, «expr ^ »(2, «expr + »(n, 1))))), from calc_eval_z'_norm hz heq h1 rfl,
 ⟨hfeq, hnle⟩⟩

set_option eqn_compiler.zeta false

private noncomputable def newton_seq_aux : ∀ n : ℕ, { z : ℤ_[p] // ih n z }
| 0 => ⟨a, ih_0⟩
| k+1 => ih_n (newton_seq_aux k).2

private def newton_seq (n : ℕ) : ℤ_[p] :=
  (newton_seq_aux n).1

private theorem newton_seq_deriv_norm (n : ℕ) : ∥F.derivative.eval (newton_seq n)∥ = ∥F.derivative.eval a∥ :=
  (newton_seq_aux n).2.1

private theorem newton_seq_norm_le (n : ℕ) : ∥F.eval (newton_seq n)∥ ≤ (∥F.derivative.eval a∥^2)*T^2^n :=
  (newton_seq_aux n).2.2

private theorem newton_seq_norm_eq (n : ℕ) :
  ∥newton_seq (n+1) - newton_seq n∥ = ∥F.eval (newton_seq n)∥ / ∥F.derivative.eval (newton_seq n)∥ :=
  by 
    simp [newton_seq, newton_seq_aux, ih_n, sub_eq_add_neg, add_commₓ]

private theorem newton_seq_succ_dist (n : ℕ) : ∥newton_seq (n+1) - newton_seq n∥ ≤ ∥F.derivative.eval a∥*T^2^n :=
  calc ∥newton_seq (n+1) - newton_seq n∥ = ∥F.eval (newton_seq n)∥ / ∥F.derivative.eval (newton_seq n)∥ :=
    newton_seq_norm_eq _ 
    _ = ∥F.eval (newton_seq n)∥ / ∥F.derivative.eval a∥ :=
    by 
      rw [newton_seq_deriv_norm]
    _ ≤ ((∥F.derivative.eval a∥^2)*T^2^n) / ∥F.derivative.eval a∥ :=
    (div_le_div_right deriv_norm_pos).2 (newton_seq_norm_le _)
    _ = ∥F.derivative.eval a∥*T^2^n := div_sq_cancel (ne_of_gtₓ deriv_norm_pos) _
    

include hnsol

private theorem T_pos : T > 0 :=
  by 
    rw [T_def]
    exact div_pos (norm_pos_iff.2 hnsol) (deriv_sq_norm_pos hnorm)

private theorem newton_seq_succ_dist_weak (n : ℕ) :
  ∥newton_seq (n+2) - newton_seq (n+1)∥ < ∥F.eval a∥ / ∥F.derivative.eval a∥ :=
  have  : 2 ≤ (2^n+1) :=
    have  :=
      pow_le_pow
        (by 
          normNum :
        1 ≤ 2)
        (Nat.le_add_leftₓ _ _ : 1 ≤ n+1)
    by 
      simpa using this 
  calc ∥newton_seq (n+2) - newton_seq (n+1)∥ ≤ ∥F.derivative.eval a∥*T^2^n+1 := newton_seq_succ_dist _ 
    _ ≤ ∥F.derivative.eval a∥*T^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) (le_of_ltₓ T_lt_one) this) (norm_nonneg _)
    _ < ∥F.derivative.eval a∥*T^1 :=
    mul_lt_mul_of_pos_left
      (pow_lt_pow_of_lt_one T_pos T_lt_one
        (by 
          normNum))
      deriv_norm_pos 
    _ = ∥F.eval a∥ / ∥F.derivative.eval a∥ :=
    by 
      rw [T, sq, pow_oneₓ, NormedField.norm_div, ←mul_div_assoc, padicNormE.mul]
      apply mul_div_mul_left 
      apply deriv_norm_ne_zero <;> assumption
    

private theorem newton_seq_dist_aux (n : ℕ) : ∀ k : ℕ, ∥newton_seq (n+k) - newton_seq n∥ ≤ ∥F.derivative.eval a∥*T^2^n
| 0 =>
  by 
    simp [T_pow_nonneg hnorm, mul_nonneg]
| k+1 =>
  have  : (2^n) ≤ (2^n+k) :=
    by 
      apply pow_le_pow 
      normNum 
      apply Nat.le_add_rightₓ 
  calc ∥newton_seq (n+k+1) - newton_seq n∥ = ∥newton_seq ((n+k)+1) - newton_seq n∥ :=
    by 
      rw [add_assocₓ]
    _ = ∥(newton_seq ((n+k)+1) - newton_seq (n+k))+newton_seq (n+k) - newton_seq n∥ :=
    by 
      rw [←sub_add_sub_cancel]
    _ ≤ max ∥newton_seq ((n+k)+1) - newton_seq (n+k)∥ ∥newton_seq (n+k) - newton_seq n∥ := PadicInt.nonarchimedean _ _ 
    _ ≤ max (∥F.derivative.eval a∥*T^2^n+k) (∥F.derivative.eval a∥*T^2^n) :=
    max_le_max (newton_seq_succ_dist _) (newton_seq_dist_aux _)
    _ = ∥F.derivative.eval a∥*T^2^n :=
    max_eq_rightₓ$
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) (le_of_ltₓ T_lt_one) this) (norm_nonneg _)
    

private theorem newton_seq_dist {n k : ℕ} (hnk : n ≤ k) : ∥newton_seq k - newton_seq n∥ ≤ ∥F.derivative.eval a∥*T^2^n :=
  have hex : ∃ m, k = n+m := exists_eq_add_of_le hnk 
  let ⟨_, hex'⟩ := hex 
  by 
    rw [hex'] <;> apply newton_seq_dist_aux <;> assumption

private theorem newton_seq_dist_to_a : ∀ n : ℕ, 0 < n → ∥newton_seq n - a∥ = ∥F.eval a∥ / ∥F.derivative.eval a∥
| 1, h =>
  by 
    simp [sub_eq_add_neg, add_assocₓ, newton_seq, newton_seq_aux, ih_n]
| k+2, h =>
  have hlt : ∥newton_seq (k+2) - newton_seq (k+1)∥ < ∥newton_seq (k+1) - a∥ :=
    by 
      rw [newton_seq_dist_to_a (k+1) (succ_pos _)] <;> apply newton_seq_succ_dist_weak <;> assumption 
  have hne' : ∥newton_seq (k+2) - newton_seq (k+1)∥ ≠ ∥newton_seq (k+1) - a∥ := ne_of_ltₓ hlt 
  calc ∥newton_seq (k+2) - a∥ = ∥(newton_seq (k+2) - newton_seq (k+1))+newton_seq (k+1) - a∥ :=
    by 
      rw [←sub_add_sub_cancel]
    _ = max ∥newton_seq (k+2) - newton_seq (k+1)∥ ∥newton_seq (k+1) - a∥ := PadicInt.norm_add_eq_max_of_ne hne' 
    _ = ∥newton_seq (k+1) - a∥ := max_eq_right_of_ltₓ hlt 
    _ = ∥Polynomial.eval a F∥ / ∥Polynomial.eval a (Polynomial.derivative F)∥ := newton_seq_dist_to_a (k+1) (succ_pos _)
    

private theorem bound' : tendsto (fun n : ℕ => ∥F.derivative.eval a∥*T^2^n) at_top (𝓝 0) :=
  by 
    rw [←mul_zero ∥F.derivative.eval a∥]
    exact
      tendsto_const_nhds.mul
        (tendsto.comp (tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _) (T_lt_one hnorm))
          (Nat.tendsto_pow_at_top_at_top_of_one_lt
            (by 
              normNum)))

-- error in NumberTheory.Padics.Hensel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem bound : ∀
{ε}, «expr > »(ε, 0) → «expr∃ , »((N : exprℕ()), ∀
 {n}, «expr ≥ »(n, N) → «expr < »(«expr * »(«expr∥ ∥»(F.derivative.eval a), «expr ^ »(T, «expr ^ »(2, n))), ε)) :=
have mtn : ∀
n : exprℕ(), «expr ≥ »(«expr * »(«expr∥ ∥»(polynomial.eval a (polynomial.derivative F)), «expr ^ »(T, «expr ^ »(2, n))), 0), from λ
n, mul_nonneg (norm_nonneg _) (T_pow_nonneg _),
begin
  have [] [] [":=", expr bound' hnorm hnsol],
  simp [] [] [] ["[", expr tendsto, ",", expr nhds, "]"] [] ["at", ident this],
  intros [ident ε, ident hε],
  cases [expr this (ball 0 ε) (mem_ball_self hε) is_open_ball] ["with", ident N, ident hN],
  existsi [expr N],
  intros [ident n, ident hn],
  simpa [] [] [] ["[", expr normed_field.norm_mul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg (mtn n), "]"] [] ["using", expr hN _ hn]
end

private theorem bound'_sq : tendsto (fun n : ℕ => (∥F.derivative.eval a∥^2)*T^2^n) at_top (𝓝 0) :=
  by 
    rw [←mul_zero ∥F.derivative.eval a∥, sq]
    simp only [mul_assocₓ]
    apply tendsto.mul
    ·
      apply tendsto_const_nhds
    ·
      apply bound' 
      assumption

private theorem newton_seq_is_cauchy : IsCauSeq norm newton_seq :=
  by 
    intro ε hε 
    cases' bound hnorm hnsol hε with N hN 
    exists N 
    intro j hj 
    apply lt_of_le_of_ltₓ
    ·
      apply newton_seq_dist _ _ hj 
      assumption
    ·
      apply hN 
      apply le_reflₓ

private def newton_cau_seq : CauSeq ℤ_[p] norm :=
  ⟨_, newton_seq_is_cauchy⟩

private def soln : ℤ_[p] :=
  newton_cau_seq.lim

private theorem soln_spec {ε : ℝ} (hε : ε > 0) : ∃ N : ℕ, ∀ {i : ℕ}, i ≥ N → ∥soln - newton_cau_seq i∥ < ε :=
  Setoidₓ.symm (CauSeq.equiv_lim newton_cau_seq) _ hε

private theorem soln_deriv_norm : ∥F.derivative.eval soln∥ = ∥F.derivative.eval a∥ :=
  norm_deriv_eq newton_seq_deriv_norm

private theorem newton_seq_norm_tendsto_zero : tendsto (fun i => ∥F.eval (newton_cau_seq i)∥) at_top (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) newton_seq_norm_le bound'_sq

private theorem newton_seq_dist_tendsto :
  tendsto (fun n => ∥newton_cau_seq n - a∥) at_top (𝓝 (∥F.eval a∥ / ∥F.derivative.eval a∥)) :=
  tendsto_const_nhds.congr'$ eventually_at_top.2 ⟨1, fun _ hx => (newton_seq_dist_to_a _ hx).symm⟩

private theorem newton_seq_dist_tendsto' : tendsto (fun n => ∥newton_cau_seq n - a∥) at_top (𝓝 ∥soln - a∥) :=
  (continuous_norm.Tendsto _).comp (newton_cau_seq.tendsto_limit.sub tendsto_const_nhds)

private theorem soln_dist_to_a : ∥soln - a∥ = ∥F.eval a∥ / ∥F.derivative.eval a∥ :=
  tendsto_nhds_unique newton_seq_dist_tendsto' newton_seq_dist_tendsto

private theorem soln_dist_to_a_lt_deriv : ∥soln - a∥ < ∥F.derivative.eval a∥ :=
  by 
    rw [soln_dist_to_a, div_lt_iff]
    ·
      rwa [sq] at hnorm
    ·
      apply deriv_norm_pos 
      assumption

private theorem eval_soln : F.eval soln = 0 :=
  limit_zero_of_norm_tendsto_zero newton_seq_norm_tendsto_zero

private theorem soln_unique (z : ℤ_[p]) (hev : F.eval z = 0) (hnlt : ∥z - a∥ < ∥F.derivative.eval a∥) : z = soln :=
  have soln_dist : ∥z - soln∥ < ∥F.derivative.eval a∥ :=
    calc ∥z - soln∥ = ∥(z - a)+a - soln∥ :=
      by 
        rw [sub_add_sub_cancel]
      _ ≤ max ∥z - a∥ ∥a - soln∥ := PadicInt.nonarchimedean _ _ 
      _ < ∥F.derivative.eval a∥ := max_ltₓ hnlt (norm_sub_rev soln a ▸ soln_dist_to_a_lt_deriv)
      
  let h := z - soln 
  let ⟨q, hq⟩ := F.binom_expansion soln h 
  have  : ((F.derivative.eval soln+q*h)*h) = 0 :=
    Eq.symm
      (calc 0 = F.eval (soln+h) :=
        by 
          simp [hev, h]
        _ = (F.derivative.eval soln*h)+q*h^2 :=
        by 
          rw [hq, eval_soln, zero_addₓ]
        _ = (F.derivative.eval soln+q*h)*h :=
        by 
          rw [sq, right_distrib, mul_assocₓ]
        )
  have  : h = 0 :=
    by_contradiction$
      fun hne =>
        have  : (F.derivative.eval soln+q*h) = 0 := (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne 
        have  : F.derivative.eval soln = (-q)*h :=
          by 
            simpa using eq_neg_of_add_eq_zero this 
        lt_irreflₓ ∥F.derivative.eval soln∥
          (calc ∥F.derivative.eval soln∥ = ∥(-q)*h∥ :=
            by 
              rw [this]
            _ ≤ 1*∥h∥ :=
            by 
              rw [PadicInt.norm_mul]
              exact mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
            _ = ∥z - soln∥ :=
            by 
              simp [h]
            _ < ∥F.derivative.eval soln∥ :=
            by 
              rw [soln_deriv_norm] <;> apply soln_dist
            )
  eq_of_sub_eq_zero
    (by 
      rw [←this] <;> rfl)

end Hensel

variable{p : ℕ}[Fact p.prime]{F : Polynomial ℤ_[p]}{a : ℤ_[p]}

private theorem a_soln_is_unique (ha : F.eval a = 0) (z' : ℤ_[p]) (hz' : F.eval z' = 0)
  (hnormz' : ∥z' - a∥ < ∥F.derivative.eval a∥) : z' = a :=
  let h := z' - a 
  let ⟨q, hq⟩ := F.binom_expansion a h 
  have  : ((F.derivative.eval a+q*h)*h) = 0 :=
    Eq.symm
      (calc 0 = F.eval (a+h) :=
        show 0 = F.eval (a+z' - a)by 
          rw [add_commₓ] <;> simp [hz']
        _ = (F.derivative.eval a*h)+q*h^2 :=
        by 
          rw [hq, ha, zero_addₓ]
        _ = (F.derivative.eval a+q*h)*h :=
        by 
          rw [sq, right_distrib, mul_assocₓ]
        )
  have  : h = 0 :=
    by_contradiction$
      fun hne =>
        have  : (F.derivative.eval a+q*h) = 0 := (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne 
        have  : F.derivative.eval a = (-q)*h :=
          by 
            simpa using eq_neg_of_add_eq_zero this 
        lt_irreflₓ ∥F.derivative.eval a∥
          (calc ∥F.derivative.eval a∥ = ∥q∥*∥h∥ :=
            by 
              simp [this]
            _ ≤ 1*∥h∥ := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
            _ < ∥F.derivative.eval a∥ :=
            by 
              simpa [h]
            )
  eq_of_sub_eq_zero
    (by 
      rw [←this] <;> rfl)

variable(hnorm : ∥F.eval a∥ < (∥F.derivative.eval a∥^2))

include hnorm

private theorem a_is_soln (ha : F.eval a = 0) :
  F.eval a = 0 ∧
    ∥a - a∥ < ∥F.derivative.eval a∥ ∧
      ∥F.derivative.eval a∥ = ∥F.derivative.eval a∥ ∧ ∀ z', F.eval z' = 0 → ∥z' - a∥ < ∥F.derivative.eval a∥ → z' = a :=
  ⟨ha,
    by 
      simp [deriv_ne_zero hnorm],
    rfl, a_soln_is_unique ha⟩

theorem hensels_lemma :
  ∃ z : ℤ_[p],
    F.eval z = 0 ∧
      ∥z - a∥ < ∥F.derivative.eval a∥ ∧
        ∥F.derivative.eval z∥ = ∥F.derivative.eval a∥ ∧
          ∀ z', F.eval z' = 0 → ∥z' - a∥ < ∥F.derivative.eval a∥ → z' = z :=
  if ha : F.eval a = 0 then ⟨a, a_is_soln hnorm ha⟩ else
    by 
      refine' ⟨soln _ _, eval_soln _ _, soln_dist_to_a_lt_deriv _ _, soln_deriv_norm _ _, soln_unique _ _⟩ <;>
        assumption

