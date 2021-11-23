import Mathbin.RingTheory.Polynomial.Bernstein 
import Mathbin.Topology.ContinuousFunction.Polynomial

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

Our proof follows [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D.
The original proof, due to [Bernstein](bernstein1912) in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.

The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.

(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)

This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
-/


noncomputable theory

open_locale Classical

open_locale BigOperators

open_locale BoundedContinuousFunction

open_locale UnitInterval

/--
The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I

@[simp]
theorem bernstein_apply (n ν : ℕ) (x : I) : bernstein n ν x = (n.choose ν*x^ν)*1 - x^n - ν :=
  by 
    dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
    simp 

theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x :=
  by 
    simp only [bernstein_apply]
    exact
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (pow_nonneg
            (by 
              unitInterval)
            _))
        (pow_nonneg
          (by 
            unitInterval)
          _)

/-!
We now give a slight reformulation of `bernstein_polynomial.variance`.
-/


namespace bernstein

-- error in Analysis.SpecialFunctions.Bernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Send `k : fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/ def z {n : exprℕ()} (k : fin «expr + »(n, 1)) : exprI() :=
⟨«expr / »((k : exprℝ()), n), begin
   cases [expr n] [],
   { norm_num [] [] },
   { have [ident h₁] [":", expr «expr < »(0, (n.succ : exprℝ()))] [":=", expr by exact_mod_cast [expr nat.succ_pos _]],
     have [ident h₂] [":", expr «expr ≤ »(«expr↑ »(k), n.succ)] [":=", expr by exact_mod_cast [expr fin.le_last k]],
     rw ["[", expr set.mem_Icc, ",", expr le_div_iff h₁, ",", expr div_le_iff h₁, "]"] [],
     norm_cast [],
     simp [] [] [] ["[", expr h₂, "]"] [] [] }
 end⟩

local postfix:90 "/ₙ" => z

-- error in Analysis.SpecialFunctions.Bernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem probability
(n : exprℕ())
(x : exprI()) : «expr = »(«expr∑ , »((k : fin «expr + »(n, 1)), bernstein n k x), 1) :=
begin
  have [] [] [":=", expr bernstein_polynomial.sum exprℝ() n],
  apply_fun [expr λ p, polynomial.aeval (x : exprℝ()) p] ["at", ident this] [],
  simp [] [] [] ["[", expr alg_hom.map_sum, ",", expr finset.sum_range, "]"] [] ["at", ident this],
  exact [expr this]
end

-- error in Analysis.SpecialFunctions.Bernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem variance
{n : exprℕ()}
(h : «expr < »(0, (n : exprℝ())))
(x : exprI()) : «expr = »(«expr∑ , »((k : fin «expr + »(n, 1)), «expr * »(«expr ^ »((«expr - »(x, «expr /ₙ»(k)) : exprℝ()), 2), bernstein n k x)), «expr / »(«expr * »(x, «expr - »(1, x)), n)) :=
begin
  have [ident h'] [":", expr «expr ≠ »((n : exprℝ()), 0)] [":=", expr ne_of_gt h],
  apply_fun [expr λ x : exprℝ(), «expr * »(x, n)] [] ["using", expr group_with_zero.mul_right_injective h'],
  apply_fun [expr λ x : exprℝ(), «expr * »(x, n)] [] ["using", expr group_with_zero.mul_right_injective h'],
  dsimp [] [] [] [],
  conv_lhs [] [] { simp ["only"] ["[", expr finset.sum_mul, ",", expr z, "]"] [] },
  conv_rhs [] [] { rw [expr div_mul_cancel _ h'] },
  have [] [] [":=", expr bernstein_polynomial.variance exprℝ() n],
  apply_fun [expr λ p, polynomial.aeval (x : exprℝ()) p] ["at", ident this] [],
  simp [] [] [] ["[", expr alg_hom.map_sum, ",", expr finset.sum_range, ",", "<-", expr polynomial.nat_cast_mul, "]"] [] ["at", ident this],
  convert [] [expr this] ["using", 1],
  { congr' [1] [],
    funext [ident k],
    rw ["[", expr mul_comm _ (n : exprℝ()), ",", expr mul_comm _ (n : exprℝ()), ",", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, "]"] [],
    congr' [1] [],
    field_simp [] ["[", expr h, "]"] [] [],
    ring [] },
  { ring [] }
end

end bernstein

open bernstein

local postfix:2000 "/ₙ" => z

/--
The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, f (k/n) * bernstein n k x`.
-/
def bernsteinApproximation (n : ℕ) (f : C(I, ℝ)) : C(I, ℝ) :=
  ∑k : Finₓ (n+1), f (k)/ₙ • bernstein n k

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, ℝ)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/


namespace bernsteinApproximation

@[simp]
theorem apply (n : ℕ) (f : C(I, ℝ)) (x : I) : bernsteinApproximation n f x = ∑k : Finₓ (n+1), f (k)/ₙ*bernstein n k x :=
  by 
    simp [bernsteinApproximation]

/--
The modulus of (uniform) continuity for `f`, chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.
-/
def δ (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  f.modulus (ε / 2) (half_pos h)

/--
The set of points `k` so `k/n` is within `δ` of `x`.
-/
def S (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : Finset (Finₓ (n+1)) :=
  { k:Finₓ (n+1) | dist (k)/ₙ x < δ f ε h }.toFinset

/--
If `k ∈ S`, then `f(k/n)` is close to `f x`.
-/
theorem lt_of_mem_S {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Finₓ (n+1)} (m : k ∈ S f ε h n x) :
  |f (k)/ₙ - f x| < ε / 2 :=
  by 
    apply f.dist_lt_of_dist_lt_modulus (ε / 2) (half_pos h)
    simpa [S] using m

/--
If `k ∉ S`, then as `δ ≤ |x - k/n|`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.
This particular formulation will be helpful later.
-/
theorem le_of_mem_S_compl {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Finₓ (n+1)}
  (m : k ∈ «expr ᶜ» (S f ε h n x)) : (1 : ℝ) ≤ (δ f ε h^(-2 : ℤ))*x - (k)/ₙ^2 :=
  by 
    simp only [Finset.mem_compl, not_ltₓ, Set.mem_to_finset, Set.mem_set_of_eq, S] at m 
    fieldSimp 
    erw [le_div_iff (pow_pos f.modulus_pos 2), one_mulₓ]
    apply sq_le_sq 
    rw [abs_eq_self.mpr (le_of_ltₓ f.modulus_pos)]
    rw [dist_comm] at m 
    exact m

end bernsteinApproximation

open bernsteinApproximation

open BoundedContinuousFunction

open Filter

open_locale TopologicalSpace

-- error in Analysis.SpecialFunctions.Bernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,
and reproduced on wikipedia.
-/
theorem bernstein_approximation_uniform
(f : «exprC( , )»(exprI(), exprℝ())) : tendsto (λ n : exprℕ(), bernstein_approximation n f) at_top (expr𝓝() f) :=
begin
  simp [] [] ["only"] ["[", expr metric.nhds_basis_ball.tendsto_right_iff, ",", expr metric.mem_ball, ",", expr dist_eq_norm, "]"] [] [],
  intros [ident ε, ident h],
  let [ident δ] [] [":=", expr δ f ε h],
  have [ident nhds_zero] [] [":=", expr tendsto_const_div_at_top_nhds_0_nat «expr * »(«expr * »(2, «expr∥ ∥»(f)), «expr ^ »(δ, («expr- »(2) : exprℤ())))],
  filter_upwards ["[", expr nhds_zero.eventually (gt_mem_nhds (half_pos h)), ",", expr eventually_gt_at_top 0, "]"] [],
  intros [ident n, ident nh, ident npos'],
  have [ident npos] [":", expr «expr < »(0, (n : exprℝ()))] [":=", expr by exact_mod_cast [expr npos']],
  have [ident w₁] [":", expr «expr ≤ »(0, «expr * »(2, «expr∥ ∥»(f)))] [":=", expr mul_nonneg (by norm_num [] []) (norm_nonneg f)],
  have [ident w₂] [":", expr «expr ≤ »(0, «expr * »(«expr * »(2, «expr∥ ∥»(f)), «expr ^ »(δ, («expr- »(2) : exprℤ()))))] [":=", expr mul_nonneg w₁ pow_minus_two_nonneg],
  rw [expr continuous_map.norm_lt_iff _ h] [],
  intro [ident x],
  let [ident S] [] [":=", expr S f ε h n x],
  calc
    «expr = »(«expr| |»(«expr - »(bernstein_approximation n f, f) x), «expr| |»(«expr - »(bernstein_approximation n f x, f x))) : rfl
    «expr = »(..., «expr| |»(«expr - »(bernstein_approximation n f x, «expr * »(f x, 1)))) : by rw [expr mul_one] []
    «expr = »(..., «expr| |»(«expr - »(bernstein_approximation n f x, «expr * »(f x, «expr∑ , »((k : fin «expr + »(n, 1)), bernstein n k x))))) : by rw [expr bernstein.probability] []
    «expr = »(..., «expr| |»(«expr∑ , »((k : fin «expr + »(n, 1)), «expr * »(«expr - »(f «expr /ₙ»(k), f x), bernstein n k x)))) : by simp [] [] [] ["[", expr bernstein_approximation, ",", expr finset.mul_sum, ",", expr sub_mul, "]"] [] []
    «expr ≤ »(..., «expr∑ , »((k : fin «expr + »(n, 1)), «expr| |»(«expr * »(«expr - »(f «expr /ₙ»(k), f x), bernstein n k x)))) : finset.abs_sum_le_sum_abs _ _
    «expr = »(..., «expr∑ , »((k : fin «expr + »(n, 1)), «expr * »(«expr| |»(«expr - »(f «expr /ₙ»(k), f x)), bernstein n k x))) : by simp_rw ["[", expr abs_mul, ",", expr abs_eq_self.mpr bernstein_nonneg, "]"] []
    «expr = »(..., «expr + »(«expr∑ in , »((k), S, «expr * »(«expr| |»(«expr - »(f «expr /ₙ»(k), f x)), bernstein n k x)), «expr∑ in , »((k), «expr ᶜ»(S), «expr * »(«expr| |»(«expr - »(f «expr /ₙ»(k), f x)), bernstein n k x)))) : (S.sum_add_sum_compl _).symm
    «expr < »(..., «expr + »(«expr / »(ε, 2), «expr / »(ε, 2))) : add_lt_add_of_le_of_lt _ _
    «expr = »(..., ε) : add_halves ε,
  { calc
      «expr ≤ »(«expr∑ in , »((k), S, «expr * »(«expr| |»(«expr - »(f «expr /ₙ»(k), f x)), bernstein n k x)), «expr∑ in , »((k), S, «expr * »(«expr / »(ε, 2), bernstein n k x))) : finset.sum_le_sum (λ
       k m, mul_le_mul_of_nonneg_right (le_of_lt (lt_of_mem_S m)) bernstein_nonneg)
      «expr = »(..., «expr * »(«expr / »(ε, 2), «expr∑ in , »((k), S, bernstein n k x))) : by rw [expr finset.mul_sum] []
      «expr ≤ »(..., «expr * »(«expr / »(ε, 2), «expr∑ , »((k : fin «expr + »(n, 1)), bernstein n k x))) : mul_le_mul_of_nonneg_left (finset.sum_le_univ_sum_of_nonneg (λ
        k, bernstein_nonneg)) (le_of_lt (half_pos h))
      «expr = »(..., «expr / »(ε, 2)) : by rw ["[", expr bernstein.probability, ",", expr mul_one, "]"] [] },
  { calc
      «expr ≤ »(«expr∑ in , »((k), «expr ᶜ»(S), «expr * »(«expr| |»(«expr - »(f «expr /ₙ»(k), f x)), bernstein n k x)), «expr∑ in , »((k), «expr ᶜ»(S), «expr * »(«expr * »(2, «expr∥ ∥»(f)), bernstein n k x))) : finset.sum_le_sum (λ
       k m, mul_le_mul_of_nonneg_right (f.dist_le_two_norm _ _) bernstein_nonneg)
      «expr = »(..., «expr * »(«expr * »(2, «expr∥ ∥»(f)), «expr∑ in , »((k), «expr ᶜ»(S), bernstein n k x))) : by rw [expr finset.mul_sum] []
      «expr ≤ »(..., «expr * »(«expr * »(2, «expr∥ ∥»(f)), «expr∑ in , »((k), «expr ᶜ»(S), «expr * »(«expr * »(«expr ^ »(δ, («expr- »(2) : exprℤ())), «expr ^ »(«expr - »(x, «expr /ₙ»(k)), 2)), bernstein n k x)))) : mul_le_mul_of_nonneg_left (finset.sum_le_sum (λ
        k m, begin
          conv_lhs [] [] { rw ["<-", expr one_mul (bernstein _ _ _)] },
          exact [expr mul_le_mul_of_nonneg_right (le_of_mem_S_compl m) bernstein_nonneg]
        end)) w₁
      «expr ≤ »(..., «expr * »(«expr * »(2, «expr∥ ∥»(f)), «expr∑ , »((k : fin «expr + »(n, 1)), «expr * »(«expr * »(«expr ^ »(δ, («expr- »(2) : exprℤ())), «expr ^ »(«expr - »(x, «expr /ₙ»(k)), 2)), bernstein n k x)))) : mul_le_mul_of_nonneg_left (finset.sum_le_univ_sum_of_nonneg (λ
        k, mul_nonneg (mul_nonneg pow_minus_two_nonneg (sq_nonneg _)) bernstein_nonneg)) w₁
      «expr = »(..., «expr * »(«expr * »(«expr * »(2, «expr∥ ∥»(f)), «expr ^ »(δ, («expr- »(2) : exprℤ()))), «expr∑ , »((k : fin «expr + »(n, 1)), «expr * »(«expr ^ »(«expr - »(x, «expr /ₙ»(k)), 2), bernstein n k x)))) : by conv_rhs [] [] { rw ["[", expr mul_assoc, ",", expr finset.mul_sum, "]"],
        simp ["only"] ["[", "<-", expr mul_assoc, "]"] [] }
      «expr = »(..., «expr / »(«expr * »(«expr * »(«expr * »(«expr * »(2, «expr∥ ∥»(f)), «expr ^ »(δ, («expr- »(2) : exprℤ()))), x), «expr - »(1, x)), n)) : by { rw [expr variance npos] [],
        ring [] }
      «expr ≤ »(..., «expr / »(«expr * »(«expr * »(2, «expr∥ ∥»(f)), «expr ^ »(δ, («expr- »(2) : exprℤ()))), n)) : (div_le_div_right npos).mpr (begin
         apply [expr mul_nonneg_le_one_le w₂],
         apply [expr mul_nonneg_le_one_le w₂ (le_refl _)],
         all_goals { unit_interval }
       end)
      «expr < »(..., «expr / »(ε, 2)) : nh }
end

