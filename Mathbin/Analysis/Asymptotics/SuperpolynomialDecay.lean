import Mathbin.Analysis.NormedSpace.Ordered 
import Mathbin.Analysis.Asymptotics.Asymptotics 
import Mathbin.Topology.Algebra.Ordered.LiminfLimsup 
import Mathbin.Data.Polynomial.Eval

/-!
# Super-Polynomial Function Decay

This file defines a predicate `asymptotics.superpolynomial_decay f` for a function satisfying
  one of following equivalent definitions (The definition is in terms of the first condition):

* `x ^ n * f` tends to `𝓝 0` for all (or sufficiently large) naturals `n`
* `|x ^ n * f|` tends to `𝓝 0` for all naturals `n` (`superpolynomial_decay_iff_abs_tendsto_zero`)
* `|x ^ n * f|` is bounded for all naturals `n` (`superpolynomial_decay_iff_abs_is_bounded_under`)
* `f` is `o(x ^ c)` for all integers `c` (`superpolynomial_decay_iff_is_o`)
* `f` is `O(x ^ c)` for all integers `c` (`superpolynomial_decay_iff_is_O`)

These conditions are all equivalent to conditions in terms of polynomials, replacing `x ^ c` with
  `p(x)` or `p(x)⁻¹` as appropriate, since asymptotically `p(x)` behaves like `X ^ p.nat_degree`.
These further equivalences are not proven in mathlib but would be good future projects.

The definition of superpolynomial decay for `f : α → β` is relative to a parameter `k : α → β`.
Super-polynomial decay then means `f x` decays faster than `(k x) ^ c` for all integers `c`.
Equivalently `f x` decays faster than `p.eval (k x)` for all polynomials `p : polynomial β`.
The definition is also relative to a filter `l : filter α` where the decay rate is compared.

When the map `k` is given by `n ↦ ↑n : ℕ → ℝ` this defines negligible functions:
https://en.wikipedia.org/wiki/Negligible_function

When the map `k` is given by `(r₁,...,rₙ) ↦ r₁*...*rₙ : ℝⁿ → ℝ` this is equivalent
  to the definition of rapidly decreasing functions given here:
https://ncatlab.org/nlab/show/rapidly+decreasing+function

# Main Theorems

* `superpolynomial_decay.polynomial_mul` says that if `f(x)` is negligible,
    then so is `p(x) * f(x)` for any polynomial `p`.
* `superpolynomial_decay_iff_zpow_tendsto_zero` gives an equivalence between definitions in terms
    of decaying faster than `k(x) ^ n` for all naturals `n` or `k(x) ^ c` for all integer `c`.
-/


namespace Asymptotics

open_locale TopologicalSpace

open Filter

/-- `f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ n * f` tends to zero at `l` for all naturals `n` -/
def superpolynomial_decay {α β : Type _} [TopologicalSpace β] [CommSemiringₓ β] (l : Filter α) (k : α → β)
  (f : α → β) :=
  ∀ n : ℕ, tendsto (fun a : α => (k a ^ n)*f a) l (𝓝 0)

variable {α β : Type _} {l : Filter α} {k : α → β} {f g g' : α → β}

section CommSemiringₓ

variable [TopologicalSpace β] [CommSemiringₓ β]

theorem superpolynomial_decay.congr' (hf : superpolynomial_decay l k f) (hfg : f =ᶠ[l] g) :
  superpolynomial_decay l k g :=
  fun z => (hf z).congr' (eventually_eq.mul (eventually_eq.refl l _) hfg)

theorem superpolynomial_decay.congr (hf : superpolynomial_decay l k f) (hfg : ∀ x, f x = g x) :
  superpolynomial_decay l k g :=
  fun z => (hf z).congr fun x => (congr_argₓ fun a => (k x ^ z)*a)$ hfg x

@[simp]
theorem superpolynomial_decay_zero (l : Filter α) (k : α → β) : superpolynomial_decay l k 0 :=
  fun z =>
    by 
      simpa only [Pi.zero_apply, mul_zero] using tendsto_const_nhds

theorem superpolynomial_decay.add [HasContinuousAdd β] (hf : superpolynomial_decay l k f)
  (hg : superpolynomial_decay l k g) : superpolynomial_decay l k (f+g) :=
  fun z =>
    by 
      simpa only [mul_addₓ, add_zeroₓ, Pi.add_apply] using (hf z).add (hg z)

theorem superpolynomial_decay.mul [HasContinuousMul β] (hf : superpolynomial_decay l k f)
  (hg : superpolynomial_decay l k g) : superpolynomial_decay l k (f*g) :=
  fun z =>
    by 
      simpa only [mul_assocₓ, one_mulₓ, mul_zero, pow_zeroₓ] using (hf z).mul (hg 0)

theorem superpolynomial_decay.mul_const [HasContinuousMul β] (hf : superpolynomial_decay l k f) (c : β) :
  superpolynomial_decay l k fun n => f n*c :=
  fun z =>
    by 
      simpa only [←mul_assocₓ, zero_mul] using tendsto.mul_const c (hf z)

theorem superpolynomial_decay.const_mul [HasContinuousMul β] (hf : superpolynomial_decay l k f) (c : β) :
  superpolynomial_decay l k fun n => c*f n :=
  (hf.mul_const c).congr fun _ => mul_commₓ _ _

theorem superpolynomial_decay.param_mul (hf : superpolynomial_decay l k f) : superpolynomial_decay l k (k*f) :=
  fun z =>
    tendsto_nhds.2
      fun s hs hs0 =>
        l.sets_of_superset ((tendsto_nhds.1 (hf$ z+1)) s hs hs0)
          fun x hx =>
            by 
              simpa only [Set.mem_preimage, Pi.mul_apply, ←mul_assocₓ, ←pow_succ'ₓ] using hx

theorem superpolynomial_decay.mul_param (hf : superpolynomial_decay l k f) : superpolynomial_decay l k (f*k) :=
  hf.param_mul.congr fun _ => mul_commₓ _ _

theorem superpolynomial_decay.param_pow_mul (hf : superpolynomial_decay l k f) (n : ℕ) :
  superpolynomial_decay l k ((k ^ n)*f) :=
  by 
    induction' n with n hn
    ·
      simpa only [one_mulₓ, pow_zeroₓ] using hf
    ·
      simpa only [pow_succₓ, mul_assocₓ] using hn.param_mul

theorem superpolynomial_decay.mul_param_pow (hf : superpolynomial_decay l k f) (n : ℕ) :
  superpolynomial_decay l k (f*k ^ n) :=
  (hf.param_pow_mul n).congr fun _ => mul_commₓ _ _

theorem superpolynomial_decay.polynomial_mul [HasContinuousAdd β] [HasContinuousMul β]
  (hf : superpolynomial_decay l k f) (p : Polynomial β) : superpolynomial_decay l k fun x => (p.eval$ k x)*f x :=
  Polynomial.induction_on' p
    (fun p q hp hq =>
      by 
        simpa [add_mulₓ] using hp.add hq)
    fun n c =>
      by 
        simpa [mul_assocₓ] using (hf.param_pow_mul n).const_mul c

theorem superpolynomial_decay.mul_polynomial [HasContinuousAdd β] [HasContinuousMul β]
  (hf : superpolynomial_decay l k f) (p : Polynomial β) : superpolynomial_decay l k fun x => f x*p.eval$ k x :=
  (hf.polynomial_mul p).congr fun _ => mul_commₓ _ _

end CommSemiringₓ

section OrderedCommSemiring

variable [TopologicalSpace β] [OrderedCommSemiring β] [OrderTopology β]

theorem superpolynomial_decay.trans_eventually_le (hk : 0 ≤ᶠ[l] k) (hg : superpolynomial_decay l k g)
  (hg' : superpolynomial_decay l k g') (hfg : g ≤ᶠ[l] f) (hfg' : f ≤ᶠ[l] g') : superpolynomial_decay l k f :=
  fun z =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg z) (hg' z)
      (hfg.mp (hk.mono$ fun x hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))
      (hfg'.mp (hk.mono$ fun x hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))

end OrderedCommSemiring

section LinearOrderedCommRing

variable [TopologicalSpace β] [LinearOrderedCommRing β] [OrderTopology β]

variable (l k f)

theorem superpolynomial_decay_iff_abs_tendsto_zero :
  superpolynomial_decay l k f ↔ ∀ n : ℕ, tendsto (fun a : α => |(k a ^ n)*f a|) l (𝓝 0) :=
  ⟨fun h z => (tendsto_zero_iff_abs_tendsto_zero _).1 (h z), fun h z => (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)⟩

theorem superpolynomial_decay_iff_superpolynomial_decay_abs :
  superpolynomial_decay l k f ↔ superpolynomial_decay l (fun a => |k a|) fun a => |f a| :=
  (superpolynomial_decay_iff_abs_tendsto_zero l k f).trans
    (by 
      simp [superpolynomial_decay, abs_mul])

variable {l k f}

theorem superpolynomial_decay.trans_eventually_abs_le (hf : superpolynomial_decay l k f)
  (hfg : (abs ∘ g) ≤ᶠ[l] (abs ∘ f)) : superpolynomial_decay l k g :=
  by 
    rw [superpolynomial_decay_iff_abs_tendsto_zero] at hf⊢
    refine'
      fun z =>
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf z)
          (eventually_of_forall$ fun x => abs_nonneg _) (hfg.mono$ fun x hx => _)
    calc |(k x ^ z)*g x| = |k x ^ z|*|g x| := abs_mul (k x ^ z) (g x)_ ≤ |k x ^ z|*|f x| :=
      mul_le_mul le_rfl hx (abs_nonneg _) (abs_nonneg _)_ = |(k x ^ z)*f x| := (abs_mul (k x ^ z) (f x)).symm

theorem superpolynomial_decay.trans_abs_le (hf : superpolynomial_decay l k f) (hfg : ∀ x, |g x| ≤ |f x|) :
  superpolynomial_decay l k g :=
  hf.trans_eventually_abs_le (eventually_of_forall hfg)

end LinearOrderedCommRing

section Field

variable [TopologicalSpace β] [Field β] (l k f)

theorem superpolynomial_decay_mul_const_iff [HasContinuousMul β] {c : β} (hc0 : c ≠ 0) :
  (superpolynomial_decay l k fun n => f n*c) ↔ superpolynomial_decay l k f :=
  ⟨fun h =>
      (h.mul_const (c⁻¹)).congr
        fun x =>
          by 
            simp [mul_assocₓ, mul_inv_cancel hc0],
    fun h => h.mul_const c⟩

theorem superpolynomial_decay_const_mul_iff [HasContinuousMul β] {c : β} (hc0 : c ≠ 0) :
  (superpolynomial_decay l k fun n => c*f n) ↔ superpolynomial_decay l k f :=
  ⟨fun h =>
      (h.const_mul (c⁻¹)).congr
        fun x =>
          by 
            simp [←mul_assocₓ, inv_mul_cancel hc0],
    fun h => h.const_mul c⟩

variable {l k f}

end Field

section LinearOrderedField

variable [TopologicalSpace β] [LinearOrderedField β] [OrderTopology β]

variable (f)

-- error in Analysis.Asymptotics.SuperpolynomialDecay: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem superpolynomial_decay_iff_abs_is_bounded_under
(hk : tendsto k l at_top) : «expr ↔ »(superpolynomial_decay l k f, ∀
 z : exprℕ(), is_bounded_under ((«expr ≤ »)) l (λ a : α, «expr| |»(«expr * »(«expr ^ »(k a, z), f a)))) :=
begin
  refine [expr ⟨λ
    h
    z, tendsto.is_bounded_under_le (tendsto.abs (h z)), λ
    h, (superpolynomial_decay_iff_abs_tendsto_zero l k f).2 (λ z, _)⟩],
  obtain ["⟨", ident m, ",", ident hm, "⟩", ":=", expr h «expr + »(z, 1)],
  have [ident h1] [":", expr tendsto (λ a : α, (0 : β)) l (expr𝓝() 0)] [":=", expr tendsto_const_nhds],
  have [ident h2] [":", expr tendsto (λ
    a : α, «expr * »(«expr| |»(«expr ⁻¹»(k a)), m)) l (expr𝓝() 0)] [":=", expr «expr ▸ »(zero_mul m, tendsto.mul_const m ((tendsto_zero_iff_abs_tendsto_zero _).1 hk.inv_tendsto_at_top))],
  refine [expr tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 (eventually_of_forall (λ
     x, abs_nonneg _)) ((eventually_map.1 hm).mp _)],
  refine [expr «expr $ »((eventually_ne_of_tendsto_at_top hk 0).mono, λ x hk0 hx, _)],
  refine [expr le_trans (le_of_eq _) «expr $ »(mul_le_mul_of_nonneg_left hx, abs_nonneg «expr ⁻¹»(k x))],
  rw ["[", "<-", expr abs_mul, ",", "<-", expr mul_assoc, ",", expr pow_succ, ",", "<-", expr mul_assoc, ",", expr inv_mul_cancel hk0, ",", expr one_mul, "]"] []
end

-- error in Analysis.Asymptotics.SuperpolynomialDecay: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem superpolynomial_decay_iff_zpow_tendsto_zero
(hk : tendsto k l at_top) : «expr ↔ »(superpolynomial_decay l k f, ∀
 z : exprℤ(), tendsto (λ a : α, «expr * »(«expr ^ »(k a, z), f a)) l (expr𝓝() 0)) :=
begin
  refine [expr ⟨λ
    h z, _, λ h n, by simpa [] [] ["only"] ["[", expr zpow_coe_nat, "]"] [] ["using", expr h (n : exprℤ())]⟩],
  by_cases [expr hz, ":", expr «expr ≤ »(0, z)],
  { lift [expr z] ["to", expr exprℕ()] ["using", expr hz] [],
    simpa [] [] [] [] [] ["using", expr h z] },
  { have [] [":", expr tendsto (λ
      a, «expr ^ »(k a, z)) l (expr𝓝() 0)] [":=", expr tendsto.comp (tendsto_zpow_at_top_zero (not_le.1 hz)) hk],
    have [ident h] [":", expr tendsto f l (expr𝓝() 0)] [":=", expr by simpa [] [] [] [] [] ["using", expr h 0]],
    exact [expr «expr ▸ »(zero_mul (0 : β), this.mul h)] }
end

variable {f}

theorem superpolynomial_decay.param_zpow_mul (hk : tendsto k l at_top) (hf : superpolynomial_decay l k f) (z : ℤ) :
  superpolynomial_decay l k fun a => (k a ^ z)*f a :=
  by 
    rw [superpolynomial_decay_iff_zpow_tendsto_zero _ hk] at hf⊢
    refine' fun z' => (hf$ z'+z).congr' ((eventually_ne_of_tendsto_at_top hk 0).mono fun x hx => _)
    simp [zpow_add₀ hx, mul_assocₓ, Pi.mul_apply]

theorem superpolynomial_decay.mul_param_zpow (hk : tendsto k l at_top) (hf : superpolynomial_decay l k f) (z : ℤ) :
  superpolynomial_decay l k fun a => f a*k a ^ z :=
  (hf.param_zpow_mul hk z).congr fun _ => mul_commₓ _ _

theorem superpolynomial_decay.inv_param_mul (hk : tendsto k l at_top) (hf : superpolynomial_decay l k f) :
  superpolynomial_decay l k (k⁻¹*f) :=
  by 
    simpa using hf.param_zpow_mul hk (-1)

theorem superpolynomial_decay.param_inv_mul (hk : tendsto k l at_top) (hf : superpolynomial_decay l k f) :
  superpolynomial_decay l k (f*k⁻¹) :=
  (hf.inv_param_mul hk).congr fun _ => mul_commₓ _ _

variable (f)

theorem superpolynomial_decay_param_mul_iff (hk : tendsto k l at_top) :
  superpolynomial_decay l k (k*f) ↔ superpolynomial_decay l k f :=
  ⟨fun h =>
      (h.inv_param_mul hk).congr'
        ((eventually_ne_of_tendsto_at_top hk 0).mono
          fun x hx =>
            by 
              simp [←mul_assocₓ, inv_mul_cancel hx]),
    fun h => h.param_mul⟩

theorem superpolynomial_decay_mul_param_iff (hk : tendsto k l at_top) :
  superpolynomial_decay l k (f*k) ↔ superpolynomial_decay l k f :=
  by 
    simpa [mul_commₓ k] using superpolynomial_decay_param_mul_iff f hk

theorem superpolynomial_decay_param_pow_mul_iff (hk : tendsto k l at_top) (n : ℕ) :
  superpolynomial_decay l k ((k ^ n)*f) ↔ superpolynomial_decay l k f :=
  by 
    induction' n with n hn
    ·
      simp 
    ·
      simpa [pow_succₓ, ←mul_commₓ k, mul_assocₓ, superpolynomial_decay_param_mul_iff ((k ^ n)*f) hk] using hn

theorem superpolynomial_decay_mul_param_pow_iff (hk : tendsto k l at_top) (n : ℕ) :
  superpolynomial_decay l k (f*k ^ n) ↔ superpolynomial_decay l k f :=
  by 
    simpa [mul_commₓ f] using superpolynomial_decay_param_pow_mul_iff f hk n

variable {f}

end LinearOrderedField

section NormedLinearOrderedField

variable [NormedLinearOrderedField β]

variable (l k f)

theorem superpolynomial_decay_iff_norm_tendsto_zero :
  superpolynomial_decay l k f ↔ ∀ n : ℕ, tendsto (fun a : α => ∥(k a ^ n)*f a∥) l (𝓝 0) :=
  ⟨fun h z => tendsto_zero_iff_norm_tendsto_zero.1 (h z), fun h z => tendsto_zero_iff_norm_tendsto_zero.2 (h z)⟩

theorem superpolynomial_decay_iff_superpolynomial_decay_norm :
  superpolynomial_decay l k f ↔ superpolynomial_decay l (fun a => ∥k a∥) fun a => ∥f a∥ :=
  (superpolynomial_decay_iff_norm_tendsto_zero l k f).trans
    (by 
      simp [superpolynomial_decay])

variable {l k}

variable [OrderTopology β]

-- error in Analysis.Asymptotics.SuperpolynomialDecay: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem superpolynomial_decay_iff_is_O
(hk : tendsto k l at_top) : «expr ↔ »(superpolynomial_decay l k f, ∀
 z : exprℤ(), is_O f (λ a : α, «expr ^ »(k a, z)) l) :=
begin
  refine [expr (superpolynomial_decay_iff_zpow_tendsto_zero f hk).trans _],
  have [ident hk0] [":", expr «expr∀ᶠ in , »((x), l, «expr ≠ »(k x, 0))] [":=", expr eventually_ne_of_tendsto_at_top hk 0],
  refine [expr ⟨λ h z, _, λ h z, _⟩],
  { refine [expr is_O_of_div_tendsto_nhds (hk0.mono (λ x hx hxz, absurd (zpow_eq_zero hxz) hx)) 0 _],
    have [] [":", expr «expr = »(«expr ⁻¹»(λ
       a : α, «expr ^ »(k a, z)), λ
      a : α, «expr ^ »(k a, «expr- »(z)))] [":=", expr funext (λ x, by simp [] [] [] [] [] [])],
    rw ["[", expr div_eq_mul_inv, ",", expr mul_comm f, ",", expr this, "]"] [],
    exact [expr h «expr- »(z)] },
  { suffices [] [":", expr is_O (λ a : α, «expr * »(«expr ^ »(k a, z), f a)) (λ a : α, «expr ⁻¹»(k a)) l],
    from [expr is_O.trans_tendsto this hk.inv_tendsto_at_top],
    refine [expr ((is_O_refl (λ
        a, «expr ^ »(k a, z)) l).mul (h «expr- »(«expr + »(z, 1)))).trans «expr $ »(is_O.of_bound 1, hk0.mono (λ
       a ha0, _))],
    simp [] [] ["only"] ["[", expr one_mul, ",", expr neg_add z 1, ",", expr zpow_add₀ ha0, ",", "<-", expr mul_assoc, ",", expr zpow_neg₀, ",", expr mul_inv_cancel (zpow_ne_zero z ha0), ",", expr zpow_one, "]"] [] [] }
end

-- error in Analysis.Asymptotics.SuperpolynomialDecay: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem superpolynomial_decay_iff_is_o
(hk : tendsto k l at_top) : «expr ↔ »(superpolynomial_decay l k f, ∀
 z : exprℤ(), is_o f (λ a : α, «expr ^ »(k a, z)) l) :=
begin
  refine [expr ⟨λ h z, _, λ h, (superpolynomial_decay_iff_is_O f hk).2 (λ z, (h z).is_O)⟩],
  have [ident hk0] [":", expr «expr∀ᶠ in , »((x), l, «expr ≠ »(k x, 0))] [":=", expr eventually_ne_of_tendsto_at_top hk 0],
  have [] [":", expr is_o (λ
    x : α, (1 : β)) k l] [":=", expr is_o_of_tendsto' (hk0.mono (λ
     x hkx hkx', absurd hkx' hkx)) (by simpa [] [] [] [] [] ["using", expr hk.inv_tendsto_at_top])],
  have [] [":", expr is_o f (λ x : α, «expr * »(k x, «expr ^ »(k x, «expr - »(z, 1)))) l] [],
  by simpa [] [] [] [] [] ["using", expr this.mul_is_O «expr $ »((superpolynomial_decay_iff_is_O f hk).1 h, «expr - »(z, 1))],
  refine [expr this.trans_is_O (is_O.of_bound 1 «expr $ »(hk0.mono, λ x hkx, le_of_eq _))],
  rw ["[", expr one_mul, ",", expr zpow_sub_one₀ hkx, ",", expr mul_comm (k x), ",", expr mul_assoc, ",", expr inv_mul_cancel hkx, ",", expr mul_one, "]"] []
end

variable {f}

end NormedLinearOrderedField

end Asymptotics

