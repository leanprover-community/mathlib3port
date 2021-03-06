/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.NormedSpace.Ordered
import Mathbin.Data.Polynomial.Eval
import Mathbin.Topology.Algebra.Order.LiminfLimsup

/-!
# Super-Polynomial Function Decay

This file defines a predicate `asymptotics.superpolynomial_decay f` for a function satisfying
  one of following equivalent definitions (The definition is in terms of the first condition):

* `x ^ n * f` tends to `ð 0` for all (or sufficiently large) naturals `n`
* `|x ^ n * f|` tends to `ð 0` for all naturals `n` (`superpolynomial_decay_iff_abs_tendsto_zero`)
* `|x ^ n * f|` is bounded for all naturals `n` (`superpolynomial_decay_iff_abs_is_bounded_under`)
* `f` is `o(x ^ c)` for all integers `c` (`superpolynomial_decay_iff_is_o`)
* `f` is `O(x ^ c)` for all integers `c` (`superpolynomial_decay_iff_is_O`)

These conditions are all equivalent to conditions in terms of polynomials, replacing `x ^ c` with
  `p(x)` or `p(x)â»Â¹` as appropriate, since asymptotically `p(x)` behaves like `X ^ p.nat_degree`.
These further equivalences are not proven in mathlib but would be good future projects.

The definition of superpolynomial decay for `f : Î± â Î²` is relative to a parameter `k : Î± â Î²`.
Super-polynomial decay then means `f x` decays faster than `(k x) ^ c` for all integers `c`.
Equivalently `f x` decays faster than `p.eval (k x)` for all polynomials `p : polynomial Î²`.
The definition is also relative to a filter `l : filter Î±` where the decay rate is compared.

When the map `k` is given by `n â¦ ân : â â â` this defines negligible functions:
https://en.wikipedia.org/wiki/Negligible_function

When the map `k` is given by `(râ,...,râ) â¦ râ*...*râ : ââ¿ â â` this is equivalent
  to the definition of rapidly decreasing functions given here:
https://ncatlab.org/nlab/show/rapidly+decreasing+function

# Main Theorems

* `superpolynomial_decay.polynomial_mul` says that if `f(x)` is negligible,
    then so is `p(x) * f(x)` for any polynomial `p`.
* `superpolynomial_decay_iff_zpow_tendsto_zero` gives an equivalence between definitions in terms
    of decaying faster than `k(x) ^ n` for all naturals `n` or `k(x) ^ c` for all integer `c`.
-/


namespace Asymptotics

open TopologicalSpace

open Filter

/-- `f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ n * f` tends to zero at `l` for all naturals `n` -/
def SuperpolynomialDecay {Î± Î² : Type _} [TopologicalSpace Î²] [CommSemiringâ Î²] (l : Filter Î±) (k : Î± â Î²) (f : Î± â Î²) :=
  â n : â, Tendsto (fun a : Î± => k a ^ n * f a) l (ð 0)

variable {Î± Î² : Type _} {l : Filter Î±} {k : Î± â Î²} {f g g' : Î± â Î²}

section CommSemiringâ

variable [TopologicalSpace Î²] [CommSemiringâ Î²]

theorem SuperpolynomialDecay.congr' (hf : SuperpolynomialDecay l k f) (hfg : f =á¶ [l] g) : SuperpolynomialDecay l k g :=
  fun z => (hf z).congr' (EventuallyEq.mul (EventuallyEq.refl l _) hfg)

theorem SuperpolynomialDecay.congr (hf : SuperpolynomialDecay l k f) (hfg : â x, f x = g x) :
    SuperpolynomialDecay l k g := fun z => (hf z).congr fun x => (congr_arg fun a => k x ^ z * a) <| hfg x

@[simp]
theorem superpolynomial_decay_zero (l : Filter Î±) (k : Î± â Î²) : SuperpolynomialDecay l k 0 := fun z => by
  simpa only [â Pi.zero_apply, â mul_zero] using tendsto_const_nhds

theorem SuperpolynomialDecay.add [HasContinuousAdd Î²] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f + g) := fun z => by
  simpa only [â mul_addâ, â add_zeroâ, â Pi.add_apply] using (hf z).add (hg z)

theorem SuperpolynomialDecay.mul [HasContinuousMul Î²] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f * g) := fun z => by
  simpa only [â mul_assoc, â one_mulâ, â mul_zero, â pow_zeroâ] using (hf z).mul (hg 0)

theorem SuperpolynomialDecay.mul_const [HasContinuousMul Î²] (hf : SuperpolynomialDecay l k f) (c : Î²) :
    SuperpolynomialDecay l k fun n => f n * c := fun z => by
  simpa only [mul_assoc, â zero_mul] using tendsto.mul_const c (hf z)

theorem SuperpolynomialDecay.const_mul [HasContinuousMul Î²] (hf : SuperpolynomialDecay l k f) (c : Î²) :
    SuperpolynomialDecay l k fun n => c * f n :=
  (hf.mul_const c).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.param_mul (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (k * f) := fun z =>
  tendsto_nhds.2 fun s hs hs0 =>
    l.sets_of_superset ((tendsto_nhds.1 (hf <| z + 1)) s hs hs0) fun x hx => by
      simpa only [â Set.mem_preimage, â Pi.mul_apply, mul_assoc, pow_succ'â] using hx

theorem SuperpolynomialDecay.mul_param (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (f * k) :=
  hf.param_mul.congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.param_pow_mul (hf : SuperpolynomialDecay l k f) (n : â) :
    SuperpolynomialDecay l k (k ^ n * f) := by
  induction' n with n hn
  Â· simpa only [â one_mulâ, â pow_zeroâ] using hf
    
  Â· simpa only [â pow_succâ, â mul_assoc] using hn.param_mul
    

theorem SuperpolynomialDecay.mul_param_pow (hf : SuperpolynomialDecay l k f) (n : â) :
    SuperpolynomialDecay l k (f * k ^ n) :=
  (hf.param_pow_mul n).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.polynomial_mul [HasContinuousAdd Î²] [HasContinuousMul Î²] (hf : SuperpolynomialDecay l k f)
    (p : Polynomial Î²) : SuperpolynomialDecay l k fun x => (p.eval <| k x) * f x :=
  Polynomial.induction_on' p
    (fun p q hp hq => by
      simpa [â add_mulâ] using hp.add hq)
    fun n c => by
    simpa [â mul_assoc] using (hf.param_pow_mul n).const_mul c

theorem SuperpolynomialDecay.mul_polynomial [HasContinuousAdd Î²] [HasContinuousMul Î²] (hf : SuperpolynomialDecay l k f)
    (p : Polynomial Î²) : SuperpolynomialDecay l k fun x => f x * (p.eval <| k x) :=
  (hf.polynomial_mul p).congr fun _ => mul_comm _ _

end CommSemiringâ

section OrderedCommSemiring

variable [TopologicalSpace Î²] [OrderedCommSemiring Î²] [OrderTopology Î²]

theorem SuperpolynomialDecay.trans_eventually_le (hk : 0 â¤á¶ [l] k) (hg : SuperpolynomialDecay l k g)
    (hg' : SuperpolynomialDecay l k g') (hfg : g â¤á¶ [l] f) (hfg' : f â¤á¶ [l] g') : SuperpolynomialDecay l k f := fun z =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg z) (hg' z)
    (hfg.mp (hk.mono fun x hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))
    (hfg'.mp (hk.mono fun x hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))

end OrderedCommSemiring

section LinearOrderedCommRing

variable [TopologicalSpace Î²] [LinearOrderedCommRing Î²] [OrderTopology Î²]

variable (l k f)

theorem superpolynomial_decay_iff_abs_tendsto_zero :
    SuperpolynomialDecay l k f â â n : â, Tendsto (fun a : Î± => abs (k a ^ n * f a)) l (ð 0) :=
  â¨fun h z => (tendsto_zero_iff_abs_tendsto_zero _).1 (h z), fun h z => (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)â©

theorem superpolynomial_decay_iff_superpolynomial_decay_abs :
    SuperpolynomialDecay l k f â SuperpolynomialDecay l (fun a => abs (k a)) fun a => abs (f a) :=
  (superpolynomial_decay_iff_abs_tendsto_zero l k f).trans
    (by
      simp_rw [superpolynomial_decay, abs_mul, abs_pow])

variable {l k f}

theorem SuperpolynomialDecay.trans_eventually_abs_le (hf : SuperpolynomialDecay l k f) (hfg : abs â g â¤á¶ [l] abs â f) :
    SuperpolynomialDecay l k g := by
  rw [superpolynomial_decay_iff_abs_tendsto_zero] at hfâ¢
  refine' fun z =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf z) (eventually_of_forall fun x => abs_nonneg _)
      (hfg.mono fun x hx => _)
  calc abs (k x ^ z * g x) = abs (k x ^ z) * abs (g x) := abs_mul (k x ^ z) (g x)_ â¤ abs (k x ^ z) * abs (f x) :=
      mul_le_mul le_rfl hx (abs_nonneg _) (abs_nonneg _)_ = abs (k x ^ z * f x) := (abs_mul (k x ^ z) (f x)).symm

theorem SuperpolynomialDecay.trans_abs_le (hf : SuperpolynomialDecay l k f) (hfg : â x, abs (g x) â¤ abs (f x)) :
    SuperpolynomialDecay l k g :=
  hf.trans_eventually_abs_le (eventually_of_forall hfg)

end LinearOrderedCommRing

section Field

variable [TopologicalSpace Î²] [Field Î²] (l k f)

theorem superpolynomial_decay_mul_const_iff [HasContinuousMul Î²] {c : Î²} (hc0 : c â  0) :
    (SuperpolynomialDecay l k fun n => f n * c) â SuperpolynomialDecay l k f :=
  â¨fun h =>
    (h.mul_const câ»Â¹).congr fun x => by
      simp [â mul_assoc, â mul_inv_cancel hc0],
    fun h => h.mul_const câ©

theorem superpolynomial_decay_const_mul_iff [HasContinuousMul Î²] {c : Î²} (hc0 : c â  0) :
    (SuperpolynomialDecay l k fun n => c * f n) â SuperpolynomialDecay l k f :=
  â¨fun h =>
    (h.const_mul câ»Â¹).congr fun x => by
      simp [mul_assoc, â inv_mul_cancel hc0],
    fun h => h.const_mul câ©

variable {l k f}

end Field

section LinearOrderedField

variable [TopologicalSpace Î²] [LinearOrderedField Î²] [OrderTopology Î²]

variable (f)

theorem superpolynomial_decay_iff_abs_is_bounded_under (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f â â z : â, IsBoundedUnder (Â· â¤ Â·) l fun a : Î± => abs (k a ^ z * f a) := by
  refine'
    â¨fun h z => tendsto.is_bounded_under_le (tendsto.abs (h z)), fun h =>
      (superpolynomial_decay_iff_abs_tendsto_zero l k f).2 fun z => _â©
  obtain â¨m, hmâ© := h (z + 1)
  have h1 : tendsto (fun a : Î± => (0 : Î²)) l (ð 0) := tendsto_const_nhds
  have h2 : tendsto (fun a : Î± => abs (k a)â»Â¹ * m) l (ð 0) :=
    zero_mul m â¸ tendsto.mul_const m ((tendsto_zero_iff_abs_tendsto_zero _).1 hk.inv_tendsto_at_top)
  refine'
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 (eventually_of_forall fun x => abs_nonneg _)
      ((eventually_map.1 hm).mp _)
  refine' (hk.eventually_ne_at_top 0).mono fun x hk0 hx => _
  refine' Eq.trans_le _ (mul_le_mul_of_nonneg_left hx <| abs_nonneg (k x)â»Â¹)
  rw [â abs_mul, â mul_assoc, pow_succâ, â mul_assoc, inv_mul_cancel hk0, one_mulâ]

theorem superpolynomial_decay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f â â z : â¤, Tendsto (fun a : Î± => k a ^ z * f a) l (ð 0) := by
  refine'
    â¨fun h z => _, fun h n => by
      simpa only [â zpow_coe_nat] using h (n : â¤)â©
  by_cases' hz : 0 â¤ z
  Â· lift z to â using hz
    simpa using h z
    
  Â· have : tendsto (fun a => k a ^ z) l (ð 0) := tendsto.comp (tendsto_zpow_at_top_zero (not_leâ.1 hz)) hk
    have h : tendsto f l (ð 0) := by
      simpa using h 0
    exact zero_mul (0 : Î²) â¸ this.mul h
    

variable {f}

theorem SuperpolynomialDecay.param_zpow_mul (hk : Tendsto k l atTop) (hf : SuperpolynomialDecay l k f) (z : â¤) :
    SuperpolynomialDecay l k fun a => k a ^ z * f a := by
  rw [superpolynomial_decay_iff_zpow_tendsto_zero _ hk] at hfâ¢
  refine' fun z' => (hf <| z' + z).congr' ((hk.eventually_ne_at_top 0).mono fun x hx => _)
  simp [â zpow_addâ hx, â mul_assoc, â Pi.mul_apply]

theorem SuperpolynomialDecay.mul_param_zpow (hk : Tendsto k l atTop) (hf : SuperpolynomialDecay l k f) (z : â¤) :
    SuperpolynomialDecay l k fun a => f a * k a ^ z :=
  (hf.param_zpow_mul hk z).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.inv_param_mul (hk : Tendsto k l atTop) (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (kâ»Â¹ * f) := by
  simpa using hf.param_zpow_mul hk (-1)

theorem SuperpolynomialDecay.param_inv_mul (hk : Tendsto k l atTop) (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (f * kâ»Â¹) :=
  (hf.inv_param_mul hk).congr fun _ => mul_comm _ _

variable (f)

theorem superpolynomial_decay_param_mul_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (k * f) â SuperpolynomialDecay l k f :=
  â¨fun h =>
    (h.inv_param_mul hk).congr'
      ((hk.eventually_ne_at_top 0).mono fun x hx => by
        simp [mul_assoc, â inv_mul_cancel hx]),
    fun h => h.param_mulâ©

theorem superpolynomial_decay_mul_param_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (f * k) â SuperpolynomialDecay l k f := by
  simpa [â mul_comm k] using superpolynomial_decay_param_mul_iff f hk

theorem superpolynomial_decay_param_pow_mul_iff (hk : Tendsto k l atTop) (n : â) :
    SuperpolynomialDecay l k (k ^ n * f) â SuperpolynomialDecay l k f := by
  induction' n with n hn
  Â· simp
    
  Â· simpa [â pow_succâ, mul_comm k, â mul_assoc, â superpolynomial_decay_param_mul_iff (k ^ n * f) hk] using hn
    

theorem superpolynomial_decay_mul_param_pow_iff (hk : Tendsto k l atTop) (n : â) :
    SuperpolynomialDecay l k (f * k ^ n) â SuperpolynomialDecay l k f := by
  simpa [â mul_comm f] using superpolynomial_decay_param_pow_mul_iff f hk n

variable {f}

end LinearOrderedField

section NormedLinearOrderedField

variable [NormedLinearOrderedField Î²]

variable (l k f)

theorem superpolynomial_decay_iff_norm_tendsto_zero :
    SuperpolynomialDecay l k f â â n : â, Tendsto (fun a : Î± => â¥k a ^ n * f aâ¥) l (ð 0) :=
  â¨fun h z => tendsto_zero_iff_norm_tendsto_zero.1 (h z), fun h z => tendsto_zero_iff_norm_tendsto_zero.2 (h z)â©

theorem superpolynomial_decay_iff_superpolynomial_decay_norm :
    SuperpolynomialDecay l k f â SuperpolynomialDecay l (fun a => â¥k aâ¥) fun a => â¥f aâ¥ :=
  (superpolynomial_decay_iff_norm_tendsto_zero l k f).trans
    (by
      simp [â superpolynomial_decay])

variable {l k}

variable [OrderTopology Î²]

theorem superpolynomial_decay_iff_is_O (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f â â z : â¤, f =O[l] fun a : Î± => k a ^ z := by
  refine' (superpolynomial_decay_iff_zpow_tendsto_zero f hk).trans _
  have hk0 : âá¶  x in l, k x â  0 := hk.eventually_ne_at_top 0
  refine' â¨fun h z => _, fun h z => _â©
  Â· refine' is_O_of_div_tendsto_nhds (hk0.mono fun x hx hxz => absurd (zpow_eq_zero hxz) hx) 0 _
    have : (fun a : Î± => k a ^ z)â»Â¹ = fun a : Î± => k a ^ -z :=
      funext fun x => by
        simp
    rw [div_eq_mul_inv, mul_comm f, this]
    exact h (-z)
    
  Â· suffices : (fun a : Î± => k a ^ z * f a) =O[l] fun a : Î± => (k a)â»Â¹
    exact is_O.trans_tendsto this hk.inv_tendsto_at_top
    refine' ((is_O_refl (fun a => k a ^ z) l).mul (h (-(z + 1)))).trans (is_O.of_bound 1 <| hk0.mono fun a ha0 => _)
    simp only [â one_mulâ, â neg_add z 1, â zpow_addâ ha0, mul_assoc, â zpow_neg, â mul_inv_cancel (zpow_ne_zero z ha0),
      â zpow_one]
    

theorem superpolynomial_decay_iff_is_o (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f â â z : â¤, f =o[l] fun a : Î± => k a ^ z := by
  refine' â¨fun h z => _, fun h => (superpolynomial_decay_iff_is_O f hk).2 fun z => (h z).IsOâ©
  have hk0 : âá¶  x in l, k x â  0 := hk.eventually_ne_at_top 0
  have : (fun x : Î± => (1 : Î²)) =o[l] k :=
    is_o_of_tendsto' (hk0.mono fun x hkx hkx' => absurd hkx' hkx)
      (by
        simpa using hk.inv_tendsto_at_top)
  have : f =o[l] fun x : Î± => k x * k x ^ (z - 1) := by
    simpa using this.mul_is_O ((superpolynomial_decay_iff_is_O f hk).1 h <| z - 1)
  refine' this.trans_is_O (is_O.of_bound 1 (hk0.mono fun x hkx => le_of_eqâ _))
  rw [one_mulâ, zpow_sub_oneâ hkx, mul_comm (k x), mul_assoc, inv_mul_cancel hkx, mul_oneâ]

end NormedLinearOrderedField

end Asymptotics

