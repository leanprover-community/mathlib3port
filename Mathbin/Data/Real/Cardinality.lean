import Mathbin.SetTheory.Continuum 
import Mathbin.Analysis.SpecificLimits 
import Mathbin.Data.Rat.Denumerable 
import Mathbin.Data.Set.Intervals.ImagePreimage

/-!
# The cardinality of the reals

This file shows that the real numbers have cardinality continuum, i.e. `#ℝ = 𝔠`.

We show that `#ℝ ≤ 𝔠` by noting that every real number is determined by a Cauchy-sequence of the
form `ℕ → ℚ`, which has cardinality `𝔠`. To show that `#ℝ ≥ 𝔠` we define an injection from
`{0, 1} ^ ℕ` to `ℝ` with `f ↦ Σ n, f n * (1 / 3) ^ n`.

We conclude that all intervals with distinct endpoints have cardinality continuum.

## Main definitions

* `cardinal.cantor_function` is the function that sends `f` in `{0, 1} ^ ℕ` to `ℝ` by
  `f ↦ Σ' n, f n * (1 / 3) ^ n`

## Main statements

* `cardinal.mk_real : #ℝ = 𝔠`: the reals have cardinality continuum.
* `cardinal.not_countable_real`: the universal set of real numbers is not countable.
  We can use this same proof to show that all the other sets in this file are not countable.
* 8 lemmas of the form `mk_Ixy_real` for `x,y ∈ {i,o,c}` state that intervals on the reals
  have cardinality continuum.

## Notation

* `𝔠` : notation for `cardinal.continuum` in locale `cardinal`, defined in `set_theory.continuum`.

## Tags
continuum, cardinality, reals, cardinality of the reals
-/


open Nat Set

open_locale Cardinal

noncomputable theory

namespace Cardinal

variable {c : ℝ} {f g : ℕ → Bool} {n : ℕ}

/-- The body of the sum in `cantor_function`.
`cantor_function_aux c f n = c ^ n` if `f n = tt`;
`cantor_function_aux c f n = 0` if `f n = ff`. -/
def cantor_function_aux (c : ℝ) (f : ℕ → Bool) (n : ℕ) : ℝ :=
  cond (f n) (c^n) 0

@[simp]
theorem cantor_function_aux_tt (h : f n = tt) : cantor_function_aux c f n = (c^n) :=
  by 
    simp [cantor_function_aux, h]

@[simp]
theorem cantor_function_aux_ff (h : f n = ff) : cantor_function_aux c f n = 0 :=
  by 
    simp [cantor_function_aux, h]

theorem cantor_function_aux_nonneg (h : 0 ≤ c) : 0 ≤ cantor_function_aux c f n :=
  by 
    cases h' : f n <;> simp [h']
    apply pow_nonneg h

theorem cantor_function_aux_eq (h : f n = g n) : cantor_function_aux c f n = cantor_function_aux c g n :=
  by 
    simp [cantor_function_aux, h]

theorem cantor_function_aux_succ (f : ℕ → Bool) :
  (fun n => cantor_function_aux c f (n+1)) = fun n => c*cantor_function_aux c (fun n => f (n+1)) n :=
  by 
    ext n 
    cases h : f (n+1) <;> simp [h, pow_succₓ]

theorem summable_cantor_function (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) : Summable (cantor_function_aux c f) :=
  by 
    apply (summable_geometric_of_lt_1 h1 h2).summable_of_eq_zero_or_self 
    intro n 
    cases h : f n <;> simp [h]

/-- `cantor_function c (f : ℕ → bool)` is `Σ n, f n * c ^ n`, where `tt` is interpreted as `1` and
`ff` is interpreted as `0`. It is implemented using `cantor_function_aux`. -/
def cantor_function (c : ℝ) (f : ℕ → Bool) : ℝ :=
  ∑'n, cantor_function_aux c f n

theorem cantor_function_le (h1 : 0 ≤ c) (h2 : c < 1) (h3 : ∀ n, f n → g n) :
  cantor_function c f ≤ cantor_function c g :=
  by 
    apply tsum_le_tsum _ (summable_cantor_function f h1 h2) (summable_cantor_function g h1 h2)
    intro n 
    cases h : f n 
    simp [h, cantor_function_aux_nonneg h1]
    replace h3 : g n = tt := h3 n h 
    simp [h, h3]

theorem cantor_function_succ (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) :
  cantor_function c f = cond (f 0) 1 0+c*cantor_function c fun n => f (n+1) :=
  by 
    rw [cantor_function, tsum_eq_zero_add (summable_cantor_function f h1 h2)]
    rw [cantor_function_aux_succ, tsum_mul_left, cantor_function_aux, pow_zeroₓ]
    rfl

-- error in Data.Real.Cardinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `cantor_function c` is strictly increasing with if `0 < c < 1/2`, if we endow `ℕ → bool` with a
lexicographic order. The lexicographic order doesn't exist for these infinitary products, so we
explicitly write out what it means. -/
theorem increasing_cantor_function
(h1 : «expr < »(0, c))
(h2 : «expr < »(c, «expr / »(1, 2)))
{n : exprℕ()}
{f g : exprℕ() → bool}
(hn : ∀ k «expr < » n, «expr = »(f k, g k))
(fn : «expr = »(f n, ff))
(gn : «expr = »(g n, tt)) : «expr < »(cantor_function c f, cantor_function c g) :=
begin
  have [ident h3] [":", expr «expr < »(c, 1)] [],
  { apply [expr h2.trans],
    norm_num [] [] },
  induction [expr n] [] ["with", ident n, ident ih] ["generalizing", ident f, ident g],
  { let [ident f_max] [":", expr exprℕ() → bool] [":=", expr λ n, nat.rec ff (λ _ _, tt) n],
    have [ident hf_max] [":", expr ∀ n, f n → f_max n] [],
    { intros [ident n, ident hn],
      cases [expr n] [],
      rw ["[", expr fn, "]"] ["at", ident hn],
      contradiction,
      apply [expr rfl] },
    let [ident g_min] [":", expr exprℕ() → bool] [":=", expr λ n, nat.rec tt (λ _ _, ff) n],
    have [ident hg_min] [":", expr ∀ n, g_min n → g n] [],
    { intros [ident n, ident hn],
      cases [expr n] [],
      rw ["[", expr gn, "]"] [],
      apply [expr rfl],
      contradiction },
    apply [expr (cantor_function_le (le_of_lt h1) h3 hf_max).trans_lt],
    refine [expr lt_of_lt_of_le _ (cantor_function_le (le_of_lt h1) h3 hg_min)],
    have [] [":", expr «expr < »(«expr / »(c, «expr - »(1, c)), 1)] [],
    { rw ["[", expr div_lt_one, ",", expr lt_sub_iff_add_lt, "]"] [],
      { convert [] [expr add_lt_add h2 h2] [],
        norm_num [] [] },
      rwa [expr sub_pos] [] },
    convert [] [expr this] [],
    { rw ["[", expr cantor_function_succ _ (le_of_lt h1) h3, ",", expr div_eq_mul_inv, ",", "<-", expr tsum_geometric_of_lt_1 (le_of_lt h1) h3, "]"] [],
      apply [expr zero_add] },
    { convert [] [expr tsum_eq_single 0 _] [],
      { apply_instance },
      { intros [ident n, ident hn],
        cases [expr n] [],
        contradiction,
        refl } } },
  rw ["[", expr cantor_function_succ f (le_of_lt h1) h3, ",", expr cantor_function_succ g (le_of_lt h1) h3, "]"] [],
  rw ["[", expr «expr $ »(hn 0, zero_lt_succ n), "]"] [],
  apply [expr add_lt_add_left],
  rw [expr mul_lt_mul_left h1] [],
  exact [expr ih (λ k hk, «expr $ »(hn _, succ_lt_succ hk)) fn gn]
end

-- error in Data.Real.Cardinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `cantor_function c` is injective if `0 < c < 1/2`. -/
theorem cantor_function_injective
(h1 : «expr < »(0, c))
(h2 : «expr < »(c, «expr / »(1, 2))) : function.injective (cantor_function c) :=
begin
  intros [ident f, ident g, ident hfg],
  classical,
  by_contra [ident h],
  revert [ident hfg],
  have [] [":", expr «expr∃ , »((n), «expr ≠ »(f n, g n))] [],
  { rw ["[", "<-", expr not_forall, "]"] [],
    intro [ident h'],
    apply [expr h],
    ext [] [] [],
    apply [expr h'] },
  let [ident n] [] [":=", expr nat.find this],
  have [ident hn] [":", expr ∀ k : exprℕ(), «expr < »(k, n) → «expr = »(f k, g k)] [],
  { intros [ident k, ident hk],
    apply [expr of_not_not],
    exact [expr nat.find_min this hk] },
  cases [expr fn, ":", expr f n] [],
  { apply [expr ne_of_lt],
    refine [expr increasing_cantor_function h1 h2 hn fn _],
    apply [expr eq_tt_of_not_eq_ff],
    rw ["[", "<-", expr fn, "]"] [],
    apply [expr ne.symm],
    exact [expr nat.find_spec this] },
  { apply [expr ne_of_gt],
    refine [expr increasing_cantor_function h1 h2 (λ k hk, (hn k hk).symm) _ fn],
    apply [expr eq_ff_of_not_eq_tt],
    rw ["[", "<-", expr fn, "]"] [],
    apply [expr ne.symm],
    exact [expr nat.find_spec this] }
end

/-- The cardinality of the reals, as a type. -/
theorem mk_real : # ℝ = 𝔠 :=
  by 
    apply le_antisymmₓ
    ·
      rw [real.equiv_Cauchy.cardinal_eq]
      apply mk_quotient_le.trans 
      apply (mk_subtype_le _).trans_eq 
      rw [←power_def, mk_nat, mk_rat, omega_power_omega]
    ·
      convert mk_le_of_injective (cantor_function_injective _ _)
      rw [←power_def, mk_bool, mk_nat, two_power_omega]
      exact 1 / 3
      normNum 
      normNum

/-- The cardinality of the reals, as a set. -/
theorem mk_univ_real : # (Set.Univ : Set ℝ) = 𝔠 :=
  by 
    rw [mk_univ, mk_real]

/-- **Non-Denumerability of the Continuum**: The reals are not countable. -/
theorem not_countable_real : ¬countable (Set.Univ : Set ℝ) :=
  by 
    rw [←mk_set_le_omega, not_leₓ, mk_univ_real]
    apply cantor

-- error in Data.Real.Cardinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The cardinality of the interval (a, ∞). -/
theorem mk_Ioi_real (a : exprℝ()) : «expr = »(«expr#»() (Ioi a), expr𝔠()) :=
begin
  refine [expr le_antisymm «expr ▸ »(mk_real, mk_set_le _) _],
  rw ["[", "<-", expr not_lt, "]"] [],
  intro [ident h],
  refine [expr ne_of_lt _ mk_univ_real],
  have [ident hu] [":", expr «expr = »(«expr ∪ »(«expr ∪ »(Iio a, {a}), Ioi a), set.univ)] [],
  { convert [] [expr Iic_union_Ioi] [],
    exact [expr Iio_union_right] },
  rw ["<-", expr hu] [],
  refine [expr lt_of_le_of_lt (mk_union_le _ _) _],
  refine [expr lt_of_le_of_lt (add_le_add_right (mk_union_le _ _) _) _],
  have [ident h2] [":", expr «expr = »(«expr '' »(λ x, «expr - »(«expr + »(a, a), x), Ioi a), Iio a)] [],
  { convert [] [expr image_const_sub_Ioi _ _] [],
    simp [] [] [] [] [] [] },
  rw ["<-", expr h2] [],
  refine [expr add_lt_of_lt (cantor _).le _ h],
  refine [expr add_lt_of_lt (cantor _).le (mk_image_le.trans_lt h) _],
  rw [expr mk_singleton] [],
  exact [expr one_lt_omega.trans (cantor _)]
end

/-- The cardinality of the interval [a, ∞). -/
theorem mk_Ici_real (a : ℝ) : # (Ici a) = 𝔠 :=
  le_antisymmₓ (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)

-- error in Data.Real.Cardinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The cardinality of the interval (-∞, a). -/
theorem mk_Iio_real (a : exprℝ()) : «expr = »(«expr#»() (Iio a), expr𝔠()) :=
begin
  refine [expr le_antisymm «expr ▸ »(mk_real, mk_set_le _) _],
  have [ident h2] [":", expr «expr = »(«expr '' »(λ x, «expr - »(«expr + »(a, a), x), Iio a), Ioi a)] [],
  { convert [] [expr image_const_sub_Iio _ _] [],
    simp [] [] [] [] [] [] },
  exact [expr «expr ▸ »(mk_Ioi_real a, «expr ▸ »(h2, mk_image_le))]
end

/-- The cardinality of the interval (-∞, a]. -/
theorem mk_Iic_real (a : ℝ) : # (Iic a) = 𝔠 :=
  le_antisymmₓ (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)

-- error in Data.Real.Cardinality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The cardinality of the interval (a, b). -/
theorem mk_Ioo_real {a b : exprℝ()} (h : «expr < »(a, b)) : «expr = »(«expr#»() (Ioo a b), expr𝔠()) :=
begin
  refine [expr le_antisymm «expr ▸ »(mk_real, mk_set_le _) _],
  have [ident h1] [":", expr «expr ≤ »(«expr#»() «expr '' »(λ
     x, «expr - »(x, a), Ioo a b), «expr#»() (Ioo a b))] [":=", expr mk_image_le],
  refine [expr le_trans _ h1],
  rw ["[", expr image_sub_const_Ioo, ",", expr sub_self, "]"] [],
  replace [ident h] [] [":=", expr sub_pos_of_lt h],
  have [ident h2] [":", expr «expr ≤ »(«expr#»() «expr '' »(has_inv.inv, Ioo 0 «expr - »(b, a)), «expr#»() (Ioo 0 «expr - »(b, a)))] [":=", expr mk_image_le],
  refine [expr le_trans _ h2],
  rw ["[", expr image_inv_Ioo_0_left h, ",", expr mk_Ioi_real, "]"] []
end

/-- The cardinality of the interval [a, b). -/
theorem mk_Ico_real {a b : ℝ} (h : a < b) : # (Ico a b) = 𝔠 :=
  le_antisymmₓ (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)

/-- The cardinality of the interval [a, b]. -/
theorem mk_Icc_real {a b : ℝ} (h : a < b) : # (Icc a b) = 𝔠 :=
  le_antisymmₓ (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)

/-- The cardinality of the interval (a, b]. -/
theorem mk_Ioc_real {a b : ℝ} (h : a < b) : # (Ioc a b) = 𝔠 :=
  le_antisymmₓ (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)

end Cardinal

