import Mathbin.Data.Polynomial.AlgebraMap 
import Mathbin.Data.Polynomial.Degree.Lemmas 
import Mathbin.Data.Polynomial.Div

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

-/


noncomputable theory

open_locale Classical

open Finset

namespace Polynomial

universe u v w z

variable{R : Type u}{S : Type v}{T : Type w}{A : Type z}{a b : R}{n : ℕ}

section CommRingₓ

variable[CommRingₓ R]{p q : Polynomial R}

variable[CommRingₓ S]

theorem nat_degree_pos_of_aeval_root [Algebra R S] {p : Polynomial R} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
  (inj : ∀ (x : R), algebraMap R S x = 0 → x = 0) : 0 < p.nat_degree :=
  nat_degree_pos_of_eval₂_root hp (algebraMap R S) hz inj

theorem degree_pos_of_aeval_root [Algebra R S] {p : Polynomial R} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
  (inj : ∀ (x : R), algebraMap R S x = 0 → x = 0) : 0 < p.degree :=
  nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_aeval_root hp hz inj)

theorem aeval_mod_by_monic_eq_self_of_root [Algebra R S] {p q : Polynomial R} (hq : q.monic) {x : S}
  (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p :=
  eval₂_mod_by_monic_eq_self_of_root hq hx

theorem mod_by_monic_eq_of_dvd_sub [Nontrivial R] (hq : q.monic) {p₁ p₂ : Polynomial R} (h : q ∣ p₁ - p₂) :
  p₁ %ₘ q = p₂ %ₘ q :=
  by 
    obtain ⟨f, sub_eq⟩ := h 
    refine' (div_mod_by_monic_unique ((p₂ /ₘ q)+f) _ hq ⟨_, degree_mod_by_monic_lt _ hq⟩).2
    rw [sub_eq_iff_eq_add.mp sub_eq, mul_addₓ, ←add_assocₓ, mod_by_monic_add_div _ hq, add_commₓ]

theorem add_mod_by_monic [Nontrivial R] (hq : q.monic) (p₁ p₂ : Polynomial R) : (p₁+p₂) %ₘ q = (p₁ %ₘ q)+p₂ %ₘ q :=
  (div_mod_by_monic_unique ((p₁ /ₘ q)+p₂ /ₘ q) _ hq
      ⟨by 
          rw [mul_addₓ, add_left_commₓ, add_assocₓ, mod_by_monic_add_div _ hq, ←add_assocₓ, add_commₓ (q*_),
            mod_by_monic_add_div _ hq],
        (degree_add_le _ _).trans_lt (max_ltₓ (degree_mod_by_monic_lt _ hq) (degree_mod_by_monic_lt _ hq))⟩).2

theorem smul_mod_by_monic [Nontrivial R] (hq : q.monic) (c : R) (p : Polynomial R) : c • p %ₘ q = c • (p %ₘ q) :=
  (div_mod_by_monic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
      ⟨by 
          rw [mul_smul_comm, ←smul_add, mod_by_monic_add_div p hq],
        (degree_smul_le _ _).trans_lt (degree_mod_by_monic_lt _ hq)⟩).2

/--
`polynomial.mod_by_monic_hom (hq : monic (q : polynomial R))` is `_ %ₘ q` as a `R`-linear map.
-/
@[simps]
def mod_by_monic_hom [Nontrivial R] (hq : q.monic) : Polynomial R →ₗ[R] Polynomial R :=
  { toFun := fun p => p %ₘ q, map_add' := add_mod_by_monic hq, map_smul' := smul_mod_by_monic hq }

end CommRingₓ

section NoZeroDivisors

variable[Ringₓ R][NoZeroDivisors R]{p q : Polynomial R}

instance  : NoZeroDivisors (Polynomial R) :=
  { eq_zero_or_eq_zero_of_mul_eq_zero :=
      fun a b h =>
        by 
          rw [←leading_coeff_eq_zero, ←leading_coeff_eq_zero]
          refine' eq_zero_or_eq_zero_of_mul_eq_zero _ 
          rw [←leading_coeff_zero, ←leading_coeff_mul, h] }

theorem nat_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p*q) = nat_degree p+nat_degree q :=
  by 
    rw [←WithBot.coe_eq_coe, ←degree_eq_nat_degree (mul_ne_zero hp hq), WithBot.coe_add, ←degree_eq_nat_degree hp,
      ←degree_eq_nat_degree hq, degree_mul]

@[simp]
theorem nat_degree_pow (p : Polynomial R) (n : ℕ) : nat_degree (p ^ n) = n*nat_degree p :=
  if hp0 : p = 0 then
    if hn0 : n = 0 then
      by 
        simp [hp0, hn0]
    else
      by 
        rw [hp0, zero_pow (Nat.pos_of_ne_zeroₓ hn0)] <;> simp 
  else
    nat_degree_pow'
      (by 
        rw [←leading_coeff_pow, Ne.def, leading_coeff_eq_zero] <;> exact pow_ne_zero _ hp0)

theorem degree_le_mul_left (p : Polynomial R) (hq : q ≠ 0) : degree p ≤ degree (p*q) :=
  if hp : p = 0 then
    by 
      simp only [hp, zero_mul, le_reflₓ]
  else
    by 
      rw [degree_mul, degree_eq_nat_degree hp, degree_eq_nat_degree hq] <;>
        exact WithBot.coe_le_coe.2 (Nat.le_add_rightₓ _ _)

theorem nat_degree_le_of_dvd {p q : Polynomial R} (h1 : p ∣ q) (h2 : q ≠ 0) : p.nat_degree ≤ q.nat_degree :=
  by 
    rcases h1 with ⟨q, rfl⟩
    rw [mul_ne_zero_iff] at h2 
    rw [nat_degree_mul h2.1 h2.2]
    exact Nat.le_add_rightₓ _ _

end NoZeroDivisors

section NoZeroDivisors

variable[CommRingₓ R][NoZeroDivisors R]{p q : Polynomial R}

theorem root_mul : is_root (p*q) a ↔ is_root p a ∨ is_root q a :=
  by 
    simpRw [is_root, eval_mul, mul_eq_zero]

theorem root_or_root_of_root_mul (h : is_root (p*q) a) : is_root p a ∨ is_root q a :=
  root_mul.1 h

end NoZeroDivisors

section Ringₓ

variable[Ringₓ R][IsDomain R]{p q : Polynomial R}

instance  : IsDomain (Polynomial R) :=
  { Polynomial.no_zero_divisors, Polynomial.nontrivial with  }

theorem nat_trailing_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) :
  (p*q).natTrailingDegree = p.nat_trailing_degree+q.nat_trailing_degree :=
  by 
    simp only [←tsub_eq_of_eq_add_rev (nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree _)]
    rw [reverse_mul_of_domain, nat_degree_mul hp hq,
      nat_degree_mul (mt reverse_eq_zero.mp hp) (mt reverse_eq_zero.mp hq), reverse_nat_degree, reverse_nat_degree,
      tsub_add_eq_tsub_tsub, Nat.add_comm, add_tsub_assoc_of_le (Nat.sub_leₓ _ _), add_commₓ,
      add_tsub_assoc_of_le (Nat.sub_leₓ _ _)]

end Ringₓ

section CommRingₓ

variable[CommRingₓ R][IsDomain R]{p q : Polynomial R}

section Roots

open Multiset

theorem degree_eq_zero_of_is_unit (h : IsUnit p) : degree p = 0 :=
  let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h 
  have hp0 : p ≠ 0 :=
    fun hp0 =>
      by 
        simpa [hp0] using hq 
  have hq0 : q ≠ 0 :=
    fun hp0 =>
      by 
        simpa [hp0] using hq 
  have  : nat_degree (1 : Polynomial R) = nat_degree (p*q) := congr_argₓ _ hq 
  by 
    rw [nat_degree_one, nat_degree_mul hp0 hq0, eq_comm, _root_.add_eq_zero_iff, ←WithBot.coe_eq_coe,
        ←degree_eq_nat_degree hp0] at this <;>
      exact this.1

@[simp]
theorem degree_coe_units (u : Units (Polynomial R)) : degree (u : Polynomial R) = 0 :=
  degree_eq_zero_of_is_unit ⟨u, rfl⟩

theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_is_unit_X_sub_C r,
    fun _ _ =>
      by 
        simpRw [dvd_iff_is_root, is_root.def, eval_mul, mul_eq_zero]
        exact id⟩

theorem prime_X : Prime (X : Polynomial R) :=
  by 
    convert prime_X_sub_C (0 : R)
    simp 

theorem monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : monic p) : Prime p :=
  have  : p = X - C (-p.coeff 0) :=
    by 
      simpa [hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1 
  this.symm ▸ prime_X_sub_C _

theorem irreducible_X_sub_C (r : R) : Irreducible (X - C r) :=
  (prime_X_sub_C r).Irreducible

theorem irreducible_X : Irreducible (X : Polynomial R) :=
  Prime.irreducible prime_X

theorem monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).Irreducible

theorem eq_of_monic_of_associated (hp : p.monic) (hq : q.monic) (hpq : Associated p q) : p = q :=
  by 
    obtain ⟨u, hu⟩ := hpq 
    unfold monic  at hp hq 
    rw [eq_C_of_degree_le_zero (le_of_eqₓ$ degree_coe_units _)] at hu 
    rw [←hu, leading_coeff_mul, hp, one_mulₓ, leading_coeff_C] at hq 
    rwa [hq, C_1, mul_oneₓ] at hu 
    infer_instance

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem root_multiplicity_mul
{p q : polynomial R}
{x : R}
(hpq : «expr ≠ »(«expr * »(p, q), 0)) : «expr = »(root_multiplicity x «expr * »(p, q), «expr + »(root_multiplicity x p, root_multiplicity x q)) :=
begin
  have [ident hp] [":", expr «expr ≠ »(p, 0)] [":=", expr left_ne_zero_of_mul hpq],
  have [ident hq] [":", expr «expr ≠ »(q, 0)] [":=", expr right_ne_zero_of_mul hpq],
  rw ["[", expr root_multiplicity_eq_multiplicity «expr * »(p, q), ",", expr dif_neg hpq, ",", expr root_multiplicity_eq_multiplicity p, ",", expr dif_neg hp, ",", expr root_multiplicity_eq_multiplicity q, ",", expr dif_neg hq, ",", expr multiplicity.mul' (prime_X_sub_C x), "]"] []
end

theorem root_multiplicity_X_sub_C_self {x : R} : root_multiplicity x (X - C x) = 1 :=
  by 
    rw [root_multiplicity_eq_multiplicity, dif_neg (X_sub_C_ne_zero x), multiplicity.get_multiplicity_self]

theorem root_multiplicity_X_sub_C {x y : R} : root_multiplicity x (X - C y) = if x = y then 1 else 0 :=
  by 
    splitIfs with hxy
    ·
      rw [hxy]
      exact root_multiplicity_X_sub_C_self 
    exact root_multiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem root_multiplicity_X_sub_C_pow
(a : R)
(n : exprℕ()) : «expr = »(root_multiplicity a «expr ^ »(«expr - »(X, C a), n), n) :=
begin
  induction [expr n] [] ["with", ident n, ident hn] [],
  { refine [expr root_multiplicity_eq_zero _],
    simp [] [] ["only"] ["[", expr eval_one, ",", expr is_root.def, ",", expr not_false_iff, ",", expr one_ne_zero, ",", expr pow_zero, "]"] [] [] },
  have [ident hzero] [] [":=", expr ne_zero_of_monic (monic_pow (monic_X_sub_C a) n.succ)],
  rw [expr pow_succ «expr - »(X, C a) n] ["at", ident hzero, "⊢"],
  simp [] [] ["only"] ["[", expr root_multiplicity_mul hzero, ",", expr root_multiplicity_X_sub_C_self, ",", expr hn, ",", expr nat.one_add, "]"] [] []
end

/-- If `(X - a) ^ n` divides a polynomial `p` then the multiplicity of `a` as root of `p` is at
least `n`. -/
theorem root_multiplicity_of_dvd {p : Polynomial R} {a : R} {n : ℕ} (hzero : p ≠ 0) (h : (X - C a) ^ n ∣ p) :
  n ≤ root_multiplicity a p :=
  by 
    obtain ⟨q, hq⟩ := exists_eq_mul_right_of_dvd h 
    rw [hq] at hzero 
    simp only [hq, root_multiplicity_mul hzero, root_multiplicity_X_sub_C_pow, ge_iff_le, _root_.zero_le,
      le_add_iff_nonneg_right]

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
theorem root_multiplicity_add
{p q : polynomial R}
(a : R)
(hzero : «expr ≠ »(«expr + »(p, q), 0)) : «expr ≤ »(min (root_multiplicity a p) (root_multiplicity a q), root_multiplicity a «expr + »(p, q)) :=
begin
  refine [expr root_multiplicity_of_dvd hzero _],
  have [ident hdivp] [":", expr «expr ∣ »(«expr ^ »(«expr - »(X, C a), root_multiplicity a p), p)] [":=", expr pow_root_multiplicity_dvd p a],
  have [ident hdivq] [":", expr «expr ∣ »(«expr ^ »(«expr - »(X, C a), root_multiplicity a q), q)] [":=", expr pow_root_multiplicity_dvd q a],
  exact [expr min_pow_dvd_add hdivp hdivq]
end

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_multiset_roots : ∀
{p : polynomial R}
(hp : «expr ≠ »(p, 0)), «expr∃ , »((s : multiset R), «expr ∧ »(«expr ≤ »((s.card : with_bot exprℕ()), degree p), ∀
  a, «expr = »(s.count a, root_multiplicity a p)))
| p := λ
hp, by haveI [] [] [":=", expr classical.prop_decidable «expr∃ , »((x), is_root p x)]; exact [expr if h : «expr∃ , »((x), is_root p x) then let ⟨x, hx⟩ := h in
 have hpd : «expr < »(0, degree p) := degree_pos_of_root hp hx,
 have hd0 : «expr ≠ »(«expr /ₘ »(p, «expr - »(X, C x)), 0) := λ
 h, by rw ["[", "<-", expr mul_div_by_monic_eq_iff_is_root.2 hx, ",", expr h, ",", expr mul_zero, "]"] ["at", ident hp]; exact [expr hp rfl],
 have wf : «expr < »(degree «expr /ₘ »(p, _), degree p) := degree_div_by_monic_lt _ (monic_X_sub_C x) hp «expr ▸ »((degree_X_sub_C x).symm, exprdec_trivial()),
 let ⟨t, htd, htr⟩ := @exists_multiset_roots «expr /ₘ »(p, «expr - »(X, C x)) hd0 in
 have hdeg : «expr ≤ »(degree «expr - »(X, C x), degree p) := begin
   rw ["[", expr degree_X_sub_C, ",", expr degree_eq_nat_degree hp, "]"] [],
   rw [expr degree_eq_nat_degree hp] ["at", ident hpd],
   exact [expr with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 hpd)]
 end,
 have hdiv0 : «expr ≠ »(«expr /ₘ »(p, «expr - »(X, C x)), 0) := «expr $ »(mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)).1, not_lt.2 hdeg),
 ⟨«expr ::ₘ »(x, t), calc
    «expr = »((card «expr ::ₘ »(x, t) : with_bot exprℕ()), «expr + »(t.card, 1)) : by exact_mod_cast [expr card_cons _ _]
    «expr ≤ »(..., degree p) : by rw ["[", "<-", expr degree_add_div_by_monic (monic_X_sub_C x) hdeg, ",", expr degree_X_sub_C, ",", expr add_comm, "]"] []; exact [expr add_le_add (le_refl (1 : with_bot exprℕ())) htd], begin
    assume [binders (a)],
    conv_rhs [] [] { rw ["<-", expr mul_div_by_monic_eq_iff_is_root.mpr hx] },
    rw ["[", expr root_multiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0), ",", expr root_multiplicity_X_sub_C, ",", "<-", expr htr a, "]"] [],
    split_ifs [] ["with", ident ha],
    { rw ["[", expr ha, ",", expr count_cons_self, ",", expr nat.succ_eq_add_one, ",", expr add_comm, "]"] [] },
    { rw ["[", expr count_cons_of_ne ha, ",", expr zero_add, "]"] [] }
  end⟩ else ⟨0, «expr ▸ »((degree_eq_nat_degree hp).symm, with_bot.coe_le_coe.2 (nat.zero_le _)), by { intro [ident a],
    rw ["[", expr count_zero, ",", expr root_multiplicity_eq_zero (not_exists.mp h a), "]"] [] }⟩]

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : Polynomial R) : Multiset R :=
  if h : p = 0 then ∅ else Classical.some (exists_multiset_roots h)

@[simp]
theorem roots_zero : (0 : Polynomial R).roots = 0 :=
  dif_pos rfl

theorem card_roots (hp0 : p ≠ 0) : ((roots p).card : WithBot ℕ) ≤ degree p :=
  by 
    unfold roots 
    rw [dif_neg hp0]
    exact (Classical.some_spec (exists_multiset_roots hp0)).1

theorem card_roots' {p : Polynomial R} (hp0 : p ≠ 0) : p.roots.card ≤ nat_degree p :=
  WithBot.coe_le_coe.1 (le_transₓ (card_roots hp0) (le_of_eqₓ$ degree_eq_nat_degree hp0))

theorem card_roots_sub_C {p : Polynomial R} {a : R} (hp0 : 0 < degree p) :
  ((p - C a).roots.card : WithBot ℕ) ≤ degree p :=
  calc ((p - C a).roots.card : WithBot ℕ) ≤ degree (p - C a) :=
    card_roots$ mt sub_eq_zero.1$ fun h => not_le_of_gtₓ hp0$ h.symm ▸ degree_C_le 
    _ = degree p :=
    by 
      rw [sub_eq_add_neg, ←C_neg] <;> exact degree_add_C hp0
    

theorem card_roots_sub_C' {p : Polynomial R} {a : R} (hp0 : 0 < degree p) : (p - C a).roots.card ≤ nat_degree p :=
  WithBot.coe_le_coe.1
    (le_transₓ (card_roots_sub_C hp0)
      (le_of_eqₓ$
        degree_eq_nat_degree
          fun h =>
            by 
              simp_all [lt_irreflₓ]))

@[simp]
theorem count_roots (hp : p ≠ 0) : p.roots.count a = root_multiplicity a p :=
  by 
    rw [roots, dif_neg hp]
    exact (Classical.some_spec (exists_multiset_roots hp)).2 a

@[simp]
theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a :=
  by 
    rw [←count_pos, count_roots hp, root_multiplicity_pos hp]

theorem eq_zero_of_infinite_is_root (p : Polynomial R) (h : Set.Infinite { x | is_root p x }) : p = 0 :=
  by 
    byContra hp 
    apply h 
    convert p.roots.to_finset.finite_to_set using 1 
    ext1 r 
    simp only [mem_roots hp, Multiset.mem_to_finset, Set.mem_set_of_eq, Finset.mem_coe]

theorem exists_max_root [LinearOrderₓ R] (p : Polynomial R) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.is_root x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _$ not_not.mp (mt (eq_zero_of_infinite_is_root p) hp)

theorem exists_min_root [LinearOrderₓ R] (p : Polynomial R) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.is_root x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _$ not_not.mp (mt (eq_zero_of_infinite_is_root p) hp)

theorem eq_of_infinite_eval_eq {R : Type _} [CommRingₓ R] [IsDomain R] (p q : Polynomial R)
  (h : Set.Infinite { x | eval x p = eval x q }) : p = q :=
  by 
    rw [←sub_eq_zero]
    apply eq_zero_of_infinite_is_root 
    simpa only [is_root, eval_sub, sub_eq_zero]

theorem roots_mul {p q : Polynomial R} (hpq : (p*q) ≠ 0) : (p*q).roots = p.roots+q.roots :=
  Multiset.ext.mpr$
    fun r =>
      by 
        rw [count_add, count_roots hpq, count_roots (left_ne_zero_of_mul hpq), count_roots (right_ne_zero_of_mul hpq),
          root_multiplicity_mul hpq]

@[simp]
theorem mem_roots_sub_C {p : Polynomial R} {a x : R} (hp0 : 0 < degree p) : x ∈ (p - C a).roots ↔ p.eval x = a :=
  (mem_roots (show p - C a ≠ 0 from mt sub_eq_zero.1$ fun h => not_le_of_gtₓ hp0$ h.symm ▸ degree_C_le)).trans
    (by 
      rw [is_root.def, eval_sub, eval_C, sub_eq_zero])

@[simp]
theorem roots_X_sub_C (r : R) : roots (X - C r) = {r} :=
  by 
    ext s 
    rw [count_roots (X_sub_C_ne_zero r), root_multiplicity_X_sub_C]
    splitIfs with h
    ·
      rw [h, count_singleton_self]
    ·
      rw [singleton_eq_cons, count_cons_of_ne h, count_zero]

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem roots_C (x : R) : «expr = »((C x).roots, 0) :=
if H : «expr = »(x, 0) then by rw ["[", expr H, ",", expr C_0, ",", expr roots_zero, "]"] [] else «expr $ »(multiset.ext.mpr, λ
 r, have h : «expr ≠ »(C x, 0), from λ h, «expr $ »(H, «expr $ »(C_inj.1, «expr ▸ »(h.symm, C_0.symm))),
 have not_root : «expr¬ »(is_root (C x) r) := mt (λ h : «expr = »(eval r (C x), 0), trans eval_C.symm h) H,
 by rw ["[", expr count_roots h, ",", expr count_zero, ",", expr root_multiplicity_eq_zero not_root, "]"] [])

@[simp]
theorem roots_one : (1 : Polynomial R).roots = ∅ :=
  roots_C 1

theorem roots_list_prod (L : List (Polynomial R)) :
  (0 : Polynomial R) ∉ L → L.prod.roots = (L : Multiset (Polynomial R)).bind roots :=
  (List.recOn L fun _ => roots_one)$
    fun hd tl ih H =>
      by 
        rw [List.mem_cons_iffₓ, not_or_distrib] at H 
        rw [List.prod_cons, roots_mul (mul_ne_zero (Ne.symm H.1)$ List.prod_ne_zero H.2), ←Multiset.cons_coe,
          Multiset.cons_bind, ih H.2]

theorem roots_multiset_prod (m : Multiset (Polynomial R)) : (0 : Polynomial R) ∉ m → m.prod.roots = m.bind roots :=
  by 
    rcases m with ⟨L⟩
    simpa only [coe_prod, quot_mk_to_coe''] using roots_list_prod L

theorem roots_prod {ι : Type _} (f : ι → Polynomial R) (s : Finset ι) :
  s.prod f ≠ 0 → (s.prod f).roots = s.val.bind fun i => roots (f i) :=
  by 
    rcases s with ⟨m, hm⟩
    simpa [Multiset.prod_eq_zero_iff, bind_map] using roots_multiset_prod (m.map f)

theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val :=
  (roots_prod (fun a => X - C a) s (prod_ne_zero_iff.mpr fun a _ => X_sub_C_ne_zero a)).trans
    (by 
      simpRw [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_id'])

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : (roots ((X : Polynomial R) ^ n - C a)).card ≤ n :=
  WithBot.coe_le_coe.1$
    calc ((roots ((X : Polynomial R) ^ n - C a)).card : WithBot ℕ) ≤ degree ((X : Polynomial R) ^ n - C a) :=
      card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a
      

section NthRoots

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nth_roots (n : ℕ) (a : R) : Multiset R :=
  roots ((X : Polynomial R) ^ n - C a)

@[simp]
theorem mem_nth_roots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nth_roots n a ↔ x ^ n = a :=
  by 
    rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a), is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero]

@[simp]
theorem nth_roots_zero (r : R) : nth_roots 0 r = 0 :=
  by 
    simp only [empty_eq_zero, pow_zeroₓ, nth_roots, ←C_1, ←C_sub, roots_C]

theorem card_nth_roots (n : ℕ) (a : R) : (nth_roots n a).card ≤ n :=
  if hn : n = 0 then
    if h : (X : Polynomial R) ^ n - C a = 0 then
      by 
        simp only [Nat.zero_leₓ, nth_roots, roots, h, dif_pos rfl, empty_eq_zero, card_zero]
    else
      WithBot.coe_le_coe.1
        (le_transₓ (card_roots h)
          (by 
            rw [hn, pow_zeroₓ, ←C_1, ←RingHom.map_sub]
            exact degree_C_le))
  else
    by 
      rw [←WithBot.coe_le_coe, ←degree_X_pow_sub_C (Nat.pos_of_ne_zeroₓ hn) a] <;>
        exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zeroₓ hn) a)

/-- The multiset `nth_roots ↑n (1 : R)` as a finset. -/
def nth_roots_finset (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : Finset R :=
  Multiset.toFinset (nth_roots n (1 : R))

@[simp]
theorem mem_nth_roots_finset {n : ℕ} (h : 0 < n) {x : R} : x ∈ nth_roots_finset n R ↔ x ^ (n : ℕ) = 1 :=
  by 
    rw [nth_roots_finset, mem_to_finset, mem_nth_roots h]

end NthRoots

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coeff_comp_degree_mul_degree
(hqd0 : «expr ≠ »(nat_degree q, 0)) : «expr = »(coeff (p.comp q) «expr * »(nat_degree p, nat_degree q), «expr * »(leading_coeff p, «expr ^ »(leading_coeff q, nat_degree p))) :=
if hp0 : «expr = »(p, 0) then by simp [] [] [] ["[", expr hp0, "]"] [] [] else calc
  «expr = »(coeff (p.comp q) «expr * »(nat_degree p, nat_degree q), p.sum (λ
    n
    a, coeff «expr * »(C a, «expr ^ »(q, n)) «expr * »(nat_degree p, nat_degree q))) : by rw ["[", expr comp, ",", expr eval₂, ",", expr coeff_sum, "]"] []
  «expr = »(..., coeff «expr * »(C (leading_coeff p), «expr ^ »(q, nat_degree p)) «expr * »(nat_degree p, nat_degree q)) : finset.sum_eq_single _ (begin
     assume [binders (b hbs hbp)],
     have [ident hq0] [":", expr «expr ≠ »(q, 0)] [],
     from [expr λ hq0, hqd0 (by rw ["[", expr hq0, ",", expr nat_degree_zero, "]"] [])],
     have [] [":", expr «expr ≠ »(coeff p b, 0)] [],
     by rwa [expr mem_support_iff] ["at", ident hbs],
     refine [expr coeff_eq_zero_of_degree_lt _],
     erw ["[", expr degree_mul, ",", expr degree_C this, ",", expr degree_pow, ",", expr zero_add, ",", expr degree_eq_nat_degree hq0, ",", "<-", expr with_bot.coe_nsmul, ",", expr nsmul_eq_mul, ",", expr with_bot.coe_lt_coe, ",", expr nat.cast_id, ",", expr mul_lt_mul_right (pos_iff_ne_zero.mpr hqd0), "]"] [],
     exact [expr lt_of_le_of_ne (le_nat_degree_of_ne_zero this) hbp]
   end) (begin
     intro [ident h],
     contrapose ["!"] [ident hp0],
     rw [expr mem_support_iff] ["at", ident h],
     push_neg ["at", ident h],
     rwa ["<-", expr leading_coeff_eq_zero] []
   end)
  «expr = »(..., _) : have «expr = »(coeff «expr ^ »(q, nat_degree p) «expr * »(nat_degree p, nat_degree q), leading_coeff «expr ^ »(q, nat_degree p)), by rw ["[", expr leading_coeff, ",", expr nat_degree_pow, "]"] [],
  by rw ["[", expr coeff_C_mul, ",", expr this, ",", expr leading_coeff_pow, "]"] []

theorem nat_degree_comp : nat_degree (p.comp q) = nat_degree p*nat_degree q :=
  le_antisymmₓ nat_degree_comp_le
    (if hp0 : p = 0 then
      by 
        rw [hp0, zero_comp, nat_degree_zero, zero_mul]
    else
      if hqd0 : nat_degree q = 0 then
        have  : degree q ≤ 0 :=
          by 
            rw [←WithBot.coe_zero, ←hqd0] <;> exact degree_le_nat_degree 
        by 
          rw [eq_C_of_degree_le_zero this] <;> simp 
      else
        le_nat_degree_of_ne_zero$
          have hq0 : q ≠ 0 :=
            fun hq0 =>
              hqd0$
                by 
                  rw [hq0, nat_degree_zero]
          calc coeff (p.comp q) (nat_degree p*nat_degree q) = leading_coeff p*leading_coeff q ^ nat_degree p :=
            coeff_comp_degree_mul_degree hqd0 
            _ ≠ 0 := mul_ne_zero (mt leading_coeff_eq_zero.1 hp0) (pow_ne_zero _ (mt leading_coeff_eq_zero.1 hq0))
            )

theorem leading_coeff_comp (hq : nat_degree q ≠ 0) :
  leading_coeff (p.comp q) = leading_coeff p*leading_coeff q ^ nat_degree p :=
  by 
    rw [←coeff_comp_degree_mul_degree hq, ←nat_degree_comp] <;> rfl

theorem units_coeff_zero_smul (c : Units (Polynomial R)) (p : Polynomial R) : (c : Polynomial R).coeff 0 • p = c*p :=
  by 
    rw [←Polynomial.C_mul', ←Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

@[simp]
theorem nat_degree_coe_units (u : Units (Polynomial R)) : nat_degree (u : Polynomial R) = 0 :=
  nat_degree_eq_of_degree_eq_some (degree_coe_units u)

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_eq_zero_iff : «expr ↔ »(«expr = »(p.comp q, 0), «expr ∨ »(«expr = »(p, 0), «expr ∧ »(«expr = »(p.eval (q.coeff 0), 0), «expr = »(q, C (q.coeff 0))))) :=
begin
  split,
  { intro [ident h],
    have [ident key] [":", expr «expr ∨ »(«expr = »(p.nat_degree, 0), «expr = »(q.nat_degree, 0))] [],
    { rw ["[", "<-", expr mul_eq_zero, ",", "<-", expr nat_degree_comp, ",", expr h, ",", expr nat_degree_zero, "]"] [] },
    replace [ident key] [] [":=", expr or.imp eq_C_of_nat_degree_eq_zero eq_C_of_nat_degree_eq_zero key],
    cases [expr key] [],
    { rw ["[", expr key, ",", expr C_comp, "]"] ["at", ident h],
      exact [expr or.inl (key.trans h)] },
    { rw ["[", expr key, ",", expr comp_C, ",", expr C_eq_zero, "]"] ["at", ident h],
      exact [expr or.inr ⟨h, key⟩] } },
  { exact [expr λ
     h, or.rec (λ
      h, by rw ["[", expr h, ",", expr zero_comp, "]"] []) (λ
      h, by rw ["[", expr h.2, ",", expr comp_C, ",", expr h.1, ",", expr C_0, "]"] []) h] }
end

theorem zero_of_eval_zero [Infinite R] (p : Polynomial R) (h : ∀ x, p.eval x = 0) : p = 0 :=
  by 
    classical <;>
      byContra hp <;>
        exact Fintype.false ⟨p.roots.to_finset, fun x => multiset.mem_to_finset.mpr ((mem_roots hp).mpr (h _))⟩

theorem funext [Infinite R] {p q : Polynomial R} (ext : ∀ (r : R), p.eval r = q.eval r) : p = q :=
  by 
    rw [←sub_eq_zero]
    apply zero_of_eval_zero 
    intro x 
    rw [eval_sub, sub_eq_zero, ext]

variable[CommRingₓ T]

/-- The set of distinct roots of `p` in `E`.

If you have a non-separable polynomial, use `polynomial.roots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def root_set (p : Polynomial T) S [CommRingₓ S] [IsDomain S] [Algebra T S] : Set S :=
  (p.map (algebraMap T S)).roots.toFinset

theorem root_set_def (p : Polynomial T) S [CommRingₓ S] [IsDomain S] [Algebra T S] :
  p.root_set S = (p.map (algebraMap T S)).roots.toFinset :=
  rfl

@[simp]
theorem root_set_zero S [CommRingₓ S] [IsDomain S] [Algebra T S] : (0 : Polynomial T).RootSet S = ∅ :=
  by 
    rw [root_set_def, Polynomial.map_zero, roots_zero, to_finset_zero, Finset.coe_empty]

@[simp]
theorem root_set_C [CommRingₓ S] [IsDomain S] [Algebra T S] (a : T) : (C a).RootSet S = ∅ :=
  by 
    rw [root_set_def, map_C, roots_C, Multiset.to_finset_zero, Finset.coe_empty]

instance root_set_fintype (p : Polynomial T) (S : Type _) [CommRingₓ S] [IsDomain S] [Algebra T S] :
  Fintype (p.root_set S) :=
  FinsetCoe.fintype _

theorem root_set_finite (p : Polynomial T) (S : Type _) [CommRingₓ S] [IsDomain S] [Algebra T S] :
  (p.root_set S).Finite :=
  ⟨Polynomial.rootSetFintype p S⟩

end Roots

theorem is_unit_iff {f : Polynomial R} : IsUnit f ↔ ∃ r : R, IsUnit r ∧ C r = f :=
  ⟨fun hf =>
      ⟨f.coeff 0, is_unit_C.1$ eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf) ▸ hf,
        (eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf)).symm⟩,
    fun ⟨r, hr, hrf⟩ => hrf ▸ is_unit_C.2 hr⟩

theorem coeff_coe_units_zero_ne_zero (u : Units (Polynomial R)) : coeff (u : Polynomial R) 0 ≠ 0 :=
  by 
    conv  in 0 => rw [←nat_degree_coe_units u]
    rw [←leading_coeff, Ne.def, leading_coeff_eq_zero]
    exact Units.ne_zero _

theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q :=
  let ⟨u, hu⟩ := h 
  by 
    simp [hu.symm]

theorem degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : is_root p x) : degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_is_root.2 hx 
  have  : IsUnit (X - C x) ∨ IsUnit g := hi.is_unit_or_is_unit hg 
  this.elim
    (fun h =>
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x 
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_is_unit h 
      by 
        rw [h₁] at h₂ <;>
          exact
            absurd h₂
              (by 
                decide))
    fun hgu =>
      by 
        rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zeroₓ]

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Division by a monic polynomial doesn't change the leading coefficient. -/
theorem leading_coeff_div_by_monic_of_monic
{R : Type u}
[comm_ring R]
[is_domain R]
{p q : polynomial R}
(hmonic : q.monic)
(hdegree : «expr ≤ »(q.degree, p.degree)) : «expr = »(«expr /ₘ »(p, q).leading_coeff, p.leading_coeff) :=
begin
  have [ident hp] [] [":=", expr mod_by_monic_add_div p hmonic],
  have [ident hzero] [":", expr «expr ≠ »(«expr /ₘ »(p, q), 0)] [],
  { intro [ident h],
    exact [expr not_lt_of_le hdegree ((div_by_monic_eq_zero_iff hmonic).1 h)] },
  have [ident deglt] [":", expr «expr < »(«expr %ₘ »(p, q).degree, «expr * »(q, «expr /ₘ »(p, q)).degree)] [],
  { rw [expr degree_mul] [],
    refine [expr lt_of_lt_of_le (degree_mod_by_monic_lt p hmonic) _],
    rw ["[", expr degree_eq_nat_degree (monic.ne_zero hmonic), ",", expr degree_eq_nat_degree hzero, "]"] [],
    norm_cast [],
    simp [] [] ["only"] ["[", expr zero_le, ",", expr le_add_iff_nonneg_right, "]"] [] [] },
  have [ident hrew] [] [":=", expr leading_coeff_add_of_degree_lt deglt],
  rw [expr leading_coeff_mul q «expr /ₘ »(p, q)] ["at", ident hrew],
  simp [] [] ["only"] ["[", expr hmonic, ",", expr one_mul, ",", expr monic.leading_coeff, "]"] [] ["at", ident hrew],
  nth_rewrite [1] ["<-", expr hp] [],
  exact [expr hrew.symm]
end

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_monic_of_dvd_of_nat_degree_le
(hp : p.monic)
(hq : q.monic)
(hdiv : «expr ∣ »(p, q))
(hdeg : «expr ≤ »(q.nat_degree, p.nat_degree)) : «expr = »(q, p) :=
begin
  obtain ["⟨", ident r, ",", ident hr, "⟩", ":=", expr hdiv],
  have [ident rzero] [":", expr «expr ≠ »(r, 0)] [],
  { intro [ident h],
    simpa [] [] [] ["[", expr h, ",", expr monic.ne_zero hq, "]"] [] ["using", expr hr] },
  rw ["[", expr hr, ",", expr nat_degree_mul (monic.ne_zero hp) rzero, "]"] ["at", ident hdeg],
  have [ident hdegeq] [":", expr «expr = »(«expr + »(p.nat_degree, r.nat_degree), p.nat_degree)] [],
  { suffices [ident hdegle] [":", expr «expr ≤ »(p.nat_degree, «expr + »(p.nat_degree, r.nat_degree))],
    { exact [expr le_antisymm hdeg hdegle] },
    exact [expr nat.le.intro rfl] },
  replace [ident hdegeq] [] [":=", expr eq_C_of_nat_degree_eq_zero ((@add_right_inj _ _ p.nat_degree _ 0).1 hdegeq)],
  suffices [ident hlead] [":", expr «expr = »(1, r.leading_coeff)],
  { have [ident hcoeff] [] [":=", expr leading_coeff_C (r.coeff 0)],
    rw ["[", "<-", expr hdegeq, ",", "<-", expr hlead, "]"] ["at", ident hcoeff],
    rw ["[", "<-", expr hcoeff, ",", expr C_1, "]"] ["at", ident hdegeq],
    rwa ["[", expr hdegeq, ",", expr mul_one, "]"] ["at", ident hr] },
  have [ident hprod] [":", expr «expr = »(q.leading_coeff, «expr * »(p.leading_coeff, r.leading_coeff))] [],
  { simp [] [] ["only"] ["[", expr hr, ",", expr leading_coeff_mul, "]"] [] [] },
  rwa ["[", expr monic.leading_coeff hp, ",", expr monic.leading_coeff hq, ",", expr one_mul, "]"] ["at", ident hprod]
end

end CommRingₓ

section 

variable[Semiringₓ R][CommRingₓ S][IsDomain S](φ : R →+* S)

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_unit_of_is_unit_leading_coeff_of_is_unit_map
(f : polynomial R)
(hf : is_unit (leading_coeff f))
(H : is_unit (map φ f)) : is_unit f :=
begin
  have [ident dz] [] [":=", expr degree_eq_zero_of_is_unit H],
  rw [expr degree_map_eq_of_leading_coeff_ne_zero] ["at", ident dz],
  { rw [expr eq_C_of_degree_eq_zero dz] [],
    refine [expr is_unit.map (C.to_monoid_hom : «expr →* »(R, polynomial R)) _],
    convert [] [expr hf] [],
    rw [expr (degree_eq_iff_nat_degree_eq _).1 dz] [],
    rintro [ident rfl],
    simpa [] [] [] [] [] ["using", expr H] },
  { intro [ident h],
    have [ident u] [":", expr is_unit (φ f.leading_coeff)] [":=", expr is_unit.map φ.to_monoid_hom hf],
    rw [expr h] ["at", ident u],
    simpa [] [] [] [] [] ["using", expr u] }
end

end 

section 

variable[CommRingₓ R][IsDomain R][CommRingₓ S][IsDomain S](φ : R →+* S)

-- error in Data.Polynomial.RingDivision: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A polynomial over an integral domain `R` is irreducible if it is monic and
  irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
  it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
theorem monic.irreducible_of_irreducible_map
(f : polynomial R)
(h_mon : monic f)
(h_irr : irreducible (map φ f)) : irreducible f :=
begin
  fsplit,
  { intro [ident h],
    exact [expr h_irr.not_unit (is_unit.map (map_ring_hom φ).to_monoid_hom h)] },
  { intros [ident a, ident b, ident h],
    have [ident q] [] [":=", expr (leading_coeff_mul a b).symm],
    rw ["<-", expr h] ["at", ident q],
    dsimp [] ["[", expr monic, "]"] [] ["at", ident h_mon],
    rw [expr h_mon] ["at", ident q],
    have [ident au] [":", expr is_unit a.leading_coeff] [":=", expr is_unit_of_mul_eq_one _ _ q],
    rw [expr mul_comm] ["at", ident q],
    have [ident bu] [":", expr is_unit b.leading_coeff] [":=", expr is_unit_of_mul_eq_one _ _ q],
    clear [ident q, ident h_mon],
    have [ident h'] [] [":=", expr congr_arg (map φ) h],
    simp [] [] ["only"] ["[", expr map_mul, "]"] [] ["at", ident h'],
    cases [expr h_irr.is_unit_or_is_unit h'] ["with", ident w, ident w],
    { left,
      exact [expr is_unit_of_is_unit_leading_coeff_of_is_unit_map _ _ au w] },
    { right,
      exact [expr is_unit_of_is_unit_leading_coeff_of_is_unit_map _ _ bu w] } }
end

end 

end Polynomial

