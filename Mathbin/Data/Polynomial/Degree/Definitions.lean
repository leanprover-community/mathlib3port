import Mathbin.Data.Nat.WithBot 
import Mathbin.Data.Polynomial.Induction 
import Mathbin.Data.Polynomial.Monomial

/-!
# Theory of univariate polynomials

The definitions include
`degree`, `monic`, `leading_coeff`

Results include
- `degree_mul` : The degree of the product is the sum of degrees
- `leading_coeff_add_of_degree_eq` and `leading_coeff_add_of_degree_lt` :
    The leading_coefficient of a sum is determined by the leading coefficients and degrees
-/


noncomputable theory

open Finsupp Finset

open_locale BigOperators Classical

namespace Polynomial

universe u v

variable{R : Type u}{S : Type v}{a b : R}{n m : ℕ}

section Semiringₓ

variable[Semiringₓ R]{p q r : Polynomial R}

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : Polynomial R) : WithBot ℕ :=
  p.support.sup some

theorem degree_lt_wf : WellFounded fun p q : Polynomial R => degree p < degree q :=
  InvImage.wfₓ degree (WithBot.well_founded_lt Nat.lt_wf)

instance  : HasWellFounded (Polynomial R) :=
  ⟨_, degree_lt_wf⟩

/-- `nat_degree p` forces `degree p` to ℕ, by defining nat_degree 0 = 0. -/
def nat_degree (p : Polynomial R) : ℕ :=
  (degree p).getOrElse 0

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leading_coeff (p : Polynomial R) : R :=
  coeff p (nat_degree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def monic (p : Polynomial R) :=
  leading_coeff p = (1 : R)

@[nontriviality]
theorem monic_of_subsingleton [Subsingleton R] (p : Polynomial R) : monic p :=
  Subsingleton.elimₓ _ _

theorem monic.def : monic p ↔ leading_coeff p = 1 :=
  Iff.rfl

instance monic.decidable [DecidableEq R] : Decidable (monic p) :=
  by 
    unfold monic <;> infer_instance

@[simp]
theorem monic.leading_coeff {p : Polynomial R} (hp : p.monic) : leading_coeff p = 1 :=
  hp

theorem monic.coeff_nat_degree {p : Polynomial R} (hp : p.monic) : p.coeff p.nat_degree = 1 :=
  hp

@[simp]
theorem degree_zero : degree (0 : Polynomial R) = ⊥ :=
  rfl

@[simp]
theorem nat_degree_zero : nat_degree (0 : Polynomial R) = 0 :=
  rfl

@[simp]
theorem coeff_nat_degree : coeff p (nat_degree p) = leading_coeff p :=
  rfl

theorem degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
  ⟨fun h =>
      by 
        rw [degree, ←max_eq_sup_with_bot] at h <;> exact support_eq_empty.1 (max_eq_none.1 h),
    fun h => h.symm ▸ rfl⟩

@[nontriviality]
theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ :=
  by 
    rw [Subsingleton.elimₓ p 0, degree_zero]

@[nontriviality]
theorem nat_degree_of_subsingleton [Subsingleton R] : nat_degree p = 0 :=
  by 
    rw [Subsingleton.elimₓ p 0, nat_degree_zero]

theorem degree_eq_nat_degree (hp : p ≠ 0) : degree p = (nat_degree p : WithBot ℕ) :=
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := not_not.1 hn 
  by 
    rw [nat_degree, hn] <;> rfl

theorem degree_eq_iff_nat_degree_eq {p : Polynomial R} {n : ℕ} (hp : p ≠ 0) : p.degree = n ↔ p.nat_degree = n :=
  by 
    rw [degree_eq_nat_degree hp, WithBot.coe_eq_coe]

theorem degree_eq_iff_nat_degree_eq_of_pos {p : Polynomial R} {n : ℕ} (hn : 0 < n) : p.degree = n ↔ p.nat_degree = n :=
  by 
    split 
    ·
      intro H 
      rwa [←degree_eq_iff_nat_degree_eq]
      rintro rfl 
      rw [degree_zero] at H 
      exact Option.noConfusion H
    ·
      intro H 
      rwa [degree_eq_iff_nat_degree_eq]
      rintro rfl 
      rw [nat_degree_zero] at H 
      rw [H] at hn 
      exact lt_irreflₓ _ hn

theorem nat_degree_eq_of_degree_eq_some {p : Polynomial R} {n : ℕ} (h : degree p = n) : nat_degree p = n :=
  have hp0 : p ≠ 0 :=
    fun hp0 =>
      by 
        rw [hp0] at h <;> exact Option.noConfusion h 
  Option.some_inj.1$
    show (nat_degree p : WithBot ℕ) = n by 
      rwa [←degree_eq_nat_degree hp0]

@[simp]
theorem degree_le_nat_degree : degree p ≤ nat_degree p :=
  WithBot.giGetOrElseBot.gc.le_u_l _

theorem nat_degree_eq_of_degree_eq [Semiringₓ S] {q : Polynomial S} (h : degree p = degree q) :
  nat_degree p = nat_degree q :=
  by 
    unfold nat_degree <;> rw [h]

theorem le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : WithBot ℕ) ≤ degree p :=
  show @LE.le (WithBot ℕ) _ (some n : WithBot ℕ) (p.support.sup some : WithBot ℕ) from
    Finset.le_sup (mem_support_iff.2 h)

theorem le_nat_degree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ nat_degree p :=
  by 
    rw [←WithBot.coe_le_coe, ←degree_eq_nat_degree]
    exact le_degree_of_ne_zero h
    ·
      intro h 
      subst h 
      exact h rfl

theorem le_nat_degree_of_mem_supp (a : ℕ) : a ∈ p.support → a ≤ nat_degree p :=
  le_nat_degree_of_ne_zero ∘ mem_support_iff.mp

theorem supp_subset_range (h : nat_degree p < m) : p.support ⊆ Finset.range m :=
  fun n hn => mem_range.2$ (le_nat_degree_of_mem_supp _ hn).trans_lt h

theorem supp_subset_range_nat_degree_succ : p.support ⊆ Finset.range (nat_degree p+1) :=
  supp_subset_range (Nat.lt_succ_selfₓ _)

theorem degree_le_degree (h : coeff q (nat_degree p) ≠ 0) : degree p ≤ degree q :=
  by 
    byCases' hp : p = 0
    ·
      rw [hp]
      exact bot_le
    ·
      rw [degree_eq_nat_degree hp]
      exact le_degree_of_ne_zero h

theorem degree_ne_of_nat_degree_ne {n : ℕ} : p.nat_degree ≠ n → degree p ≠ n :=
  mt$
    fun h =>
      by 
        rw [nat_degree, h, Option.get_or_else_coe]

theorem nat_degree_le_iff_degree_le {n : ℕ} : nat_degree p ≤ n ↔ degree p ≤ n :=
  WithBot.get_or_else_bot_le_iff

alias Polynomial.nat_degree_le_iff_degree_le ↔ ..

theorem nat_degree_le_nat_degree [Semiringₓ S] {q : Polynomial S} (hpq : p.degree ≤ q.degree) :
  p.nat_degree ≤ q.nat_degree :=
  WithBot.giGetOrElseBot.gc.monotone_l hpq

@[simp]
theorem degree_C (ha : a ≠ 0) : degree (C a) = (0 : WithBot ℕ) :=
  by 
    rw [degree, ←monomial_zero_left, support_monomial 0 _ ha, sup_singleton]
    rfl

theorem degree_C_le : degree (C a) ≤ 0 :=
  by 
    byCases' h : a = 0 <;> [rw [h, C_0], rw [degree_C h]] <;> [exact bot_le, exact le_reflₓ _]

theorem degree_one_le : degree (1 : Polynomial R) ≤ (0 : WithBot ℕ) :=
  by 
    rw [←C_1] <;> exact degree_C_le

-- error in Data.Polynomial.Degree.Definitions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem nat_degree_C (a : R) : «expr = »(nat_degree (C a), 0) :=
begin
  by_cases [expr ha, ":", expr «expr = »(a, 0)],
  { have [] [":", expr «expr = »(C a, 0)] [],
    { rw ["[", expr ha, ",", expr C_0, "]"] [] },
    rw ["[", expr nat_degree, ",", expr degree_eq_bot.2 this, "]"] [],
    refl },
  { rw ["[", expr nat_degree, ",", expr degree_C ha, "]"] [],
    refl }
end

@[simp]
theorem nat_degree_one : nat_degree (1 : Polynomial R) = 0 :=
  nat_degree_C 1

@[simp]
theorem nat_degree_nat_cast (n : ℕ) : nat_degree (n : Polynomial R) = 0 :=
  by 
    simp only [←C_eq_nat_cast, nat_degree_C]

@[simp]
theorem degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n :=
  by 
    rw [degree, support_monomial _ _ ha] <;> rfl

@[simp]
theorem degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : degree (C a*X ^ n) = n :=
  by 
    rw [←monomial_eq_C_mul_X, degree_monomial n ha]

theorem degree_monomial_le (n : ℕ) (a : R) : degree (monomial n a) ≤ n :=
  if h : a = 0 then
    by 
      rw [h, (monomial n).map_zero] <;> exact bot_le
  else le_of_eqₓ (degree_monomial n h)

theorem degree_C_mul_X_pow_le (n : ℕ) (a : R) : degree (C a*X ^ n) ≤ n :=
  by 
    rw [C_mul_X_pow_eq_monomial]
    apply degree_monomial_le

theorem degree_C_mul_X_le (a : R) : degree (C a*X) ≤ 1 :=
  by 
    simpa only [pow_oneₓ] using degree_C_mul_X_pow_le 1 a

@[simp]
theorem nat_degree_C_mul_X_pow (n : ℕ) (a : R) (ha : a ≠ 0) : nat_degree (C a*X ^ n) = n :=
  nat_degree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp]
theorem nat_degree_C_mul_X (a : R) (ha : a ≠ 0) : nat_degree (C a*X) = 1 :=
  by 
    simpa only [pow_oneₓ] using nat_degree_C_mul_X_pow 1 a ha

@[simp]
theorem nat_degree_monomial (i : ℕ) (r : R) (hr : r ≠ 0) : nat_degree (monomial i r) = i :=
  by 
    rw [←C_mul_X_pow_eq_monomial, nat_degree_C_mul_X_pow i r hr]

theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
  not_not.1 (mt le_degree_of_ne_zero (not_le_of_gtₓ h))

theorem coeff_eq_zero_of_nat_degree_lt {p : Polynomial R} {n : ℕ} (h : p.nat_degree < n) : p.coeff n = 0 :=
  by 
    apply coeff_eq_zero_of_degree_lt 
    byCases' hp : p = 0
    ·
      subst hp 
      exact WithBot.bot_lt_coe n
    ·
      rwa [degree_eq_nat_degree hp, WithBot.coe_lt_coe]

@[simp]
theorem coeff_nat_degree_succ_eq_zero {p : Polynomial R} : p.coeff (p.nat_degree+1) = 0 :=
  coeff_eq_zero_of_nat_degree_lt (lt_add_one _)

theorem ite_le_nat_degree_coeff (p : Polynomial R) (n : ℕ) (I : Decidable (n < 1+nat_degree p)) :
  @ite _ (n < 1+nat_degree p) I (coeff p n) 0 = coeff p n :=
  by 
    splitIfs
    ·
      rfl
    ·
      exact (coeff_eq_zero_of_nat_degree_lt (not_leₓ.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm

theorem as_sum_support (p : Polynomial R) : p = ∑i in p.support, monomial i (p.coeff i) :=
  (sum_monomial_eq p).symm

theorem as_sum_support_C_mul_X_pow (p : Polynomial R) : p = ∑i in p.support, C (p.coeff i)*X ^ i :=
  trans p.as_sum_support$
    by 
      simp only [C_mul_X_pow_eq_monomial]

-- error in Data.Polynomial.Degree.Definitions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.nat_degree < n`.
-/
theorem sum_over_range'
[add_comm_monoid S]
(p : polynomial R)
{f : exprℕ() → R → S}
(h : ∀ n, «expr = »(f n 0, 0))
(n : exprℕ())
(w : «expr < »(p.nat_degree, n)) : «expr = »(p.sum f, «expr∑ in , »((a : exprℕ()), range n, f a (coeff p a))) :=
begin
  rcases [expr p],
  have [] [] [":=", expr supp_subset_range w],
  simp [] [] ["only"] ["[", expr polynomial.sum, ",", expr support, ",", expr coeff, ",", expr nat_degree, ",", expr degree, "]"] [] ["at", "⊢", ident this],
  exact [expr finsupp.sum_of_support_subset _ this _ (λ n hn, h n)]
end

/--
We can reexpress a sum over `p.support` as a sum over `range (p.nat_degree + 1)`.
-/
theorem sum_over_range [AddCommMonoidₓ S] (p : Polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
  p.sum f = ∑a : ℕ in range (p.nat_degree+1), f a (coeff p a) :=
  sum_over_range' p h (p.nat_degree+1) (lt_add_one _)

theorem as_sum_range' (p : Polynomial R) (n : ℕ) (w : p.nat_degree < n) : p = ∑i in range n, monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans$ p.sum_over_range' monomial_zero_right _ w

theorem as_sum_range (p : Polynomial R) : p = ∑i in range (p.nat_degree+1), monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans$ p.sum_over_range$ monomial_zero_right

theorem as_sum_range_C_mul_X_pow (p : Polynomial R) : p = ∑i in range (p.nat_degree+1), C (coeff p i)*X ^ i :=
  p.as_sum_range.trans$
    by 
      simp only [C_mul_X_pow_eq_monomial]

theorem coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n ≠ 0 :=
  fun h => mem_support_iff.mp (mem_of_max hn) h

theorem eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) : p = (C (p.coeff 1)*X)+C (p.coeff 0) :=
  ext
    fun n =>
      Nat.casesOn n
        (by 
          simp )
        fun n =>
          Nat.casesOn n
            (by 
              simp [coeff_C])
            fun m =>
              have  : degree p < m.succ.succ :=
                lt_of_le_of_ltₓ h
                  (by 
                    decide)
              by 
                simp [coeff_eq_zero_of_degree_lt this, coeff_C, Nat.succ_ne_zero, coeff_X, Nat.succ_inj', @eq_comm ℕ 0]

theorem eq_X_add_C_of_degree_eq_one (h : degree p = 1) : p = (C p.leading_coeff*X)+C (p.coeff 0) :=
  (eq_X_add_C_of_degree_le_one (show degree p ≤ 1 from h ▸ le_reflₓ _)).trans
    (by 
      simp [leading_coeff, nat_degree_eq_of_degree_eq_some h])

theorem eq_X_add_C_of_nat_degree_le_one (h : nat_degree p ≤ 1) : p = (C (p.coeff 1)*X)+C (p.coeff 0) :=
  eq_X_add_C_of_degree_le_one$ degree_le_of_nat_degree_le h

theorem exists_eq_X_add_C_of_nat_degree_le_one (h : nat_degree p ≤ 1) : ∃ a b, p = (C a*X)+C b :=
  ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_nat_degree_le_one h⟩

theorem degree_X_pow_le (n : ℕ) : degree (X ^ n : Polynomial R) ≤ n :=
  by 
    simpa only [C_1, one_mulₓ] using degree_C_mul_X_pow_le n (1 : R)

theorem degree_X_le : degree (X : Polynomial R) ≤ 1 :=
  degree_monomial_le _ _

theorem nat_degree_X_le : (X : Polynomial R).natDegree ≤ 1 :=
  nat_degree_le_of_degree_le degree_X_le

theorem support_C_mul_X_pow (c : R) (n : ℕ) : (C c*X ^ n).Support ⊆ singleton n :=
  by 
    rw [C_mul_X_pow_eq_monomial]
    exact support_monomial' _ _

theorem mem_support_C_mul_X_pow {n a : ℕ} {c : R} (h : a ∈ (C c*X ^ n).Support) : a = n :=
  mem_singleton.1$ support_C_mul_X_pow _ _ h

theorem card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : (C c*X ^ n).Support.card ≤ 1 :=
  by 
    rw [←card_singleton n]
    apply card_le_of_subset (support_C_mul_X_pow c n)

theorem card_supp_le_succ_nat_degree (p : Polynomial R) : p.support.card ≤ p.nat_degree+1 :=
  by 
    rw [←Finset.card_range (p.nat_degree+1)]
    exact Finset.card_le_of_subset supp_subset_range_nat_degree_succ

theorem le_degree_of_mem_supp (a : ℕ) : a ∈ p.support → «expr↑ » a ≤ degree p :=
  le_degree_of_ne_zero ∘ mem_support_iff.mp

theorem nonempty_support_iff : p.support.nonempty ↔ p ≠ 0 :=
  by 
    rw [Ne.def, nonempty_iff_ne_empty, Ne.def, ←support_eq_empty]

theorem support_C_mul_X_pow_nonzero {c : R} {n : ℕ} (h : c ≠ 0) : (C c*X ^ n).Support = singleton n :=
  by 
    rw [C_mul_X_pow_eq_monomial]
    exact support_monomial _ _ h

end Semiringₓ

section NonzeroSemiring

variable[Semiringₓ R][Nontrivial R]{p q : Polynomial R}

@[simp]
theorem degree_one : degree (1 : Polynomial R) = (0 : WithBot ℕ) :=
  degree_C (show (1 : R) ≠ 0 from zero_ne_one.symm)

@[simp]
theorem degree_X : degree (X : Polynomial R) = 1 :=
  degree_monomial _ one_ne_zero

@[simp]
theorem nat_degree_X : (X : Polynomial R).natDegree = 1 :=
  nat_degree_eq_of_degree_eq_some degree_X

end NonzeroSemiring

section Ringₓ

variable[Ringₓ R]

theorem coeff_mul_X_sub_C {p : Polynomial R} {r : R} {a : ℕ} : coeff (p*X - C r) (a+1) = coeff p a - coeff p (a+1)*r :=
  by 
    simp [mul_sub]

theorem C_eq_int_cast (n : ℤ) : C (n : R) = n :=
  (C : R →+* _).map_int_cast n

@[simp]
theorem degree_neg (p : Polynomial R) : degree (-p) = degree p :=
  by 
    unfold degree <;> rw [support_neg]

@[simp]
theorem nat_degree_neg (p : Polynomial R) : nat_degree (-p) = nat_degree p :=
  by 
    simp [nat_degree]

@[simp]
theorem nat_degree_int_cast (n : ℤ) : nat_degree (n : Polynomial R) = 0 :=
  by 
    simp only [←C_eq_int_cast, nat_degree_C]

end Ringₓ

section Semiringₓ

variable[Semiringₓ R]

/-- The second-highest coefficient, or 0 for constants -/
def next_coeff (p : Polynomial R) : R :=
  if p.nat_degree = 0 then 0 else p.coeff (p.nat_degree - 1)

@[simp]
theorem next_coeff_C_eq_zero (c : R) : next_coeff (C c) = 0 :=
  by 
    rw [next_coeff]
    simp 

theorem next_coeff_of_pos_nat_degree (p : Polynomial R) (hp : 0 < p.nat_degree) :
  next_coeff p = p.coeff (p.nat_degree - 1) :=
  by 
    rw [next_coeff, if_neg]
    contrapose! hp 
    simpa

end Semiringₓ

section Semiringₓ

variable[Semiringₓ R]{p q : Polynomial R}{ι : Type _}

theorem coeff_nat_degree_eq_zero_of_degree_lt (h : degree p < degree q) : coeff p (nat_degree q) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_leₓ h degree_le_nat_degree)

theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree p) : p ≠ 0 :=
  mt degree_eq_bot.2 (Ne.symm (ne_of_ltₓ (lt_of_le_of_ltₓ bot_le h)))

theorem ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
  Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_leₓ
      (bot_lt_iff_ne_bot.mpr
        (by 
          rwa [Ne.def, Polynomial.degree_eq_bot]))
      hpq :
    q.degree > ⊥)

theorem ne_zero_of_nat_degree_gt {n : ℕ} (h : n < nat_degree p) : p ≠ 0 :=
  fun H =>
    by 
      simpa [H, Nat.not_lt_zeroₓ] using h

theorem degree_lt_degree (h : nat_degree p < nat_degree q) : degree p < degree q :=
  by 
    byCases' hp : p = 0
    ·
      simp [hp]
      rw [bot_lt_iff_ne_bot]
      intro hq 
      simpa [hp, degree_eq_bot.mp hq, lt_irreflₓ] using h
    ·
      rw [degree_eq_nat_degree hp, degree_eq_nat_degree$ ne_zero_of_nat_degree_gt h]
      exactModCast h

-- error in Data.Polynomial.Degree.Definitions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat_degree_lt_nat_degree_iff
(hp : «expr ≠ »(p, 0)) : «expr ↔ »(«expr < »(nat_degree p, nat_degree q), «expr < »(degree p, degree q)) :=
⟨degree_lt_degree, begin
   intro [ident h],
   have [ident hq] [":", expr «expr ≠ »(q, 0)] [":=", expr ne_zero_of_degree_gt h],
   rw ["[", expr degree_eq_nat_degree hp, ",", expr degree_eq_nat_degree hq, "]"] ["at", ident h],
   exact_mod_cast [expr h]
 end⟩

theorem eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) :=
  by 
    ext (_ | n)
    ·
      simp 
    rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
    exact h.trans_lt (WithBot.some_lt_some.2 n.succ_pos)

theorem eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero (h ▸ le_reflₓ _)

theorem degree_le_zero_iff : degree p ≤ 0 ↔ p = C (coeff p 0) :=
  ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

theorem degree_add_le (p q : Polynomial R) : degree (p+q) ≤ max (degree p) (degree q) :=
  calc degree (p+q) = (p+q).Support.sup some := rfl 
    _ ≤ (p.support ∪ q.support).sup some := sup_mono support_add 
    _ = p.support.sup some⊔q.support.sup some := sup_union
    

theorem nat_degree_add_le (p q : Polynomial R) : nat_degree (p+q) ≤ max (nat_degree p) (nat_degree q) :=
  by 
    cases le_max_iff.1 (degree_add_le p q) <;> simp [nat_degree_le_nat_degree h]

@[simp]
theorem leading_coeff_zero : leading_coeff (0 : Polynomial R) = 0 :=
  rfl

@[simp]
theorem leading_coeff_eq_zero : leading_coeff p = 0 ↔ p = 0 :=
  ⟨fun h => by_contradiction$ fun hp => mt mem_support_iff.1 (not_not.2 h) (mem_of_max (degree_eq_nat_degree hp)),
    fun h => h.symm ▸ leading_coeff_zero⟩

theorem leading_coeff_ne_zero : leading_coeff p ≠ 0 ↔ p ≠ 0 :=
  by 
    rw [Ne.def, leading_coeff_eq_zero]

theorem leading_coeff_eq_zero_iff_deg_eq_bot : leading_coeff p = 0 ↔ degree p = ⊥ :=
  by 
    rw [leading_coeff_eq_zero, degree_eq_bot]

theorem nat_degree_mem_support_of_nonzero (H : p ≠ 0) : p.nat_degree ∈ p.support :=
  by 
    rw [mem_support_iff]
    exact (not_congr leading_coeff_eq_zero).mpr H

theorem nat_degree_eq_support_max' (h : p ≠ 0) : p.nat_degree = p.support.max' (nonempty_support_iff.mpr h) :=
  (le_max' _ _$ nat_degree_mem_support_of_nonzero h).antisymm$ max'_le _ _ _ le_nat_degree_of_mem_supp

theorem nat_degree_C_mul_X_pow_le (a : R) (n : ℕ) : nat_degree (C a*X ^ n) ≤ n :=
  nat_degree_le_iff_degree_le.2$ degree_C_mul_X_pow_le _ _

theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p+q) = degree p :=
  le_antisymmₓ (max_eq_left_of_ltₓ h ▸ degree_add_le _ _)$
    degree_le_degree$
      by 
        rw [coeff_add, coeff_nat_degree_eq_zero_of_degree_lt h, add_zeroₓ]
        exact mt leading_coeff_eq_zero.1 (ne_zero_of_degree_gt h)

theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p+q) = degree q :=
  by 
    rw [add_commₓ, degree_add_eq_left_of_degree_lt h]

theorem degree_add_C (hp : 0 < degree p) : degree (p+C a) = degree p :=
  add_commₓ (C a) p ▸ degree_add_eq_right_of_degree_lt$ lt_of_le_of_ltₓ degree_C_le hp

theorem degree_add_eq_of_leading_coeff_add_ne_zero (h : (leading_coeff p+leading_coeff q) ≠ 0) :
  degree (p+q) = max p.degree q.degree :=
  le_antisymmₓ (degree_add_le _ _)$
    match lt_trichotomyₓ (degree p) (degree q) with 
    | Or.inl hlt =>
      by 
        rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_ltₓ hlt] <;> exact le_reflₓ _
    | Or.inr (Or.inl HEq) =>
      le_of_not_gtₓ$
        fun hlt : max (degree p) (degree q) > degree (p+q) =>
          h$
            show (leading_coeff p+leading_coeff q) = 0 by 
              rw [HEq, max_selfₓ] at hlt 
              rw [leading_coeff, leading_coeff, nat_degree_eq_of_degree_eq HEq, ←coeff_add]
              exact coeff_nat_degree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) =>
      by 
        rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_ltₓ hlt] <;> exact le_reflₓ _

theorem degree_erase_le (p : Polynomial R) (n : ℕ) : degree (p.erase n) ≤ degree p :=
  by 
    rcases p with ⟨⟩
    simp only [erase, degree, coeff, support]
    convert sup_mono (erase_subset _ _)

theorem degree_erase_lt (hp : p ≠ 0) : degree (p.erase (nat_degree p)) < degree p :=
  by 
    apply lt_of_le_of_neₓ (degree_erase_le _ _)
    rw [degree_eq_nat_degree hp, degree, support_erase]
    exact fun h => not_mem_erase _ _ (mem_of_max h)

theorem degree_update_le (p : Polynomial R) (n : ℕ) (a : R) : degree (p.update n a) ≤ max (degree p) n :=
  by 
    simp only [degree, coeff_update_apply, le_max_iff, Finset.sup_le_iff, mem_support_iff]
    intro b hb 
    splitIfs  at hb with h
    ·
      subst b 
      exact Or.inr le_rfl
    ·
      exact Or.inl (le_degree_of_ne_zero hb)

theorem degree_sum_le (s : Finset ι) (f : ι → Polynomial R) : degree (∑i in s, f i) ≤ s.sup fun b => degree (f b) :=
  Finset.induction_on s
      (by 
        simp only [sum_empty, sup_empty, degree_zero, le_reflₓ])$
    fun a s has ih =>
      calc degree (∑i in insert a s, f i) ≤ max (degree (f a)) (degree (∑i in s, f i)) :=
        by 
          rw [sum_insert has] <;> exact degree_add_le _ _ 
        _ ≤ _ :=
        by 
          rw [sup_insert, sup_eq_max] <;> exact max_le_max le_rfl ih
        

theorem degree_mul_le (p q : Polynomial R) : degree (p*q) ≤ degree p+degree q :=
  calc degree (p*q) ≤ p.support.sup fun i => degree (Sum q fun j a => C (coeff p i*a)*X ^ i+j) :=
    by 
      simp only [monomial_eq_C_mul_X.symm]
      convert degree_sum_le _ _ 
      exact mul_eq_sum_sum 
    _ ≤ p.support.sup fun i => q.support.sup fun j => degree (C (coeff p i*coeff q j)*X ^ i+j) :=
    Finset.sup_mono_fun fun i hi => degree_sum_le _ _ 
    _ ≤ degree p+degree q :=
    by 
      refine' Finset.sup_le fun a ha => Finset.sup_le fun b hb => le_transₓ (degree_C_mul_X_pow_le _ _) _ 
      rw [WithBot.coe_add]
      rw [mem_support_iff] at ha hb 
      exact add_le_add (le_degree_of_ne_zero ha) (le_degree_of_ne_zero hb)
    

theorem degree_pow_le (p : Polynomial R) : ∀ n : ℕ, degree (p ^ n) ≤ n • degree p
| 0 =>
  by 
    rw [pow_zeroₓ, zero_nsmul] <;> exact degree_one_le
| n+1 =>
  calc degree (p ^ n+1) ≤ degree p+degree (p ^ n) :=
    by 
      rw [pow_succₓ] <;> exact degree_mul_le _ _ 
    _ ≤ _ :=
    by 
      rw [succ_nsmul] <;> exact add_le_add (le_reflₓ _) (degree_pow_le _)
    

@[simp]
theorem leading_coeff_monomial (a : R) (n : ℕ) : leading_coeff (monomial n a) = a :=
  by 
    byCases' ha : a = 0
    ·
      simp only [ha, (monomial n).map_zero, leading_coeff_zero]
    ·
      rw [leading_coeff, nat_degree_monomial _ _ ha, coeff_monomial]
      simp 

theorem leading_coeff_C_mul_X_pow (a : R) (n : ℕ) : leading_coeff (C a*X ^ n) = a :=
  by 
    rw [C_mul_X_pow_eq_monomial, leading_coeff_monomial]

@[simp]
theorem leading_coeff_C (a : R) : leading_coeff (C a) = a :=
  leading_coeff_monomial a 0

@[simp]
theorem leading_coeff_X_pow (n : ℕ) : leading_coeff ((X : Polynomial R) ^ n) = 1 :=
  by 
    simpa only [C_1, one_mulₓ] using leading_coeff_C_mul_X_pow (1 : R) n

@[simp]
theorem leading_coeff_X : leading_coeff (X : Polynomial R) = 1 :=
  by 
    simpa only [pow_oneₓ] using @leading_coeff_X_pow R _ 1

@[simp]
theorem monic_X_pow (n : ℕ) : monic (X ^ n : Polynomial R) :=
  leading_coeff_X_pow n

@[simp]
theorem monic_X : monic (X : Polynomial R) :=
  leading_coeff_X

@[simp]
theorem leading_coeff_one : leading_coeff (1 : Polynomial R) = 1 :=
  leading_coeff_C 1

@[simp]
theorem monic_one : monic (1 : Polynomial R) :=
  leading_coeff_C _

theorem monic.ne_zero {R : Type _} [Semiringₓ R] [Nontrivial R] {p : Polynomial R} (hp : p.monic) : p ≠ 0 :=
  by 
    rintro rfl 
    simpa [monic] using hp

theorem monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {p : Polynomial R} (hp : p.monic) : p ≠ 0 :=
  by 
    nontriviality R 
    exact hp.ne_zero

-- error in Data.Polynomial.Degree.Definitions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem monic.ne_zero_of_polynomial_ne {r} (hp : monic p) (hne : «expr ≠ »(q, r)) : «expr ≠ »(p, 0) :=
by { haveI [] [] [":=", expr nontrivial.of_polynomial_ne hne],
  exact [expr hp.ne_zero] }

theorem leading_coeff_add_of_degree_lt (h : degree p < degree q) : leading_coeff (p+q) = leading_coeff q :=
  have  : coeff p (nat_degree q) = 0 := coeff_nat_degree_eq_zero_of_degree_lt h 
  by 
    simp only [leading_coeff, nat_degree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this, coeff_add,
      zero_addₓ]

theorem leading_coeff_add_of_degree_eq (h : degree p = degree q) (hlc : (leading_coeff p+leading_coeff q) ≠ 0) :
  leading_coeff (p+q) = leading_coeff p+leading_coeff q :=
  have  : nat_degree (p+q) = nat_degree p :=
    by 
      apply nat_degree_eq_of_degree_eq <;> rw [degree_add_eq_of_leading_coeff_add_ne_zero hlc, h, max_selfₓ]
  by 
    simp only [leading_coeff, this, nat_degree_eq_of_degree_eq h, coeff_add]

@[simp]
theorem coeff_mul_degree_add_degree (p q : Polynomial R) :
  coeff (p*q) (nat_degree p+nat_degree q) = leading_coeff p*leading_coeff q :=
  calc
    coeff (p*q) (nat_degree p+nat_degree q) =
      ∑x in nat.antidiagonal (nat_degree p+nat_degree q), coeff p x.1*coeff q x.2 :=
    coeff_mul _ _ _ 
    _ = coeff p (nat_degree p)*coeff q (nat_degree q) :=
    by 
      refine' Finset.sum_eq_single (nat_degree p, nat_degree q) _ _
      ·
        rintro ⟨i, j⟩ h₁ h₂ 
        rw [nat.mem_antidiagonal] at h₁ 
        byCases' H : nat_degree p < i
        ·
          rw [coeff_eq_zero_of_degree_lt (lt_of_le_of_ltₓ degree_le_nat_degree (WithBot.coe_lt_coe.2 H)), zero_mul]
        ·
          rw [not_lt_iff_eq_or_lt] at H 
          cases H
          ·
            subst H 
            rw [add_left_cancel_iffₓ] at h₁ 
            dsimp  at h₁ 
            subst h₁ 
            exfalso 
            exact h₂ rfl
          ·
            suffices  : nat_degree q < j
            ·
              rw [coeff_eq_zero_of_degree_lt (lt_of_le_of_ltₓ degree_le_nat_degree (WithBot.coe_lt_coe.2 this)),
                mul_zero]
            ·
              byContra H' 
              rw [not_ltₓ] at H' 
              exact ne_of_ltₓ (Nat.lt_of_lt_of_leₓ (Nat.add_lt_add_rightₓ H j) (Nat.add_le_add_leftₓ H' _)) h₁
      ·
        intro H 
        exfalso 
        apply H 
        rw [nat.mem_antidiagonal]
    

theorem degree_mul' (h : (leading_coeff p*leading_coeff q) ≠ 0) : degree (p*q) = degree p+degree q :=
  have hp : p ≠ 0 :=
    by 
      refine' mt _ h <;>
        exact
          fun hp =>
            by 
              rw [hp, leading_coeff_zero, zero_mul]
  have hq : q ≠ 0 :=
    by 
      refine' mt _ h <;>
        exact
          fun hq =>
            by 
              rw [hq, leading_coeff_zero, mul_zero]
  le_antisymmₓ (degree_mul_le _ _)
    (by 
      rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq]
      refine' le_degree_of_ne_zero _ 
      rwa [coeff_mul_degree_add_degree])

theorem monic.degree_mul (hq : monic q) : degree (p*q) = degree p+degree q :=
  if hp : p = 0 then
    by 
      simp [hp]
  else
    degree_mul'$
      by 
        rwa [hq.leading_coeff, mul_oneₓ, Ne.def, leading_coeff_eq_zero]

theorem nat_degree_mul' (h : (leading_coeff p*leading_coeff q) ≠ 0) : nat_degree (p*q) = nat_degree p+nat_degree q :=
  have hp : p ≠ 0 :=
    mt leading_coeff_eq_zero.2
      fun h₁ =>
        h$
          by 
            rw [h₁, zero_mul]
  have hq : q ≠ 0 :=
    mt leading_coeff_eq_zero.2
      fun h₁ =>
        h$
          by 
            rw [h₁, mul_zero]
  nat_degree_eq_of_degree_eq_some$
    by 
      rw [degree_mul' h, WithBot.coe_add, degree_eq_nat_degree hp, degree_eq_nat_degree hq]

theorem leading_coeff_mul' (h : (leading_coeff p*leading_coeff q) ≠ 0) :
  leading_coeff (p*q) = leading_coeff p*leading_coeff q :=
  by 
    unfold leading_coeff 
    rw [nat_degree_mul' h, coeff_mul_degree_add_degree]
    rfl

theorem monomial_nat_degree_leading_coeff_eq_self (h : p.support.card ≤ 1) :
  monomial p.nat_degree p.leading_coeff = p :=
  by 
    rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
    byCases' ha : a = 0 <;> simp [ha]

theorem C_mul_X_pow_eq_self (h : p.support.card ≤ 1) : (C p.leading_coeff*X ^ p.nat_degree) = p :=
  by 
    rw [C_mul_X_pow_eq_monomial, monomial_nat_degree_leading_coeff_eq_self h]

theorem leading_coeff_pow' : leading_coeff p ^ n ≠ 0 → leading_coeff (p ^ n) = leading_coeff p ^ n :=
  Nat.recOn n
      (by 
        simp )$
    fun n ih h =>
      have h₁ : leading_coeff p ^ n ≠ 0 :=
        fun h₁ =>
          h$
            by 
              rw [pow_succₓ, h₁, mul_zero]
      have h₂ : (leading_coeff p*leading_coeff (p ^ n)) ≠ 0 :=
        by 
          rwa [pow_succₓ, ←ih h₁] at h 
      by 
        rw [pow_succₓ, pow_succₓ, leading_coeff_mul' h₂, ih h₁]

theorem degree_pow' : ∀ {n : ℕ}, leading_coeff p ^ n ≠ 0 → degree (p ^ n) = n • degree p
| 0 =>
  fun h =>
    by 
      rw [pow_zeroₓ, ←C_1] at * <;> rw [degree_C h, zero_nsmul]
| n+1 =>
  fun h =>
    have h₁ : leading_coeff p ^ n ≠ 0 :=
      fun h₁ =>
        h$
          by 
            rw [pow_succₓ, h₁, mul_zero]
    have h₂ : (leading_coeff p*leading_coeff (p ^ n)) ≠ 0 :=
      by 
        rwa [pow_succₓ, ←leading_coeff_pow' h₁] at h 
    by 
      rw [pow_succₓ, degree_mul' h₂, succ_nsmul, degree_pow' h₁]

theorem nat_degree_pow' {n : ℕ} (h : leading_coeff p ^ n ≠ 0) : nat_degree (p ^ n) = n*nat_degree p :=
  if hp0 : p = 0 then
    if hn0 : n = 0 then
      by 
        simp 
    else
      by 
        rw [hp0, zero_pow (Nat.pos_of_ne_zeroₓ hn0)] <;> simp 
  else
    have hpn : p ^ n ≠ 0 :=
      fun hpn0 =>
        have h1 := h 
        by 
          rw [←leading_coeff_pow' h1, hpn0, leading_coeff_zero] at h <;> exact h rfl 
    Option.some_inj.1$
      show (nat_degree (p ^ n) : WithBot ℕ) = (n*nat_degree p : ℕ)by 
        rw [←degree_eq_nat_degree hpn, degree_pow' h, degree_eq_nat_degree hp0, ←WithBot.coe_nsmul] <;> simp 

theorem leading_coeff_mul_monic {p q : Polynomial R} (hq : monic q) : leading_coeff (p*q) = leading_coeff p :=
  Decidable.byCases
    (fun H : leading_coeff p = 0 =>
      by 
        rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
    fun H : leading_coeff p ≠ 0 =>
      by 
        rw [leading_coeff_mul', hq.leading_coeff, mul_oneₓ] <;> rwa [hq.leading_coeff, mul_oneₓ]

@[simp]
theorem leading_coeff_mul_X_pow {p : Polynomial R} {n : ℕ} : leading_coeff (p*X ^ n) = leading_coeff p :=
  leading_coeff_mul_monic (monic_X_pow n)

@[simp]
theorem leading_coeff_mul_X {p : Polynomial R} : leading_coeff (p*X) = leading_coeff p :=
  leading_coeff_mul_monic monic_X

theorem nat_degree_mul_le {p q : Polynomial R} : nat_degree (p*q) ≤ nat_degree p+nat_degree q :=
  by 
    apply nat_degree_le_of_degree_le 
    apply le_transₓ (degree_mul_le p q)
    rw [WithBot.coe_add]
    refine' add_le_add _ _ <;> apply degree_le_nat_degree

theorem subsingleton_of_monic_zero (h : monic (0 : Polynomial R)) : (∀ p q : Polynomial R, p = q) ∧ ∀ a b : R, a = b :=
  by 
    rw [monic.def, leading_coeff_zero] at h <;>
      exact
        ⟨fun p q =>
            by 
              rw [←mul_oneₓ p, ←mul_oneₓ q, ←C_1, ←h, C_0, mul_zero, mul_zero],
          fun a b =>
            by 
              rw [←mul_oneₓ a, ←mul_oneₓ b, ←h, mul_zero, mul_zero]⟩

theorem zero_le_degree_iff {p : Polynomial R} : 0 ≤ degree p ↔ p ≠ 0 :=
  by 
    rw [Ne.def, ←degree_eq_bot] <;>
      cases degree p <;>
        exact
          by 
            decide

theorem degree_nonneg_iff_ne_zero : 0 ≤ degree p ↔ p ≠ 0 :=
  ⟨fun h0p hp0 =>
      absurd h0p
        (by 
          rw [hp0, degree_zero] <;>
            exact
              by 
                decide),
    fun hp0 =>
      le_of_not_gtₓ
        fun h =>
          by 
            simp_all [Gt, degree_eq_bot]⟩

theorem nat_degree_eq_zero_iff_degree_le_zero : p.nat_degree = 0 ↔ p.degree ≤ 0 :=
  by 
    rw [←nonpos_iff_eq_zero, nat_degree_le_iff_degree_le, WithBot.coe_zero]

theorem degree_le_iff_coeff_zero (f : Polynomial R) (n : WithBot ℕ) : degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
  ⟨fun H : Finset.sup f.support some ≤ n m Hm : n < (m : WithBot ℕ) =>
      Decidable.of_not_not$
        fun H4 =>
          have H1 : m ∉ f.support := fun H2 => not_lt_of_geₓ ((Finset.sup_le_iff.1 H) m H2 : (m : WithBot ℕ) ≤ n) Hm 
          H1$ mem_support_iff.2 H4,
    fun H => Finset.sup_le$ fun b Hb => Decidable.of_not_not$ fun Hn => mem_support_iff.1 Hb$ H b$ lt_of_not_geₓ Hn⟩

theorem degree_lt_iff_coeff_zero (f : Polynomial R) (n : ℕ) : degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 :=
  by 
    refine' ⟨fun hf m hm => coeff_eq_zero_of_degree_lt (lt_of_lt_of_leₓ hf (WithBot.coe_le_coe.2 hm)), _⟩
    simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff, WithBot.some_eq_coe,
      WithBot.coe_lt_coe, ←@not_leₓ ℕ]
    exact fun h m => mt (h m)

theorem degree_smul_le (a : R) (p : Polynomial R) : degree (a • p) ≤ degree p :=
  by 
    apply (degree_le_iff_coeff_zero _ _).2 fun m hm => _ 
    rw [degree_lt_iff_coeff_zero] at hm 
    simp [hm m (le_reflₓ _)]

theorem nat_degree_smul_le (a : R) (p : Polynomial R) : nat_degree (a • p) ≤ nat_degree p :=
  nat_degree_le_nat_degree (degree_smul_le a p)

-- error in Data.Polynomial.Degree.Definitions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_lt_degree_mul_X (hp : «expr ≠ »(p, 0)) : «expr < »(p.degree, «expr * »(p, X).degree) :=
by haveI [] [] [":=", expr nontrivial.of_polynomial_ne hp]; exact [expr have «expr ≠ »(«expr * »(leading_coeff p, leading_coeff X), 0), by simpa [] [] [] [] [] [],
 by erw ["[", expr degree_mul' this, ",", expr degree_eq_nat_degree hp, ",", expr degree_X, ",", "<-", expr with_bot.coe_one, ",", "<-", expr with_bot.coe_add, ",", expr with_bot.coe_lt_coe, "]"] []; exact [expr nat.lt_succ_self _]]

theorem nat_degree_pos_iff_degree_pos : 0 < nat_degree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le nat_degree_le_iff_degree_le

theorem eq_C_of_nat_degree_le_zero (h : nat_degree p ≤ 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero$ degree_le_of_nat_degree_le h

theorem eq_C_of_nat_degree_eq_zero (h : nat_degree p = 0) : p = C (coeff p 0) :=
  eq_C_of_nat_degree_le_zero h.le

theorem ne_zero_of_coe_le_degree (hdeg : «expr↑ » n ≤ p.degree) : p ≠ 0 :=
  by 
    rw [←degree_nonneg_iff_ne_zero] <;>
      exact
        trans
          (by 
            exactModCast n.zero_le)
          hdeg

theorem le_nat_degree_of_coe_le_degree (hdeg : «expr↑ » n ≤ p.degree) : n ≤ p.nat_degree :=
  WithBot.coe_le_coe.mp ((degree_eq_nat_degree$ ne_zero_of_coe_le_degree hdeg) ▸ hdeg)

end Semiringₓ

section NontrivialSemiring

variable[Semiringₓ R][Nontrivial R]{p q : Polynomial R}

@[simp]
theorem degree_X_pow (n : ℕ) : degree ((X : Polynomial R) ^ n) = n :=
  by 
    rw [X_pow_eq_monomial, degree_monomial _ (@one_ne_zero R _ _)]

@[simp]
theorem nat_degree_X_pow (n : ℕ) : nat_degree ((X : Polynomial R) ^ n) = n :=
  nat_degree_eq_of_degree_eq_some (degree_X_pow n)

theorem not_is_unit_X : ¬IsUnit (X : Polynomial R) :=
  fun ⟨⟨_, g, hfg, hgf⟩, rfl⟩ =>
    @zero_ne_one R _ _$
      by 
        change (g*monomial 1 1) = 1 at hgf 
        rw [←coeff_one_zero, ←hgf]
        simp 

@[simp]
theorem degree_mul_X : degree (p*X) = degree p+1 :=
  by 
    simp [monic_X.degree_mul]

@[simp]
theorem degree_mul_X_pow : degree (p*X ^ n) = degree p+n :=
  by 
    simp [(monic_X_pow n).degree_mul]

end NontrivialSemiring

section Ringₓ

variable[Ringₓ R]{p q : Polynomial R}

theorem degree_sub_le (p q : Polynomial R) : degree (p - q) ≤ max (degree p) (degree q) :=
  by 
    simpa only [sub_eq_add_neg, degree_neg q] using degree_add_le p (-q)

theorem degree_sub_lt (hd : degree p = degree q) (hp0 : p ≠ 0) (hlc : leading_coeff p = leading_coeff q) :
  degree (p - q) < degree p :=
  have hp : (monomial (nat_degree p) (leading_coeff p)+p.erase (nat_degree p)) = p := monomial_add_erase _ _ 
  have hq : (monomial (nat_degree q) (leading_coeff q)+q.erase (nat_degree q)) = q := monomial_add_erase _ _ 
  have hd' : nat_degree p = nat_degree q :=
    by 
      unfold nat_degree <;> rw [hd]
  have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc degree (p - q) = degree (erase (nat_degree q) p+-erase (nat_degree q) q) :=
    by 
      conv  => toLHS rw [←hp, ←hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]
    _ ≤ max (degree (erase (nat_degree q) p)) (degree (erase (nat_degree q) q)) :=
    degree_neg (erase (nat_degree q) q) ▸ degree_add_le _ _ 
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩
    

theorem nat_degree_X_sub_C_le {r : R} : (X - C r).natDegree ≤ 1 :=
  nat_degree_le_iff_degree_le.2$
    le_transₓ (degree_sub_le _ _)$ max_leₓ degree_X_le$ le_transₓ degree_C_le$ WithBot.coe_le_coe.2 zero_le_one

-- error in Data.Polynomial.Degree.Definitions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_sum_fin_lt
{n : exprℕ()}
(f : fin n → R) : «expr < »(degree «expr∑ , »((i : fin n), «expr * »(C (f i), «expr ^ »(X, (i : exprℕ())))), n) :=
begin
  haveI [] [":", expr is_commutative (with_bot exprℕ()) max] [":=", expr ⟨max_comm⟩],
  haveI [] [":", expr is_associative (with_bot exprℕ()) max] [":=", expr ⟨max_assoc⟩],
  calc
    «expr ≤ »(«expr∑ , »((i), «expr * »(C (f i), «expr ^ »(X, (i : exprℕ())))).degree, finset.univ.fold ((«expr ⊔ »)) «expr⊥»() (λ
      i, «expr * »(C (f i), «expr ^ »(X, (i : exprℕ()))).degree)) : degree_sum_le _ _
    «expr = »(..., finset.univ.fold max «expr⊥»() (λ i, «expr * »(C (f i), «expr ^ »(X, (i : exprℕ()))).degree)) : rfl
    «expr < »(..., n) : (finset.fold_max_lt (n : with_bot exprℕ())).mpr ⟨with_bot.bot_lt_coe _, _⟩,
  rintros ["⟨", ident i, ",", ident hi, "⟩", "-"],
  calc
    «expr ≤ »(«expr * »(C (f ⟨i, hi⟩), «expr ^ »(X, i)).degree, «expr + »((C _).degree, «expr ^ »(X, i).degree)) : degree_mul_le _ _
    «expr ≤ »(..., «expr + »(0, i)) : add_le_add degree_C_le (degree_X_pow_le i)
    «expr = »(..., i) : zero_add _
    «expr < »(..., n) : with_bot.some_lt_some.mpr hi
end

theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p :=
  by 
    rw [←degree_neg q] at h 
    rw [sub_eq_add_neg, degree_add_eq_left_of_degree_lt h]

theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q :=
  by 
    rw [←degree_neg q] at h 
    rw [sub_eq_add_neg, degree_add_eq_right_of_degree_lt h, degree_neg]

end Ringₓ

section NonzeroRing

variable[Nontrivial R][Ringₓ R]

@[simp]
theorem degree_X_sub_C (a : R) : degree (X - C a) = 1 :=
  have  : degree (C a) < degree (X : Polynomial R) :=
    calc degree (C a) ≤ 0 := degree_C_le 
      _ < 1 := WithBot.some_lt_some.mpr zero_lt_one 
      _ = degree X := degree_X.symm 
      
  by 
    rw [degree_sub_eq_left_of_degree_lt this, degree_X]

@[simp]
theorem degree_X_add_C (a : R) : degree (X+C a) = 1 :=
  have  : degree (C a) < degree (X : Polynomial R) :=
    calc degree (C a) ≤ 0 := degree_C_le 
      _ < 1 := WithBot.some_lt_some.mpr zero_lt_one 
      _ = degree X := degree_X.symm 
      
  by 
    rw [degree_add_eq_left_of_degree_lt this, degree_X]

@[simp]
theorem nat_degree_X_sub_C (x : R) : (X - C x).natDegree = 1 :=
  nat_degree_eq_of_degree_eq_some$ degree_X_sub_C x

@[simp]
theorem next_coeff_X_sub_C (c : R) : next_coeff (X - C c) = -c :=
  by 
    simp [next_coeff_of_pos_nat_degree]

theorem degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : Polynomial R) ^ n - C a) = n :=
  have  : degree (C a) < degree ((X : Polynomial R) ^ n) :=
    calc degree (C a) ≤ 0 := degree_C_le 
      _ < degree ((X : Polynomial R) ^ n) :=
      by 
        rwa [degree_X_pow] <;> exact WithBot.coe_lt_coe.2 hn 
      
  by 
    rw [degree_sub_eq_left_of_degree_lt this, degree_X_pow]

theorem X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : Polynomial R) ^ n - C a ≠ 0 :=
  mt degree_eq_bot.2
    (show degree ((X : Polynomial R) ^ n - C a) ≠ ⊥by 
      rw [degree_X_pow_sub_C hn a] <;>
        exact
          by 
            decide)

theorem X_sub_C_ne_zero (r : R) : X - C r ≠ 0 :=
  pow_oneₓ (X : Polynomial R) ▸ X_pow_sub_C_ne_zero zero_lt_one r

theorem zero_nmem_multiset_map_X_sub_C {α : Type _} (m : Multiset α) (f : α → R) :
  (0 : Polynomial R) ∉ m.map fun a => X - C (f a) :=
  fun mem =>
    let ⟨a, _, ha⟩ := Multiset.mem_map.mp mem 
    X_sub_C_ne_zero _ ha

theorem nat_degree_X_pow_sub_C {n : ℕ} {r : R} : (X ^ n - C r).natDegree = n :=
  by 
    byCases' hn : n = 0
    ·
      rw [hn, pow_zeroₓ, ←C_1, ←RingHom.map_sub, nat_degree_C]
    ·
      exact nat_degree_eq_of_degree_eq_some (degree_X_pow_sub_C (pos_iff_ne_zero.mpr hn) r)

@[simp]
theorem leading_coeff_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} : (X ^ n - C r).leadingCoeff = 1 :=
  by 
    rw [leading_coeff, nat_degree_X_pow_sub_C, coeff_sub, coeff_X_pow_self, coeff_C, if_neg (pos_iff_ne_zero.mp hn),
      sub_zero]

@[simp]
theorem leading_coeff_X_pow_sub_one {n : ℕ} (hn : 0 < n) : (X ^ n - 1 : Polynomial R).leadingCoeff = 1 :=
  leading_coeff_X_pow_sub_C hn

end NonzeroRing

section NoZeroDivisors

variable[Semiringₓ R][NoZeroDivisors R]{p q : Polynomial R}

@[simp]
theorem degree_mul : degree (p*q) = degree p+degree q :=
  if hp0 : p = 0 then
    by 
      simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then
      by 
        simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
    else degree_mul'$ mul_ne_zero (mt leading_coeff_eq_zero.1 hp0) (mt leading_coeff_eq_zero.1 hq0)

@[simp]
theorem degree_pow [Nontrivial R] (p : Polynomial R) (n : ℕ) : degree (p ^ n) = n • degree p :=
  by 
    induction n <;> [simp only [pow_zeroₓ, degree_one, zero_nsmul], simp only [pow_succₓ, succ_nsmul, degree_mul]]

@[simp]
theorem leading_coeff_mul (p q : Polynomial R) : leading_coeff (p*q) = leading_coeff p*leading_coeff q :=
  by 
    byCases' hp : p = 0
    ·
      simp only [hp, zero_mul, leading_coeff_zero]
    ·
      byCases' hq : q = 0
      ·
        simp only [hq, mul_zero, leading_coeff_zero]
      ·
        rw [leading_coeff_mul']
        exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) (mt leading_coeff_eq_zero.1 hq)

@[simp]
theorem leading_coeff_X_add_C [Nontrivial R] (a b : R) (ha : a ≠ 0) : leading_coeff ((C a*X)+C b) = a :=
  by 
    rw [add_commₓ, leading_coeff_add_of_degree_lt]
    ·
      simp 
    ·
      simpa [degree_C ha] using lt_of_le_of_ltₓ degree_C_le (WithBot.coe_lt_coe.2 zero_lt_one)

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` has `no_zero_divisors`, and thus
  `leading_coeff` is multiplicative -/
def leading_coeff_hom : Polynomial R →* R :=
  { toFun := leading_coeff,
    map_one' :=
      by 
        simp ,
    map_mul' := leading_coeff_mul }

@[simp]
theorem leading_coeff_hom_apply (p : Polynomial R) : leading_coeff_hom p = leading_coeff p :=
  rfl

@[simp]
theorem leading_coeff_pow (p : Polynomial R) (n : ℕ) : leading_coeff (p ^ n) = leading_coeff p ^ n :=
  (leading_coeff_hom : Polynomial R →* R).map_pow p n

end NoZeroDivisors

end Polynomial

