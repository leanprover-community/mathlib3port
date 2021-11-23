import Mathbin.Algebra.Polynomial.BigOperators 
import Mathbin.Algebra.Squarefree 
import Mathbin.FieldTheory.Minpoly 
import Mathbin.FieldTheory.SplittingField

/-!

# Separable polynomials

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

## Main definitions

* `polynomial.separable f`: a polynomial `f` is separable iff it is coprime with its derivative.
* `polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/


universe u v w

open_locale Classical BigOperators

open Finset

namespace Polynomial

section CommSemiringₓ

variable{R : Type u}[CommSemiringₓ R]{S : Type v}[CommSemiringₓ S]

/-- A polynomial is separable iff it is coprime with its derivative. -/
def separable (f : Polynomial R) : Prop :=
  IsCoprime f f.derivative

theorem separable_def (f : Polynomial R) : f.separable ↔ IsCoprime f f.derivative :=
  Iff.rfl

theorem separable_def' (f : Polynomial R) : f.separable ↔ ∃ a b : Polynomial R, ((a*f)+b*f.derivative) = 1 :=
  Iff.rfl

theorem not_separable_zero [Nontrivial R] : ¬separable (0 : Polynomial R) :=
  by 
    rintro ⟨x, y, h⟩
    simpa only [derivative_zero, mul_zero, add_zeroₓ, zero_ne_one] using h

theorem separable_one : (1 : Polynomial R).Separable :=
  is_coprime_one_left

theorem separable_X_add_C (a : R) : (X+C a).Separable :=
  by 
    rw [separable_def, derivative_add, derivative_X, derivative_C, add_zeroₓ]
    exact is_coprime_one_right

theorem separable_X : (X : Polynomial R).Separable :=
  by 
    rw [separable_def, derivative_X]
    exact is_coprime_one_right

theorem separable_C (r : R) : (C r).Separable ↔ IsUnit r :=
  by 
    rw [separable_def, derivative_C, is_coprime_zero_right, is_unit_C]

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem separable.of_mul_left {f g : polynomial R} (h : «expr * »(f, g).separable) : f.separable :=
begin
  have [] [] [":=", expr h.of_mul_left_left],
  rw [expr derivative_mul] ["at", ident this],
  exact [expr is_coprime.of_mul_right_left (is_coprime.of_add_mul_left_right this)]
end

theorem separable.of_mul_right {f g : Polynomial R} (h : (f*g).Separable) : g.separable :=
  by 
    rw [mul_commₓ] at h 
    exact h.of_mul_left

theorem separable.of_dvd {f g : Polynomial R} (hf : f.separable) (hfg : g ∣ f) : g.separable :=
  by 
    rcases hfg with ⟨f', rfl⟩
    exact separable.of_mul_left hf

theorem separable_gcd_left {F : Type _} [Field F] {f : Polynomial F} (hf : f.separable) (g : Polynomial F) :
  (EuclideanDomain.gcd f g).Separable :=
  separable.of_dvd hf (EuclideanDomain.gcd_dvd_left f g)

theorem separable_gcd_right {F : Type _} [Field F] {g : Polynomial F} (f : Polynomial F) (hg : g.separable) :
  (EuclideanDomain.gcd f g).Separable :=
  separable.of_dvd hg (EuclideanDomain.gcd_dvd_right f g)

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem separable.is_coprime {f g : polynomial R} (h : «expr * »(f, g).separable) : is_coprime f g :=
begin
  have [] [] [":=", expr h.of_mul_left_left],
  rw [expr derivative_mul] ["at", ident this],
  exact [expr is_coprime.of_mul_right_right (is_coprime.of_add_mul_left_right this)]
end

theorem separable.of_pow' {f : Polynomial R} : ∀ {n : ℕ} h : (f^n).Separable, IsUnit f ∨ f.separable ∧ n = 1 ∨ n = 0
| 0 => fun h => Or.inr$ Or.inr rfl
| 1 => fun h => Or.inr$ Or.inl ⟨pow_oneₓ f ▸ h, rfl⟩
| n+2 =>
  fun h =>
    by 
      rw [pow_succₓ, pow_succₓ] at h 
      exact Or.inl (is_coprime_self.1 h.is_coprime.of_mul_right_left)

theorem separable.of_pow {f : Polynomial R} (hf : ¬IsUnit f) {n : ℕ} (hn : n ≠ 0) (hfs : (f^n).Separable) :
  f.separable ∧ n = 1 :=
  (hfs.of_pow'.resolve_left hf).resolve_right hn

theorem separable.map {p : Polynomial R} (h : p.separable) {f : R →+* S} : (p.map f).Separable :=
  let ⟨a, b, H⟩ := h
  ⟨a.map f, b.map f,
    by 
      rw [derivative_map, ←map_mul, ←map_mul, ←map_add, H, map_one]⟩

variable(R)(p q : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
noncomputable def expand : Polynomial R →ₐ[R] Polynomial R :=
  { (eval₂_ring_hom C (X^p) : Polynomial R →+* Polynomial R) with commutes' := fun r => eval₂_C _ _ }

theorem coe_expand : (expand R p : Polynomial R → Polynomial R) = eval₂ C (X^p) :=
  rfl

variable{R}

theorem expand_eq_sum {f : Polynomial R} : expand R p f = f.sum fun e a => C a*(X^p)^e :=
  by 
    dsimp [expand, eval₂]
    rfl

@[simp]
theorem expand_C (r : R) : expand R p (C r) = C r :=
  eval₂_C _ _

@[simp]
theorem expand_X : expand R p X = (X^p) :=
  eval₂_X _ _

@[simp]
theorem expand_monomial (r : R) : expand R p (monomial q r) = monomial (q*p) r :=
  by 
    simpRw [monomial_eq_smul_X, AlgHom.map_smul, AlgHom.map_pow, expand_X, mul_commₓ, pow_mulₓ]

theorem expand_expand (f : Polynomial R) : expand R p (expand R q f) = expand R (p*q) f :=
  Polynomial.induction_on f
    (fun r =>
      by 
        simpRw [expand_C])
    (fun f g ihf ihg =>
      by 
        simpRw [AlgHom.map_add, ihf, ihg])
    fun n r ih =>
      by 
        simpRw [AlgHom.map_mul, expand_C, AlgHom.map_pow, expand_X, AlgHom.map_pow, expand_X, pow_mulₓ]

theorem expand_mul (f : Polynomial R) : expand R (p*q) f = expand R p (expand R q f) :=
  (expand_expand p q f).symm

@[simp]
theorem expand_one (f : Polynomial R) : expand R 1 f = f :=
  Polynomial.induction_on f
    (fun r =>
      by 
        rw [expand_C])
    (fun f g ihf ihg =>
      by 
        rw [AlgHom.map_add, ihf, ihg])
    fun n r ih =>
      by 
        rw [AlgHom.map_mul, expand_C, AlgHom.map_pow, expand_X, pow_oneₓ]

theorem expand_pow (f : Polynomial R) : expand R (p^q) f = (expand R p^[q]) f :=
  Nat.recOn q
      (by 
        rw [pow_zeroₓ, expand_one, Function.iterate_zero, id])$
    fun n ih =>
      by 
        rw [Function.iterate_succ_apply', pow_succₓ, expand_mul, ih]

theorem derivative_expand (f : Polynomial R) : (expand R p f).derivative = expand R p f.derivative*p*X^p - 1 :=
  by 
    rw [coe_expand, derivative_eval₂_C, derivative_pow, derivative_X, mul_oneₓ]

theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : Polynomial R) (n : ℕ) :
  (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 :=
  by 
    simp only [expand_eq_sum]
    simpRw [coeff_sum, ←pow_mulₓ, C_mul_X_pow_eq_monomial, coeff_monomial, Sum]
    splitIfs with h
    ·
      rw [Finset.sum_eq_single (n / p), Nat.mul_div_cancel'ₓ h, if_pos rfl]
      ·
        intro b hb1 hb2 
        rw [if_neg]
        intro hb3 
        apply hb2 
        rw [←hb3, Nat.mul_div_cancel_leftₓ b hp]
      ·
        intro hn 
        rw [not_mem_support_iff.1 hn]
        splitIfs <;> rfl
    ·
      rw [Finset.sum_eq_zero]
      intro k hk 
      rw [if_neg]
      exact fun hkn => h ⟨k, hkn.symm⟩

@[simp]
theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : Polynomial R) (n : ℕ) : (expand R p f).coeff (n*p) = f.coeff n :=
  by 
    rw [coeff_expand hp, if_pos (dvd_mul_left _ _), Nat.mul_div_cancelₓ _ hp]

@[simp]
theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : Polynomial R) (n : ℕ) : (expand R p f).coeff (p*n) = f.coeff n :=
  by 
    rw [mul_commₓ, coeff_expand_mul hp]

theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : Polynomial R} : expand R p f = expand R p g ↔ f = g :=
  ⟨fun H =>
      ext$
        fun n =>
          by 
            rw [←coeff_expand_mul hp, H, coeff_expand_mul hp],
    congr_argₓ _⟩

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : Polynomial R} : expand R p f = 0 ↔ f = 0 :=
  by 
    rw [←(expand R p).map_zero, expand_inj hp, AlgHom.map_zero]

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : Polynomial R} {r : R} : expand R p f = C r ↔ f = C r :=
  by 
    rw [←expand_C, expand_inj hp, expand_C]

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat_degree_expand
(p : exprℕ())
(f : polynomial R) : «expr = »((expand R p f).nat_degree, «expr * »(f.nat_degree, p)) :=
begin
  cases [expr p.eq_zero_or_pos] ["with", ident hp, ident hp],
  { rw ["[", expr hp, ",", expr coe_expand, ",", expr pow_zero, ",", expr mul_zero, ",", "<-", expr C_1, ",", expr eval₂_hom, ",", expr nat_degree_C, "]"] [] },
  by_cases [expr hf, ":", expr «expr = »(f, 0)],
  { rw ["[", expr hf, ",", expr alg_hom.map_zero, ",", expr nat_degree_zero, ",", expr zero_mul, "]"] [] },
  have [ident hf1] [":", expr «expr ≠ »(expand R p f, 0)] [":=", expr mt (expand_eq_zero hp).1 hf],
  rw ["[", "<-", expr with_bot.coe_eq_coe, ",", "<-", expr degree_eq_nat_degree hf1, "]"] [],
  refine [expr le_antisymm «expr $ »((degree_le_iff_coeff_zero _ _).2, λ n hn, _) _],
  { rw [expr coeff_expand hp] [],
    split_ifs [] ["with", ident hpn],
    { rw [expr coeff_eq_zero_of_nat_degree_lt] [],
      contrapose ["!"] [ident hn],
      rw ["[", expr with_bot.coe_le_coe, ",", "<-", expr nat.div_mul_cancel hpn, "]"] [],
      exact [expr nat.mul_le_mul_right p hn] },
    { refl } },
  { refine [expr le_degree_of_ne_zero _],
    rw ["[", expr coeff_expand_mul hp, ",", "<-", expr leading_coeff, "]"] [],
    exact [expr mt leading_coeff_eq_zero.1 hf] }
end

theorem map_expand {p : ℕ} (hp : 0 < p) {f : R →+* S} {q : Polynomial R} :
  map f (expand R p q) = expand S p (map f q) :=
  by 
    ext 
    rw [coeff_map, coeff_expand hp, coeff_expand hp]
    splitIfs <;> simp 

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Expansion is injective. -/
theorem expand_injective {n : exprℕ()} (hn : «expr < »(0, n)) : function.injective (expand R n) :=
λ g g' h, begin
  ext [] [] [],
  have [ident h'] [":", expr «expr = »((expand R n g).coeff «expr * »(n, n_1), (expand R n g').coeff «expr * »(n, n_1))] [":=", expr begin
     apply [expr polynomial.ext_iff.1],
     exact [expr h]
   end],
  rw ["[", expr polynomial.coeff_expand hn g «expr * »(n, n_1), ",", expr polynomial.coeff_expand hn g' «expr * »(n, n_1), "]"] ["at", ident h'],
  simp [] [] ["only"] ["[", expr if_true, ",", expr dvd_mul_right, "]"] [] ["at", ident h'],
  rw [expr nat.mul_div_right n_1 hn] ["at", ident h'],
  exact [expr h']
end

end CommSemiringₓ

section CommRingₓ

variable{R : Type u}[CommRingₓ R]

theorem separable_X_sub_C {x : R} : separable (X - C x) :=
  by 
    simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)

theorem separable.mul {f g : Polynomial R} (hf : f.separable) (hg : g.separable) (h : IsCoprime f g) :
  (f*g).Separable :=
  by 
    rw [separable_def, derivative_mul]
    exact ((hf.mul_right h).add_mul_left_right _).mul_left ((h.symm.mul_right hg).mul_add_right_right _)

theorem separable_prod' {ι : Sort _} {f : ι → Polynomial R} {s : Finset ι} :
  (∀ x _ : x ∈ s, ∀ y _ : y ∈ s, x ≠ y → IsCoprime (f x) (f y)) →
    (∀ x _ : x ∈ s, (f x).Separable) → (∏x in s, f x).Separable :=
  (Finset.induction_on s fun _ _ => separable_one)$
    fun a s has ih h1 h2 =>
      by 
        simpRw [Finset.forall_mem_insert, forall_and_distrib]  at h1 h2 
        rw [prod_insert has]
        exact
          h2.1.mul (ih h1.2.2 h2.2)
            (IsCoprime.prod_right$ fun i his => h1.1.2 i his$ Ne.symm$ ne_of_mem_of_not_mem his has)

theorem separable_prod {ι : Sort _} [Fintype ι] {f : ι → Polynomial R} (h1 : Pairwise (IsCoprime on f))
  (h2 : ∀ x, (f x).Separable) : (∏x, f x).Separable :=
  separable_prod' (fun x hx y hy hxy => h1 x y hxy) fun x hx => h2 x

theorem separable.inj_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} {f : ι → R} {s : Finset ι}
  (hfs : (∏i in s, X - C (f i)).Separable) {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (hfxy : f x = f y) : x = y :=
  by 
    byContra hxy 
    rw [←insert_erase hx, prod_insert (not_mem_erase _ _), ←insert_erase (mem_erase_of_ne_of_mem (Ne.symm hxy) hy),
      prod_insert (not_mem_erase _ _), ←mul_assocₓ, hfxy, ←sq] at hfs 
    cases
      (hfs.of_mul_left.of_pow
          (by 
            exact not_is_unit_X_sub_C)
          two_ne_zero).2

theorem separable.injective_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} [Fintype ι] {f : ι → R}
  (hfs : (∏i, X - C (f i)).Separable) : Function.Injective f :=
  fun x y hfxy => hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_unit_of_self_mul_dvd_separable
{p q : polynomial R}
(hp : p.separable)
(hq : «expr ∣ »(«expr * »(q, q), p)) : is_unit q :=
begin
  obtain ["⟨", ident p, ",", ident rfl, "⟩", ":=", expr hq],
  apply [expr is_coprime_self.mp],
  have [] [":", expr is_coprime «expr * »(q, «expr * »(q, p)) «expr * »(q, «expr + »(«expr + »(«expr * »(q.derivative, p), «expr * »(q.derivative, p)), «expr * »(q, p.derivative)))] [],
  { simp [] [] ["only"] ["[", "<-", expr mul_assoc, ",", expr mul_add, "]"] [] [],
    convert [] [expr hp] [],
    rw ["[", expr derivative_mul, ",", expr derivative_mul, "]"] [],
    ring [] },
  exact [expr is_coprime.of_mul_right_left (is_coprime.of_mul_left_left this)]
end

end CommRingₓ

section IsDomain

variable(R : Type u)[CommRingₓ R][IsDomain R]

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_local_ring_hom_expand
{p : exprℕ()}
(hp : «expr < »(0, p)) : is_local_ring_hom («expr↑ »(expand R p) : «expr →+* »(polynomial R, polynomial R)) :=
begin
  refine [expr ⟨λ f hf1, _⟩],
  rw ["<-", expr coe_fn_coe_base] ["at", ident hf1],
  have [ident hf2] [] [":=", expr eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf1)],
  rw ["[", expr coeff_expand hp, ",", expr if_pos (dvd_zero _), ",", expr p.zero_div, "]"] ["at", ident hf2],
  rw ["[", expr hf2, ",", expr is_unit_C, "]"] ["at", ident hf1],
  rw [expr expand_eq_C hp] ["at", ident hf2],
  rwa ["[", expr hf2, ",", expr is_unit_C, "]"] []
end

end IsDomain

section Field

variable{F : Type u}[Field F]{K : Type v}[Field K]

theorem separable_iff_derivative_ne_zero {f : Polynomial F} (hf : Irreducible f) : f.separable ↔ f.derivative ≠ 0 :=
  ⟨fun h1 h2 => hf.not_unit$ is_coprime_zero_right.1$ h2 ▸ h1,
    fun h =>
      is_coprime_of_dvd (mt And.right h)$
        fun g hg1 hg2 ⟨p, hg3⟩ hg4 =>
          let ⟨u, hu⟩ := (hf.is_unit_or_is_unit hg3).resolve_left hg1 
          have  : f ∣ f.derivative :=
            by 
              convLHS => rw [hg3, ←hu]
              rwa [Units.mul_right_dvd]
          not_lt_of_le (nat_degree_le_of_dvd this h)$ nat_degree_derivative_lt h⟩

theorem separable_map (f : F →+* K) {p : Polynomial F} : (p.map f).Separable ↔ p.separable :=
  by 
    simpRw [separable_def, derivative_map, is_coprime_map]

section CharP

/-- The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`. -/
noncomputable def contract (p : ℕ) (f : Polynomial F) : Polynomial F :=
  ∑n in range (f.nat_degree+1), monomial n (f.coeff (n*p))

variable(p : ℕ)[hp : Fact p.prime]

include hp

theorem coeff_contract (f : Polynomial F) (n : ℕ) : (contract p f).coeff n = f.coeff (n*p) :=
  by 
    simp only [contract, coeff_monomial, sum_ite_eq', finset_sum_coeff, mem_range, not_ltₓ, ite_eq_left_iff]
    intro hn 
    apply (coeff_eq_zero_of_nat_degree_lt _).symm 
    calc f.nat_degree < f.nat_degree+1 := Nat.lt_succ_selfₓ _ _ ≤ n*1 :=
      by 
        simpa only [mul_oneₓ] using hn _ ≤ n*p :=
      mul_le_mul_of_nonneg_left (@Nat.Prime.one_lt p (Fact.out _)).le (zero_le n)

theorem of_irreducible_expand {f : Polynomial F} (hf : Irreducible (expand F p f)) : Irreducible f :=
  @of_irreducible_map _ _ _ (is_local_ring_hom_expand F hp.1.Pos) hf

theorem of_irreducible_expand_pow {f : Polynomial F} {n : ℕ} : Irreducible (expand F (p^n) f) → Irreducible f :=
  (Nat.recOn n
      fun hf =>
        by 
          rwa [pow_zeroₓ, expand_one] at hf)$
    fun n ih hf =>
      ih$
        of_irreducible_expand p$
          by 
            rw [pow_succₓ] at hf 
            rwa [expand_expand]

variable[HF : CharP F p]

include HF

theorem expand_char (f : Polynomial F) : map (frobenius F p) (expand F p f) = (f^p) :=
  by 
    refine' f.induction_on' (fun a b ha hb => _) fun n a => _
    ·
      rw [AlgHom.map_add, map_add, ha, hb, add_pow_char]
    ·
      rw [expand_monomial, map_monomial, monomial_eq_C_mul_X, monomial_eq_C_mul_X, mul_powₓ, ←C.map_pow, frobenius_def]
      ringExp

theorem map_expand_pow_char (f : Polynomial F) (n : ℕ) : map (frobenius F p^n) (expand F (p^n) f) = (f^p^n) :=
  by 
    induction n
    ·
      simp [RingHom.one_def]
    symm 
    rw [pow_succ'ₓ, pow_mulₓ, ←n_ih, ←expand_char, pow_succₓ, RingHom.mul_def, ←map_map, mul_commₓ, expand_mul,
      ←map_expand (Nat.Prime.pos hp.1)]

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem expand_contract
{f : polynomial F}
(hf : «expr = »(f.derivative, 0)) : «expr = »(expand F p (contract p f), f) :=
begin
  ext [] [ident n] [],
  rw ["[", expr coeff_expand hp.1.pos, ",", expr coeff_contract, "]"] [],
  split_ifs [] ["with", ident h],
  { rw [expr nat.div_mul_cancel h] [] },
  { cases [expr n] [],
    { exact [expr absurd (dvd_zero p) h] },
    have [] [] [":=", expr coeff_derivative f n],
    rw ["[", expr hf, ",", expr coeff_zero, ",", expr zero_eq_mul, "]"] ["at", ident this],
    cases [expr this] [],
    { rw [expr this] [] },
    rw ["[", "<-", expr nat.cast_succ, ",", expr char_p.cast_eq_zero_iff F p, "]"] ["at", ident this],
    exact [expr absurd this h] }
end

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem separable_or
{f : polynomial F}
(hf : irreducible f) : «expr ∨ »(f.separable, «expr ∧ »(«expr¬ »(f.separable), «expr∃ , »((g : polynomial F), «expr ∧ »(irreducible g, «expr = »(expand F p g, f))))) :=
if H : «expr = »(f.derivative, 0) then or.inr ⟨by rw ["[", expr separable_iff_derivative_ne_zero hf, ",", expr not_not, ",", expr H, "]"] [], contract p f, by haveI [] [] [":=", expr is_local_ring_hom_expand F hp.1.pos]; exact [expr of_irreducible_map «expr↑ »(expand F p) (by rwa ["<-", expr expand_contract p H] ["at", ident hf])], expand_contract p H⟩ else «expr $ »(or.inl, (separable_iff_derivative_ne_zero hf).2 H)

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_separable_of_irreducible
{f : polynomial F}
(hf : irreducible f)
(hf0 : «expr ≠ »(f, 0)) : «expr∃ , »((n : exprℕ())
 (g : polynomial F), «expr ∧ »(g.separable, «expr = »(expand F «expr ^ »(p, n) g, f))) :=
begin
  unfreezingI { induction [expr hn, ":", expr f.nat_degree] ["using", ident nat.strong_induction_on] ["with", ident N, ident ih] ["generalizing", ident f] },
  rcases [expr separable_or p hf, "with", ident h, "|", "⟨", ident h1, ",", ident g, ",", ident hg, ",", ident hgf, "⟩"],
  { refine [expr ⟨0, f, h, _⟩],
    rw ["[", expr pow_zero, ",", expr expand_one, "]"] [] },
  { cases [expr N] ["with", ident N],
    { rw ["[", expr nat_degree_eq_zero_iff_degree_le_zero, ",", expr degree_le_zero_iff, "]"] ["at", ident hn],
      rw ["[", expr hn, ",", expr separable_C, ",", expr is_unit_iff_ne_zero, ",", expr not_not, "]"] ["at", ident h1],
      rw ["[", expr h1, ",", expr C_0, "]"] ["at", ident hn],
      exact [expr absurd hn hf0] },
    have [ident hg1] [":", expr «expr = »(«expr * »(g.nat_degree, p), N.succ)] [],
    { rwa ["[", "<-", expr nat_degree_expand, ",", expr hgf, "]"] [] },
    have [ident hg2] [":", expr «expr ≠ »(g.nat_degree, 0)] [],
    { intro [ident this],
      rw ["[", expr this, ",", expr zero_mul, "]"] ["at", ident hg1],
      cases [expr hg1] [] },
    have [ident hg3] [":", expr «expr < »(g.nat_degree, N.succ)] [],
    { rw ["[", "<-", expr mul_one g.nat_degree, ",", "<-", expr hg1, "]"] [],
      exact [expr nat.mul_lt_mul_of_pos_left hp.1.one_lt (nat.pos_of_ne_zero hg2)] },
    have [ident hg4] [":", expr «expr ≠ »(g, 0)] [],
    { rintro [ident rfl],
      exact [expr hg2 nat_degree_zero] },
    rcases [expr ih _ hg3 hg hg4 rfl, "with", "⟨", ident n, ",", ident g, ",", ident hg5, ",", ident rfl, "⟩"],
    refine [expr ⟨«expr + »(n, 1), g, hg5, _⟩],
    rw ["[", "<-", expr hgf, ",", expr expand_expand, ",", expr pow_succ, "]"] [] }
end

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_unit_or_eq_zero_of_separable_expand
{f : polynomial F}
(n : exprℕ())
(hf : (expand F «expr ^ »(p, n) f).separable) : «expr ∨ »(is_unit f, «expr = »(n, 0)) :=
begin
  rw [expr or_iff_not_imp_right] [],
  intro [ident hn],
  have [ident hf2] [":", expr «expr = »((expand F «expr ^ »(p, n) f).derivative, 0)] [],
  { by rw ["[", expr derivative_expand, ",", expr nat.cast_pow, ",", expr char_p.cast_eq_zero, ",", expr zero_pow (nat.pos_of_ne_zero hn), ",", expr zero_mul, ",", expr mul_zero, "]"] [] },
  rw ["[", expr separable_def, ",", expr hf2, ",", expr is_coprime_zero_right, ",", expr is_unit_iff, "]"] ["at", ident hf],
  rcases [expr hf, "with", "⟨", ident r, ",", ident hr, ",", ident hrf, "⟩"],
  rw ["[", expr eq_comm, ",", expr expand_eq_C (pow_pos hp.1.pos _), "]"] ["at", ident hrf],
  rwa ["[", expr hrf, ",", expr is_unit_C, "]"] []
end

theorem unique_separable_of_irreducible {f : Polynomial F} (hf : Irreducible f) (hf0 : f ≠ 0) (n₁ : ℕ)
  (g₁ : Polynomial F) (hg₁ : g₁.separable) (hgf₁ : expand F (p^n₁) g₁ = f) (n₂ : ℕ) (g₂ : Polynomial F)
  (hg₂ : g₂.separable) (hgf₂ : expand F (p^n₂) g₂ = f) : n₁ = n₂ ∧ g₁ = g₂ :=
  by 
    revert g₁ g₂ 
    wlog (discharger := tactic.skip) hn : n₁ ≤ n₂ := le_totalₓ n₁ n₂ using n₁ n₂, n₂ n₁
    (
      intros 
      rw [le_iff_exists_add] at hn 
      rcases hn with ⟨k, rfl⟩
      rw [←hgf₁, pow_addₓ, expand_mul, expand_inj (pow_pos hp.1.Pos n₁)] at hgf₂ 
      subst hgf₂ 
      subst hgf₁ 
      rcases is_unit_or_eq_zero_of_separable_expand p k hg₁ with (h | rfl)
      ·
        rw [is_unit_iff] at h 
        rcases h with ⟨r, hr, rfl⟩
        simpRw [expand_C]  at hf 
        exact absurd (is_unit_C.2 hr) hf.1
      ·
        rw [add_zeroₓ, pow_zeroₓ, expand_one]
        split  <;> rfl)
    exact
      fun g₁ g₂ hg₁ hgf₁ hg₂ hgf₂ =>
        let ⟨hn, hg⟩ := this g₂ g₁ hg₂ hgf₂ hg₁ hgf₁
        ⟨hn.symm, hg.symm⟩

end CharP

theorem separable_prod_X_sub_C_iff' {ι : Sort _} {f : ι → F} {s : Finset ι} :
  (∏i in s, X - C (f i)).Separable ↔ ∀ x _ : x ∈ s y _ : y ∈ s, f x = f y → x = y :=
  ⟨fun hfs x hx y hy hfxy => hfs.inj_of_prod_X_sub_C hx hy hfxy,
    fun H =>
      by 
        rw [←prod_attach]
        exact
          separable_prod'
            (fun x hx y hy hxy =>
              @pairwise_coprime_X_sub _ _ { x // x ∈ s } (fun x => f x)
                (fun x y hxy => Subtype.eq$ H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
            fun _ _ => separable_X_sub_C⟩

theorem separable_prod_X_sub_C_iff {ι : Sort _} [Fintype ι] {f : ι → F} :
  (∏i, X - C (f i)).Separable ↔ Function.Injective f :=
  separable_prod_X_sub_C_iff'.trans$
    by 
      simpRw [mem_univ, true_implies_iff, Function.Injective]

section Splits

open_locale BigOperators

variable{i : F →+* K}

theorem not_unit_X_sub_C (a : F) : ¬IsUnit (X - C a) :=
  fun h =>
    have one_eq_zero : (1 : WithBot ℕ) = 0 :=
      by 
        simpa using degree_eq_zero_of_is_unit h 
    one_ne_zero (Option.some_injective _ one_eq_zero)

theorem nodup_of_separable_prod {s : Multiset F} (hs : separable (Multiset.map (fun a => X - C a) s).Prod) : s.nodup :=
  by 
    rw [Multiset.nodup_iff_ne_cons_cons]
    rintro a t rfl 
    refine' not_unit_X_sub_C a (is_unit_of_self_mul_dvd_separable hs _)
    simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)

theorem multiplicity_le_one_of_separable {p q : Polynomial F} (hq : ¬IsUnit q) (hsep : separable p) :
  multiplicity q p ≤ 1 :=
  by 
    contrapose! hq 
    apply is_unit_of_self_mul_dvd_separable hsep 
    rw [←sq]
    apply multiplicity.pow_dvd_of_le_multiplicity 
    simpa only [Nat.cast_one, Nat.cast_bit0] using Enat.add_one_le_of_lt hq

theorem separable.squarefree {p : Polynomial F} (hsep : separable p) : Squarefree p :=
  by 
    rw [multiplicity.squarefree_iff_multiplicity_le_one p]
    intro f 
    byCases' hunit : IsUnit f
    ·
      exact Or.inr hunit 
    exact Or.inl (multiplicity_le_one_of_separable hunit hsep)

/--If `is_unit n` in a nontrivial `comm_ring R`, then `X ^ n - u` is separable for any unit `u`. -/
theorem separable_X_pow_sub_C_unit {R : Type _} [CommRingₓ R] [Nontrivial R] {n : ℕ} (u : Units R)
  (hn : IsUnit (n : R)) : separable ((X^n) - C (u : R)) :=
  by 
    rcases n.eq_zero_or_pos with (rfl | hpos)
    ·
      simpa using hn 
    apply (separable_def' ((X^n) - C (u : R))).2
    obtain ⟨n', hn'⟩ := hn.exists_left_inv 
    refine' ⟨-C («expr↑ » (u⁻¹)), (C («expr↑ » (u⁻¹))*C n')*X, _⟩
    rw [derivative_sub, derivative_C, sub_zero, derivative_pow X n, derivative_X, mul_oneₓ]
    calc
      (((-C («expr↑ » (u⁻¹)))*(X^n) - C («expr↑ » u))+((C («expr↑ » (u⁻¹))*C n')*X)*«expr↑ » n*X^n - 1) =
        (C («expr↑ » (u⁻¹)*«expr↑ » u) - C («expr↑ » (u⁻¹))*X^n)+(C («expr↑ » (u⁻¹))*C (n'*«expr↑ » n))*X*X^n - 1 :=
      by 
        simp only [C.map_mul, C_eq_nat_cast]
        ring _ = 1 :=
      by 
        simp only [Units.inv_mul, hn', C.map_one, mul_oneₓ, ←pow_succₓ, Nat.sub_add_cancelₓ (show 1 ≤ n from hpos),
          sub_add_cancel]

/--If `n ≠ 0` in `F`, then ` X ^ n - a` is separable for any `a ≠ 0`. -/
theorem separable_X_pow_sub_C {n : ℕ} (a : F) (hn : (n : F) ≠ 0) (ha : a ≠ 0) : separable ((X^n) - C a) :=
  separable_X_pow_sub_C_unit (Units.mk0 a ha) (IsUnit.mk0 n hn)

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a field `F`, `X ^ n - 1` is separable iff `↑n ≠ 0`. -/
theorem X_pow_sub_one_separable_iff
{n : exprℕ()} : «expr ↔ »((«expr - »(«expr ^ »(X, n), 1) : polynomial F).separable, «expr ≠ »((n : F), 0)) :=
begin
  refine [expr ⟨_, λ h, separable_X_pow_sub_C_unit 1 (is_unit.mk0 «expr↑ »(n) h)⟩],
  rw ["[", expr separable_def', ",", expr derivative_sub, ",", expr derivative_X_pow, ",", expr derivative_one, ",", expr sub_zero, "]"] [],
  rintro ["(", ident h, ":", expr is_coprime _ _, ")", ident hn'],
  rw ["[", "<-", expr C_eq_nat_cast, ",", expr hn', ",", expr C.map_zero, ",", expr zero_mul, ",", expr is_coprime_zero_right, "]"] ["at", ident h],
  have [] [] [":=", expr not_is_unit_X_pow_sub_one F n],
  contradiction
end

/--If `n ≠ 0` in `F`, then ` X ^ n - a` is squarefree for any `a ≠ 0`. -/
theorem squarefree_X_pow_sub_C {n : ℕ} (a : F) (hn : (n : F) ≠ 0) (ha : a ≠ 0) : Squarefree ((X^n) - C a) :=
  (separable_X_pow_sub_C a hn ha).Squarefree

theorem root_multiplicity_le_one_of_separable {p : Polynomial F} (hp : p ≠ 0) (hsep : separable p) (x : F) :
  root_multiplicity x p ≤ 1 :=
  by 
    rw [root_multiplicity_eq_multiplicity, dif_neg hp, ←Enat.coe_le_coe, Enat.coe_get, Nat.cast_one]
    exact multiplicity_le_one_of_separable (not_unit_X_sub_C _) hsep

theorem count_roots_le_one {p : Polynomial F} (hsep : separable p) (x : F) : p.roots.count x ≤ 1 :=
  by 
    byCases' hp : p = 0
    ·
      simp [hp]
    rw [count_roots hp]
    exact root_multiplicity_le_one_of_separable hp hsep x

theorem nodup_roots {p : Polynomial F} (hsep : separable p) : p.roots.nodup :=
  Multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)

theorem card_root_set_eq_nat_degree [Algebra F K] {p : Polynomial F} (hsep : p.separable)
  (hsplit : splits (algebraMap F K) p) : Fintype.card (p.root_set K) = p.nat_degree :=
  by 
    simpRw [root_set_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Multiset.to_finset_card_of_nodup, ←nat_degree_eq_card_roots hsplit]
    exact nodup_roots hsep.map

theorem eq_X_sub_C_of_separable_of_root_eq {x : F} {h : Polynomial F} (h_ne_zero : h ≠ 0) (h_sep : h.separable)
  (h_root : h.eval x = 0) (h_splits : splits i h) (h_roots : ∀ y _ : y ∈ (h.map i).roots, y = i x) :
  h = C (leading_coeff h)*X - C x :=
  by 
    apply Polynomial.eq_X_sub_C_of_splits_of_single_root i h_splits 
    apply Finset.mk.inj
    ·
      change _ = {i x}
      rw [Finset.eq_singleton_iff_unique_mem]
      split 
      ·
        apply finset.mem_mk.mpr 
        rw
          [mem_roots
            (show h.map i ≠ 0 by 
              exact map_ne_zero h_ne_zero)]
        rw [is_root.def, ←eval₂_eq_eval_map, eval₂_hom, h_root]
        exact RingHom.map_zero i
      ·
        exact h_roots
    ·
      exact nodup_roots (separable.map h_sep)

theorem exists_finset_of_splits (i : F →+* K) {f : Polynomial F} (sep : separable f) (sp : splits i f) :
  ∃ s : Finset K, f.map i = C (i f.leading_coeff)*s.prod fun a : K => (X : Polynomial K) - C a :=
  by 
    classical 
    obtain ⟨s, h⟩ := exists_multiset_of_splits i sp 
    use s.to_finset 
    rw [h, Finset.prod_eq_multiset_prod, ←Multiset.to_finset_eq]
    apply nodup_of_separable_prod 
    apply separable.of_mul_right 
    rw [←h]
    exact sep.map

end Splits

end Field

end Polynomial

open Polynomial

theorem Irreducible.separable {F : Type u} [Field F] [CharZero F] {f : Polynomial F} (hf : Irreducible f) :
  f.separable :=
  by 
    rw [separable_iff_derivative_ne_zero hf, Ne, ←degree_eq_bot, degree_derivative_eq]
    rintro ⟨⟩
    rw [pos_iff_ne_zero, Ne, nat_degree_eq_zero_iff_degree_le_zero, degree_le_zero_iff]
    refine' fun hf1 => hf.not_unit _ 
    rw [hf1, is_unit_C, is_unit_iff_ne_zero]
    intro hf2 
    rw [hf2, C_0] at hf1 
    exact absurd hf1 hf.ne_zero

section CommRingₓ

variable(F K : Type _)[CommRingₓ F][Ringₓ K][Algebra F K]

/-- Typeclass for separable field extension: `K` is a separable field extension of `F` iff
the minimal polynomial of every `x : K` is separable.

We define this for general (commutative) rings and only assume `F` and `K` are fields if this
is needed for a proof.
-/
class IsSeparable : Prop where 
  is_integral' (x : K) : IsIntegral F x 
  separable' (x : K) : (minpoly F x).Separable

variable(F){K}

theorem IsSeparable.is_integral [IsSeparable F K] : ∀ x : K, IsIntegral F x :=
  IsSeparable.is_integral'

theorem IsSeparable.separable [IsSeparable F K] : ∀ x : K, (minpoly F x).Separable :=
  IsSeparable.separable'

variable{F K}

theorem is_separable_iff : IsSeparable F K ↔ ∀ x : K, IsIntegral F x ∧ (minpoly F x).Separable :=
  ⟨fun h x => ⟨@IsSeparable.is_integral F _ _ _ h x, @IsSeparable.separable F _ _ _ h x⟩,
    fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

end CommRingₓ

instance is_separable_self (F : Type _) [Field F] : IsSeparable F F :=
  ⟨fun x => is_integral_algebra_map,
    fun x =>
      by 
        rw [minpoly.eq_X_sub_C']
        exact separable_X_sub_C⟩

/-- A finite field extension in characteristic 0 is separable. -/
instance (priority := 100)IsSeparable.of_finite (F K : Type _) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [CharZero F] : IsSeparable F K :=
  have  : ∀ x : K, IsIntegral F x := fun x => (is_algebraic_iff_is_integral _).mp (Algebra.is_algebraic_of_finite _)
  ⟨this, fun x => (minpoly.irreducible (this x)).Separable⟩

section IsSeparableTower

variable(F K E : Type _)[Field F][Field K][Field E][Algebra F K][Algebra F E][Algebra K E][IsScalarTower F K E]

theorem is_separable_tower_top_of_is_separable [IsSeparable F E] : IsSeparable K E :=
  ⟨fun x => is_integral_of_is_scalar_tower x (IsSeparable.is_integral F x),
    fun x => (IsSeparable.separable F x).map.of_dvd (minpoly.dvd_map_of_is_scalar_tower _ _ _)⟩

theorem is_separable_tower_bot_of_is_separable [h : IsSeparable F E] : IsSeparable F K :=
  is_separable_iff.2$
    fun x =>
      by 
        refine' (is_separable_iff.1 h (algebraMap K E x)).imp is_integral_tower_bot_of_is_integral_field fun hs => _ 
        obtain ⟨q, hq⟩ :=
          minpoly.dvd F x
            (IsScalarTower.aeval_eq_zero_of_aeval_algebra_map_eq_zero_field (minpoly.aeval F ((algebraMap K E) x)))
        rw [hq] at hs 
        exact hs.of_mul_left

variable{E}

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_separable.of_alg_hom
(E' : Type*)
[field E']
[algebra F E']
(f : «expr →ₐ[ ] »(E, F, E'))
[is_separable F E'] : is_separable F E :=
begin
  letI [] [":", expr algebra E E'] [":=", expr ring_hom.to_algebra f.to_ring_hom],
  haveI [] [":", expr is_scalar_tower F E E'] [":=", expr is_scalar_tower.of_algebra_map_eq (λ x, (f.commutes x).symm)],
  exact [expr is_separable_tower_bot_of_is_separable F E E']
end

end IsSeparableTower

section CardAlgHom

variable{R S T : Type _}[CommRingₓ S]

variable{K L F : Type _}[Field K][Field L][Field F]

variable[Algebra K S][Algebra K L]

-- error in FieldTheory.Separable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem alg_hom.card_of_power_basis
(pb : power_basis K S)
(h_sep : (minpoly K pb.gen).separable)
(h_splits : (minpoly K pb.gen).splits (algebra_map K L)) : «expr = »(@fintype.card «expr →ₐ[ ] »(S, K, L) (power_basis.alg_hom.fintype pb), pb.dim) :=
begin
  let [ident s] [] [":=", expr ((minpoly K pb.gen).map (algebra_map K L)).roots.to_finset],
  have [ident H] [] [":=", expr λ x, multiset.mem_to_finset],
  rw ["[", expr fintype.card_congr pb.lift_equiv', ",", expr fintype.card_of_subtype s H, ",", "<-", expr pb.nat_degree_minpoly, ",", expr nat_degree_eq_card_roots h_splits, ",", expr multiset.to_finset_card_of_nodup, "]"] [],
  exact [expr nodup_roots ((separable_map (algebra_map K L)).mpr h_sep)]
end

end CardAlgHom

