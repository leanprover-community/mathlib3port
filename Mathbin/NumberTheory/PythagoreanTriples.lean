import Mathbin.Algebra.Field.Basic 
import Mathbin.RingTheory.Int.Basic 
import Mathbin.Algebra.GroupWithZero.Power 
import Mathbin.Tactic.Ring 
import Mathbin.Tactic.RingExp 
import Mathbin.Tactic.FieldSimp 
import Mathbin.Data.Zmod.Basic

/-!
# Pythagorean Triples

The main result is the classification of Pythagorean triples. The final result is for general
Pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof. The parametrization maps the point
`(x / z, y / z)` to the slope of the line through `(-1 , 0)` and `(x / z, y / z)`. This quickly
shows that `(x / z, y / z) = (2 * m * n / (m ^ 2 + n ^ 2), (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))` where
`m / n` is the slope. In order to identify numerators and denominators we now need results showing
that these are coprime. This is easy except for the prime 2. In order to deal with that we have to
analyze the parity of `x`, `y`, `m` and `n` and eliminate all the impossible cases. This takes up
the bulk of the proof below.
-/


theorem sq_ne_two_fin_zmod_four (z : Zmod 4) : (z*z) ≠ 2 :=
  by 
    change Finₓ 4 at z 
    finCases z <;> normNum [Finₓ.ext_iff, Finₓ.coe_bit0, Finₓ.coe_bit1]

theorem Int.sq_ne_two_mod_four (z : ℤ) : (z*z) % 4 ≠ 2 :=
  suffices ¬(z*z) % (4 : ℕ) = 2 % (4 : ℕ)by 
    normNum  at this 
  by 
    rw [←Zmod.int_coe_eq_int_coe_iff']
    simpa using sq_ne_two_fin_zmod_four _

noncomputable theory

open_locale Classical

/-- Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z * z`. -/
def PythagoreanTriple (x y z : ℤ) : Prop :=
  ((x*x)+y*y) = z*z

/-- Pythagorean triples are interchangable, i.e `x * x + y * y = y * y + x * x = z * z`.
This comes from additive commutativity. -/
theorem pythagorean_triple_comm {x y z : ℤ} : PythagoreanTriple x y z ↔ PythagoreanTriple y x z :=
  by 
    delta' PythagoreanTriple 
    rw [add_commₓ]

/-- The zeroth Pythagorean triple is all zeros. -/
theorem PythagoreanTriple.zero : PythagoreanTriple 0 0 0 :=
  by 
    simp only [PythagoreanTriple, zero_mul, zero_addₓ]

namespace PythagoreanTriple

variable {x y z : ℤ} (h : PythagoreanTriple x y z)

include h

theorem Eq : ((x*x)+y*y) = z*z :=
  h

@[symm]
theorem symm : PythagoreanTriple y x z :=
  by 
    rwa [pythagorean_triple_comm]

/-- A triple is still a triple if you multiply `x`, `y` and `z`
by a constant `k`. -/
theorem mul (k : ℤ) : PythagoreanTriple (k*x) (k*y) (k*z) :=
  by 
    byCases' hk : k = 0
    ·
      simp only [PythagoreanTriple, hk, zero_mul, zero_addₓ]
    ·
      calc (((k*x)*k*x)+(k*y)*k*y) = (k^2)*(x*x)+y*y :=
        by 
          ring _ = (k^2)*z*z :=
        by 
          rw [h.eq]_ = (k*z)*k*z :=
        by 
          ring

omit h

/-- `(k*x, k*y, k*z)` is a Pythagorean triple if and only if
`(x, y, z)` is also a triple. -/
theorem mul_iff (k : ℤ) (hk : k ≠ 0) : PythagoreanTriple (k*x) (k*y) (k*z) ↔ PythagoreanTriple x y z :=
  by 
    refine' ⟨_, fun h => h.mul k⟩
    simp only [PythagoreanTriple]
    intro h 
    rw [←mul_left_inj' (mul_ne_zero hk hk)]
    convert h using 1 <;> ring

include h

/-- A Pythagorean triple `x, y, z` is “classified” if there exist integers `k, m, n` such that
either
 * `x = k * (m ^ 2 - n ^ 2)` and `y = k * (2 * m * n)`, or
 * `x = k * (2 * m * n)` and `y = k * (m ^ 2 - n ^ 2)`. -/
@[nolint unused_arguments]
def is_classified :=
  ∃ k m n : ℤ, (((x = k*(m^2) - (n^2)) ∧ y = k*(2*m)*n) ∨ (x = k*(2*m)*n) ∧ y = k*(m^2) - (n^2)) ∧ Int.gcdₓ m n = 1

/-- A primitive pythogorean triple `x, y, z` is a pythagorean triple with `x` and `y` coprime.
 Such a triple is “primitively classified” if there exist coprime integers `m, n` such that either
 * `x = m ^ 2 - n ^ 2` and `y = 2 * m * n`, or
 * `x = 2 * m * n` and `y = m ^ 2 - n ^ 2`.
-/
@[nolint unused_arguments]
def is_primitive_classified :=
  ∃ m n : ℤ,
    ((x = (m^2) - (n^2) ∧ y = (2*m)*n) ∨ (x = (2*m)*n) ∧ y = (m^2) - (n^2)) ∧
      Int.gcdₓ m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)

theorem mul_is_classified (k : ℤ) (hc : h.is_classified) : (h.mul k).IsClassified :=
  by 
    obtain ⟨l, m, n, ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co⟩⟩ := hc
    ·
      use k*l, m, n 
      apply And.intro _ co 
      left 
      split  <;> ring
    ·
      use k*l, m, n 
      apply And.intro _ co 
      right 
      split  <;> ring

theorem even_odd_of_coprime (hc : Int.gcdₓ x y = 1) : x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0 :=
  by 
    cases' Int.mod_two_eq_zero_or_one x with hx hx <;> cases' Int.mod_two_eq_zero_or_one y with hy hy
    ·
      exfalso 
      apply
        Nat.not_coprime_of_dvd_of_dvdₓ
          (by 
            decide :
          1 < 2)
          _ _ hc
      ·
        apply Int.dvd_nat_abs_of_of_nat_dvd 
        apply Int.dvd_of_mod_eq_zero hx
      ·
        apply Int.dvd_nat_abs_of_of_nat_dvd 
        apply Int.dvd_of_mod_eq_zero hy
    ·
      left 
      exact ⟨hx, hy⟩
    ·
      right 
      exact ⟨hx, hy⟩
    ·
      exfalso 
      obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, (x = (x0*2)+1) ∧ y = (y0*2)+1
      ·
        cases' exists_eq_mul_left_of_dvd (Int.dvd_sub_of_mod_eq hx) with x0 hx2 
        cases' exists_eq_mul_left_of_dvd (Int.dvd_sub_of_mod_eq hy) with y0 hy2 
        rw [sub_eq_iff_eq_add] at hx2 hy2 
        exact ⟨x0, y0, hx2, hy2⟩
      apply Int.sq_ne_two_mod_four z 
      rw
        [show (z*z) = (4*(((x0*x0)+x0)+y0*y0)+y0)+2by 
          rw [←h.eq]
          ring]
      normNum [Int.add_mod]

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gcd_dvd : «expr ∣ »((int.gcd x y : exprℤ()), z) :=
begin
  by_cases [expr h0, ":", expr «expr = »(int.gcd x y, 0)],
  { have [ident hx] [":", expr «expr = »(x, 0)] [],
    { apply [expr int.nat_abs_eq_zero.mp],
      apply [expr nat.eq_zero_of_gcd_eq_zero_left h0] },
    have [ident hy] [":", expr «expr = »(y, 0)] [],
    { apply [expr int.nat_abs_eq_zero.mp],
      apply [expr nat.eq_zero_of_gcd_eq_zero_right h0] },
    have [ident hz] [":", expr «expr = »(z, 0)] [],
    { simpa [] [] ["only"] ["[", expr pythagorean_triple, ",", expr hx, ",", expr hy, ",", expr add_zero, ",", expr zero_eq_mul, ",", expr mul_zero, ",", expr or_self, "]"] [] ["using", expr h] },
    simp [] [] ["only"] ["[", expr hz, ",", expr dvd_zero, "]"] [] [] },
  obtain ["⟨", ident k, ",", ident x0, ",", ident y0, ",", ident k0, ",", ident h2, ",", ident rfl, ",", ident rfl, "⟩", ":", expr «expr∃ , »((k : exprℕ())
    (x0
     y0), «expr ∧ »(«expr < »(0, k), «expr ∧ »(«expr = »(int.gcd x0 y0, 1), «expr ∧ »(«expr = »(x, «expr * »(x0, k)), «expr = »(y, «expr * »(y0, k)))))), ":=", expr int.exists_gcd_one' (nat.pos_of_ne_zero h0)],
  rw ["[", expr int.gcd_mul_right, ",", expr h2, ",", expr int.nat_abs_of_nat, ",", expr one_mul, "]"] [],
  rw ["[", "<-", expr int.pow_dvd_pow_iff (exprdec_trivial() : «expr < »(0, 2)), ",", expr sq z, ",", "<-", expr h.eq, "]"] [],
  rw [expr (by ring [] : «expr = »(«expr + »(«expr * »(«expr * »(x0, k), «expr * »(x0, k)), «expr * »(«expr * »(y0, k), «expr * »(y0, k))), «expr * »(«expr ^ »(k, 2), «expr + »(«expr * »(x0, x0), «expr * »(y0, y0)))))] [],
  exact [expr dvd_mul_right _ _]
end

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normalize : pythagorean_triple «expr / »(x, int.gcd x y) «expr / »(y, int.gcd x y) «expr / »(z, int.gcd x y) :=
begin
  by_cases [expr h0, ":", expr «expr = »(int.gcd x y, 0)],
  { have [ident hx] [":", expr «expr = »(x, 0)] [],
    { apply [expr int.nat_abs_eq_zero.mp],
      apply [expr nat.eq_zero_of_gcd_eq_zero_left h0] },
    have [ident hy] [":", expr «expr = »(y, 0)] [],
    { apply [expr int.nat_abs_eq_zero.mp],
      apply [expr nat.eq_zero_of_gcd_eq_zero_right h0] },
    have [ident hz] [":", expr «expr = »(z, 0)] [],
    { simpa [] [] ["only"] ["[", expr pythagorean_triple, ",", expr hx, ",", expr hy, ",", expr add_zero, ",", expr zero_eq_mul, ",", expr mul_zero, ",", expr or_self, "]"] [] ["using", expr h] },
    simp [] [] ["only"] ["[", expr hx, ",", expr hy, ",", expr hz, ",", expr int.zero_div, "]"] [] [],
    exact [expr zero] },
  rcases [expr h.gcd_dvd, "with", "⟨", ident z0, ",", ident rfl, "⟩"],
  obtain ["⟨", ident k, ",", ident x0, ",", ident y0, ",", ident k0, ",", ident h2, ",", ident rfl, ",", ident rfl, "⟩", ":", expr «expr∃ , »((k : exprℕ())
    (x0
     y0), «expr ∧ »(«expr < »(0, k), «expr ∧ »(«expr = »(int.gcd x0 y0, 1), «expr ∧ »(«expr = »(x, «expr * »(x0, k)), «expr = »(y, «expr * »(y0, k)))))), ":=", expr int.exists_gcd_one' (nat.pos_of_ne_zero h0)],
  have [ident hk] [":", expr «expr ≠ »((k : exprℤ()), 0)] [],
  { norm_cast [],
    rwa [expr pos_iff_ne_zero] ["at", ident k0] },
  rw ["[", expr int.gcd_mul_right, ",", expr h2, ",", expr int.nat_abs_of_nat, ",", expr one_mul, "]"] ["at", ident h, "⊢"],
  rw ["[", expr mul_comm x0, ",", expr mul_comm y0, ",", expr mul_iff k hk, "]"] ["at", ident h],
  rwa ["[", expr int.mul_div_cancel _ hk, ",", expr int.mul_div_cancel _ hk, ",", expr int.mul_div_cancel_left _ hk, "]"] []
end

theorem is_classified_of_is_primitive_classified (hp : h.is_primitive_classified) : h.is_classified :=
  by 
    obtain ⟨m, n, H⟩ := hp 
    use 1, m, n 
    rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩ <;>
      ·
        apply And.intro _ co 
        rw [one_mulₓ]
        rw [one_mulₓ]
        tauto

theorem is_classified_of_normalize_is_primitive_classified (hc : h.normalize.is_primitive_classified) :
  h.is_classified :=
  by 
    convert h.normalize.mul_is_classified (Int.gcdₓ x y) (is_classified_of_is_primitive_classified h.normalize hc) <;>
      rw [Int.mul_div_cancel']
    ·
      exact Int.gcd_dvd_left x y
    ·
      exact Int.gcd_dvd_right x y
    ·
      exact h.gcd_dvd

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ne_zero_of_coprime (hc : «expr = »(int.gcd x y, 1)) : «expr ≠ »(z, 0) :=
begin
  suffices [] [":", expr «expr < »(0, «expr * »(z, z))],
  { rintro [ident rfl],
    norm_num [] ["at", ident this] },
  rw ["[", "<-", expr h.eq, ",", "<-", expr sq, ",", "<-", expr sq, "]"] [],
  have [ident hc'] [":", expr «expr ≠ »(int.gcd x y, 0)] [],
  { rw [expr hc] [],
    exact [expr one_ne_zero] },
  cases [expr int.ne_zero_of_gcd hc'] ["with", ident hxz, ident hyz],
  { apply [expr lt_add_of_pos_of_le (sq_pos_of_ne_zero x hxz) (sq_nonneg y)] },
  { apply [expr lt_add_of_le_of_pos (sq_nonneg x) (sq_pos_of_ne_zero y hyz)] }
end

theorem is_primitive_classified_of_coprime_of_zero_left (hc : Int.gcdₓ x y = 1) (hx : x = 0) :
  h.is_primitive_classified :=
  by 
    subst x 
    change Nat.gcdₓ 0 (Int.natAbs y) = 1 at hc 
    rw [Nat.gcd_zero_leftₓ (Int.natAbs y)] at hc 
    cases' Int.nat_abs_eq y with hy hy
    ·
      use 1, 0
      rw [hy, hc, Int.gcd_zero_right]
      normNum
    ·
      use 0, 1
      rw [hy, hc, Int.gcd_zero_left]
      normNum

theorem coprime_of_coprime (hc : Int.gcdₓ x y = 1) : Int.gcdₓ y z = 1 :=
  by 
    byContra H 
    obtain ⟨p, hp, hpy, hpz⟩ := nat.prime.not_coprime_iff_dvd.mp H 
    apply hp.not_dvd_one 
    rw [←hc]
    apply Nat.dvd_gcdₓ (Int.Prime.dvd_nat_abs_of_coe_dvd_sq hp _ _) hpy 
    rw [sq, eq_sub_of_add_eq h]
    rw [←Int.coe_nat_dvd_left] at hpy hpz 
    exact dvd_sub (hpz.mul_right _) (hpy.mul_right _)

end PythagoreanTriple

section circleEquivGen

/-!
### A parametrization of the unit circle

For the classification of pythogorean triples, we will use a parametrization of the unit circle.
-/


variable {K : Type _} [Field K]

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--  A parameterization of the unit circle that is useful for classifying Pythagorean triples.
 (To be applied in the case where `K = ℚ`.) -/
def circle_equiv_gen
(hk : ∀
 x : K, «expr ≠ »(«expr + »(1, «expr ^ »(x, 2)), 0)) : «expr ≃ »(K, {p : «expr × »(K, K) // «expr ∧ »(«expr = »(«expr + »(«expr ^ »(p.1, 2), «expr ^ »(p.2, 2)), 1), «expr ≠ »(p.2, «expr- »(1)))}) :=
{ to_fun := λ
  x, ⟨⟨«expr / »(«expr * »(2, x), «expr + »(1, «expr ^ »(x, 2))), «expr / »(«expr - »(1, «expr ^ »(x, 2)), «expr + »(1, «expr ^ »(x, 2)))⟩, by { field_simp [] ["[", expr hk x, ",", expr div_pow, "]"] [] [],
     ring [] }, begin
     simp [] [] ["only"] ["[", expr ne.def, ",", expr div_eq_iff (hk x), ",", "<-", expr neg_mul_eq_neg_mul, ",", expr one_mul, ",", expr neg_add, ",", expr sub_eq_add_neg, ",", expr add_left_inj, "]"] [] [],
     simpa [] [] ["only"] ["[", expr eq_neg_iff_add_eq_zero, ",", expr one_pow, "]"] [] ["using", expr hk 1]
   end⟩,
  inv_fun := λ p, «expr / »((p : «expr × »(K, K)).1, «expr + »((p : «expr × »(K, K)).2, 1)),
  left_inv := λ x, begin
    have [ident h2] [":", expr «expr = »((«expr + »(1, 1) : K), 2)] [":=", expr rfl],
    have [ident h3] [":", expr «expr ≠ »((2 : K), 0)] [],
    { convert [] [expr hk 1] [],
      rw ["[", expr one_pow 2, ",", expr h2, "]"] [] },
    field_simp [] ["[", expr hk x, ",", expr h2, ",", expr add_assoc, ",", expr add_comm, ",", expr add_sub_cancel'_right, ",", expr mul_comm, "]"] [] []
  end,
  right_inv := λ ⟨⟨x, y⟩, hxy, hy⟩, begin
    change [expr «expr = »(«expr + »(«expr ^ »(x, 2), «expr ^ »(y, 2)), 1)] [] ["at", ident hxy],
    have [ident h2] [":", expr «expr ≠ »(«expr + »(y, 1), 0)] [],
    { apply [expr mt eq_neg_of_add_eq_zero],
      exact [expr hy] },
    have [ident h3] [":", expr «expr = »(«expr + »(«expr ^ »(«expr + »(y, 1), 2), «expr ^ »(x, 2)), «expr * »(2, «expr + »(y, 1)))] [],
    { rw ["[", expr (add_neg_eq_iff_eq_add.mpr hxy.symm).symm, "]"] [],
      ring [] },
    have [ident h4] [":", expr «expr ≠ »((2 : K), 0)] [],
    { convert [] [expr hk 1] [],
      rw [expr one_pow 2] [],
      refl },
    simp [] [] ["only"] ["[", expr prod.mk.inj_iff, ",", expr subtype.mk_eq_mk, "]"] [] [],
    split,
    { field_simp [] ["[", expr h3, "]"] [] [],
      ring [] },
    { field_simp [] ["[", expr h3, "]"] [] [],
      rw ["[", "<-", expr add_neg_eq_iff_eq_add.mpr hxy.symm, "]"] [],
      ring [] }
  end }

@[simp]
theorem circle_equiv_apply (hk : ∀ x : K, (1+x^2) ≠ 0) (x : K) :
  (circleEquivGen hk x : K × K) = ⟨(2*x) / 1+x^2, (1 - (x^2)) / 1+x^2⟩ :=
  rfl

@[simp]
theorem circle_equiv_symm_apply (hk : ∀ x : K, (1+x^2) ≠ 0) (v : { p : K × K // ((p.1^2)+p.2^2) = 1 ∧ p.2 ≠ -1 }) :
  (circleEquivGen hk).symm v = (v : K × K).1 / (v : K × K).2+1 :=
  rfl

end circleEquivGen

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem coprime_sq_sub_sq_add_of_even_odd
{m n : exprℤ()}
(h : «expr = »(int.gcd m n, 1))
(hm : «expr = »(«expr % »(m, 2), 0))
(hn : «expr = »(«expr % »(n, 2), 1)) : «expr = »(int.gcd «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)) «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 1) :=
begin
  by_contradiction [ident H],
  obtain ["⟨", ident p, ",", ident hp, ",", ident hp1, ",", ident hp2, "⟩", ":=", expr nat.prime.not_coprime_iff_dvd.mp H],
  rw ["<-", expr int.coe_nat_dvd_left] ["at", ident hp1, ident hp2],
  have [ident h2m] [":", expr «expr ∣ »((p : exprℤ()), «expr * »(2, «expr ^ »(m, 2)))] [],
  { convert [] [expr dvd_add hp2 hp1] [],
    ring [] },
  have [ident h2n] [":", expr «expr ∣ »((p : exprℤ()), «expr * »(2, «expr ^ »(n, 2)))] [],
  { convert [] [expr dvd_sub hp2 hp1] [],
    ring [] },
  have [ident hmc] [":", expr «expr ∨ »(«expr = »(p, 2), «expr ∣ »(p, int.nat_abs m))] [":=", expr prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2m],
  have [ident hnc] [":", expr «expr ∨ »(«expr = »(p, 2), «expr ∣ »(p, int.nat_abs n))] [":=", expr prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2n],
  by_cases [expr h2, ":", expr «expr = »(p, 2)],
  { have [ident h3] [":", expr «expr = »(«expr % »(«expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2), 1)] [],
    { norm_num ["[", expr sq, ",", expr int.add_mod, ",", expr int.mul_mod, ",", expr hm, ",", expr hn, "]"] [] },
    have [ident h4] [":", expr «expr = »(«expr % »(«expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2), 0)] [],
    { apply [expr int.mod_eq_zero_of_dvd],
      rwa [expr h2] ["at", ident hp2] },
    rw [expr h4] ["at", ident h3],
    exact [expr zero_ne_one h3] },
  { apply [expr hp.not_dvd_one],
    rw ["<-", expr h] [],
    exact [expr nat.dvd_gcd (or.resolve_left hmc h2) (or.resolve_left hnc h2)] }
end

private theorem coprime_sq_sub_sq_add_of_odd_even {m n : ℤ} (h : Int.gcdₓ m n = 1) (hm : m % 2 = 1) (hn : n % 2 = 0) :
  Int.gcdₓ ((m^2) - (n^2)) ((m^2)+n^2) = 1 :=
  by 
    rw [Int.gcdₓ, ←Int.nat_abs_neg ((m^2) - (n^2))]
    rw
      [(by 
        ring :
      -((m^2) - (n^2)) = (n^2) - (m^2)),
      add_commₓ]
    apply coprime_sq_sub_sq_add_of_even_odd _ hn hm 
    rwa [Int.gcd_comm]

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem coprime_sq_sub_mul_of_even_odd
{m n : exprℤ()}
(h : «expr = »(int.gcd m n, 1))
(hm : «expr = »(«expr % »(m, 2), 0))
(hn : «expr = »(«expr % »(n, 2), 1)) : «expr = »(int.gcd «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)) «expr * »(«expr * »(2, m), n), 1) :=
begin
  by_contradiction [ident H],
  obtain ["⟨", ident p, ",", ident hp, ",", ident hp1, ",", ident hp2, "⟩", ":=", expr nat.prime.not_coprime_iff_dvd.mp H],
  rw ["<-", expr int.coe_nat_dvd_left] ["at", ident hp1, ident hp2],
  have [ident hnp] [":", expr «expr¬ »(«expr ∣ »((p : exprℤ()), int.gcd m n))] [],
  { rw [expr h] [],
    norm_cast [],
    exact [expr mt nat.dvd_one.mp (nat.prime.ne_one hp)] },
  cases [expr int.prime.dvd_mul hp hp2] ["with", ident hp2m, ident hpn],
  { rw [expr int.nat_abs_mul] ["at", ident hp2m],
    cases [expr (nat.prime.dvd_mul hp).mp hp2m] ["with", ident hp2, ident hpm],
    { have [ident hp2'] [":", expr «expr = »(p, 2)] [":=", expr (nat.le_of_dvd zero_lt_two hp2).antisymm hp.two_le],
      revert [ident hp1],
      rw [expr hp2'] [],
      apply [expr mt int.mod_eq_zero_of_dvd],
      norm_num ["[", expr sq, ",", expr int.sub_mod, ",", expr int.mul_mod, ",", expr hm, ",", expr hn, "]"] [] },
    apply [expr mt (int.dvd_gcd (int.coe_nat_dvd_left.mpr hpm)) hnp],
    apply [expr (or_self _).mp],
    apply [expr int.prime.dvd_mul' hp],
    rw [expr (by ring [] : «expr = »(«expr * »(n, n), «expr + »(«expr- »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2))), «expr * »(m, m))))] [],
    apply [expr dvd_add (dvd_neg_of_dvd hp1)],
    exact [expr dvd_mul_of_dvd_left (int.coe_nat_dvd_left.mpr hpm) m] },
  rw [expr int.gcd_comm] ["at", ident hnp],
  apply [expr mt (int.dvd_gcd (int.coe_nat_dvd_left.mpr hpn)) hnp],
  apply [expr (or_self _).mp],
  apply [expr int.prime.dvd_mul' hp],
  rw [expr (by ring [] : «expr = »(«expr * »(m, m), «expr + »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), «expr * »(n, n))))] [],
  apply [expr dvd_add hp1],
  exact [expr (int.coe_nat_dvd_left.mpr hpn).mul_right n]
end

private theorem coprime_sq_sub_mul_of_odd_even {m n : ℤ} (h : Int.gcdₓ m n = 1) (hm : m % 2 = 1) (hn : n % 2 = 0) :
  Int.gcdₓ ((m^2) - (n^2)) ((2*m)*n) = 1 :=
  by 
    rw [Int.gcdₓ, ←Int.nat_abs_neg ((m^2) - (n^2))]
    rw
      [(by 
        ring :
      ((2*m)*n) = (2*n)*m),
      (by 
        ring :
      -((m^2) - (n^2)) = (n^2) - (m^2))]
    apply coprime_sq_sub_mul_of_even_odd _ hn hm 
    rwa [Int.gcd_comm]

private theorem coprime_sq_sub_mul {m n : ℤ} (h : Int.gcdₓ m n = 1)
  (hmn : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) : Int.gcdₓ ((m^2) - (n^2)) ((2*m)*n) = 1 :=
  by 
    cases' hmn with h1 h2
    ·
      exact coprime_sq_sub_mul_of_even_odd h h1.left h1.right
    ·
      exact coprime_sq_sub_mul_of_odd_even h h2.left h2.right

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem coprime_sq_sub_sq_sum_of_odd_odd
{m n : exprℤ()}
(h : «expr = »(int.gcd m n, 1))
(hm : «expr = »(«expr % »(m, 2), 1))
(hn : «expr = »(«expr % »(n, 2), 1)) : «expr ∧ »(«expr ∣ »(2, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))), «expr ∧ »(«expr ∣ »(2, «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2))), «expr ∧ »(«expr = »(«expr % »(«expr / »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2), 2), 0), «expr = »(int.gcd «expr / »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2) «expr / »(«expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2), 1)))) :=
begin
  cases [expr exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hm)] ["with", ident m0, ident hm2],
  cases [expr exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hn)] ["with", ident n0, ident hn2],
  rw [expr sub_eq_iff_eq_add] ["at", ident hm2, ident hn2],
  subst [expr m],
  subst [expr n],
  have [ident h1] [":", expr «expr = »(«expr + »(«expr ^ »(«expr + »(«expr * »(m0, 2), 1), 2), «expr ^ »(«expr + »(«expr * »(n0, 2), 1), 2)), «expr * »(2, «expr + »(«expr * »(2, «expr + »(«expr + »(«expr + »(«expr ^ »(m0, 2), «expr ^ »(n0, 2)), m0), n0)), 1)))] [],
  by ring_exp [] [],
  have [ident h2] [":", expr «expr = »(«expr - »(«expr ^ »(«expr + »(«expr * »(m0, 2), 1), 2), «expr ^ »(«expr + »(«expr * »(n0, 2), 1), 2)), «expr * »(2, «expr * »(2, «expr - »(«expr + »(«expr - »(«expr ^ »(m0, 2), «expr ^ »(n0, 2)), m0), n0))))] [],
  by ring_exp [] [],
  have [ident h3] [":", expr «expr = »(«expr % »(«expr / »(«expr - »(«expr ^ »(«expr + »(«expr * »(m0, 2), 1), 2), «expr ^ »(«expr + »(«expr * »(n0, 2), 1), 2)), 2), 2), 0)] [],
  { rw ["[", expr h2, ",", expr int.mul_div_cancel_left, ",", expr int.mul_mod_right, "]"] [],
    exact [expr exprdec_trivial()] },
  refine [expr ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, _⟩],
  have [ident h20] [":", expr «expr ≠ »((2 : exprℤ()), 0)] [":=", expr exprdec_trivial()],
  rw ["[", expr h1, ",", expr h2, ",", expr int.mul_div_cancel_left _ h20, ",", expr int.mul_div_cancel_left _ h20, "]"] [],
  by_contra [ident h4],
  obtain ["⟨", ident p, ",", ident hp, ",", ident hp1, ",", ident hp2, "⟩", ":=", expr nat.prime.not_coprime_iff_dvd.mp h4],
  apply [expr hp.not_dvd_one],
  rw ["<-", expr h] [],
  rw ["<-", expr int.coe_nat_dvd_left] ["at", ident hp1, ident hp2],
  apply [expr nat.dvd_gcd],
  { apply [expr int.prime.dvd_nat_abs_of_coe_dvd_sq hp],
    convert [] [expr dvd_add hp1 hp2] [],
    ring_exp [] [] },
  { apply [expr int.prime.dvd_nat_abs_of_coe_dvd_sq hp],
    convert [] [expr dvd_sub hp2 hp1] [],
    ring_exp [] [] }
end

namespace PythagoreanTriple

variable {x y z : ℤ} (h : PythagoreanTriple x y z)

include h

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_primitive_classified_aux
(hc : «expr = »(x.gcd y, 1))
(hzpos : «expr < »(0, z))
{m n : exprℤ()}
(hm2n2 : «expr < »(0, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))))
(hv2 : «expr = »(«expr / »((x : exprℚ()), z), «expr / »(«expr * »(«expr * »(2, m), n), «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)))))
(hw2 : «expr = »(«expr / »((y : exprℚ()), z), «expr / »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)))))
(H : «expr = »(int.gcd «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)) «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 1))
(co : «expr = »(int.gcd m n, 1))
(pp : «expr ∨ »(«expr ∧ »(«expr = »(«expr % »(m, 2), 0), «expr = »(«expr % »(n, 2), 1)), «expr ∧ »(«expr = »(«expr % »(m, 2), 1), «expr = »(«expr % »(n, 2), 0)))) : h.is_primitive_classified :=
begin
  have [ident hz] [":", expr «expr ≠ »(z, 0)] [],
  apply [expr ne_of_gt hzpos],
  have [ident h2] [":", expr «expr ∧ »(«expr = »(y, «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2))), «expr = »(z, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))))] [],
  { apply [expr rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H],
    rw ["[", expr hw2, "]"] [],
    norm_cast [] },
  use ["[", expr m, ",", expr n, "]"],
  apply [expr and.intro _ (and.intro co pp)],
  right,
  refine [expr ⟨_, h2.left⟩],
  rw ["[", "<-", expr rat.coe_int_inj _ _, ",", "<-", expr div_left_inj' (mt (rat.coe_int_inj z 0).mp hz), ",", expr hv2, ",", expr h2.right, "]"] [],
  norm_cast []
end

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_primitive_classified_of_coprime_of_odd_of_pos
(hc : «expr = »(int.gcd x y, 1))
(hyo : «expr = »(«expr % »(y, 2), 1))
(hzpos : «expr < »(0, z)) : h.is_primitive_classified :=
begin
  by_cases [expr h0, ":", expr «expr = »(x, 0)],
  { exact [expr h.is_primitive_classified_of_coprime_of_zero_left hc h0] },
  let [ident v] [] [":=", expr «expr / »((x : exprℚ()), z)],
  let [ident w] [] [":=", expr «expr / »((y : exprℚ()), z)],
  have [ident hz] [":", expr «expr ≠ »(z, 0)] [],
  apply [expr ne_of_gt hzpos],
  have [ident hq] [":", expr «expr = »(«expr + »(«expr ^ »(v, 2), «expr ^ »(w, 2)), 1)] [],
  { field_simp [] ["[", expr hz, ",", expr sq, "]"] [] [],
    norm_cast [],
    exact [expr h] },
  have [ident hvz] [":", expr «expr ≠ »(v, 0)] [],
  { field_simp [] ["[", expr hz, "]"] [] [],
    exact [expr h0] },
  have [ident hw1] [":", expr «expr ≠ »(w, «expr- »(1))] [],
  { contrapose ["!"] [ident hvz, "with", ident hw1],
    rw ["[", expr hw1, ",", expr neg_sq, ",", expr one_pow, ",", expr add_left_eq_self, "]"] ["at", ident hq],
    exact [expr pow_eq_zero hq] },
  have [ident hQ] [":", expr ∀ x : exprℚ(), «expr ≠ »(«expr + »(1, «expr ^ »(x, 2)), 0)] [],
  { intro [ident q],
    apply [expr ne_of_gt],
    exact [expr lt_add_of_pos_of_le zero_lt_one (sq_nonneg q)] },
  have [ident hp] [":", expr «expr ∈ »((⟨v, w⟩ : «expr × »(exprℚ(), exprℚ())), {p : «expr × »(exprℚ(), exprℚ()) | «expr ∧ »(«expr = »(«expr + »(«expr ^ »(p.1, 2), «expr ^ »(p.2, 2)), 1), «expr ≠ »(p.2, «expr- »(1)))})] [":=", expr ⟨hq, hw1⟩],
  let [ident q] [] [":=", expr (circle_equiv_gen hQ).symm ⟨⟨v, w⟩, hp⟩],
  have [ident ht4] [":", expr «expr ∧ »(«expr = »(v, «expr / »(«expr * »(2, q), «expr + »(1, «expr ^ »(q, 2)))), «expr = »(w, «expr / »(«expr - »(1, «expr ^ »(q, 2)), «expr + »(1, «expr ^ »(q, 2)))))] [],
  { apply [expr prod.mk.inj],
    have [] [] [":=", expr ((circle_equiv_gen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm],
    exact [expr congr_arg subtype.val this] },
  let [ident m] [] [":=", expr (q.denom : exprℤ())],
  let [ident n] [] [":=", expr q.num],
  have [ident hm0] [":", expr «expr ≠ »(m, 0)] [],
  { norm_cast [],
    apply [expr rat.denom_ne_zero q] },
  have [ident hq2] [":", expr «expr = »(q, «expr / »(n, m))] [":=", expr (rat.num_div_denom q).symm],
  have [ident hm2n2] [":", expr «expr < »(0, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)))] [],
  { apply [expr lt_add_of_pos_of_le _ (sq_nonneg n)],
    exact [expr lt_of_le_of_ne (sq_nonneg m) (ne.symm (pow_ne_zero 2 hm0))] },
  have [ident hw2] [":", expr «expr = »(w, «expr / »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))))] [],
  { rw ["[", expr ht4.2, ",", expr hq2, "]"] [],
    field_simp [] ["[", expr hm2n2, ",", expr rat.denom_ne_zero q, ",", "-", ident rat.num_div_denom, "]"] [] [] },
  have [ident hm2n20] [":", expr «expr ≠ »(«expr + »(«expr ^ »((m : exprℚ()), 2), «expr ^ »((n : exprℚ()), 2)), 0)] [],
  { norm_cast [],
    simpa [] [] ["only"] ["[", expr int.coe_nat_pow, "]"] [] ["using", expr ne_of_gt hm2n2] },
  have [ident hv2] [":", expr «expr = »(v, «expr / »(«expr * »(«expr * »(2, m), n), «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))))] [],
  { apply [expr eq.symm],
    apply [expr (div_eq_iff hm2n20).mpr],
    rw ["[", expr ht4.1, "]"] [],
    field_simp [] ["[", expr hQ q, "]"] [] [],
    rw ["[", expr hq2, "]"] [] { occs := occurrences.pos «expr[ , ]»([2, 3]) },
    field_simp [] ["[", expr rat.denom_ne_zero q, ",", "-", ident rat.num_div_denom, "]"] [] [],
    ring [] },
  have [ident hnmcp] [":", expr «expr = »(int.gcd n m, 1)] [":=", expr q.cop],
  have [ident hmncp] [":", expr «expr = »(int.gcd m n, 1)] [],
  { rw [expr int.gcd_comm] [],
    exact [expr hnmcp] },
  cases [expr int.mod_two_eq_zero_or_one m] ["with", ident hm2, ident hm2]; cases [expr int.mod_two_eq_zero_or_one n] ["with", ident hn2, ident hn2],
  { exfalso,
    have [ident h1] [":", expr «expr ∣ »(2, (int.gcd n m : exprℤ()))] [],
    { exact [expr int.dvd_gcd (int.dvd_of_mod_eq_zero hn2) (int.dvd_of_mod_eq_zero hm2)] },
    rw [expr hnmcp] ["at", ident h1],
    revert [ident h1],
    norm_num [] [] },
  { apply [expr h.is_primitive_classified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp],
    { apply [expr or.intro_left],
      exact [expr and.intro hm2 hn2] },
    { apply [expr coprime_sq_sub_sq_add_of_even_odd hmncp hm2 hn2] } },
  { apply [expr h.is_primitive_classified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp],
    { apply [expr or.intro_right],
      exact [expr and.intro hm2 hn2] },
    apply [expr coprime_sq_sub_sq_add_of_odd_even hmncp hm2 hn2] },
  { exfalso,
    have [ident h1] [":", expr «expr ∧ »(«expr ∣ »(2, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))), «expr ∧ »(«expr ∣ »(2, «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2))), «expr ∧ »(«expr = »(«expr % »(«expr / »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2), 2), 0), «expr = »(int.gcd «expr / »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2) «expr / »(«expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2), 1))))] [],
    { exact [expr coprime_sq_sub_sq_sum_of_odd_odd hmncp hm2 hn2] },
    have [ident h2] [":", expr «expr ∧ »(«expr = »(y, «expr / »(«expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2)), «expr = »(z, «expr / »(«expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2)))] [],
    { apply [expr rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2],
      { show [expr «expr = »(w, _)],
        rw ["[", "<-", expr rat.mk_eq_div, ",", "<-", expr rat.div_mk_div_cancel_left (by norm_num [] [] : «expr ≠ »((2 : exprℤ()), 0)), "]"] [],
        rw ["[", expr int.div_mul_cancel h1.1, ",", expr int.div_mul_cancel h1.2.1, ",", expr hw2, "]"] [],
        norm_cast [] },
      { apply [expr (mul_lt_mul_right (by norm_num [] [] : «expr < »(0, (2 : exprℤ())))).mp],
        rw ["[", expr int.div_mul_cancel h1.1, ",", expr zero_mul, "]"] [],
        exact [expr hm2n2] } },
    rw ["[", expr h2.1, ",", expr h1.2.2.1, "]"] ["at", ident hyo],
    revert [ident hyo],
    norm_num [] [] }
end

theorem is_primitive_classified_of_coprime_of_pos (hc : Int.gcdₓ x y = 1) (hzpos : 0 < z) : h.is_primitive_classified :=
  by 
    cases' h.even_odd_of_coprime hc with h1 h2
    ·
      exact h.is_primitive_classified_of_coprime_of_odd_of_pos hc h1.right hzpos 
    rw [Int.gcd_comm] at hc 
    obtain ⟨m, n, H⟩ := h.symm.is_primitive_classified_of_coprime_of_odd_of_pos hc h2.left hzpos 
    use m, n 
    tauto

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_primitive_classified_of_coprime (hc : «expr = »(int.gcd x y, 1)) : h.is_primitive_classified :=
begin
  by_cases [expr hz, ":", expr «expr < »(0, z)],
  { exact [expr h.is_primitive_classified_of_coprime_of_pos hc hz] },
  have [ident h'] [":", expr pythagorean_triple x y «expr- »(z)] [],
  { simpa [] [] [] ["[", expr pythagorean_triple, ",", expr neg_mul_neg, "]"] [] ["using", expr h.eq] },
  apply [expr h'.is_primitive_classified_of_coprime_of_pos hc],
  apply [expr lt_of_le_of_ne _ (h'.ne_zero_of_coprime hc).symm],
  exact [expr le_neg.mp (not_lt.mp hz)]
end

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem classified : h.is_classified :=
begin
  by_cases [expr h0, ":", expr «expr = »(int.gcd x y, 0)],
  { have [ident hx] [":", expr «expr = »(x, 0)] [],
    { apply [expr int.nat_abs_eq_zero.mp],
      apply [expr nat.eq_zero_of_gcd_eq_zero_left h0] },
    have [ident hy] [":", expr «expr = »(y, 0)] [],
    { apply [expr int.nat_abs_eq_zero.mp],
      apply [expr nat.eq_zero_of_gcd_eq_zero_right h0] },
    use ["[", expr 0, ",", expr 1, ",", expr 0, "]"],
    norm_num ["[", expr hx, ",", expr hy, "]"] [] },
  apply [expr h.is_classified_of_normalize_is_primitive_classified],
  apply [expr h.normalize.is_primitive_classified_of_coprime],
  apply [expr int.gcd_div_gcd_div_gcd (nat.pos_of_ne_zero h0)]
end

omit h

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coprime_classification : «expr ↔ »(«expr ∧ »(pythagorean_triple x y z, «expr = »(int.gcd x y, 1)), «expr∃ , »((m
   n), «expr ∧ »(«expr ∨ »(«expr ∧ »(«expr = »(x, «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2))), «expr = »(y, «expr * »(«expr * »(2, m), n))), «expr ∧ »(«expr = »(x, «expr * »(«expr * »(2, m), n)), «expr = »(y, «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2))))), «expr ∧ »(«expr ∨ »(«expr = »(z, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))), «expr = »(z, «expr- »(«expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))))), «expr ∧ »(«expr = »(int.gcd m n, 1), «expr ∨ »(«expr ∧ »(«expr = »(«expr % »(m, 2), 0), «expr = »(«expr % »(n, 2), 1)), «expr ∧ »(«expr = »(«expr % »(m, 2), 1), «expr = »(«expr % »(n, 2), 0)))))))) :=
begin
  split,
  { intro [ident h],
    obtain ["⟨", ident m, ",", ident n, ",", ident H, "⟩", ":=", expr h.left.is_primitive_classified_of_coprime h.right],
    use ["[", expr m, ",", expr n, "]"],
    rcases [expr H, "with", "⟨", "⟨", ident rfl, ",", ident rfl, "⟩", "|", "⟨", ident rfl, ",", ident rfl, "⟩", ",", ident co, ",", ident pp, "⟩"],
    { refine [expr ⟨or.inl ⟨rfl, rfl⟩, _, co, pp⟩],
      have [] [":", expr «expr = »(«expr ^ »(z, 2), «expr ^ »(«expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2))] [],
      { rw ["[", expr sq, ",", "<-", expr h.left.eq, "]"] [],
        ring [] },
      simpa [] [] [] [] [] ["using", expr eq_or_eq_neg_of_sq_eq_sq _ _ this] },
    { refine [expr ⟨or.inr ⟨rfl, rfl⟩, _, co, pp⟩],
      have [] [":", expr «expr = »(«expr ^ »(z, 2), «expr ^ »(«expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)), 2))] [],
      { rw ["[", expr sq, ",", "<-", expr h.left.eq, "]"] [],
        ring [] },
      simpa [] [] [] [] [] ["using", expr eq_or_eq_neg_of_sq_eq_sq _ _ this] } },
  { delta [ident pythagorean_triple] [],
    rintro ["⟨", ident m, ",", ident n, ",", "⟨", ident rfl, ",", ident rfl, "⟩", "|", "⟨", ident rfl, ",", ident rfl, "⟩", ",", ident rfl, "|", ident rfl, ",", ident co, ",", ident pp, "⟩"]; { split,
      { ring [] },
      exact [expr coprime_sq_sub_mul co pp] } <|> { split,
      { ring [] },
      rw [expr int.gcd_comm] [],
      exact [expr coprime_sq_sub_mul co pp] } }
end

/-- by assuming `x` is odd and `z` is positive we get a slightly more precise classification of
the pythagorean triple `x ^ 2 + y ^ 2 = z ^ 2`-/
theorem coprime_classification' {x y z : ℤ} (h : PythagoreanTriple x y z) (h_coprime : Int.gcdₓ x y = 1)
  (h_parity : x % 2 = 1) (h_pos : 0 < z) :
  ∃ m n,
    x = (m^2) - (n^2) ∧
      (y = (2*m)*n) ∧ (z = (m^2)+n^2) ∧ Int.gcdₓ m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m :=
  by 
    obtain ⟨m, n, ht1, ht2, ht3, ht4⟩ := pythagorean_triple.coprime_classification.mp (And.intro h h_coprime)
    cases' le_or_ltₓ 0 m with hm hm
    ·
      use m, n 
      cases' ht1 with h_odd h_even
      ·
        apply And.intro h_odd.1
        apply And.intro h_odd.2
        cases' ht2 with h_pos h_neg
        ·
          apply And.intro h_pos (And.intro ht3 (And.intro ht4 hm))
        ·
          exfalso 
          revert h_pos 
          rw [h_neg]
          exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (add_nonneg (sq_nonneg m) (sq_nonneg n))))
      exfalso 
      rcases h_even with ⟨rfl, -⟩
      rw [mul_assocₓ, Int.mul_mod_right] at h_parity 
      exact zero_ne_one h_parity
    ·
      use -m, -n 
      cases' ht1 with h_odd h_even
      ·
        rw [neg_sq m]
        rw [neg_sq n]
        apply And.intro h_odd.1
        split 
        ·
          rw [h_odd.2]
          ring 
        cases' ht2 with h_pos h_neg
        ·
          apply And.intro h_pos 
          split 
          ·
            delta' Int.gcdₓ 
            rw [Int.nat_abs_neg, Int.nat_abs_neg]
            exact ht3
          ·
            rw [Int.neg_mod_two, Int.neg_mod_two]
            apply And.intro ht4 
            linarith
        ·
          exfalso 
          revert h_pos 
          rw [h_neg]
          exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (add_nonneg (sq_nonneg m) (sq_nonneg n))))
      exfalso 
      rcases h_even with ⟨rfl, -⟩
      rw [mul_assocₓ, Int.mul_mod_right] at h_parity 
      exact zero_ne_one h_parity

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Formula for Pythagorean Triples** -/
theorem classification : «expr ↔ »(pythagorean_triple x y z, «expr∃ , »((k
   m
   n), «expr ∧ »(«expr ∨ »(«expr ∧ »(«expr = »(x, «expr * »(k, «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)))), «expr = »(y, «expr * »(k, «expr * »(«expr * »(2, m), n)))), «expr ∧ »(«expr = »(x, «expr * »(k, «expr * »(«expr * »(2, m), n))), «expr = »(y, «expr * »(k, «expr - »(«expr ^ »(m, 2), «expr ^ »(n, 2)))))), «expr ∨ »(«expr = »(z, «expr * »(k, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)))), «expr = »(z, «expr * »(«expr- »(k), «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2)))))))) :=
begin
  split,
  { intro [ident h],
    obtain ["⟨", ident k, ",", ident m, ",", ident n, ",", ident H, "⟩", ":=", expr h.classified],
    use ["[", expr k, ",", expr m, ",", expr n, "]"],
    rcases [expr H, "with", "⟨", ident rfl, ",", ident rfl, "⟩", "|", "⟨", ident rfl, ",", ident rfl, "⟩"],
    { refine [expr ⟨or.inl ⟨rfl, rfl⟩, _⟩],
      have [] [":", expr «expr = »(«expr ^ »(z, 2), «expr ^ »(«expr * »(k, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))), 2))] [],
      { rw ["[", expr sq, ",", "<-", expr h.eq, "]"] [],
        ring [] },
      simpa [] [] [] [] [] ["using", expr eq_or_eq_neg_of_sq_eq_sq _ _ this] },
    { refine [expr ⟨or.inr ⟨rfl, rfl⟩, _⟩],
      have [] [":", expr «expr = »(«expr ^ »(z, 2), «expr ^ »(«expr * »(k, «expr + »(«expr ^ »(m, 2), «expr ^ »(n, 2))), 2))] [],
      { rw ["[", expr sq, ",", "<-", expr h.eq, "]"] [],
        ring [] },
      simpa [] [] [] [] [] ["using", expr eq_or_eq_neg_of_sq_eq_sq _ _ this] } },
  { rintro ["⟨", ident k, ",", ident m, ",", ident n, ",", "⟨", ident rfl, ",", ident rfl, "⟩", "|", "⟨", ident rfl, ",", ident rfl, "⟩", ",", ident rfl, "|", ident rfl, "⟩"]; delta [ident pythagorean_triple] []; ring [] }
end

end PythagoreanTriple

