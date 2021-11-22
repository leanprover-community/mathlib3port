import Mathbin.Algebra.Field 
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

variable{x y z : ℤ}(h : PythagoreanTriple x y z)

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
      exFalso 
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
      exFalso 
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

theorem gcd_dvd : (Int.gcdₓ x y : ℤ) ∣ z :=
  by 
    byCases' h0 : Int.gcdₓ x y = 0
    ·
      have hx : x = 0
      ·
        apply int.nat_abs_eq_zero.mp 
        apply Nat.eq_zero_of_gcd_eq_zero_leftₓ h0 
      have hy : y = 0
      ·
        apply int.nat_abs_eq_zero.mp 
        apply Nat.eq_zero_of_gcd_eq_zero_rightₓ h0 
      have hz : z = 0
      ·
        simpa only [PythagoreanTriple, hx, hy, add_zeroₓ, zero_eq_mul, mul_zero, or_selfₓ] using h 
      simp only [hz, dvd_zero]
    obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ : ∃ (k : ℕ)(x0 y0 : _), 0 < k ∧ Int.gcdₓ x0 y0 = 1 ∧ (x = x0*k) ∧ y = y0*k :=
      Int.exists_gcd_one' (Nat.pos_of_ne_zeroₓ h0)
    rw [Int.gcd_mul_right, h2, Int.nat_abs_of_nat, one_mulₓ]
    rw
      [←Int.pow_dvd_pow_iff
        (by 
          decide :
        0 < 2),
      sq z, ←h.eq]
    rw
      [(by 
        ring :
      (((x0*k)*x0*k)+(y0*k)*y0*k) = (k^2)*(x0*x0)+y0*y0)]
    exact dvd_mul_right _ _

theorem normalize : PythagoreanTriple (x / Int.gcdₓ x y) (y / Int.gcdₓ x y) (z / Int.gcdₓ x y) :=
  by 
    byCases' h0 : Int.gcdₓ x y = 0
    ·
      have hx : x = 0
      ·
        apply int.nat_abs_eq_zero.mp 
        apply Nat.eq_zero_of_gcd_eq_zero_leftₓ h0 
      have hy : y = 0
      ·
        apply int.nat_abs_eq_zero.mp 
        apply Nat.eq_zero_of_gcd_eq_zero_rightₓ h0 
      have hz : z = 0
      ·
        simpa only [PythagoreanTriple, hx, hy, add_zeroₓ, zero_eq_mul, mul_zero, or_selfₓ] using h 
      simp only [hx, hy, hz, Int.zero_div]
      exact zero 
    rcases h.gcd_dvd with ⟨z0, rfl⟩
    obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ : ∃ (k : ℕ)(x0 y0 : _), 0 < k ∧ Int.gcdₓ x0 y0 = 1 ∧ (x = x0*k) ∧ y = y0*k :=
      Int.exists_gcd_one' (Nat.pos_of_ne_zeroₓ h0)
    have hk : (k : ℤ) ≠ 0
    ·
      normCast 
      rwa [pos_iff_ne_zero] at k0 
    rw [Int.gcd_mul_right, h2, Int.nat_abs_of_nat, one_mulₓ] at h⊢
    rw [mul_commₓ x0, mul_commₓ y0, mul_iff k hk] at h 
    rwa [Int.mul_div_cancel _ hk, Int.mul_div_cancel _ hk, Int.mul_div_cancel_left _ hk]

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

theorem ne_zero_of_coprime (hc : Int.gcdₓ x y = 1) : z ≠ 0 :=
  by 
    suffices  : 0 < z*z
    ·
      rintro rfl 
      normNum  at this 
    rw [←h.eq, ←sq, ←sq]
    have hc' : Int.gcdₓ x y ≠ 0
    ·
      rw [hc]
      exact one_ne_zero 
    cases' Int.ne_zero_of_gcd hc' with hxz hyz
    ·
      apply lt_add_of_pos_of_le (sq_pos_of_ne_zero x hxz) (sq_nonneg y)
    ·
      apply lt_add_of_le_of_pos (sq_nonneg x) (sq_pos_of_ne_zero y hyz)

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

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem coprime_of_coprime (hc : «expr = »(int.gcd x y, 1)) : «expr = »(int.gcd y z, 1) :=
begin
  by_contradiction [ident H],
  obtain ["⟨", ident p, ",", ident hp, ",", ident hpy, ",", ident hpz, "⟩", ":=", expr nat.prime.not_coprime_iff_dvd.mp H],
  apply [expr hp.not_dvd_one],
  rw ["[", "<-", expr hc, "]"] [],
  apply [expr nat.dvd_gcd (int.prime.dvd_nat_abs_of_coe_dvd_sq hp _ _) hpy],
  rw ["[", expr sq, ",", expr eq_sub_of_add_eq h, "]"] [],
  rw ["[", "<-", expr int.coe_nat_dvd_left, "]"] ["at", ident hpy, ident hpz],
  exact [expr dvd_sub (hpz.mul_right _) (hpy.mul_right _)]
end

end PythagoreanTriple

section circleEquivGen

/-!
### A parametrization of the unit circle

For the classification of pythogorean triples, we will use a parametrization of the unit circle.
-/


variable{K : Type _}[Field K]

/--  A parameterization of the unit circle that is useful for classifying Pythagorean triples.
 (To be applied in the case where `K = ℚ`.) -/
def circleEquivGen (hk : ∀ x : K, (1+x^2) ≠ 0) : K ≃ { p : K × K // ((p.1^2)+p.2^2) = 1 ∧ p.2 ≠ -1 } :=
  { toFun :=
      fun x =>
        ⟨⟨(2*x) / 1+x^2, (1 - (x^2)) / 1+x^2⟩,
          by 
            fieldSimp [hk x, div_pow]
            ring,
          by 
            simp only [Ne.def, div_eq_iff (hk x), ←neg_mul_eq_neg_mul, one_mulₓ, neg_add, sub_eq_add_neg, add_left_injₓ]
            simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1⟩,
    invFun := fun p => (p : K × K).1 / (p : K × K).2+1,
    left_inv :=
      fun x =>
        by 
          have h2 : (1+1 : K) = 2 := rfl 
          have h3 : (2 : K) ≠ 0
          ·
            convert hk 1
            rw [one_pow 2, h2]
          fieldSimp [hk x, h2, add_assocₓ, add_commₓ, add_sub_cancel'_right, mul_commₓ],
    right_inv :=
      fun ⟨⟨x, y⟩, hxy, hy⟩ =>
        by 
          change ((x^2)+y^2) = 1 at hxy 
          have h2 : (y+1) ≠ 0
          ·
            apply mt eq_neg_of_add_eq_zero 
            exact hy 
          have h3 : (((y+1)^2)+x^2) = 2*y+1
          ·
            rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm]
            ring 
          have h4 : (2 : K) ≠ 0
          ·
            convert hk 1
            rw [one_pow 2]
            rfl 
          simp only [Prod.mk.inj_iffₓ, Subtype.mk_eq_mk]
          split 
          ·
            fieldSimp [h3]
            ring
          ·
            fieldSimp [h3]
            rw [←add_neg_eq_iff_eq_add.mpr hxy.symm]
            ring }

@[simp]
theorem circle_equiv_apply (hk : ∀ x : K, (1+x^2) ≠ 0) (x : K) :
  (circleEquivGen hk x : K × K) = ⟨(2*x) / 1+x^2, (1 - (x^2)) / 1+x^2⟩ :=
  rfl

@[simp]
theorem circle_equiv_symm_apply (hk : ∀ x : K, (1+x^2) ≠ 0) (v : { p : K × K // ((p.1^2)+p.2^2) = 1 ∧ p.2 ≠ -1 }) :
  (circleEquivGen hk).symm v = (v : K × K).1 / (v : K × K).2+1 :=
  rfl

end circleEquivGen

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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

-- error in NumberTheory.PythagoreanTriples: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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

variable{x y z : ℤ}(h : PythagoreanTriple x y z)

include h

theorem is_primitive_classified_aux (hc : x.gcd y = 1) (hzpos : 0 < z) {m n : ℤ} (hm2n2 : 0 < (m^2)+n^2)
  (hv2 : (x : ℚ) / z = ((2*m)*n) / (m^2)+n^2) (hw2 : (y : ℚ) / z = ((m^2) - (n^2)) / (m^2)+n^2)
  (H : Int.gcdₓ ((m^2) - (n^2)) ((m^2)+n^2) = 1) (co : Int.gcdₓ m n = 1)
  (pp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) : h.is_primitive_classified :=
  by 
    have hz : z ≠ 0
    apply ne_of_gtₓ hzpos 
    have h2 : y = (m^2) - (n^2) ∧ z = (m^2)+n^2
    ·
      apply Rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H 
      rw [hw2]
      normCast 
    use m, n 
    apply And.intro _ (And.intro co pp)
    right 
    refine' ⟨_, h2.left⟩
    rw [←Rat.coe_int_inj _ _, ←div_left_inj' ((mt (Rat.coe_int_inj z 0).mp) hz), hv2, h2.right]
    normCast

theorem is_primitive_classified_of_coprime_of_odd_of_pos (hc : Int.gcdₓ x y = 1) (hyo : y % 2 = 1) (hzpos : 0 < z) :
  h.is_primitive_classified :=
  by 
    byCases' h0 : x = 0
    ·
      exact h.is_primitive_classified_of_coprime_of_zero_left hc h0 
    let v := (x : ℚ) / z 
    let w := (y : ℚ) / z 
    have hz : z ≠ 0
    apply ne_of_gtₓ hzpos 
    have hq : ((v^2)+w^2) = 1
    ·
      fieldSimp [hz, sq]
      normCast 
      exact h 
    have hvz : v ≠ 0
    ·
      fieldSimp [hz]
      exact h0 
    have hw1 : w ≠ -1
    ·
      contrapose! hvz with hw1 
      rw [hw1, neg_sq, one_pow, add_left_eq_self] at hq 
      exact pow_eq_zero hq 
    have hQ : ∀ x : ℚ, (1+x^2) ≠ 0
    ·
      intro q 
      apply ne_of_gtₓ 
      exact lt_add_of_pos_of_le zero_lt_one (sq_nonneg q)
    have hp : (⟨v, w⟩ : ℚ × ℚ) ∈ { p : ℚ × ℚ | ((p.1^2)+p.2^2) = 1 ∧ p.2 ≠ -1 } := ⟨hq, hw1⟩
    let q := (circleEquivGen hQ).symm ⟨⟨v, w⟩, hp⟩
    have ht4 : (v = (2*q) / 1+q^2) ∧ w = (1 - (q^2)) / 1+q^2
    ·
      apply Prod.mk.inj 
      have  := ((circleEquivGen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm 
      exact congr_argₓ Subtype.val this 
    let m := (q.denom : ℤ)
    let n := q.num 
    have hm0 : m ≠ 0
    ·
      normCast 
      apply Rat.denom_ne_zero q 
    have hq2 : q = n / m := (Rat.num_div_denom q).symm 
    have hm2n2 : 0 < (m^2)+n^2
    ·
      apply lt_add_of_pos_of_le _ (sq_nonneg n)
      exact lt_of_le_of_neₓ (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm0))
    have hw2 : w = ((m^2) - (n^2)) / (m^2)+n^2
    ·
      rw [ht4.2, hq2]
      fieldSimp [hm2n2, Rat.denom_ne_zero q, -Rat.num_div_denom]
    have hm2n20 : (((m : ℚ)^2)+(n : ℚ)^2) ≠ 0
    ·
      normCast 
      simpa only [Int.coe_nat_pow] using ne_of_gtₓ hm2n2 
    have hv2 : v = ((2*m)*n) / (m^2)+n^2
    ·
      apply Eq.symm 
      apply (div_eq_iff hm2n20).mpr 
      rw [ht4.1]
      fieldSimp [hQ q]
      rw [hq2]
      fieldSimp [Rat.denom_ne_zero q, -Rat.num_div_denom]
      ring 
    have hnmcp : Int.gcdₓ n m = 1 := q.cop 
    have hmncp : Int.gcdₓ m n = 1
    ·
      rw [Int.gcd_comm]
      exact hnmcp 
    cases' Int.mod_two_eq_zero_or_one m with hm2 hm2 <;> cases' Int.mod_two_eq_zero_or_one n with hn2 hn2
    ·
      exFalso 
      have h1 : 2 ∣ (Int.gcdₓ n m : ℤ)
      ·
        exact Int.dvd_gcd (Int.dvd_of_mod_eq_zero hn2) (Int.dvd_of_mod_eq_zero hm2)
      rw [hnmcp] at h1 
      revert h1 
      normNum
    ·
      apply h.is_primitive_classified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
      ·
        apply Or.intro_left 
        exact And.intro hm2 hn2
      ·
        apply coprime_sq_sub_sq_add_of_even_odd hmncp hm2 hn2
    ·
      apply h.is_primitive_classified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
      ·
        apply Or.intro_rightₓ 
        exact And.intro hm2 hn2 
      apply coprime_sq_sub_sq_add_of_odd_even hmncp hm2 hn2
    ·
      exFalso 
      have h1 :
        (2 ∣ (m^2)+n^2) ∧
          2 ∣ (m^2) - (n^2) ∧ ((m^2) - (n^2)) / 2 % 2 = 0 ∧ Int.gcdₓ (((m^2) - (n^2)) / 2) (((m^2)+n^2) / 2) = 1
      ·
        exact coprime_sq_sub_sq_sum_of_odd_odd hmncp hm2 hn2 
      have h2 : y = ((m^2) - (n^2)) / 2 ∧ z = ((m^2)+n^2) / 2
      ·
        apply Rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2
        ·
          show w = _ 
          rw [←Rat.mk_eq_div,
            ←Rat.div_mk_div_cancel_left
              (by 
                normNum :
              (2 : ℤ) ≠ 0)]
          rw [Int.div_mul_cancel h1.1, Int.div_mul_cancel h1.2.1, hw2]
          normCast
        ·
          apply
            (mul_lt_mul_right
                (by 
                  normNum :
                0 < (2 : ℤ))).mp
              
          rw [Int.div_mul_cancel h1.1, zero_mul]
          exact hm2n2 
      rw [h2.1, h1.2.2.1] at hyo 
      revert hyo 
      normNum

theorem is_primitive_classified_of_coprime_of_pos (hc : Int.gcdₓ x y = 1) (hzpos : 0 < z) : h.is_primitive_classified :=
  by 
    cases' h.even_odd_of_coprime hc with h1 h2
    ·
      exact h.is_primitive_classified_of_coprime_of_odd_of_pos hc h1.right hzpos 
    rw [Int.gcd_comm] at hc 
    obtain ⟨m, n, H⟩ := h.symm.is_primitive_classified_of_coprime_of_odd_of_pos hc h2.left hzpos 
    use m, n 
    tauto

theorem is_primitive_classified_of_coprime (hc : Int.gcdₓ x y = 1) : h.is_primitive_classified :=
  by 
    byCases' hz : 0 < z
    ·
      exact h.is_primitive_classified_of_coprime_of_pos hc hz 
    have h' : PythagoreanTriple x y (-z)
    ·
      simpa [PythagoreanTriple, neg_mul_neg] using h.eq 
    apply h'.is_primitive_classified_of_coprime_of_pos hc 
    apply lt_of_le_of_neₓ _ (h'.ne_zero_of_coprime hc).symm 
    exact le_neg.mp (not_lt.mp hz)

theorem classified : h.is_classified :=
  by 
    byCases' h0 : Int.gcdₓ x y = 0
    ·
      have hx : x = 0
      ·
        apply int.nat_abs_eq_zero.mp 
        apply Nat.eq_zero_of_gcd_eq_zero_leftₓ h0 
      have hy : y = 0
      ·
        apply int.nat_abs_eq_zero.mp 
        apply Nat.eq_zero_of_gcd_eq_zero_rightₓ h0 
      use 0, 1, 0
      normNum [hx, hy]
    apply h.is_classified_of_normalize_is_primitive_classified 
    apply h.normalize.is_primitive_classified_of_coprime 
    apply Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zeroₓ h0)

omit h

theorem coprime_classification :
  PythagoreanTriple x y z ∧ Int.gcdₓ x y = 1 ↔
    ∃ m n,
      ((x = (m^2) - (n^2) ∧ y = (2*m)*n) ∨ (x = (2*m)*n) ∧ y = (m^2) - (n^2)) ∧
        ((z = (m^2)+n^2) ∨ z = -(m^2)+n^2) ∧ Int.gcdₓ m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :=
  by 
    split 
    ·
      intro h 
      obtain ⟨m, n, H⟩ := h.left.is_primitive_classified_of_coprime h.right 
      use m, n 
      rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩
      ·
        refine' ⟨Or.inl ⟨rfl, rfl⟩, _, co, pp⟩
        have  : (z^2) = (((m^2)+n^2)^2)
        ·
          rw [sq, ←h.left.eq]
          ring 
        simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
      ·
        refine' ⟨Or.inr ⟨rfl, rfl⟩, _, co, pp⟩
        have  : (z^2) = (((m^2)+n^2)^2)
        ·
          rw [sq, ←h.left.eq]
          ring 
        simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    ·
      delta' PythagoreanTriple 
      rintro ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl, co, pp⟩ <;>
        first |
          split 
          ·
            ring 
          exact coprime_sq_sub_mul co pp|
          split 
          ·
            ring 
          rw [Int.gcd_comm]
          exact coprime_sq_sub_mul co pp

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
          exFalso 
          revert h_pos 
          rw [h_neg]
          exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (add_nonneg (sq_nonneg m) (sq_nonneg n))))
      exFalso 
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
          exFalso 
          revert h_pos 
          rw [h_neg]
          exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (add_nonneg (sq_nonneg m) (sq_nonneg n))))
      exFalso 
      rcases h_even with ⟨rfl, -⟩
      rw [mul_assocₓ, Int.mul_mod_right] at h_parity 
      exact zero_ne_one h_parity

/-- **Formula for Pythagorean Triples** -/
theorem classification :
  PythagoreanTriple x y z ↔
    ∃ k m n,
      (((x = k*(m^2) - (n^2)) ∧ y = k*(2*m)*n) ∨ (x = k*(2*m)*n) ∧ y = k*(m^2) - (n^2)) ∧
        ((z = k*(m^2)+n^2) ∨ z = (-k)*(m^2)+n^2) :=
  by 
    split 
    ·
      intro h 
      obtain ⟨k, m, n, H⟩ := h.classified 
      use k, m, n 
      rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      ·
        refine' ⟨Or.inl ⟨rfl, rfl⟩, _⟩
        have  : (z^2) = ((k*(m^2)+n^2)^2)
        ·
          rw [sq, ←h.eq]
          ring 
        simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
      ·
        refine' ⟨Or.inr ⟨rfl, rfl⟩, _⟩
        have  : (z^2) = ((k*(m^2)+n^2)^2)
        ·
          rw [sq, ←h.eq]
          ring 
        simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    ·
      rintro ⟨k, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl⟩ <;> delta' PythagoreanTriple <;> ring

end PythagoreanTriple

