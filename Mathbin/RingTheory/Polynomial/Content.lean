import Mathbin.Algebra.GcdMonoid.Finset 
import Mathbin.Data.Polynomial.FieldDivision 
import Mathbin.Data.Polynomial.EraseLead 
import Mathbin.Data.Polynomial.CancelLeads

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : polynomial R`.
 - `p.content` is the `gcd` of the coefficients of `p`.
 - `p.is_primitive` indicates that `p.content = 1`.

## Main Results
 - `polynomial.content_mul`:
  If `p q : polynomial R`, then `(p * q).content = p.content * q.content`.
 - `polynomial.normalized_gcd_monoid`:
  The polynomial ring of a GCD domain is itself a GCD domain.

-/


namespace Polynomial

section Primitive

variable{R : Type _}[CommSemiringₓ R]

/-- A polynomial is primitive when the only constant polynomials dividing it are units -/
def is_primitive (p : Polynomial R) : Prop :=
  ∀ (r : R), C r ∣ p → IsUnit r

theorem is_primitive_iff_is_unit_of_C_dvd {p : Polynomial R} : p.is_primitive ↔ ∀ (r : R), C r ∣ p → IsUnit r :=
  Iff.rfl

@[simp]
theorem is_primitive_one : is_primitive (1 : Polynomial R) :=
  fun r h => is_unit_C.mp (is_unit_of_dvd_one (C r) h)

theorem monic.is_primitive {p : Polynomial R} (hp : p.monic) : p.is_primitive :=
  by 
    rintro r ⟨q, h⟩
    exact
      is_unit_of_mul_eq_one r (q.coeff p.nat_degree)
        (by 
          rwa [←coeff_C_mul, ←h])

theorem is_primitive.ne_zero [Nontrivial R] {p : Polynomial R} (hp : p.is_primitive) : p ≠ 0 :=
  by 
    rintro rfl 
    exact (hp 0 (dvd_zero (C 0))).ne_zero rfl

end Primitive

variable{R : Type _}[CommRingₓ R][IsDomain R]

section NormalizedGcdMonoid

variable[NormalizedGcdMonoid R]

/-- `p.content` is the `gcd` of the coefficients of `p`. -/
def content (p : Polynomial R) : R :=
  p.support.gcd p.coeff

theorem content_dvd_coeff {p : Polynomial R} (n : ℕ) : p.content ∣ p.coeff n :=
  by 
    byCases' h : n ∈ p.support
    ·
      apply Finset.gcd_dvd h 
    rw [mem_support_iff, not_not] at h 
    rw [h]
    apply dvd_zero

-- error in RingTheory.Polynomial.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem content_C {r : R} : «expr = »((C r).content, normalize r) :=
begin
  rw [expr content] [],
  by_cases [expr h0, ":", expr «expr = »(r, 0)],
  { simp [] [] [] ["[", expr h0, "]"] [] [] },
  have [ident h] [":", expr «expr = »((C r).support, {0})] [":=", expr support_monomial _ _ h0],
  simp [] [] [] ["[", expr h, "]"] [] []
end

@[simp]
theorem content_zero : content (0 : Polynomial R) = 0 :=
  by 
    rw [←C_0, content_C, normalize_zero]

@[simp]
theorem content_one : content (1 : Polynomial R) = 1 :=
  by 
    rw [←C_1, content_C, normalize_one]

-- error in RingTheory.Polynomial.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem content_X_mul {p : polynomial R} : «expr = »(content «expr * »(X, p), content p) :=
begin
  rw ["[", expr content, ",", expr content, ",", expr finset.gcd_def, ",", expr finset.gcd_def, "]"] [],
  refine [expr congr rfl _],
  have [ident h] [":", expr «expr = »(«expr * »(X, p).support, p.support.map ⟨nat.succ, nat.succ_injective⟩)] [],
  { ext [] [ident a] [],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr finset.mem_map, ",", expr function.embedding.coe_fn_mk, ",", expr ne.def, ",", expr mem_support_iff, "]"] [] [],
    cases [expr a] [],
    { simp [] [] [] ["[", expr coeff_X_mul_zero, ",", expr nat.succ_ne_zero, "]"] [] [] },
    rw ["[", expr mul_comm, ",", expr coeff_mul_X, "]"] [],
    split,
    { intro [ident h],
      use [expr a],
      simp [] [] [] ["[", expr h, "]"] [] [] },
    { rintros ["⟨", ident b, ",", "⟨", ident h1, ",", ident h2, "⟩", "⟩"],
      rw ["<-", expr nat.succ_injective h2] [],
      apply [expr h1] } },
  rw [expr h] [],
  simp [] [] ["only"] ["[", expr finset.map_val, ",", expr function.comp_app, ",", expr function.embedding.coe_fn_mk, ",", expr multiset.map_map, "]"] [] [],
  refine [expr congr (congr rfl _) rfl],
  ext [] [ident a] [],
  rw [expr mul_comm] [],
  simp [] [] [] ["[", expr coeff_mul_X, "]"] [] []
end

@[simp]
theorem content_X_pow {k : ℕ} : content ((X : Polynomial R) ^ k) = 1 :=
  by 
    induction' k with k hi
    ·
      simp 
    rw [pow_succₓ, content_X_mul, hi]

@[simp]
theorem content_X : content (X : Polynomial R) = 1 :=
  by 
    rw [←mul_oneₓ X, content_X_mul, content_one]

theorem content_C_mul (r : R) (p : Polynomial R) : (C r*p).content = normalize r*p.content :=
  by 
    byCases' h0 : r = 0
    ·
      simp [h0]
    rw [content]
    rw [content]
    rw [←Finset.gcd_mul_left]
    refine' congr (congr rfl _) _ <;> ext <;> simp [h0, mem_support_iff]

@[simp]
theorem content_monomial {r : R} {k : ℕ} : content (monomial k r) = normalize r :=
  by 
    rw [monomial_eq_C_mul_X, content_C_mul, content_X_pow, mul_oneₓ]

theorem content_eq_zero_iff {p : Polynomial R} : content p = 0 ↔ p = 0 :=
  by 
    rw [content, Finset.gcd_eq_zero_iff]
    split  <;> intro h
    ·
      ext n 
      byCases' h0 : n ∈ p.support
      ·
        rw [h n h0, coeff_zero]
      ·
        rw [mem_support_iff] at h0 
        pushNeg  at h0 
        simp [h0]
    ·
      intro x h0 
      simp [h]

@[simp]
theorem normalize_content {p : Polynomial R} : normalize p.content = p.content :=
  Finset.normalize_gcd

theorem content_eq_gcd_range_of_lt (p : Polynomial R) (n : ℕ) (h : p.nat_degree < n) :
  p.content = (Finset.range n).gcd p.coeff :=
  by 
    apply dvd_antisymm_of_normalize_eq normalize_content Finset.normalize_gcd
    ·
      rw [Finset.dvd_gcd_iff]
      intro i hi 
      apply content_dvd_coeff _
    ·
      apply Finset.gcd_mono 
      intro i 
      simp only [Nat.lt_succ_iff, mem_support_iff, Ne.def, Finset.mem_range]
      contrapose! 
      intro h1 
      apply coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_leₓ h h1)

theorem content_eq_gcd_range_succ (p : Polynomial R) : p.content = (Finset.range p.nat_degree.succ).gcd p.coeff :=
  content_eq_gcd_range_of_lt _ _ (Nat.lt_succ_selfₓ _)

theorem content_eq_gcd_leading_coeff_content_erase_lead (p : Polynomial R) :
  p.content = GcdMonoid.gcd p.leading_coeff (erase_lead p).content :=
  by 
    byCases' h : p = 0
    ·
      simp [h]
    rw [←leading_coeff_eq_zero, leading_coeff, ←Ne.def, ←mem_support_iff] at h 
    rw [content, ←Finset.insert_erase h, Finset.gcd_insert, leading_coeff, content, erase_lead_support]
    refine' congr rfl (Finset.gcd_congr rfl fun i hi => _)
    rw [Finset.mem_erase] at hi 
    rw [erase_lead_coeff, if_neg hi.1]

theorem dvd_content_iff_C_dvd {p : Polynomial R} {r : R} : r ∣ p.content ↔ C r ∣ p :=
  by 
    rw [C_dvd_iff_dvd_coeff]
    split 
    ·
      intro h i 
      apply h.trans (content_dvd_coeff _)
    ·
      intro h 
      rw [content, Finset.dvd_gcd_iff]
      intro i hi 
      apply h i

theorem C_content_dvd (p : Polynomial R) : C p.content ∣ p :=
  dvd_content_iff_C_dvd.1 dvd_rfl

theorem is_primitive_iff_content_eq_one {p : Polynomial R} : p.is_primitive ↔ p.content = 1 :=
  by 
    rw [←normalize_content, normalize_eq_one, is_primitive]
    simpRw [←dvd_content_iff_C_dvd]
    exact ⟨fun h => h p.content (dvd_refl p.content), fun h r hdvd => is_unit_of_dvd_unit hdvd h⟩

theorem is_primitive.content_eq_one {p : Polynomial R} (hp : p.is_primitive) : p.content = 1 :=
  is_primitive_iff_content_eq_one.mp hp

open_locale Classical

noncomputable theory

section PrimPart

/-- The primitive part of a polynomial `p` is the primitive polynomial gained by dividing `p` by
  `p.content`. If `p = 0`, then `p.prim_part = 1`.  -/
def prim_part (p : Polynomial R) : Polynomial R :=
  if p = 0 then 1 else Classical.some (C_content_dvd p)

theorem eq_C_content_mul_prim_part (p : Polynomial R) : p = C p.content*p.prim_part :=
  by 
    byCases' h : p = 0
    ·
      simp [h]
    rw [prim_part, if_neg h, ←Classical.some_spec (C_content_dvd p)]

@[simp]
theorem prim_part_zero : prim_part (0 : Polynomial R) = 1 :=
  if_pos rfl

theorem is_primitive_prim_part (p : Polynomial R) : p.prim_part.is_primitive :=
  by 
    byCases' h : p = 0
    ·
      simp [h]
    rw [←content_eq_zero_iff] at h 
    rw [is_primitive_iff_content_eq_one]
    apply mul_left_cancel₀ h 
    convRHS => rw [p.eq_C_content_mul_prim_part, mul_oneₓ, content_C_mul, normalize_content]

theorem content_prim_part (p : Polynomial R) : p.prim_part.content = 1 :=
  p.is_primitive_prim_part.content_eq_one

theorem prim_part_ne_zero (p : Polynomial R) : p.prim_part ≠ 0 :=
  p.is_primitive_prim_part.ne_zero

theorem nat_degree_prim_part (p : Polynomial R) : p.prim_part.nat_degree = p.nat_degree :=
  by 
    byCases' h : C p.content = 0
    ·
      rw [C_eq_zero, content_eq_zero_iff] at h 
      simp [h]
    convRHS => rw [p.eq_C_content_mul_prim_part, nat_degree_mul h p.prim_part_ne_zero, nat_degree_C, zero_addₓ]

@[simp]
theorem is_primitive.prim_part_eq {p : Polynomial R} (hp : p.is_primitive) : p.prim_part = p :=
  by 
    rw [←one_mulₓ p.prim_part, ←C_1, ←hp.content_eq_one, ←p.eq_C_content_mul_prim_part]

theorem is_unit_prim_part_C (r : R) : IsUnit (C r).primPart :=
  by 
    byCases' h0 : r = 0
    ·
      simp [h0]
    unfold IsUnit 
    refine'
      ⟨⟨C («expr↑ » (norm_unit r⁻¹)), C («expr↑ » (norm_unit r)),
          by 
            rw [←RingHom.map_mul, Units.inv_mul, C_1],
          by 
            rw [←RingHom.map_mul, Units.mul_inv, C_1]⟩,
        _⟩
    rw [←normalize_eq_zero, ←C_eq_zero] at h0 
    apply mul_left_cancel₀ h0 
    convRHS => rw [←content_C, ←(C r).eq_C_content_mul_prim_part]
    simp only [Units.coe_mk, normalize_apply, RingHom.map_mul]
    rw [mul_assocₓ, ←RingHom.map_mul, Units.mul_inv, C_1, mul_oneₓ]

theorem prim_part_dvd (p : Polynomial R) : p.prim_part ∣ p :=
  Dvd.intro_left (C p.content) p.eq_C_content_mul_prim_part.symm

end PrimPart

theorem gcd_content_eq_of_dvd_sub {a : R} {p q : Polynomial R} (h : C a ∣ p - q) :
  GcdMonoid.gcd a p.content = GcdMonoid.gcd a q.content :=
  by 
    rw
      [content_eq_gcd_range_of_lt p (max p.nat_degree q.nat_degree).succ
        (lt_of_le_of_ltₓ (le_max_leftₓ _ _) (Nat.lt_succ_selfₓ _))]
    rw
      [content_eq_gcd_range_of_lt q (max p.nat_degree q.nat_degree).succ
        (lt_of_le_of_ltₓ (le_max_rightₓ _ _) (Nat.lt_succ_selfₓ _))]
    apply Finset.gcd_eq_of_dvd_sub 
    intro x hx 
    cases' h with w hw 
    use w.coeff x 
    rw [←coeff_sub, hw, coeff_C_mul]

theorem content_mul_aux {p q : Polynomial R} :
  GcdMonoid.gcd (p*q).eraseLead.content p.leading_coeff = GcdMonoid.gcd (p.erase_lead*q).content p.leading_coeff :=
  by 
    rw [gcd_comm (content _) _, gcd_comm (content _) _]
    apply gcd_content_eq_of_dvd_sub 
    rw [←self_sub_C_mul_X_pow, ←self_sub_C_mul_X_pow, sub_mul, sub_sub, add_commₓ, sub_add, sub_sub_cancel,
      leading_coeff_mul, RingHom.map_mul, mul_assocₓ, mul_assocₓ]
    apply dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)

@[simp]
theorem content_mul {p q : Polynomial R} : (p*q).content = p.content*q.content :=
  by 
    classical 
    suffices h : ∀ (n : ℕ) (p q : Polynomial R), (p*q).degree < n → (p*q).content = p.content*q.content
    ·
      apply h 
      apply lt_of_le_of_ltₓ degree_le_nat_degree (WithBot.coe_lt_coe.2 (Nat.lt_succ_selfₓ _))
    intro n 
    induction' n with n ih
    ·
      intro p q hpq 
      rw [WithBot.coe_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot, mul_eq_zero] at hpq 
      rcases hpq with (rfl | rfl) <;> simp 
    intro p q hpq 
    byCases' p0 : p = 0
    ·
      simp [p0]
    byCases' q0 : q = 0
    ·
      simp [q0]
    rw [degree_eq_nat_degree (mul_ne_zero p0 q0), WithBot.coe_lt_coe, Nat.lt_succ_iff_lt_or_eq, ←WithBot.coe_lt_coe,
      ←degree_eq_nat_degree (mul_ne_zero p0 q0), nat_degree_mul p0 q0] at hpq 
    rcases hpq with (hlt | heq)
    ·
      apply ih _ _ hlt 
    rw [←p.nat_degree_prim_part, ←q.nat_degree_prim_part, ←WithBot.coe_eq_coe, WithBot.coe_add,
      ←degree_eq_nat_degree p.prim_part_ne_zero, ←degree_eq_nat_degree q.prim_part_ne_zero] at heq 
    rw [p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part]
    suffices h : (q.prim_part*p.prim_part).content = 1
    ·
      rw [mul_assocₓ, content_C_mul, content_C_mul, mul_commₓ p.prim_part, mul_assocₓ, content_C_mul, content_C_mul, h,
        mul_oneₓ, content_prim_part, content_prim_part, mul_oneₓ, mul_oneₓ]
    rw [←normalize_content, normalize_eq_one, is_unit_iff_dvd_one, content_eq_gcd_leading_coeff_content_erase_lead,
      leading_coeff_mul, gcd_comm]
    apply (gcd_mul_dvd_mul_gcd _ _ _).trans 
    rw [content_mul_aux, ih, content_prim_part, mul_oneₓ, gcd_comm, ←content_eq_gcd_leading_coeff_content_erase_lead,
      content_prim_part, one_mulₓ, mul_commₓ q.prim_part, content_mul_aux, ih, content_prim_part, mul_oneₓ, gcd_comm,
      ←content_eq_gcd_leading_coeff_content_erase_lead, content_prim_part]
    ·
      rw [←HEq, degree_mul, WithBot.add_lt_add_iff_right]
      ·
        apply degree_erase_lt p.prim_part_ne_zero
      ·
        rw [Ne.def, degree_eq_bot]
        apply q.prim_part_ne_zero
    ·
      rw [mul_commₓ, ←HEq, degree_mul, WithBot.add_lt_add_iff_left]
      ·
        apply degree_erase_lt q.prim_part_ne_zero
      ·
        rw [Ne.def, degree_eq_bot]
        apply p.prim_part_ne_zero

theorem is_primitive.mul {p q : Polynomial R} (hp : p.is_primitive) (hq : q.is_primitive) : (p*q).IsPrimitive :=
  by 
    rw [is_primitive_iff_content_eq_one, content_mul, hp.content_eq_one, hq.content_eq_one, mul_oneₓ]

@[simp]
theorem prim_part_mul {p q : Polynomial R} (h0 : (p*q) ≠ 0) : (p*q).primPart = p.prim_part*q.prim_part :=
  by 
    rw [Ne.def, ←content_eq_zero_iff, ←C_eq_zero] at h0 
    apply mul_left_cancel₀ h0 
    convLHS => rw [←(p*q).eq_C_content_mul_prim_part, p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part]
    rw [content_mul, RingHom.map_mul]
    ring

theorem is_primitive.is_primitive_of_dvd {p q : Polynomial R} (hp : p.is_primitive) (hdvd : q ∣ p) : q.is_primitive :=
  by 
    rcases hdvd with ⟨r, rfl⟩
    rw [is_primitive_iff_content_eq_one, ←normalize_content, normalize_eq_one, is_unit_iff_dvd_one]
    apply Dvd.intro r.content 
    rwa [is_primitive_iff_content_eq_one, content_mul] at hp

theorem is_primitive.dvd_prim_part_iff_dvd {p q : Polynomial R} (hp : p.is_primitive) (hq : q ≠ 0) :
  p ∣ q.prim_part ↔ p ∣ q :=
  by 
    refine' ⟨fun h => h.trans (Dvd.intro_left _ q.eq_C_content_mul_prim_part.symm), fun h => _⟩
    rcases h with ⟨r, rfl⟩
    apply Dvd.intro _ 
    rw [prim_part_mul hq, hp.prim_part_eq]

-- error in RingTheory.Polynomial.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_primitive_lcm_of_is_primitive
{p q : polynomial R}
(hp : p.is_primitive)
(hq : q.is_primitive) : «expr∃ , »((r : polynomial R), «expr ∧ »(r.is_primitive, ∀
  s : polynomial R, «expr ↔ »(«expr ∧ »(«expr ∣ »(p, s), «expr ∣ »(q, s)), «expr ∣ »(r, s)))) :=
begin
  classical,
  have [ident h] [":", expr «expr∃ , »((n : exprℕ())
    (r : polynomial R), «expr ∧ »(«expr = »(r.nat_degree, n), «expr ∧ »(r.is_primitive, «expr ∧ »(«expr ∣ »(p, r), «expr ∣ »(q, r)))))] [":=", expr ⟨«expr * »(p, q).nat_degree, «expr * »(p, q), rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩],
  rcases [expr nat.find_spec h, "with", "⟨", ident r, ",", ident rdeg, ",", ident rprim, ",", ident pr, ",", ident qr, "⟩"],
  refine [expr ⟨r, rprim, λ s, ⟨_, λ rs, ⟨pr.trans rs, qr.trans rs⟩⟩⟩],
  suffices [ident hs] [":", expr ∀
   (n : exprℕ())
   (s : polynomial R), «expr = »(s.nat_degree, n) → «expr ∧ »(«expr ∣ »(p, s), «expr ∣ »(q, s)) → «expr ∣ »(r, s)],
  { apply [expr hs s.nat_degree s rfl] },
  clear [ident s],
  by_contra [ident con],
  push_neg ["at", ident con],
  rcases [expr nat.find_spec con, "with", "⟨", ident s, ",", ident sdeg, ",", "⟨", ident ps, ",", ident qs, "⟩", ",", ident rs, "⟩"],
  have [ident s0] [":", expr «expr ≠ »(s, 0)] [],
  { contrapose ["!"] [ident rs],
    simp [] [] [] ["[", expr rs, "]"] [] [] },
  have [ident hs] [] [":=", expr nat.find_min' h ⟨_, s.nat_degree_prim_part, s.is_primitive_prim_part, (hp.dvd_prim_part_iff_dvd s0).2 ps, (hq.dvd_prim_part_iff_dvd s0).2 qs⟩],
  rw ["<-", expr rdeg] ["at", ident hs],
  by_cases [expr sC, ":", expr «expr ≤ »(s.nat_degree, 0)],
  { rw ["[", expr eq_C_of_nat_degree_le_zero (le_trans hs sC), ",", expr is_primitive_iff_content_eq_one, ",", expr content_C, ",", expr normalize_eq_one, "]"] ["at", ident rprim],
    rw ["[", expr eq_C_of_nat_degree_le_zero (le_trans hs sC), ",", "<-", expr dvd_content_iff_C_dvd, "]"] ["at", ident rs],
    apply [expr rs rprim.dvd] },
  have [ident hcancel] [] [":=", expr nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree hs (lt_of_not_ge sC)],
  rw [expr sdeg] ["at", ident hcancel],
  apply [expr nat.find_min con hcancel],
  refine [expr ⟨_, rfl, ⟨dvd_cancel_leads_of_dvd_of_dvd pr ps, dvd_cancel_leads_of_dvd_of_dvd qr qs⟩, λ rcs, rs _⟩],
  rw ["<-", expr rprim.dvd_prim_part_iff_dvd s0] [],
  rw ["[", expr cancel_leads, ",", expr tsub_eq_zero_iff_le.mpr hs, ",", expr pow_zero, ",", expr mul_one, "]"] ["at", ident rcs],
  have [ident h] [] [":=", expr dvd_add rcs (dvd.intro_left _ rfl)],
  have [ident hC0] [] [":=", expr rprim.ne_zero],
  rw ["[", expr ne.def, ",", "<-", expr leading_coeff_eq_zero, ",", "<-", expr C_eq_zero, "]"] ["at", ident hC0],
  rw ["[", expr sub_add_cancel, ",", "<-", expr rprim.dvd_prim_part_iff_dvd (mul_ne_zero hC0 s0), "]"] ["at", ident h],
  rcases [expr is_unit_prim_part_C r.leading_coeff, "with", "⟨", ident u, ",", ident hu, "⟩"],
  apply [expr h.trans (associated.symm ⟨u, _⟩).dvd],
  rw ["[", expr prim_part_mul (mul_ne_zero hC0 s0), ",", expr hu, ",", expr mul_comm, "]"] []
end

theorem dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part {p q : Polynomial R} (hq : q ≠ 0) :
  p ∣ q ↔ p.content ∣ q.content ∧ p.prim_part ∣ q.prim_part :=
  by 
    split  <;> intro h
    ·
      rcases h with ⟨r, rfl⟩
      rw [content_mul, p.is_primitive_prim_part.dvd_prim_part_iff_dvd hq]
      exact ⟨Dvd.intro _ rfl, p.prim_part_dvd.trans (Dvd.intro _ rfl)⟩
    ·
      rw [p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part]
      exact mul_dvd_mul (RingHom.map_dvd C h.1) h.2

instance (priority := 100)NormalizedGcdMonoid : NormalizedGcdMonoid (Polynomial R) :=
  normalizedGcdMonoidOfExistsLcm$
    fun p q =>
      by 
        rcases exists_primitive_lcm_of_is_primitive p.is_primitive_prim_part q.is_primitive_prim_part with
          ⟨r, rprim, hr⟩
        refine' ⟨C (lcm p.content q.content)*r, fun s => _⟩
        byCases' hs : s = 0
        ·
          simp [hs]
        byCases' hpq : C (lcm p.content q.content) = 0
        ·
          rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq 
          rcases hpq with (hpq | hpq) <;> simp [hpq, hs]
        iterate 3
          rw [dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part hs]
        rw [content_mul, rprim.content_eq_one, mul_oneₓ, content_C, normalize_lcm, lcm_dvd_iff,
          prim_part_mul (mul_ne_zero hpq rprim.ne_zero), rprim.prim_part_eq,
          IsUnit.mul_left_dvd _ _ _ (is_unit_prim_part_C (lcm p.content q.content)), ←hr s.prim_part]
        tauto

-- error in RingTheory.Polynomial.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_gcd_le_left {p : polynomial R} (hp : «expr ≠ »(p, 0)) (q) : «expr ≤ »((gcd p q).degree, p.degree) :=
begin
  by_cases [expr hq, ":", expr «expr = »(q, 0)],
  { simp [] [] [] ["[", expr hq, "]"] [] [] },
  have [] [] [":=", expr nat_degree_le_iff_degree_le.mp (nat_degree_le_of_dvd (gcd_dvd_left p q) hp)],
  rwa [expr degree_eq_nat_degree hp] []
end

theorem degree_gcd_le_right p {q : Polynomial R} (hq : q ≠ 0) : (gcd p q).degree ≤ q.degree :=
  by 
    rw [gcd_comm]
    exact degree_gcd_le_left hq p

end NormalizedGcdMonoid

end Polynomial

