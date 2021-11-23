import Mathbin.Algebra.GcdMonoid.Basic 
import Mathbin.RingTheory.Coprime.Basic 
import Mathbin.RingTheory.Ideal.Basic

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/


noncomputable theory

open_locale Classical

open EuclideanDomain Set Ideal

section GcdMonoid

variable{R : Type _}[EuclideanDomain R][GcdMonoid R]

open GcdMonoid

theorem left_div_gcd_ne_zero {p q : R} (hp : p ≠ 0) : p / GcdMonoid.gcd p q ≠ 0 :=
  by 
    obtain ⟨r, hr⟩ := GcdMonoid.gcd_dvd_left p q 
    obtain ⟨pq0, r0⟩ : GcdMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hp)
    rw [hr, mul_commₓ, mul_div_cancel _ pq0]
    exact r0

theorem right_div_gcd_ne_zero {p q : R} (hq : q ≠ 0) : q / GcdMonoid.gcd p q ≠ 0 :=
  by 
    obtain ⟨r, hr⟩ := GcdMonoid.gcd_dvd_right p q 
    obtain ⟨pq0, r0⟩ : GcdMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hq)
    rw [hr, mul_commₓ, mul_div_cancel _ pq0]
    exact r0

end GcdMonoid

variable{α : Type _}[EuclideanDomain α][DecidableEq α]

-- error in RingTheory.EuclideanDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem span_gcd {α} [euclidean_domain α] (x y : α) : «expr = »(span ({gcd x y} : set α), span ({x, y} : set α)) :=
begin
  apply [expr le_antisymm],
  { refine [expr span_le.2 (λ x, _)],
    simp [] [] ["only"] ["[", expr set.mem_singleton_iff, ",", expr set_like.mem_coe, ",", expr mem_span_pair, "]"] [] [],
    rintro [ident rfl],
    exact [expr ⟨gcd_a x y, gcd_b x y, by simp [] [] [] ["[", expr gcd_eq_gcd_ab, ",", expr mul_comm, "]"] [] []⟩] },
  { assume [binders (z)],
    simp [] [] [] ["[", expr mem_span_singleton, ",", expr euclidean_domain.gcd_dvd_left, ",", expr mem_span_pair, ",", expr @eq_comm _ _ z, "]"] [] [] { contextual := tt },
    exact [expr λ a b _, dvd_add ((gcd_dvd_left x y).mul_left _) ((gcd_dvd_right x y).mul_left _)] }
end

theorem gcd_is_unit_iff {α} [EuclideanDomain α] {x y : α} : IsUnit (gcd x y) ↔ IsCoprime x y :=
  ⟨fun h =>
      let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 h
      ⟨b*gcd_a x y, b*gcd_b x y,
        by 
          rw [←hb, gcd_eq_gcd_ab, mul_commₓ x, mul_commₓ y, mul_addₓ, mul_assocₓ, mul_assocₓ]⟩,
    fun ⟨a, b, h⟩ =>
      is_unit_iff_dvd_one.2$ h ▸ dvd_add ((gcd_dvd_left x y).mul_left _) ((gcd_dvd_right x y).mul_left _)⟩

theorem is_coprime_of_dvd {α} [EuclideanDomain α] {x y : α} (z : ¬(x = 0 ∧ y = 0))
  (H : ∀ z _ : z ∈ Nonunits α, z ≠ 0 → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  by 
    rw [←gcd_is_unit_iff]
    byContra h 
    refine' H _ h _ (gcd_dvd_left _ _) (gcd_dvd_right _ _)
    rwa [Ne, EuclideanDomain.gcd_eq_zero_iff]

theorem dvd_or_coprime {α} [EuclideanDomain α] (x y : α) (h : Irreducible x) : x ∣ y ∨ IsCoprime x y :=
  by 
    refine' or_iff_not_imp_left.2 fun h' => _ 
    apply is_coprime_of_dvd
    ·
      (
        rintro ⟨rfl, rfl⟩)
      simpa using h
    ·
      (
        rintro z nu nz ⟨w, rfl⟩ dy)
      refine' h' (dvd_trans _ dy)
      simpa using mul_dvd_mul_left z (is_unit_iff_dvd_one.1$ (of_irreducible_mul h).resolve_left nu)

