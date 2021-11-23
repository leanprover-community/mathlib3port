import Mathbin.RingTheory.Int.Basic 
import Mathbin.RingTheory.Localization

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results
 - `polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial is irreducible iff it is irreducible in a fraction field.
 - `polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
 - `polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials divide each other iff they do in a fraction field.
 - `polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/


open_locale nonZeroDivisors

variable{R : Type _}[CommRingₓ R][IsDomain R]

namespace Polynomial

section NormalizedGcdMonoid

variable[NormalizedGcdMonoid R]

section 

variable{S : Type _}[CommRingₓ S][IsDomain S]{φ : R →+* S}(hinj : Function.Injective φ)

variable{f : Polynomial R}(hf : f.is_primitive)

include hinj hf

-- error in RingTheory.Polynomial.GaussLemma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_primitive.is_unit_iff_is_unit_map_of_injective : «expr ↔ »(is_unit f, is_unit (map φ f)) :=
begin
  refine [expr ⟨(map_ring_hom φ).is_unit_map, λ h, _⟩],
  rcases [expr is_unit_iff.1 h, "with", "⟨", "_", ",", "⟨", ident u, ",", ident rfl, "⟩", ",", ident hu, "⟩"],
  have [ident hdeg] [] [":=", expr degree_C u.ne_zero],
  rw ["[", expr hu, ",", expr degree_map' hinj, "]"] ["at", ident hdeg],
  rw ["[", expr eq_C_of_degree_eq_zero hdeg, ",", expr is_primitive_iff_content_eq_one, ",", expr content_C, ",", expr normalize_eq_one, "]"] ["at", ident hf],
  rwa ["[", expr eq_C_of_degree_eq_zero hdeg, ",", expr is_unit_C, "]"] []
end

theorem is_primitive.irreducible_of_irreducible_map_of_injective (h_irr : Irreducible (map φ f)) : Irreducible f :=
  by 
    refine' ⟨fun h => h_irr.not_unit (IsUnit.map (map_ring_hom φ).toMonoidHom h), _⟩
    intro a b h 
    rcases
      h_irr.is_unit_or_is_unit
        (by 
          rw [h, map_mul]) with
      (hu | hu)
    ·
      left 
      rwa [(hf.is_primitive_of_dvd (Dvd.intro _ h.symm)).is_unit_iff_is_unit_map_of_injective hinj]
    right 
    rwa [(hf.is_primitive_of_dvd (Dvd.intro_left _ h.symm)).is_unit_iff_is_unit_map_of_injective hinj]

end 

section FractionMap

variable{K : Type _}[Field K][Algebra R K][IsFractionRing R K]

theorem is_primitive.is_unit_iff_is_unit_map {p : Polynomial R} (hp : p.is_primitive) :
  IsUnit p ↔ IsUnit (p.map (algebraMap R K)) :=
  hp.is_unit_iff_is_unit_map_of_injective (IsFractionRing.injective _ _)

open IsLocalization

theorem is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part {p : Polynomial K} (h0 : p ≠ 0)
  (h : IsUnit (integer_normalization R⁰ p).primPart) : IsUnit p :=
  by 
    rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
    obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ p 
    rw [Subtype.coe_mk, Algebra.smul_def, algebra_map_apply] at hc 
    apply is_unit_of_mul_is_unit_right 
    rw [←hc, (integer_normalization R⁰ p).eq_C_content_mul_prim_part, ←hu, ←RingHom.map_mul, is_unit_iff]
    refine'
      ⟨algebraMap R K ((integer_normalization R⁰ p).content*«expr↑ » u), is_unit_iff_ne_zero.2 fun con => _,
        by 
          simp ⟩
    replace con := (algebraMap R K).injective_iff.1 (IsFractionRing.injective _ _) _ Con 
    rw [mul_eq_zero, content_eq_zero_iff, IsFractionRing.integer_normalization_eq_zero_iff] at con 
    rcases Con with (con | con)
    ·
      apply h0 Con
    ·
      apply Units.ne_zero _ Con

-- error in RingTheory.Polynomial.GaussLemma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Gauss's Lemma** states that a primitive polynomial is irreducible iff it is irreducible in the
  fraction field. -/
theorem is_primitive.irreducible_iff_irreducible_map_fraction_map
{p : polynomial R}
(hp : p.is_primitive) : «expr ↔ »(irreducible p, irreducible (p.map (algebra_map R K))) :=
begin
  refine [expr ⟨λ
    hi, ⟨λ
     h, hi.not_unit (hp.is_unit_iff_is_unit_map.2 h), λ
     a b hab, _⟩, hp.irreducible_of_irreducible_map_of_injective (is_fraction_ring.injective _ _)⟩],
  obtain ["⟨", "⟨", ident c, ",", ident c0, "⟩", ",", ident hc, "⟩", ":=", expr integer_normalization_map_to_map «expr ⁰»(R) a],
  obtain ["⟨", "⟨", ident d, ",", ident d0, "⟩", ",", ident hd, "⟩", ":=", expr integer_normalization_map_to_map «expr ⁰»(R) b],
  rw ["[", expr algebra.smul_def, ",", expr algebra_map_apply, ",", expr subtype.coe_mk, "]"] ["at", ident hc, ident hd],
  rw [expr mem_non_zero_divisors_iff_ne_zero] ["at", ident c0, ident d0],
  have [ident hcd0] [":", expr «expr ≠ »(«expr * »(c, d), 0)] [":=", expr mul_ne_zero c0 d0],
  rw ["[", expr ne.def, ",", "<-", expr C_eq_zero, "]"] ["at", ident hcd0],
  have [ident h1] [":", expr «expr = »(«expr * »(«expr * »(C c, C d), p), «expr * »(integer_normalization «expr ⁰»(R) a, integer_normalization «expr ⁰»(R) b))] [],
  { apply [expr map_injective (algebra_map R K) (is_fraction_ring.injective _ _) _],
    rw ["[", expr map_mul, ",", expr map_mul, ",", expr map_mul, ",", expr hc, ",", expr hd, ",", expr map_C, ",", expr map_C, ",", expr hab, "]"] [],
    ring [] },
  obtain ["⟨", ident u, ",", ident hu, "⟩", ":", expr associated «expr * »(c, d) «expr * »(content (integer_normalization «expr ⁰»(R) a), content (integer_normalization «expr ⁰»(R) b))],
  { rw ["[", "<-", expr dvd_dvd_iff_associated, ",", "<-", expr normalize_eq_normalize_iff, ",", expr normalize.map_mul, ",", expr normalize.map_mul, ",", expr normalize_content, ",", expr normalize_content, ",", "<-", expr mul_one «expr * »(normalize c, normalize d), ",", "<-", expr hp.content_eq_one, ",", "<-", expr content_C, ",", "<-", expr content_C, ",", "<-", expr content_mul, ",", "<-", expr content_mul, ",", "<-", expr content_mul, ",", expr h1, "]"] [] },
  rw ["[", "<-", expr ring_hom.map_mul, ",", expr eq_comm, ",", expr (integer_normalization «expr ⁰»(R) a).eq_C_content_mul_prim_part, ",", expr (integer_normalization «expr ⁰»(R) b).eq_C_content_mul_prim_part, ",", expr mul_assoc, ",", expr mul_comm _ «expr * »(C _, _), ",", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, ",", "<-", expr ring_hom.map_mul, ",", "<-", expr hu, ",", expr ring_hom.map_mul, ",", expr mul_assoc, ",", expr mul_assoc, ",", "<-", expr mul_assoc (C «expr↑ »(u)), "]"] ["at", ident h1],
  have [ident h0] [":", expr «expr ∧ »(«expr ≠ »(a, 0), «expr ≠ »(b, 0))] [],
  { classical,
    rw ["[", expr ne.def, ",", expr ne.def, ",", "<-", expr decidable.not_or_iff_and_not, ",", "<-", expr mul_eq_zero, ",", "<-", expr hab, "]"] [],
    intro [ident con],
    apply [expr hp.ne_zero (map_injective (algebra_map R K) (is_fraction_ring.injective _ _) _)],
    simp [] [] [] ["[", expr con, "]"] [] [] },
  rcases [expr hi.is_unit_or_is_unit (mul_left_cancel₀ hcd0 h1).symm, "with", ident h, "|", ident h],
  { right,
    apply [expr is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.2 (is_unit_of_mul_is_unit_right h)] },
  { left,
    apply [expr is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.1 h] }
end

-- error in RingTheory.Polynomial.GaussLemma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_primitive.dvd_of_fraction_map_dvd_fraction_map
{p q : polynomial R}
(hp : p.is_primitive)
(hq : q.is_primitive)
(h_dvd : «expr ∣ »(p.map (algebra_map R K), q.map (algebra_map R K))) : «expr ∣ »(p, q) :=
begin
  rcases [expr h_dvd, "with", "⟨", ident r, ",", ident hr, "⟩"],
  obtain ["⟨", "⟨", ident s, ",", ident s0, "⟩", ",", ident hs, "⟩", ":=", expr integer_normalization_map_to_map «expr ⁰»(R) r],
  rw ["[", expr subtype.coe_mk, ",", expr algebra.smul_def, ",", expr algebra_map_apply, "]"] ["at", ident hs],
  have [ident h] [":", expr «expr ∣ »(p, «expr * »(q, C s))] [],
  { use [expr integer_normalization «expr ⁰»(R) r],
    apply [expr map_injective (algebra_map R K) (is_fraction_ring.injective _ _)],
    rw ["[", expr map_mul, ",", expr map_mul, ",", expr hs, ",", expr hr, ",", expr mul_assoc, ",", expr mul_comm r, "]"] [],
    simp [] [] [] [] [] [] },
  rw ["[", "<-", expr hp.dvd_prim_part_iff_dvd, ",", expr prim_part_mul, ",", expr hq.prim_part_eq, ",", expr associated.dvd_iff_dvd_right, "]"] ["at", ident h],
  { exact [expr h] },
  { symmetry,
    rcases [expr is_unit_prim_part_C s, "with", "⟨", ident u, ",", ident hu, "⟩"],
    use [expr u],
    rw [expr hu] [] },
  iterate [2] { apply [expr mul_ne_zero hq.ne_zero],
    rw ["[", expr ne.def, ",", expr C_eq_zero, "]"] [],
    contrapose ["!"] [ident s0],
    simp [] [] [] ["[", expr s0, ",", expr mem_non_zero_divisors_iff_ne_zero, "]"] [] [] }
end

variable(K)

theorem is_primitive.dvd_iff_fraction_map_dvd_fraction_map {p q : Polynomial R} (hp : p.is_primitive)
  (hq : q.is_primitive) : p ∣ q ↔ p.map (algebraMap R K) ∣ q.map (algebraMap R K) :=
  ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ map_mul (algebraMap R K)⟩,
    fun h => hp.dvd_of_fraction_map_dvd_fraction_map hq h⟩

end FractionMap

/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem is_primitive.int.irreducible_iff_irreducible_map_cast {p : Polynomial ℤ} (hp : p.is_primitive) :
  Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  hp.irreducible_iff_irreducible_map_fraction_map

theorem is_primitive.int.dvd_iff_map_cast_dvd_map_cast (p q : Polynomial ℤ) (hp : p.is_primitive)
  (hq : q.is_primitive) : p ∣ q ↔ p.map (Int.castRingHom ℚ) ∣ q.map (Int.castRingHom ℚ) :=
  hp.dvd_iff_fraction_map_dvd_fraction_map ℚ hq

end NormalizedGcdMonoid

end Polynomial

