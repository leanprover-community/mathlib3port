import Mathbin.Algebra.Algebra.Basic 
import Mathbin.Algebra.CharP.ExpChar 
import Mathbin.FieldTheory.Separable

/-!

# Separable degree

This file contains basics about the separable degree of a polynomial.

## Main results

- `is_separable_contraction`: is the condition that `g(x^(q^m)) = f(x)` for some `m : ℕ`
- `has_separable_contraction`: the condition of having a separable contraction
- `has_separable_contraction.degree`: the separable degree, defined as the degree of some
  separable contraction
- `irreducible_has_separable_contraction`: any irreducible polynomial can be contracted
  to a separable polynomial
- `has_separable_contraction.dvd_degree'`: the degree of a separable contraction divides the degree,
  in function of the exponential characteristic of the field
- `has_separable_contraction.dvd_degree` and `has_separable_contraction.eq_degree` specialize the
  statement of `separable_degree_dvd_degree`
- `is_separable_contraction.degree_eq`: the separable degree is well-defined, implemented as the
  statement that the degree of any separable contraction equals `has_separable_contraction.degree`

## Tags

separable degree, degree, polynomial
-/


namespace Polynomial

noncomputable theory

open_locale Classical

section CommSemiringₓ

variable {F : Type} [CommSemiringₓ F] (q : ℕ)

/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
def is_separable_contraction (f : Polynomial F) (g : Polynomial F) : Prop :=
  g.separable ∧ ∃ m : ℕ, expand F (q^m) g = f

/-- The condition of having a separable contration. -/
def has_separable_contraction (f : Polynomial F) : Prop :=
  ∃ g : Polynomial F, is_separable_contraction q f g

variable {q} {f : Polynomial F} (hf : has_separable_contraction q f)

/-- A choice of a separable contraction. -/
def has_separable_contraction.contraction : Polynomial F :=
  Classical.some hf

/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
def has_separable_contraction.degree : ℕ :=
  hf.contraction.nat_degree

/-- The separable degree divides the degree, in function of the exponential characteristic of F. -/
theorem is_separable_contraction.dvd_degree' {g} (hf : is_separable_contraction q f g) :
  ∃ m : ℕ, (g.nat_degree*q^m) = f.nat_degree :=
  by 
    obtain ⟨m, rfl⟩ := hf.2
    use m 
    rw [nat_degree_expand]

theorem has_separable_contraction.dvd_degree' : ∃ m : ℕ, (hf.degree*q^m) = f.nat_degree :=
  (Classical.some_spec hf).dvd_degree'

/-- The separable degree divides the degree. -/
theorem has_separable_contraction.dvd_degree : hf.degree ∣ f.nat_degree :=
  let ⟨a, ha⟩ := hf.dvd_degree' 
  Dvd.intro (q^a) ha

/-- In exponential characteristic one, the separable degree equals the degree. -/
theorem has_separable_contraction.eq_degree {f : Polynomial F} (hf : has_separable_contraction 1 f) :
  hf.degree = f.nat_degree :=
  let ⟨a, ha⟩ := hf.dvd_degree' 
  by 
    rw [←ha, one_pow a, mul_oneₓ]

end CommSemiringₓ

section Field

variable {F : Type} [Field F]

variable (q : ℕ) {f : Polynomial F} (hf : has_separable_contraction q f)

/-- Every irreducible polynomial can be contracted to a separable polynomial.
https://stacks.math.columbia.edu/tag/09H0 -/
theorem irreducible_has_separable_contraction (q : ℕ) [hF : ExpChar F q] (f : Polynomial F) [irred : Irreducible f] :
  has_separable_contraction q f :=
  by 
    cases' hF
    ·
      exact
        ⟨f, irred.separable,
          ⟨0,
            by 
              rw [pow_zeroₓ, expand_one]⟩⟩
    ·
      rcases exists_separable_of_irreducible q irred ‹q.prime›.ne_zero with ⟨n, g, hgs, hge⟩
      exact ⟨g, hgs, n, hge⟩

-- error in FieldTheory.SeparableDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A helper lemma: if two expansions (along the positive characteristic) of two polynomials `g` and
`g'` agree, and the one with the larger degree is separable, then their degrees are the same. -/
theorem contraction_degree_eq_aux
[hq : fact q.prime]
[hF : char_p F q]
(g g' : polynomial F)
(m m' : exprℕ())
(h_expand : «expr = »(expand F «expr ^ »(q, m) g, expand F «expr ^ »(q, m') g'))
(h : «expr < »(m, m'))
(hg : g.separable) : «expr = »(g.nat_degree, g'.nat_degree) :=
begin
  obtain ["⟨", ident s, ",", ident rfl, "⟩", ":=", expr nat.exists_eq_add_of_lt h],
  rw ["[", expr add_assoc, ",", expr pow_add, ",", expr expand_mul, "]"] ["at", ident h_expand],
  let [ident aux] [] [":=", expr expand_injective (pow_pos hq.1.pos m) h_expand],
  rw [expr aux] ["at", ident hg],
  have [] [] [":=", expr (is_unit_or_eq_zero_of_separable_expand q «expr + »(s, 1) hq.out.pos hg).resolve_right s.succ_ne_zero],
  rw ["[", expr aux, ",", expr nat_degree_expand, ",", expr nat_degree_eq_of_degree_eq_some (degree_eq_zero_of_is_unit this), ",", expr zero_mul, "]"] []
end

-- error in FieldTheory.SeparableDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two expansions (along the positive characteristic) of two separable polynomials
`g` and `g'` agree, then they have the same degree. -/
theorem contraction_degree_eq_or_insep
[hq : fact q.prime]
[char_p F q]
(g g' : polynomial F)
(m m' : exprℕ())
(h_expand : «expr = »(expand F «expr ^ »(q, m) g, expand F «expr ^ »(q, m') g'))
(hg : g.separable)
(hg' : g'.separable) : «expr = »(g.nat_degree, g'.nat_degree) :=
begin
  by_cases [expr h, ":", expr «expr = »(m, m')],
  { rw [expr h] ["at", ident h_expand],
    have [ident expand_deg] [":", expr «expr = »((expand F «expr ^ »(q, m') g).nat_degree, (expand F «expr ^ »(q, m') g').nat_degree)] [],
    by rw [expr h_expand] [],
    rw ["[", expr nat_degree_expand «expr ^ »(q, m') g, ",", expr nat_degree_expand «expr ^ »(q, m') g', "]"] ["at", ident expand_deg],
    apply [expr nat.eq_of_mul_eq_mul_left (pow_pos hq.1.pos m')],
    rw ["[", expr mul_comm, "]"] ["at", ident expand_deg],
    rw [expr expand_deg] [],
    rw ["[", expr mul_comm, "]"] [] },
  { cases [expr ne.lt_or_lt h] [],
    { exact [expr contraction_degree_eq_aux q g g' m m' h_expand h_1 hg] },
    { exact [expr (contraction_degree_eq_aux q g' g m' m h_expand.symm h_1 hg').symm] } }
end

-- error in FieldTheory.SeparableDegree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The separable degree equals the degree of any separable contraction, i.e., it is unique. -/
theorem is_separable_contraction.degree_eq
[hF : exp_char F q]
(g : polynomial F)
(hg : is_separable_contraction q f g) : «expr = »(g.nat_degree, hf.degree) :=
begin
  casesI [expr hF] [],
  { rcases [expr hg, "with", "⟨", ident g, ",", ident m, ",", ident hm, "⟩"],
    rw ["[", expr one_pow, ",", expr expand_one, "]"] ["at", ident hm],
    rw [expr hf.eq_degree] [],
    rw [expr hm] [] },
  { rcases [expr hg, "with", "⟨", ident hg, ",", ident m, ",", ident hm, "⟩"],
    let [ident g'] [] [":=", expr classical.some hf],
    cases [expr (classical.some_spec hf).2] ["with", ident m', ident hm'],
    haveI [] [":", expr fact q.prime] [":=", expr fact_iff.2 hF_hprime],
    apply [expr contraction_degree_eq_or_insep q g g' m m'],
    rw ["[", expr hm, ",", expr hm', "]"] [],
    exact [expr hg],
    exact [expr (classical.some_spec hf).1] }
end

end Field

end Polynomial

