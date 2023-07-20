/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.CharP.ExpChar
import Mathbin.FieldTheory.Separable

#align_import field_theory.separable_degree from "leanprover-community/mathlib"@"a87d22575d946e1e156fc1edd1e1269600a8a282"

/-!

# Separable degree

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains basics about the separable degree of a polynomial.

## Main results

- `is_separable_contraction`: is the condition that, for `g` a separable polynomial, we have that
   `g(x^(q^m)) = f(x)` for some `m : ℕ`.
- `has_separable_contraction`: the condition of having a separable contraction
- `has_separable_contraction.degree`: the separable degree, defined as the degree of some
  separable contraction
- `irreducible.has_separable_contraction`: any irreducible polynomial can be contracted
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

noncomputable section

open scoped Classical Polynomial

section CommSemiring

variable {F : Type _} [CommSemiring F] (q : ℕ)

#print Polynomial.IsSeparableContraction /-
/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
def IsSeparableContraction (f : F[X]) (g : F[X]) : Prop :=
  g.Separable ∧ ∃ m : ℕ, expand F (q ^ m) g = f
#align polynomial.is_separable_contraction Polynomial.IsSeparableContraction
-/

#print Polynomial.HasSeparableContraction /-
/-- The condition of having a separable contration. -/
def HasSeparableContraction (f : F[X]) : Prop :=
  ∃ g : F[X], IsSeparableContraction q f g
#align polynomial.has_separable_contraction Polynomial.HasSeparableContraction
-/

variable {q} {f : F[X]} (hf : HasSeparableContraction q f)

#print Polynomial.HasSeparableContraction.contraction /-
/-- A choice of a separable contraction. -/
def HasSeparableContraction.contraction : F[X] :=
  Classical.choose hf
#align polynomial.has_separable_contraction.contraction Polynomial.HasSeparableContraction.contraction
-/

#print Polynomial.HasSeparableContraction.degree /-
/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
def HasSeparableContraction.degree : ℕ :=
  hf.contraction.natDegree
#align polynomial.has_separable_contraction.degree Polynomial.HasSeparableContraction.degree
-/

#print Polynomial.IsSeparableContraction.dvd_degree' /-
/-- The separable degree divides the degree, in function of the exponential characteristic of F. -/
theorem IsSeparableContraction.dvd_degree' {g} (hf : IsSeparableContraction q f g) :
    ∃ m : ℕ, g.natDegree * q ^ m = f.natDegree :=
  by
  obtain ⟨m, rfl⟩ := hf.2
  use m
  rw [nat_degree_expand]
#align polynomial.is_separable_contraction.dvd_degree' Polynomial.IsSeparableContraction.dvd_degree'
-/

#print Polynomial.HasSeparableContraction.dvd_degree' /-
theorem HasSeparableContraction.dvd_degree' : ∃ m : ℕ, hf.degree * q ^ m = f.natDegree :=
  (Classical.choose_spec hf).dvd_degree'
#align polynomial.has_separable_contraction.dvd_degree' Polynomial.HasSeparableContraction.dvd_degree'
-/

#print Polynomial.HasSeparableContraction.dvd_degree /-
/-- The separable degree divides the degree. -/
theorem HasSeparableContraction.dvd_degree : hf.degree ∣ f.natDegree :=
  let ⟨a, ha⟩ := hf.dvd_degree'
  Dvd.intro (q ^ a) ha
#align polynomial.has_separable_contraction.dvd_degree Polynomial.HasSeparableContraction.dvd_degree
-/

#print Polynomial.HasSeparableContraction.eq_degree /-
/-- In exponential characteristic one, the separable degree equals the degree. -/
theorem HasSeparableContraction.eq_degree {f : F[X]} (hf : HasSeparableContraction 1 f) :
    hf.degree = f.natDegree := by
  let ⟨a, ha⟩ := hf.dvd_degree'
  rw [← ha, one_pow a, mul_one]
#align polynomial.has_separable_contraction.eq_degree Polynomial.HasSeparableContraction.eq_degree
-/

end CommSemiring

section Field

variable {F : Type _} [Field F]

variable (q : ℕ) {f : F[X]} (hf : HasSeparableContraction q f)

#print Polynomial.Irreducible.hasSeparableContraction /-
/-- Every irreducible polynomial can be contracted to a separable polynomial.
https://stacks.math.columbia.edu/tag/09H0 -/
theorem Polynomial.Irreducible.hasSeparableContraction (q : ℕ) [hF : ExpChar F q] (f : F[X])
    (irred : Irreducible f) : HasSeparableContraction q f :=
  by
  cases hF
  · exact ⟨f, irred.separable, ⟨0, by rw [pow_zero, expand_one]⟩⟩
  · rcases exists_separable_of_irreducible q irred ‹q.prime›.NeZero with ⟨n, g, hgs, hge⟩
    exact ⟨g, hgs, n, hge⟩
#align irreducible.has_separable_contraction Polynomial.Irreducible.hasSeparableContraction
-/

#print Polynomial.contraction_degree_eq_or_insep /-
/-- If two expansions (along the positive characteristic) of two separable polynomials `g` and `g'`
agree, then they have the same degree. -/
theorem contraction_degree_eq_or_insep [hq : NeZero q] [CharP F q] (g g' : F[X]) (m m' : ℕ)
    (h_expand : expand F (q ^ m) g = expand F (q ^ m') g') (hg : g.Separable) (hg' : g'.Separable) :
    g.natDegree = g'.natDegree := by
  wlog hm : m ≤ m'
  · exact (this g' g m' m h_expand.symm hg' hg (le_of_not_le hm)).symm
  obtain ⟨s, rfl⟩ := exists_add_of_le hm
  rw [pow_add, expand_mul, expand_inj (pow_pos (NeZero.pos q) m)] at h_expand 
  subst h_expand
  rcases is_unit_or_eq_zero_of_separable_expand q s (NeZero.pos q) hg with (h | rfl)
  · rw [nat_degree_expand, nat_degree_eq_zero_of_is_unit h, MulZeroClass.zero_mul]
  · rw [nat_degree_expand, pow_zero, mul_one]
#align polynomial.contraction_degree_eq_or_insep Polynomial.contraction_degree_eq_or_insep
-/

#print Polynomial.IsSeparableContraction.degree_eq /-
/-- The separable degree equals the degree of any separable contraction, i.e., it is unique. -/
theorem IsSeparableContraction.degree_eq [hF : ExpChar F q] (g : F[X])
    (hg : IsSeparableContraction q f g) : g.natDegree = hf.degree :=
  by
  cases hF
  · rcases hg with ⟨g, m, hm⟩
    rw [one_pow, expand_one] at hm 
    rw [hf.eq_degree]
    rw [hm]
  · rcases hg with ⟨hg, m, hm⟩
    let g' := Classical.choose hf
    cases' (Classical.choose_spec hf).2 with m' hm'
    haveI : Fact q.prime := fact_iff.2 hF_hprime
    apply contraction_degree_eq_or_insep q g g' m m'
    rw [hm, hm']
    exact hg; exact (Classical.choose_spec hf).1
#align polynomial.is_separable_contraction.degree_eq Polynomial.IsSeparableContraction.degree_eq
-/

end Field

end Polynomial

