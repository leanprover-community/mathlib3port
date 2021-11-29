import Mathbin.Data.Polynomial.AlgebraMap 
import Mathbin.Data.Polynomial.Monic

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`polynomial S` by the image of `ring_hom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
`map_alg`, where `map_alg : polynomial R →ₐ[R] polynomial S` is the only `R`-algebra map
that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semiring, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_lifts_ring`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/


open_locale Classical BigOperators

noncomputable theory

namespace Polynomial

universe u v w

section Semiringₓ

variable{R : Type u}[Semiringₓ R]{S : Type v}[Semiringₓ S]{f : R →+* S}

/-- We define the subsemiring of polynomials that lifts as the image of `ring_hom.of (map f)`. -/
def lifts (f : R →+* S) : Subsemiring (Polynomial S) :=
  RingHom.srange (map_ring_hom f)

theorem mem_lifts (p : Polynomial S) : p ∈ lifts f ↔ ∃ q : Polynomial R, map f q = p :=
  by 
    simp only [coe_map_ring_hom, lifts, RingHom.mem_srange]

theorem lifts_iff_set_range (p : Polynomial S) : p ∈ lifts f ↔ p ∈ Set.Range (map f) :=
  by 
    simp only [coe_map_ring_hom, lifts, Set.mem_range, RingHom.mem_srange]

theorem lifts_iff_ring_hom_srange (p : Polynomial S) : p ∈ lifts f ↔ p ∈ (map_ring_hom f).srange :=
  by 
    simp only [coe_map_ring_hom, lifts, Set.mem_range, RingHom.mem_srange]

theorem lifts_iff_coeff_lifts (p : Polynomial S) : p ∈ lifts f ↔ ∀ (n : ℕ), p.coeff n ∈ Set.Range f :=
  by 
    rw [lifts_iff_ring_hom_srange, mem_map_srange f]
    rfl

/--If `(r : R)`, then `C (f r)` lifts. -/
theorem C_mem_lifts (f : R →+* S) (r : R) : C (f r) ∈ lifts f :=
  ⟨C r,
    by 
      simp only [coe_map_ring_hom, map_C, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true, and_selfₓ]⟩

/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
theorem C'_mem_lifts {f : R →+* S} {s : S} (h : s ∈ Set.Range f) : C s ∈ lifts f :=
  by 
    obtain ⟨r, rfl⟩ := Set.mem_range.1 h 
    use C r 
    simp only [coe_map_ring_hom, map_C, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true, and_selfₓ]

/-- The polynomial `X` lifts. -/
theorem X_mem_lifts (f : R →+* S) : (X : Polynomial S) ∈ lifts f :=
  ⟨X,
    by 
      simp only [coe_map_ring_hom, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true, map_X, and_selfₓ]⟩

/-- The polynomial `X ^ n` lifts. -/
theorem X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (X ^ n : Polynomial S) ∈ lifts f :=
  ⟨X ^ n,
    by 
      simp only [coe_map_ring_hom, map_pow, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true, map_X, and_selfₓ]⟩

/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
theorem base_mul_mem_lifts {p : Polynomial S} (r : R) (hp : p ∈ lifts f) : (C (f r)*p) ∈ lifts f :=
  by 
    simp only [lifts, RingHom.mem_srange] at hp⊢
    obtain ⟨p₁, rfl⟩ := hp 
    use C r*p₁ 
    simp only [coe_map_ring_hom, map_C, map_mul]

/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
theorem monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ Set.Range f) : monomial n s ∈ lifts f :=
  by 
    obtain ⟨r, rfl⟩ := Set.mem_range.1 h 
    use monomial n r 
    simp only [coe_map_ring_hom, Set.mem_univ, map_monomial, Subsemiring.coe_top, eq_self_iff_true, and_selfₓ]

/-- If `p` lifts then `p.erase n` lifts. -/
theorem erase_mem_lifts {p : Polynomial S} (n : ℕ) (h : p ∈ lifts f) : p.erase n ∈ lifts f :=
  by 
    rw [lifts_iff_ring_hom_srange, mem_map_srange] at h⊢
    intro k 
    byCases' hk : k = n
    ·
      use 0
      simp only [hk, RingHom.map_zero, erase_same]
    obtain ⟨i, hi⟩ := h k 
    use i 
    simp only [hi, hk, erase_ne, Ne.def, not_false_iff]

section LiftDeg

-- error in Data.Polynomial.Lifts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem monomial_mem_lifts_and_degree_eq
{s : S}
{n : exprℕ()}
(hl : «expr ∈ »(monomial n s, lifts f)) : «expr∃ , »((q : polynomial R), «expr ∧ »(«expr = »(map f q, monomial n s), «expr = »(q.degree, (monomial n s).degree))) :=
begin
  by_cases [expr hzero, ":", expr «expr = »(s, 0)],
  { use [expr 0],
    simp [] [] ["only"] ["[", expr hzero, ",", expr degree_zero, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr monomial_zero_right, ",", expr map_zero, "]"] [] [] },
  rw [expr lifts_iff_set_range] ["at", ident hl],
  obtain ["⟨", ident q, ",", ident hq, "⟩", ":=", expr hl],
  replace [ident hq] [] [":=", expr ext_iff.1 hq n],
  have [ident hcoeff] [":", expr «expr = »(f (q.coeff n), s)] [],
  { simp [] [] [] ["[", expr coeff_monomial, "]"] [] ["at", ident hq],
    exact [expr hq] },
  use [expr monomial n (q.coeff n)],
  split,
  { simp [] [] ["only"] ["[", expr hcoeff, ",", expr map_monomial, "]"] [] [] },
  have [ident hqzero] [":", expr «expr ≠ »(q.coeff n, 0)] [],
  { intro [ident habs],
    simp [] [] ["only"] ["[", expr habs, ",", expr ring_hom.map_zero, "]"] [] ["at", ident hcoeff],
    exact [expr hzero hcoeff.symm] },
  repeat { rw [expr monomial_eq_C_mul_X] [] },
  simp [] [] ["only"] ["[", expr hzero, ",", expr hqzero, ",", expr ne.def, ",", expr not_false_iff, ",", expr degree_C_mul_X_pow, "]"] [] []
end

-- error in Data.Polynomial.Lifts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
theorem mem_lifts_and_degree_eq
{p : polynomial S}
(hlifts : «expr ∈ »(p, lifts f)) : «expr∃ , »((q : polynomial R), «expr ∧ »(«expr = »(map f q, p), «expr = »(q.degree, p.degree))) :=
begin
  generalize' [ident hd] [":"] [expr «expr = »(p.nat_degree, d)],
  revert [ident hd, ident p],
  apply [expr nat.strong_induction_on d],
  intros [ident n, ident hn, ident p, ident hlifts, ident hdeg],
  by_cases [expr erase_zero, ":", expr «expr = »(p.erase_lead, 0)],
  { rw ["[", "<-", expr erase_lead_add_monomial_nat_degree_leading_coeff p, ",", expr erase_zero, ",", expr zero_add, ",", expr leading_coeff, "]"] [],
    exact [expr monomial_mem_lifts_and_degree_eq (monomial_mem_lifts p.nat_degree ((lifts_iff_coeff_lifts p).1 hlifts p.nat_degree))] },
  have [ident deg_erase] [] [":=", expr or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) erase_zero],
  have [ident pzero] [":", expr «expr ≠ »(p, 0)] [],
  { intro [ident habs],
    exfalso,
    rw ["[", expr habs, ",", expr erase_lead_zero, ",", expr eq_self_iff_true, ",", expr not_true, "]"] ["at", ident erase_zero],
    exact [expr erase_zero] },
  have [ident lead_zero] [":", expr «expr ≠ »(p.coeff p.nat_degree, 0)] [],
  { rw ["[", "<-", expr leading_coeff, ",", expr ne.def, ",", expr leading_coeff_eq_zero, "]"] []; exact [expr pzero] },
  obtain ["⟨", ident lead, ",", ident hlead, "⟩", ":=", expr monomial_mem_lifts_and_degree_eq (monomial_mem_lifts p.nat_degree ((lifts_iff_coeff_lifts p).1 hlifts p.nat_degree))],
  have [ident deg_lead] [":", expr «expr = »(lead.degree, p.nat_degree)] [],
  { rw ["[", expr hlead.2, ",", expr monomial_eq_C_mul_X, ",", expr degree_C_mul_X_pow p.nat_degree lead_zero, "]"] [] },
  rw [expr hdeg] ["at", ident deg_erase],
  obtain ["⟨", ident erase, ",", ident herase, "⟩", ":=", expr hn p.erase_lead.nat_degree deg_erase (erase_mem_lifts p.nat_degree hlifts) (refl p.erase_lead.nat_degree)],
  use [expr «expr + »(erase, lead)],
  split,
  { simp [] [] ["only"] ["[", expr hlead, ",", expr herase, ",", expr map_add, "]"] [] [],
    nth_rewrite [0] [expr erase_lead_add_monomial_nat_degree_leading_coeff p] [] },
  rw ["[", "<-", expr hdeg, ",", expr erase_lead, "]"] ["at", ident deg_erase],
  replace [ident deg_erase] [] [":=", expr lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 deg_erase)],
  rw ["[", "<-", expr deg_lead, ",", "<-", expr herase.2, "]"] ["at", ident deg_erase],
  rw ["[", expr degree_add_eq_right_of_degree_lt deg_erase, ",", expr deg_lead, ",", expr degree_eq_nat_degree pzero, "]"] []
end

end LiftDeg

section Monic

-- error in Data.Polynomial.Lifts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
theorem lifts_and_degree_eq_and_monic
[nontrivial S]
{p : polynomial S}
(hlifts : «expr ∈ »(p, lifts f))
(hmonic : p.monic) : «expr∃ , »((q : polynomial R), «expr ∧ »(«expr = »(map f q, p), «expr ∧ »(«expr = »(q.degree, p.degree), q.monic))) :=
begin
  by_cases [expr Rtrivial, ":", expr nontrivial R],
  swap,
  { rw [expr not_nontrivial_iff_subsingleton] ["at", ident Rtrivial],
    obtain ["⟨", ident q, ",", ident hq, "⟩", ":=", expr mem_lifts_and_degree_eq hlifts],
    use [expr q],
    exact [expr ⟨hq.1, hq.2, @monic_of_subsingleton _ _ Rtrivial q⟩] },
  by_cases [expr er_zero, ":", expr «expr = »(p.erase_lead, 0)],
  { rw ["[", "<-", expr erase_lead_add_C_mul_X_pow p, ",", expr er_zero, ",", expr zero_add, ",", expr monic.def.1 hmonic, ",", expr C_1, ",", expr one_mul, "]"] [],
    use [expr «expr ^ »(X, p.nat_degree)],
    repeat { split },
    { simp [] [] ["only"] ["[", expr map_pow, ",", expr map_X, "]"] [] [] },
    { rw ["[", expr @degree_X_pow R _ Rtrivial, ",", expr degree_X_pow, "]"] [] },
    { exact [expr monic_pow monic_X p.nat_degree] } },
  obtain ["⟨", ident q, ",", ident hq, "⟩", ":=", expr mem_lifts_and_degree_eq (erase_mem_lifts p.nat_degree hlifts)],
  have [ident deg_er] [":", expr «expr < »(p.erase_lead.nat_degree, p.nat_degree)] [":=", expr or.resolve_right (erase_lead_nat_degree_lt_or_erase_lead_eq_zero p) er_zero],
  replace [ident deg_er] [] [":=", expr with_bot.coe_lt_coe.2 deg_er],
  rw ["[", "<-", expr degree_eq_nat_degree er_zero, ",", expr erase_lead, ",", "<-", expr hq.2, ",", "<-", expr @degree_X_pow R _ Rtrivial p.nat_degree, "]"] ["at", ident deg_er],
  use [expr «expr + »(q, «expr ^ »(X, p.nat_degree))],
  repeat { split },
  { simp [] [] ["only"] ["[", expr hq, ",", expr map_add, ",", expr map_pow, ",", expr map_X, "]"] [] [],
    nth_rewrite [3] ["[", "<-", expr erase_lead_add_C_mul_X_pow p, "]"] [],
    rw ["[", expr erase_lead, ",", expr monic.leading_coeff hmonic, ",", expr C_1, ",", expr one_mul, "]"] [] },
  { rw ["[", expr degree_add_eq_right_of_degree_lt deg_er, ",", expr @degree_X_pow R _ Rtrivial p.nat_degree, ",", expr degree_eq_nat_degree (monic.ne_zero hmonic), "]"] [] },
  { rw ["[", expr monic.def, ",", expr leading_coeff_add_of_degree_lt deg_er, "]"] [],
    exact [expr monic_pow monic_X p.nat_degree] }
end

end Monic

end Semiringₓ

section Ringₓ

variable{R : Type u}[Ringₓ R]{S : Type v}[Ringₓ S](f : R →+* S)

/-- The subring of polynomials that lift. -/
def lifts_ring (f : R →+* S) : Subring (Polynomial S) :=
  RingHom.range (map_ring_hom f)

/-- If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and only if it is in
the subsemiring of polynomials that lift. -/
theorem lifts_iff_lifts_ring (p : Polynomial S) : p ∈ lifts f ↔ p ∈ lifts_ring f :=
  by 
    simp only [lifts, lifts_ring, RingHom.mem_range, RingHom.mem_srange]

end Ringₓ

section Algebra

variable{R : Type u}[CommSemiringₓ R]{S : Type v}[Semiringₓ S][Algebra R S]

/-- The map `polynomial R → polynomial S` as an algebra homomorphism. -/
def map_alg (R : Type u) [CommSemiringₓ R] (S : Type v) [Semiringₓ S] [Algebra R S] : Polynomial R →ₐ[R] Polynomial S :=
  @aeval _ (Polynomial S) _ _ _ (X : Polynomial S)

/-- `map_alg` is the morphism induced by `R → S`. -/
theorem map_alg_eq_map (p : Polynomial R) : map_alg R S p = map (algebraMap R S) p :=
  by 
    simp only [map_alg, aeval_def, eval₂, map, algebra_map_apply, RingHom.coe_comp]

/-- A polynomial `p` lifts if and only if it is in the image of `map_alg`. -/
theorem mem_lifts_iff_mem_alg (R : Type u) [CommSemiringₓ R] {S : Type v} [Semiringₓ S] [Algebra R S]
  (p : Polynomial S) : p ∈ lifts (algebraMap R S) ↔ p ∈ AlgHom.range (@map_alg R _ S _ _) :=
  by 
    simp only [coe_map_ring_hom, lifts, map_alg_eq_map, AlgHom.mem_range, RingHom.mem_srange]

/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
theorem smul_mem_lifts {p : Polynomial S} (r : R) (hp : p ∈ lifts (algebraMap R S)) : r • p ∈ lifts (algebraMap R S) :=
  by 
    rw [mem_lifts_iff_mem_alg] at hp⊢
    exact Subalgebra.smul_mem (map_alg R S).range hp r

end Algebra

end Polynomial

