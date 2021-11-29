import Mathbin.Data.Polynomial.FieldDivision 
import Mathbin.RingTheory.IntegralClosure 
import Mathbin.RingTheory.Polynomial.GaussLemma

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`.

After stating the defining property we specialize to the setting of field extensions
and derive some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/


open_locale Classical

open Polynomial Set Function

variable {A B : Type _}

section MinPolyDef

variable (A) [CommRingₓ A] [Ringₓ B] [Algebra A B]

/--
Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`is_integral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
noncomputable def minpoly (x : B) : Polynomial A :=
  if hx : IsIntegral A x then WellFounded.min degree_lt_wf _ hx else 0

end MinPolyDef

namespace minpoly

section Ringₓ

variable [CommRingₓ A] [Ringₓ B] [Algebra A B]

variable {x : B}

/-- A minimal polynomial is monic. -/
theorem monic (hx : IsIntegral A x) : monic (minpoly A x) :=
  by 
    delta' minpoly 
    rw [dif_pos hx]
    exact (WellFounded.min_mem degree_lt_wf _ hx).1

/-- A minimal polynomial is nonzero. -/
theorem ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly A x ≠ 0 :=
  ne_zero_of_monic (monic hx)

theorem eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0 :=
  dif_neg hx

variable (A x)

/-- An element is a root of its minimal polynomial. -/
@[simp]
theorem aeval : aeval x (minpoly A x) = 0 :=
  by 
    delta' minpoly 
    splitIfs with hx
    ·
      exact (WellFounded.min_mem degree_lt_wf _ hx).2
    ·
      exact aeval_zero _

/-- A minimal polynomial is not `1`. -/
theorem ne_one [Nontrivial B] : minpoly A x ≠ 1 :=
  by 
    intro h 
    refine' (one_ne_zero : (1 : B) ≠ 0) _ 
    simpa using congr_argₓ (Polynomial.aeval x) h

theorem map_ne_one [Nontrivial B] {R : Type _} [Semiringₓ R] [Nontrivial R] (f : A →+* R) : (minpoly A x).map f ≠ 1 :=
  by 
    byCases' hx : IsIntegral A x
    ·
      exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x)
    ·
      rw [eq_zero hx, Polynomial.map_zero]
      exact zero_ne_one

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A minimal polynomial is not a unit. -/ theorem not_is_unit [nontrivial B] : «expr¬ »(is_unit (minpoly A x)) :=
begin
  haveI [] [":", expr nontrivial A] [":=", expr (algebra_map A B).domain_nontrivial],
  by_cases [expr hx, ":", expr is_integral A x],
  { exact [expr mt (eq_one_of_is_unit_of_monic (monic hx)) (ne_one A x)] },
  { rw ["[", expr eq_zero hx, "]"] [],
    exact [expr not_is_unit_zero] }
end

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_range_of_degree_eq_one (hx : «expr = »((minpoly A x).degree, 1)) : «expr ∈ »(x, (algebra_map A B).range) :=
begin
  have [ident h] [":", expr is_integral A x] [],
  { by_contra [ident h],
    rw ["[", expr eq_zero h, ",", expr degree_zero, ",", "<-", expr with_bot.coe_one, "]"] ["at", ident hx],
    exact [expr ne_of_lt (show «expr < »(«expr⊥»(), «expr↑ »(1)), from with_bot.bot_lt_coe 1) hx] },
  have [ident key] [] [":=", expr minpoly.aeval A x],
  rw ["[", expr eq_X_add_C_of_degree_eq_one hx, ",", expr (minpoly.monic h).leading_coeff, ",", expr C_1, ",", expr one_mul, ",", expr aeval_add, ",", expr aeval_C, ",", expr aeval_X, ",", "<-", expr eq_neg_iff_add_eq_zero, ",", "<-", expr ring_hom.map_neg, "]"] ["at", ident key],
  exact [expr ⟨«expr- »((minpoly A x).coeff 0), key.symm⟩]
end

/-- The defining property of the minimal polynomial of an element `x`:
it is the monic polynomial with smallest degree that has `x` as its root. -/
theorem min {p : Polynomial A} (pmonic : p.monic) (hp : Polynomial.aeval x p = 0) : degree (minpoly A x) ≤ degree p :=
  by 
    delta' minpoly 
    splitIfs with hx
    ·
      exact le_of_not_ltₓ (WellFounded.not_lt_min degree_lt_wf _ hx ⟨pmonic, hp⟩)
    ·
      simp only [degree_zero, bot_le]

end Ringₓ

section CommRingₓ

variable [CommRingₓ A]

section Ringₓ

variable [Ringₓ B] [Algebra A B] [Nontrivial B]

variable {x : B}

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The degree of a minimal polynomial, as a natural number, is positive. -/
theorem nat_degree_pos (hx : is_integral A x) : «expr < »(0, nat_degree (minpoly A x)) :=
begin
  rw [expr pos_iff_ne_zero] [],
  intro [ident ndeg_eq_zero],
  have [ident eq_one] [":", expr «expr = »(minpoly A x, 1)] [],
  { rw [expr eq_C_of_nat_degree_eq_zero ndeg_eq_zero] [],
    convert [] [expr C_1] [],
    simpa [] [] ["only"] ["[", expr ndeg_eq_zero.symm, "]"] [] ["using", expr (monic hx).leading_coeff] },
  simpa [] [] ["only"] ["[", expr eq_one, ",", expr alg_hom.map_one, ",", expr one_ne_zero, "]"] [] ["using", expr aeval A x]
end

/-- The degree of a minimal polynomial is positive. -/
theorem degree_pos (hx : IsIntegral A x) : 0 < degree (minpoly A x) :=
  nat_degree_pos_iff_degree_pos.mp (nat_degree_pos hx)

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebra_map A B a` is `X - C a`. -/
theorem eq_X_sub_C_of_algebra_map_inj
[nontrivial A]
(a : A)
(hf : function.injective (algebra_map A B)) : «expr = »(minpoly A (algebra_map A B a), «expr - »(X, C a)) :=
begin
  have [ident hdegle] [":", expr «expr ≤ »((minpoly A (algebra_map A B a)).nat_degree, 1)] [],
  { apply [expr with_bot.coe_le_coe.1],
    rw ["[", "<-", expr degree_eq_nat_degree (ne_zero (@is_integral_algebra_map A B _ _ _ a)), ",", expr with_top.coe_one, ",", "<-", expr degree_X_sub_C a, "]"] [],
    refine [expr min A (algebra_map A B a) (monic_X_sub_C a) _],
    simp [] [] ["only"] ["[", expr aeval_C, ",", expr aeval_X, ",", expr alg_hom.map_sub, ",", expr sub_self, "]"] [] [] },
  have [ident hdeg] [":", expr «expr = »((minpoly A (algebra_map A B a)).degree, 1)] [],
  { apply [expr (degree_eq_iff_nat_degree_eq (ne_zero (@is_integral_algebra_map A B _ _ _ a))).2],
    apply [expr le_antisymm hdegle (nat_degree_pos (@is_integral_algebra_map A B _ _ _ a))] },
  have [ident hrw] [] [":=", expr eq_X_add_C_of_degree_eq_one hdeg],
  simp [] [] ["only"] ["[", expr monic (@is_integral_algebra_map A B _ _ _ a), ",", expr one_mul, ",", expr monic.leading_coeff, ",", expr ring_hom.map_one, "]"] [] ["at", ident hrw],
  have [ident h0] [":", expr «expr = »((minpoly A (algebra_map A B a)).coeff 0, «expr- »(a))] [],
  { have [ident hroot] [] [":=", expr aeval A (algebra_map A B a)],
    rw ["[", expr hrw, ",", expr add_comm, "]"] ["at", ident hroot],
    simp [] [] ["only"] ["[", expr aeval_C, ",", expr aeval_X, ",", expr aeval_add, "]"] [] ["at", ident hroot],
    replace [ident hroot] [] [":=", expr eq_neg_of_add_eq_zero hroot],
    rw ["[", "<-", expr ring_hom.map_neg _ a, "]"] ["at", ident hroot],
    exact [expr hf hroot] },
  rw [expr hrw] [],
  simp [] [] ["only"] ["[", expr h0, ",", expr ring_hom.map_neg, ",", expr sub_eq_add_neg, "]"] [] []
end

end Ringₓ

section IsDomain

variable [IsDomain A] [Ringₓ B] [Algebra A B]

variable {x : B}

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
theorem aeval_ne_zero_of_dvd_not_unit_minpoly
{a : polynomial A}
(hx : is_integral A x)
(hamonic : a.monic)
(hdvd : dvd_not_unit a (minpoly A x)) : «expr ≠ »(polynomial.aeval x a, 0) :=
begin
  intro [ident ha],
  refine [expr not_lt_of_ge (minpoly.min A x hamonic ha) _],
  obtain ["⟨", ident hzeroa, ",", ident b, ",", ident hb_nunit, ",", ident prod, "⟩", ":=", expr hdvd],
  have [ident hbmonic] [":", expr b.monic] [],
  { rw [expr monic.def] [],
    have [] [] [":=", expr monic hx],
    rwa ["[", expr monic.def, ",", expr prod, ",", expr leading_coeff_mul, ",", expr monic.def.mp hamonic, ",", expr one_mul, "]"] ["at", ident this] },
  have [ident hzerob] [":", expr «expr ≠ »(b, 0)] [":=", expr hbmonic.ne_zero],
  have [ident degbzero] [":", expr «expr < »(0, b.nat_degree)] [],
  { apply [expr nat.pos_of_ne_zero],
    intro [ident h],
    have [ident h₁] [] [":=", expr eq_C_of_nat_degree_eq_zero h],
    rw ["[", "<-", expr h, ",", "<-", expr leading_coeff, ",", expr monic.def.1 hbmonic, ",", expr C_1, "]"] ["at", ident h₁],
    rw [expr h₁] ["at", ident hb_nunit],
    have [] [] [":=", expr is_unit_one],
    contradiction },
  rw ["[", expr prod, ",", expr degree_mul, ",", expr degree_eq_nat_degree hzeroa, ",", expr degree_eq_nat_degree hzerob, "]"] [],
  exact_mod_cast [expr lt_add_of_pos_right _ degbzero]
end

variable [IsDomain B]

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A minimal polynomial is irreducible. -/ theorem irreducible (hx : is_integral A x) : irreducible (minpoly A x) :=
begin
  cases [expr irreducible_or_factor (minpoly A x) (not_is_unit A x)] ["with", ident hirr, ident hred],
  { exact [expr hirr] },
  exfalso,
  obtain ["⟨", ident a, ",", ident b, ",", ident ha_nunit, ",", ident hb_nunit, ",", ident hab_eq, "⟩", ":=", expr hred],
  have [ident coeff_prod] [":", expr «expr = »(«expr * »(a.leading_coeff, b.leading_coeff), 1)] [],
  { rw ["[", "<-", expr monic.def.1 (monic hx), ",", "<-", expr hab_eq, "]"] [],
    simp [] [] ["only"] ["[", expr leading_coeff_mul, "]"] [] [] },
  have [ident hamonic] [":", expr «expr * »(a, C b.leading_coeff).monic] [],
  { rw [expr monic.def] [],
    simp [] [] ["only"] ["[", expr coeff_prod, ",", expr leading_coeff_mul, ",", expr leading_coeff_C, "]"] [] [] },
  have [ident hbmonic] [":", expr «expr * »(b, C a.leading_coeff).monic] [],
  { rw ["[", expr monic.def, ",", expr mul_comm, "]"] [],
    simp [] [] ["only"] ["[", expr coeff_prod, ",", expr leading_coeff_mul, ",", expr leading_coeff_C, "]"] [] [] },
  have [ident prod] [":", expr «expr = »(minpoly A x, «expr * »(«expr * »(a, C b.leading_coeff), «expr * »(b, C a.leading_coeff)))] [],
  { symmetry,
    calc
      «expr = »(«expr * »(«expr * »(a, C b.leading_coeff), «expr * »(b, C a.leading_coeff)), «expr * »(«expr * »(a, b), «expr * »(C a.leading_coeff, C b.leading_coeff))) : by ring []
      «expr = »(..., «expr * »(«expr * »(a, b), C «expr * »(a.leading_coeff, b.leading_coeff))) : by simp [] [] ["only"] ["[", expr ring_hom.map_mul, "]"] [] []
      «expr = »(..., «expr * »(a, b)) : by rw ["[", expr coeff_prod, ",", expr C_1, ",", expr mul_one, "]"] []
      «expr = »(..., minpoly A x) : hab_eq },
  have [ident hzero] [] [":=", expr aeval A x],
  rw ["[", expr prod, ",", expr aeval_mul, ",", expr mul_eq_zero, "]"] ["at", ident hzero],
  cases [expr hzero] [],
  { refine [expr aeval_ne_zero_of_dvd_not_unit_minpoly hx hamonic _ hzero],
    exact [expr ⟨hamonic.ne_zero, _, mt is_unit_of_mul_is_unit_left hb_nunit, prod⟩] },
  { refine [expr aeval_ne_zero_of_dvd_not_unit_minpoly hx hbmonic _ hzero],
    rw [expr mul_comm] ["at", ident prod],
    exact [expr ⟨hbmonic.ne_zero, _, mt is_unit_of_mul_is_unit_left ha_nunit, prod⟩] }
end

end IsDomain

end CommRingₓ

section Field

variable [Field A]

section Ringₓ

variable [Ringₓ B] [Algebra A B]

variable {x : B}

variable (A x)

/-- If an element `x` is a root of a nonzero polynomial `p`,
then the degree of `p` is at least the degree of the minimal polynomial of `x`. -/
theorem degree_le_of_ne_zero {p : Polynomial A} (pnz : p ≠ 0) (hp : Polynomial.aeval x p = 0) :
  degree (minpoly A x) ≤ degree p :=
  calc degree (minpoly A x) ≤ degree (p*C (leading_coeff p⁻¹)) :=
    min A x (monic_mul_leading_coeff_inv pnz)
      (by 
        simp [hp])
    _ = degree p := degree_mul_leading_coeff_inv p pnz
    

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root,
then this polynomial is equal to the minimal polynomial of `x`. -/
theorem unique
{p : polynomial A}
(pmonic : p.monic)
(hp : «expr = »(polynomial.aeval x p, 0))
(pmin : ∀
 q : polynomial A, q.monic → «expr = »(polynomial.aeval x q, 0) → «expr ≤ »(degree p, degree q)) : «expr = »(p, minpoly A x) :=
begin
  have [ident hx] [":", expr is_integral A x] [":=", expr ⟨p, pmonic, hp⟩],
  symmetry,
  apply [expr eq_of_sub_eq_zero],
  by_contra [ident hnz],
  have [] [] [":=", expr degree_le_of_ne_zero A x hnz (by simp [] [] [] ["[", expr hp, "]"] [] [])],
  contrapose ["!"] [ident this],
  apply [expr degree_sub_lt _ (ne_zero hx)],
  { rw ["[", expr (monic hx).leading_coeff, ",", expr pmonic.leading_coeff, "]"] [] },
  { exact [expr le_antisymm (min A x pmonic hp) (pmin (minpoly A x) (monic hx) (aeval A x))] }
end

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If an element `x` is a root of a polynomial `p`,
then the minimal polynomial of `x` divides `p`. -/
theorem dvd {p : polynomial A} (hp : «expr = »(polynomial.aeval x p, 0)) : «expr ∣ »(minpoly A x, p) :=
begin
  by_cases [expr hp0, ":", expr «expr = »(p, 0)],
  { simp [] [] ["only"] ["[", expr hp0, ",", expr dvd_zero, "]"] [] [] },
  have [ident hx] [":", expr is_integral A x] [],
  { rw ["<-", expr is_algebraic_iff_is_integral] [],
    exact [expr ⟨p, hp0, hp⟩] },
  rw ["<-", expr dvd_iff_mod_by_monic_eq_zero (monic hx)] [],
  by_contra [ident hnz],
  have [] [] [":=", expr degree_le_of_ne_zero A x hnz _],
  { contrapose ["!"] [ident this],
    exact [expr degree_mod_by_monic_lt _ (monic hx)] },
  { rw ["<-", expr mod_by_monic_add_div p (monic hx)] ["at", ident hp],
    simpa [] [] [] [] [] ["using", expr hp] }
end

theorem dvd_map_of_is_scalar_tower (A K : Type _) {R : Type _} [CommRingₓ A] [Field K] [CommRingₓ R] [Algebra A K]
  [Algebra A R] [Algebra K R] [IsScalarTower A K R] (x : R) : minpoly K x ∣ (minpoly A x).map (algebraMap A K) :=
  by 
    refine' minpoly.dvd K x _ 
    rw [←IsScalarTower.aeval_apply, minpoly.aeval]

/-- If `y` is a conjugate of `x` over a field `K`, then it is a conjugate over a subring `R`. -/
theorem aeval_of_is_scalar_tower (R : Type _) {K T U : Type _} [CommRingₓ R] [Field K] [CommRingₓ T] [Algebra R K]
  [Algebra K T] [Algebra R T] [IsScalarTower R K T] [CommSemiringₓ U] [Algebra K U] [Algebra R U] [IsScalarTower R K U]
  (x : T) (y : U) (hy : Polynomial.aeval y (minpoly K x) = 0) : Polynomial.aeval y (minpoly R x) = 0 :=
  by 
    rw [IsScalarTower.aeval_apply R K]
    exact eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap K U) y (minpoly.dvd_map_of_is_scalar_tower R K x) hy

variable {A x}

theorem eq_of_irreducible_of_monic [Nontrivial B] {p : Polynomial A} (hp1 : _root_.irreducible p)
  (hp2 : Polynomial.aeval x p = 0) (hp3 : p.monic) : p = minpoly A x :=
  let ⟨q, hq⟩ := dvd A x hp2 
  eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩)$
    mul_oneₓ (minpoly A x) ▸ hq.symm ▸ Associated.mul_left _$
      associated_one_iff_is_unit.2$ (hp1.is_unit_or_is_unit hq).resolve_left$ not_is_unit A x

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_irreducible
[nontrivial B]
{p : polynomial A}
(hp1 : _root_.irreducible p)
(hp2 : «expr = »(polynomial.aeval x p, 0)) : «expr = »(«expr * »(p, C «expr ⁻¹»(p.leading_coeff)), minpoly A x) :=
begin
  have [] [":", expr «expr ≠ »(p.leading_coeff, 0)] [":=", expr leading_coeff_ne_zero.mpr hp1.ne_zero],
  apply [expr eq_of_irreducible_of_monic],
  { exact [expr associated.irreducible ⟨⟨C «expr ⁻¹»(p.leading_coeff), C p.leading_coeff, by rwa ["[", "<-", expr C_mul, ",", expr inv_mul_cancel, ",", expr C_1, "]"] [], by rwa ["[", "<-", expr C_mul, ",", expr mul_inv_cancel, ",", expr C_1, "]"] []⟩, rfl⟩ hp1] },
  { rw ["[", expr aeval_mul, ",", expr hp2, ",", expr zero_mul, "]"] [] },
  { rwa ["[", expr polynomial.monic, ",", expr leading_coeff_mul, ",", expr leading_coeff_C, ",", expr mul_inv_cancel, "]"] [] }
end

/-- If `y` is the image of `x` in an extension, their minimal polynomials coincide.

We take `h : y = algebra_map L T x` as an argument because `rw h` typically fails
since `is_integral R y` depends on y.
-/
theorem eq_of_algebra_map_eq {K S T : Type _} [Field K] [CommRingₓ S] [CommRingₓ T] [Algebra K S] [Algebra K T]
  [Algebra S T] [IsScalarTower K S T] (hST : Function.Injective (algebraMap S T)) {x : S} {y : T} (hx : IsIntegral K x)
  (h : y = algebraMap S T x) : minpoly K x = minpoly K y :=
  minpoly.unique _ _ (minpoly.monic hx)
    (by 
      rw [h, ←IsScalarTower.algebra_map_aeval, minpoly.aeval, RingHom.map_zero])
    fun q q_monic root_q =>
      minpoly.min _ _ q_monic
        (IsScalarTower.aeval_eq_zero_of_aeval_algebra_map_eq_zero K S T hST
          (h ▸ root_q : Polynomial.aeval (algebraMap S T x) q = 0))

section GcdDomain

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. -/
theorem gcd_domain_eq_field_fractions
{A R : Type*}
(K : Type*)
[comm_ring A]
[is_domain A]
[normalized_gcd_monoid A]
[field K]
[comm_ring R]
[is_domain R]
[algebra A K]
[is_fraction_ring A K]
[algebra K R]
[algebra A R]
[is_scalar_tower A K R]
{x : R}
(hx : is_integral A x) : «expr = »(minpoly K x, (minpoly A x).map (algebra_map A K)) :=
begin
  symmetry,
  refine [expr eq_of_irreducible_of_monic _ _ _],
  { exact [expr (polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map (polynomial.monic.is_primitive (monic hx))).1 (irreducible hx)] },
  { have [ident htower] [] [":=", expr is_scalar_tower.aeval_apply A K R x (minpoly A x)],
    rwa ["[", expr aeval, ",", expr eq_comm, "]"] ["at", ident htower] },
  { exact [expr monic_map _ (monic hx)] }
end

/-- For GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root. -/
theorem gcd_domain_dvd {A R : Type _} (K : Type _) [CommRingₓ A] [IsDomain A] [NormalizedGcdMonoid A] [Field K]
  [CommRingₓ R] [IsDomain R] [Algebra A K] [IsFractionRing A K] [Algebra K R] [Algebra A R] [IsScalarTower A K R]
  {x : R} (hx : IsIntegral A x) {P : Polynomial A} (hprim : is_primitive P) (hroot : Polynomial.aeval x P = 0) :
  minpoly A x ∣ P :=
  by 
    apply (is_primitive.dvd_iff_fraction_map_dvd_fraction_map K (monic.is_primitive (monic hx)) hprim).2
    rw [←gcd_domain_eq_field_fractions K hx]
    refine' dvd _ _ _ 
    rwa [←IsScalarTower.aeval_apply]

end GcdDomain

variable (B) [Nontrivial B]

/-- If `B/K` is a nontrivial algebra over a field, and `x` is an element of `K`,
then the minimal polynomial of `algebra_map K B x` is `X - C x`. -/
theorem eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = X - C a :=
  eq_X_sub_C_of_algebra_map_inj a (algebraMap A B).Injective

theorem eq_X_sub_C' (a : A) : minpoly A a = X - C a :=
  eq_X_sub_C A a

variable (A)

/-- The minimal polynomial of `0` is `X`. -/
@[simp]
theorem zero : minpoly A (0 : B) = X :=
  by 
    simpa only [add_zeroₓ, C_0, sub_eq_add_neg, neg_zero, RingHom.map_zero] using eq_X_sub_C B (0 : A)

/-- The minimal polynomial of `1` is `X - 1`. -/
@[simp]
theorem one : minpoly A (1 : B) = X - 1 :=
  by 
    simpa only [RingHom.map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1 : A)

end Ringₓ

section IsDomain

variable [Ringₓ B] [IsDomain B] [Algebra A B]

variable {x : B}

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A minimal polynomial is prime. -/ theorem prime (hx : is_integral A x) : prime (minpoly A x) :=
begin
  refine [expr ⟨ne_zero hx, not_is_unit A x, _⟩],
  rintros [ident p, ident q, "⟨", ident d, ",", ident h, "⟩"],
  have [] [":", expr «expr = »(polynomial.aeval x «expr * »(p, q), 0)] [":=", expr by simp [] [] [] ["[", expr h, ",", expr aeval A x, "]"] [] []],
  replace [] [":", expr «expr ∨ »(«expr = »(polynomial.aeval x p, 0), «expr = »(polynomial.aeval x q, 0))] [":=", expr by simpa [] [] [] [] [] []],
  exact [expr or.imp (dvd A x) (dvd A x) this]
end

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `L/K` is a field extension and an element `y` of `K` is a root of the minimal polynomial
of an element `x ∈ L`, then `y` maps to `x` under the field embedding. -/
theorem root {x : B} (hx : is_integral A x) {y : A} (h : is_root (minpoly A x) y) : «expr = »(algebra_map A B y, x) :=
have key : «expr = »(minpoly A x, «expr - »(X, C y)) := eq_of_monic_of_associated (monic hx) (monic_X_sub_C y) (associated_of_dvd_dvd ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_is_root.2 h)) (dvd_iff_is_root.2 h)),
by { have [] [] [":=", expr aeval A x],
  rwa ["[", expr key, ",", expr alg_hom.map_sub, ",", expr aeval_X, ",", expr aeval_C, ",", expr sub_eq_zero, ",", expr eq_comm, "]"] ["at", ident this] }

-- error in FieldTheory.Minpoly: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The constant coefficient of the minimal polynomial of `x` is `0` if and only if `x = 0`. -/
@[simp]
theorem coeff_zero_eq_zero (hx : is_integral A x) : «expr ↔ »(«expr = »(coeff (minpoly A x) 0, 0), «expr = »(x, 0)) :=
begin
  split,
  { intro [ident h],
    have [ident zero_root] [] [":=", expr zero_is_root_of_coeff_zero_eq_zero h],
    rw ["<-", expr root hx zero_root] [],
    exact [expr ring_hom.map_zero _] },
  { rintro [ident rfl],
    simp [] [] [] [] [] [] }
end

/-- The minimal polynomial of a nonzero element has nonzero constant coefficient. -/
theorem coeff_zero_ne_zero (hx : IsIntegral A x) (h : x ≠ 0) : coeff (minpoly A x) 0 ≠ 0 :=
  by 
    contrapose! h 
    simpa only [hx, coeff_zero_eq_zero] using h

end IsDomain

end Field

end minpoly

