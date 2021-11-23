import Mathbin.FieldTheory.Ratfunc 
import Mathbin.RingTheory.Algebraic 
import Mathbin.RingTheory.DedekindDomain 
import Mathbin.RingTheory.IntegrallyClosed

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions
 - `function_field Fq F` states that `F` is a function field over the (finite) field `Fq`,
   i.e. it is a finite extension of the field of rational functions in one variable over `Fq`.
 - `function_field.ring_of_integers` defines the ring of integers corresponding to a function field
    as the integral closure of `polynomial Fq` in the function field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like `finite Fq` or
`is_scalar_tower (polynomial Fq) (fraction_ring (polynomial Fq)) F` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
function field, ring of integers
-/


noncomputable theory

variable(Fq F : Type)[Field Fq][Field F]

/-- `F` is a function field over the finite field `Fq` if it is a finite
extension of the field of rational functions in one variable over `Fq`.

Note that `F` can be a function field over multiple, non-isomorphic, `Fq`.
-/
abbrev FunctionField [Algebra (Ratfunc Fq) F] : Prop :=
  FiniteDimensional (Ratfunc Fq) F

-- error in NumberTheory.FunctionField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `F` is a function field over `Fq` iff it is a finite extension of `Fq(t)`. -/
protected
theorem function_field_iff
(Fqt : Type*)
[field Fqt]
[algebra (polynomial Fq) Fqt]
[is_fraction_ring (polynomial Fq) Fqt]
[algebra (ratfunc Fq) F]
[algebra Fqt F]
[algebra (polynomial Fq) F]
[is_scalar_tower (polynomial Fq) Fqt F]
[is_scalar_tower (polynomial Fq) (ratfunc Fq) F] : «expr ↔ »(function_field Fq F, finite_dimensional Fqt F) :=
begin
  let [ident e] [] [":=", expr is_localization.alg_equiv (non_zero_divisors (polynomial Fq)) (ratfunc Fq) Fqt],
  have [] [":", expr ∀ (c) (x : F), «expr = »(«expr • »(e c, x), «expr • »(c, x))] [],
  { intros [ident c, ident x],
    rw ["[", expr algebra.smul_def, ",", expr algebra.smul_def, "]"] [],
    congr,
    refine [expr congr_fun _ c],
    refine [expr is_localization.ext (non_zero_divisors (polynomial Fq)) _ _ _ _ _ _ _]; intros []; simp [] [] ["only"] ["[", expr alg_equiv.map_one, ",", expr ring_hom.map_one, ",", expr alg_equiv.map_mul, ",", expr ring_hom.map_mul, ",", expr alg_equiv.commutes, ",", "<-", expr is_scalar_tower.algebra_map_apply, "]"] [] [] },
  split; intro [ident h]; resetI,
  { let [ident b] [] [":=", expr finite_dimensional.fin_basis (ratfunc Fq) F],
    exact [expr finite_dimensional.of_fintype_basis (b.map_coeffs e this)] },
  { let [ident b] [] [":=", expr finite_dimensional.fin_basis Fqt F],
    refine [expr finite_dimensional.of_fintype_basis (b.map_coeffs e.symm _)],
    intros [ident c, ident x],
    convert [] [expr (this (e.symm c) x).symm] [],
    simp [] [] ["only"] ["[", expr e.apply_symm_apply, "]"] [] [] }
end

namespace FunctionField

/-- The function field analogue of `number_field.ring_of_integers`:
`function_field.ring_of_integers Fq Fqt F` is the integral closure of `Fq[t]` in `F`.

We don't actually assume `F` is a function field over `Fq` in the definition,
only when proving its properties.
-/
def ring_of_integers [Algebra (Polynomial Fq) F] :=
  integralClosure (Polynomial Fq) F

namespace RingOfIntegers

variable[Algebra (Polynomial Fq) F]

instance  : IsDomain (ring_of_integers Fq F) :=
  (ring_of_integers Fq F).IsDomain

instance  : IsIntegralClosure (ring_of_integers Fq F) (Polynomial Fq) F :=
  integralClosure.is_integral_closure _ _

variable[Algebra (Ratfunc Fq) F][FunctionField Fq F]

variable[IsScalarTower (Polynomial Fq) (Ratfunc Fq) F]

instance  : IsFractionRing (ring_of_integers Fq F) F :=
  integralClosure.is_fraction_ring_of_finite_extension (Ratfunc Fq) F

instance  : IsIntegrallyClosed (ring_of_integers Fq F) :=
  integralClosure.is_integrally_closed_of_finite_extension (Ratfunc Fq)

instance  [IsSeparable (Ratfunc Fq) F] : IsDedekindDomain (ring_of_integers Fq F) :=
  IsIntegralClosure.is_dedekind_domain (Polynomial Fq) (Ratfunc Fq) F _

end RingOfIntegers

end FunctionField

