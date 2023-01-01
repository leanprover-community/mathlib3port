/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata

! This file was ported from Lean 3 source module algebraic_geometry.elliptic_curve.weierstrass
! leanprover-community/mathlib commit 9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CubicDiscriminant
import Mathbin.RingTheory.AdjoinRoot
import Mathbin.Tactic.LinearCombination

/-!
# Weierstrass equations of elliptic curves

We give a working definition of an elliptic curve as a nonsingular Weierstrass curve given by a
Weierstrass equation, which is mathematically accurate in many cases but also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map
is smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is zero
(this includes all fields, all PIDs, and many other commutative rings) it can be shown (using a lot
of algebro-geometric machinery) that every elliptic curve `E` is a projective plane cubic isomorphic
to a Weierstrass curve given by the equation $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ for
some $a_i$ in `R`, and such that a certain quantity called the discriminant of `E` is a unit in `R`.
If `R` is a field, this quantity divides the discriminant of a cubic polynomial whose roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `E`.

## Main definitions

 * `weierstrass_curve`: a Weierstrass curve over a commutative ring.
 * `weierstrass_curve.Δ`: the discriminant of a Weierstrass curve.
 * `weierstrass_curve.variable_change`: the Weierstrass curve induced by a change of variables.
 * `weierstrass_curve.base_change`: the Weierstrass curve base changed over an algebra.
 * `weierstrass_curve.two_torsion_polynomial`: the 2-torsion polynomial of a Weierstrass curve.
 * `weierstrass_curve.polynomial`: the polynomial associated to a Weierstrass curve.
 * `weierstrass_curve.equation`: the Weirstrass equation of a Weierstrass curve.
 * `weierstrass_curve.nonsingular`: the nonsingular condition at a point on a Weierstrass curve.
 * `weierstrass_curve.coordinate_ring`: the coordinate ring of a Weierstrass curve.
 * `weierstrass_curve.function_field`: the function field of a Weierstrass curve.
 * `elliptic_curve`: an elliptic curve over a commutative ring.
 * `elliptic_curve.j`: the j-invariant of an elliptic curve.

## Main statements

 * `weierstrass_curve.two_torsion_polynomial_disc`: the discriminant of a Weierstrass curve is a
    constant factor of the cubic discriminant of its 2-torsion polynomial.
 * `weierstrass_curve.nonsingular_of_Δ_ne_zero`: a Weierstrass curve is nonsingular at every point
    if its discriminant is non-zero.
 * `weierstrass_curve.coordinate_ring.is_domain`: the coordinate ring of a Weierstrass curve is
    an integral domain.
 * `elliptic_curve.nonsingular`: an elliptic curve is nonsingular at every point.
 * `elliptic_curve.variable_change_j`: the j-invariant of an elliptic curve is invariant under an
    admissible linear change of variables.

## Implementation notes

The definition of elliptic curves in this file makes sense for all commutative rings `R`, but it
only gives a type which can be beefed up to a category which is equivalent to the category of
elliptic curves over the spectrum $\mathrm{Spec}(R)$ of `R` in the case that `R` has trivial Picard
group $\mathrm{Pic}(R)$ or, slightly more generally, when its 12-torsion is trivial. The issue is
that for a general ring `R`, there might be elliptic curves over $\mathrm{Spec}(R)$ in the sense of
algebraic geometry which are not globally defined by a cubic equation valid over the entire base.

## References

 * [N Katz and B Mazur, *Arithmetic Moduli of Elliptic Curves*][katz_mazur]
 * [P Deligne, *Courbes Elliptiques: Formulaire (d'après J. Tate)*][deligne_formulaire]
 * [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def map_simp : tactic Unit :=
  sorry
#align map_simp map_simp

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def eval_simp : tactic Unit :=
  sorry
#align eval_simp eval_simp

universe u v

variable {R : Type u}

/-! ## Weierstrass curves -/


/-- A Weierstrass curve $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ with parameters $a_i$. -/
@[ext]
structure WeierstrassCurve (R : Type u) where
  (a₁ a₂ a₃ a₄ a₆ : R)
#align weierstrass_curve WeierstrassCurve

instance [Inhabited R] : Inhabited <| WeierstrassCurve R :=
  ⟨⟨default, default, default, default, default⟩⟩

namespace WeierstrassCurve

variable [CommRing R] (W : WeierstrassCurve R)

section Quantity

/-! ### Standard quantities -/


/-- The `b₂` coefficient of a Weierstrass curve. -/
@[simp]
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂
#align weierstrass_curve.b₂ WeierstrassCurve.b₂

/-- The `b₄` coefficient of a Weierstrass curve. -/
@[simp]
def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃
#align weierstrass_curve.b₄ WeierstrassCurve.b₄

/-- The `b₆` coefficient of a Weierstrass curve. -/
@[simp]
def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆
#align weierstrass_curve.b₆ WeierstrassCurve.b₆

/-- The `b₈` coefficient of a Weierstrass curve. -/
@[simp]
def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2
#align weierstrass_curve.b₈ WeierstrassCurve.b₈

theorem b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 :=
  by
  simp only [b₂, b₄, b₆, b₈]
  ring1
#align weierstrass_curve.b_relation WeierstrassCurve.b_relation

/-- The `c₄` coefficient of a Weierstrass curve. -/
@[simp]
def c₄ : R :=
  W.b₂ ^ 2 - 24 * W.b₄
#align weierstrass_curve.c₄ WeierstrassCurve.c₄

/-- The `c₆` coefficient of a Weierstrass curve. -/
@[simp]
def c₆ : R :=
  -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆
#align weierstrass_curve.c₆ WeierstrassCurve.c₆

/-- The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes
if and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to
sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
@[simp]
def Δ : R :=
  -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
#align weierstrass_curve.Δ WeierstrassCurve.Δ

theorem c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 :=
  by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1
#align weierstrass_curve.c_relation WeierstrassCurve.c_relation

end Quantity

section VariableChange

/-! ### Variable changes -/


variable (u : Rˣ) (r s t : R)

/-- The Weierstrass curve over `R` induced by an admissible linear change of variables
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$. -/
@[simps]
def variableChange : WeierstrassCurve R
    where
  a₁ := ↑u⁻¹ * (W.a₁ + 2 * s)
  a₂ := ↑u⁻¹ ^ 2 * (W.a₂ - s * W.a₁ + 3 * r - s ^ 2)
  a₃ := ↑u⁻¹ ^ 3 * (W.a₃ + r * W.a₁ + 2 * t)
  a₄ := ↑u⁻¹ ^ 4 * (W.a₄ - s * W.a₃ + 2 * r * W.a₂ - (t + r * s) * W.a₁ + 3 * r ^ 2 - 2 * s * t)
  a₆ := ↑u⁻¹ ^ 6 * (W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 - t * W.a₃ - t ^ 2 - r * t * W.a₁)
#align weierstrass_curve.variable_change WeierstrassCurve.variableChange

@[simp]
theorem variable_change_b₂ : (W.variableChange u r s t).b₂ = ↑u⁻¹ ^ 2 * (W.b₂ + 12 * r) :=
  by
  simp only [b₂, variable_change_a₁, variable_change_a₂]
  ring1
#align weierstrass_curve.variable_change_b₂ WeierstrassCurve.variable_change_b₂

@[simp]
theorem variable_change_b₄ :
    (W.variableChange u r s t).b₄ = ↑u⁻¹ ^ 4 * (W.b₄ + r * W.b₂ + 6 * r ^ 2) :=
  by
  simp only [b₂, b₄, variable_change_a₁, variable_change_a₃, variable_change_a₄]
  ring1
#align weierstrass_curve.variable_change_b₄ WeierstrassCurve.variable_change_b₄

@[simp]
theorem variable_change_b₆ :
    (W.variableChange u r s t).b₆ = ↑u⁻¹ ^ 6 * (W.b₆ + 2 * r * W.b₄ + r ^ 2 * W.b₂ + 4 * r ^ 3) :=
  by
  simp only [b₂, b₄, b₆, variable_change_a₃, variable_change_a₆]
  ring1
#align weierstrass_curve.variable_change_b₆ WeierstrassCurve.variable_change_b₆

@[simp]
theorem variable_change_b₈ :
    (W.variableChange u r s t).b₈ =
      ↑u⁻¹ ^ 8 * (W.b₈ + 3 * r * W.b₆ + 3 * r ^ 2 * W.b₄ + r ^ 3 * W.b₂ + 3 * r ^ 4) :=
  by
  simp only [b₂, b₄, b₆, b₈, variable_change_a₁, variable_change_a₂, variable_change_a₃,
    variable_change_a₄, variable_change_a₆]
  ring1
#align weierstrass_curve.variable_change_b₈ WeierstrassCurve.variable_change_b₈

@[simp]
theorem variable_change_c₄ : (W.variableChange u r s t).c₄ = ↑u⁻¹ ^ 4 * W.c₄ :=
  by
  simp only [c₄, variable_change_b₂, variable_change_b₄]
  ring1
#align weierstrass_curve.variable_change_c₄ WeierstrassCurve.variable_change_c₄

@[simp]
theorem variable_change_c₆ : (W.variableChange u r s t).c₆ = ↑u⁻¹ ^ 6 * W.c₆ :=
  by
  simp only [c₆, variable_change_b₂, variable_change_b₄, variable_change_b₆]
  ring1
#align weierstrass_curve.variable_change_c₆ WeierstrassCurve.variable_change_c₆

@[simp]
theorem variable_change_Δ : (W.variableChange u r s t).Δ = ↑u⁻¹ ^ 12 * W.Δ :=
  by
  dsimp
  ring1
#align weierstrass_curve.variable_change_Δ WeierstrassCurve.variable_change_Δ

end VariableChange

section BaseChange

/-! ### Base changes -/


variable (A : Type v) [CommRing A] [Algebra R A]

/-- The Weierstrass curve over `R` base changed to `A`. -/
@[simps]
def baseChange : WeierstrassCurve A :=
  ⟨algebraMap R A W.a₁, algebraMap R A W.a₂, algebraMap R A W.a₃, algebraMap R A W.a₄,
    algebraMap R A W.a₆⟩
#align weierstrass_curve.base_change WeierstrassCurve.baseChange

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.563546683.map_simp -/
@[simp]
theorem base_change_b₂ : (W.baseChange A).b₂ = algebraMap R A W.b₂ :=
  by
  simp only [b₂, base_change_a₁, base_change_a₂]
  run_tac
    map_simp
#align weierstrass_curve.base_change_b₂ WeierstrassCurve.base_change_b₂

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.563546683.map_simp -/
@[simp]
theorem base_change_b₄ : (W.baseChange A).b₄ = algebraMap R A W.b₄ :=
  by
  simp only [b₄, base_change_a₁, base_change_a₃, base_change_a₄]
  run_tac
    map_simp
#align weierstrass_curve.base_change_b₄ WeierstrassCurve.base_change_b₄

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.563546683.map_simp -/
@[simp]
theorem base_change_b₆ : (W.baseChange A).b₆ = algebraMap R A W.b₆ :=
  by
  simp only [b₆, base_change_a₃, base_change_a₆]
  run_tac
    map_simp
#align weierstrass_curve.base_change_b₆ WeierstrassCurve.base_change_b₆

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.563546683.map_simp -/
@[simp]
theorem base_change_b₈ : (W.baseChange A).b₈ = algebraMap R A W.b₈ :=
  by
  simp only [b₈, base_change_a₁, base_change_a₂, base_change_a₃, base_change_a₄, base_change_a₆]
  run_tac
    map_simp
#align weierstrass_curve.base_change_b₈ WeierstrassCurve.base_change_b₈

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.563546683.map_simp -/
@[simp]
theorem base_change_c₄ : (W.baseChange A).c₄ = algebraMap R A W.c₄ :=
  by
  simp only [c₄, base_change_b₂, base_change_b₄]
  run_tac
    map_simp
#align weierstrass_curve.base_change_c₄ WeierstrassCurve.base_change_c₄

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.563546683.map_simp -/
@[simp]
theorem base_change_c₆ : (W.baseChange A).c₆ = algebraMap R A W.c₆ :=
  by
  simp only [c₆, base_change_b₂, base_change_b₄, base_change_b₆]
  run_tac
    map_simp
#align weierstrass_curve.base_change_c₆ WeierstrassCurve.base_change_c₆

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.563546683.map_simp -/
@[simp, nolint simp_nf]
theorem base_change_Δ : (W.baseChange A).Δ = algebraMap R A W.Δ :=
  by
  simp only [Δ, base_change_b₂, base_change_b₄, base_change_b₆, base_change_b₈]
  run_tac
    map_simp
#align weierstrass_curve.base_change_Δ WeierstrassCurve.base_change_Δ

end BaseChange

section TorsionPolynomial

/-! ### 2-torsion polynomials -/


/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If
`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `W`. -/
def twoTorsionPolynomial : Cubic R :=
  ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩
#align weierstrass_curve.two_torsion_polynomial WeierstrassCurve.twoTorsionPolynomial

theorem two_torsion_polynomial_disc : W.twoTorsionPolynomial.disc = 16 * W.Δ :=
  by
  dsimp [two_torsion_polynomial, Cubic.disc]
  ring1
#align weierstrass_curve.two_torsion_polynomial_disc WeierstrassCurve.two_torsion_polynomial_disc

theorem two_torsion_polynomial_disc_is_unit [Invertible (2 : R)] :
    IsUnit W.twoTorsionPolynomial.disc ↔ IsUnit W.Δ :=
  by
  rw [two_torsion_polynomial_disc, IsUnit.mul_iff, show (16 : R) = 2 ^ 4 by norm_num1]
  exact and_iff_right (isUnit_of_invertible <| 2 ^ 4)
#align
  weierstrass_curve.two_torsion_polynomial_disc_is_unit WeierstrassCurve.two_torsion_polynomial_disc_is_unit

theorem two_torsion_polynomial_disc_ne_zero [Nontrivial R] [Invertible (2 : R)] (hΔ : IsUnit W.Δ) :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  (W.two_torsion_polynomial_disc_is_unit.mpr hΔ).NeZero
#align
  weierstrass_curve.two_torsion_polynomial_disc_ne_zero WeierstrassCurve.two_torsion_polynomial_disc_ne_zero

end TorsionPolynomial

section Polynomial

/-! ### Weierstrass polynomials -/


open Polynomial

open Polynomial

/-- The polynomial $W(X, Y) := Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$ associated to a
Weierstrass curve `W` over `R`. For ease of polynomial manipulation, this is represented as a term
of type `R[X][X]`, where the inner variable represents $X$ and the outer variable represents $Y$. -/
noncomputable def polynomial : R[X][X] :=
  X ^ 2 + c (c W.a₁ * X + c W.a₃) * X - c (X ^ 3 + c W.a₂ * X ^ 2 + c W.a₄ * X + c W.a₆)
#align weierstrass_curve.polynomial WeierstrassCurve.polynomial

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.2972808691.eval_simp -/
@[simp]
theorem eval_polynomial (x y : R) :
    eval x (eval (c y) W.Polynomial) =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :=
  by
  simp only [Polynomial]
  run_tac
    eval_simp
  rw [add_mul, ← add_assoc]
#align weierstrass_curve.eval_polynomial WeierstrassCurve.eval_polynomial

@[simp]
theorem eval_polynomial_zero : eval 0 (eval 0 W.Polynomial) = -W.a₆ := by
  simp only [← C_0, eval_polynomial, zero_add, zero_sub, mul_zero, zero_pow (Nat.zero_lt_succ _)]
#align weierstrass_curve.eval_polynomial_zero WeierstrassCurve.eval_polynomial_zero

/-- The proposition that an affine point $(x, y)$ lies in `W`. In other words, $W(x, y) = 0$. -/
def Equation (x y : R) : Prop :=
  eval x (eval (c y) W.Polynomial) = 0
#align weierstrass_curve.equation WeierstrassCurve.Equation

theorem equation_iff' (x y : R) :
    W.Equation x y ↔
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
  by rw [equation, eval_polynomial]
#align weierstrass_curve.equation_iff' WeierstrassCurve.equation_iff'

@[simp]
theorem equation_iff (x y : R) :
    W.Equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [equation_iff', sub_eq_zero]
#align weierstrass_curve.equation_iff WeierstrassCurve.equation_iff

@[simp]
theorem equation_zero : W.Equation 0 0 ↔ W.a₆ = 0 := by
  rw [equation, C_0, eval_polynomial_zero, neg_eq_zero]
#align weierstrass_curve.equation_zero WeierstrassCurve.equation_zero

theorem equation_iff_variable_change (x y : R) :
    W.Equation x y ↔ (W.variableChange 1 x 0 y).Equation 0 0 :=
  by
  rw [equation_iff', ← neg_eq_zero, equation_zero, variable_change_a₆, inv_one, Units.val_one]
  congr 2
  ring1
#align weierstrass_curve.equation_iff_variable_change WeierstrassCurve.equation_iff_variable_change

/-- The partial derivative $W_X(X, Y)$ of $W(X, Y)$ with respect to $X$. -/
noncomputable def polynomialX : R[X][X] :=
  c (c W.a₁) * X - c (c 3 * X ^ 2 + c (2 * W.a₂) * X + c W.a₄)
#align weierstrass_curve.polynomial_X WeierstrassCurve.polynomialX

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.2972808691.eval_simp -/
@[simp]
theorem eval_polynomial_X (x y : R) :
    eval x (eval (c y) W.polynomialX) = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) :=
  by
  simp only [polynomial_X]
  run_tac
    eval_simp
#align weierstrass_curve.eval_polynomial_X WeierstrassCurve.eval_polynomial_X

@[simp]
theorem eval_polynomial_X_zero : eval 0 (eval 0 W.polynomialX) = -W.a₄ := by
  simp only [← C_0, eval_polynomial_X, zero_add, zero_sub, mul_zero, zero_pow zero_lt_two]
#align weierstrass_curve.eval_polynomial_X_zero WeierstrassCurve.eval_polynomial_X_zero

/-- The partial derivative $W_Y(X, Y)$ of $W(X, Y)$ with respect to $Y$. -/
noncomputable def polynomialY : R[X][X] :=
  c (c 2) * X + c (c W.a₁ * X + c W.a₃)
#align weierstrass_curve.polynomial_Y WeierstrassCurve.polynomialY

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.2972808691.eval_simp -/
@[simp]
theorem eval_polynomial_Y (x y : R) : eval x (eval (c y) W.polynomialY) = 2 * y + W.a₁ * x + W.a₃ :=
  by
  simp only [polynomial_Y]
  run_tac
    eval_simp
  rw [← add_assoc]
#align weierstrass_curve.eval_polynomial_Y WeierstrassCurve.eval_polynomial_Y

@[simp]
theorem eval_polynomial_Y_zero : eval 0 (eval 0 W.polynomialY) = W.a₃ := by
  simp only [← C_0, eval_polynomial_Y, zero_add, mul_zero]
#align weierstrass_curve.eval_polynomial_Y_zero WeierstrassCurve.eval_polynomial_Y_zero

/-- The proposition that an affine point $(x, y)$ on `W` is nonsingular.
In other words, either $W_X(x, y) \ne 0$ or $W_Y(x, y) \ne 0$. -/
def Nonsingular (x y : R) : Prop :=
  eval x (eval (c y) W.polynomialX) ≠ 0 ∨ eval x (eval (c y) W.polynomialY) ≠ 0
#align weierstrass_curve.nonsingular WeierstrassCurve.Nonsingular

theorem nonsingular_iff' (x y : R) :
    W.Nonsingular x y ↔
      W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0 :=
  by rw [nonsingular, eval_polynomial_X, eval_polynomial_Y]
#align weierstrass_curve.nonsingular_iff' WeierstrassCurve.nonsingular_iff'

@[simp]
theorem nonsingular_iff (x y : R) :
    W.Nonsingular x y ↔ W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃ :=
  by
  rw [nonsingular_iff', sub_ne_zero, ← @sub_ne_zero _ _ y]
  congr 3 <;> ring1
#align weierstrass_curve.nonsingular_iff WeierstrassCurve.nonsingular_iff

@[simp]
theorem nonsingular_zero : W.Nonsingular 0 0 ↔ W.a₃ ≠ 0 ∨ W.a₄ ≠ 0 := by
  rw [nonsingular, C_0, eval_polynomial_X_zero, neg_ne_zero, eval_polynomial_Y_zero, or_comm']
#align weierstrass_curve.nonsingular_zero WeierstrassCurve.nonsingular_zero

theorem nonsingular_iff_variable_change (x y : R) :
    W.Nonsingular x y ↔ (W.variableChange 1 x 0 y).Nonsingular 0 0 :=
  by
  rw [nonsingular_iff', ← neg_ne_zero, or_comm', nonsingular_zero, variable_change_a₃,
    variable_change_a₄, inv_one, Units.val_one]
  congr 3
  all_goals ring1
#align
  weierstrass_curve.nonsingular_iff_variable_change WeierstrassCurve.nonsingular_iff_variable_change

theorem nonsingular_zero_of_Δ_ne_zero (h : W.Equation 0 0) (hΔ : W.Δ ≠ 0) : W.Nonsingular 0 0 :=
  by
  simp only [equation_zero, nonsingular_zero] at *
  contrapose! hΔ
  simp [h, hΔ]
#align
  weierstrass_curve.nonsingular_zero_of_Δ_ne_zero WeierstrassCurve.nonsingular_zero_of_Δ_ne_zero

/-- A Weierstrass curve is nonsingular at every point if its discriminant is non-zero. -/
theorem nonsingular_of_Δ_ne_zero {x y : R} (h : W.Equation x y) (hΔ : W.Δ ≠ 0) :
    W.Nonsingular x y :=
  (W.nonsingular_iff_variable_change x y).mpr <|
    nonsingular_zero_of_Δ_ne_zero _ ((W.equation_iff_variable_change x y).mp h) <| by
      rwa [variable_change_Δ, inv_one, Units.val_one, one_pow, one_mul]
#align weierstrass_curve.nonsingular_of_Δ_ne_zero WeierstrassCurve.nonsingular_of_Δ_ne_zero

theorem polynomial_eq :
    W.Polynomial =
      Cubic.toPoly
        ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ :=
  by
  simp only [Polynomial, Cubic.toPoly, C_0, C_1, C_neg, C_add, C_mul]
  ring1
#align weierstrass_curve.polynomial_eq WeierstrassCurve.polynomial_eq

theorem polynomial_ne_zero [Nontrivial R] : W.Polynomial ≠ 0 :=
  by
  rw [polynomial_eq]
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero
#align weierstrass_curve.polynomial_ne_zero WeierstrassCurve.polynomial_ne_zero

theorem polynomial_degree [Nontrivial R] : W.Polynomial.degree = 2 :=
  by
  rw [polynomial_eq]
  exact Cubic.degree_of_b_ne_zero' one_ne_zero
#align weierstrass_curve.polynomial_degree WeierstrassCurve.polynomial_degree

theorem polynomial_nat_degree [Nontrivial R] : W.Polynomial.natDegree = 2 :=
  by
  rw [polynomial_eq]
  exact Cubic.nat_degree_of_b_ne_zero' one_ne_zero
#align weierstrass_curve.polynomial_nat_degree WeierstrassCurve.polynomial_nat_degree

theorem polynomial_monic : W.Polynomial.Monic :=
  by
  nontriviality R
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'
#align weierstrass_curve.polynomial_monic WeierstrassCurve.polynomial_monic

theorem polynomial_irreducible [Nontrivial R] [NoZeroDivisors R] : Irreducible W.Polynomial :=
  by
  by_contra h
  rcases(W.polynomial_monic.not_irreducible_iff_exists_add_mul_eq_coeff W.polynomial_nat_degree).mp
      h with
    ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree  at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_ne_zero' R, degree_mul] at h0
  apply (h1.symm.le.trans Cubic.degree_of_b_eq_zero').not_lt
  rcases nat.with_bot.add_eq_three_iff.mp h0.symm with (h | h | h | h)
  any_goals rw [degree_add_eq_left_of_degree_lt] <;> simp only [h] <;> decide
  any_goals rw [degree_add_eq_right_of_degree_lt] <;> simp only [h] <;> decide
#align weierstrass_curve.polynomial_irreducible WeierstrassCurve.polynomial_irreducible

/-- The coordinate ring $R[W] := R[X, Y] / \langle W(X, Y) \rangle$ of `W`.

Note that `derive comm_ring` generates a reducible instance of `comm_ring` for `coordinate_ring`.
In certain circumstances this might be extremely slow, because all instances in its definition are
unified exponentially many times. In this case, one solution is to manually add the local attribute
`local attribute [irreducible] coordinate_ring.comm_ring` to block this type-level unification.

TODO Lean 4: verify if the new def-eq cache (lean4#1102) fixed this issue.

See Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20class_group.2Emk -/
def CoordinateRing : Type u :=
  AdjoinRoot W.Polynomial deriving Inhabited, CommRing
#align weierstrass_curve.coordinate_ring WeierstrassCurve.CoordinateRing

instance [IsDomain R] [NormalizedGcdMonoid R] : IsDomain W.CoordinateRing :=
  (Ideal.Quotient.is_domain_iff_prime _).mpr <| by
    simpa only [Ideal.span_singleton_prime W.polynomial_ne_zero, ←
      GcdMonoid.irreducible_iff_prime] using W.polynomial_irreducible

instance CoordinateRing.is_domain_of_field {F : Type u} [Field F] (W : WeierstrassCurve F) :
    IsDomain W.CoordinateRing := by classical infer_instance
#align
  weierstrass_curve.coordinate_ring.is_domain_of_field WeierstrassCurve.CoordinateRing.is_domain_of_field

/-- The function field $R(W) := \mathrm{Frac}(R[W])$ of `W`. -/
@[reducible]
def FunctionField : Type u :=
  FractionRing W.CoordinateRing
#align weierstrass_curve.function_field WeierstrassCurve.FunctionField

end Polynomial

end WeierstrassCurve

/-! ## Elliptic curves -/


/-- An elliptic curve over a commutative ring. Note that this definition is only mathematically
accurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID. -/
@[ext]
structure EllipticCurve (R : Type u) [CommRing R] extends WeierstrassCurve R where
  Δ' : Rˣ
  coe_Δ' : ↑Δ' = to_weierstrass_curve.Δ
#align elliptic_curve EllipticCurve

instance : Inhabited <| EllipticCurve ℚ :=
  ⟨⟨⟨0, 0, 1, -1, 0⟩, ⟨37, 37⁻¹, by norm_num1, by norm_num1⟩,
      by
      dsimp
      ring1⟩⟩

namespace EllipticCurve

variable [CommRing R] (E : EllipticCurve R)

/-- The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`. -/
@[simp]
def j : R :=
  ↑E.Δ'⁻¹ * E.c₄ ^ 3
#align elliptic_curve.j EllipticCurve.j

theorem two_torsion_polynomial_disc_ne_zero [Nontrivial R] [Invertible (2 : R)] :
    E.twoTorsionPolynomial.disc ≠ 0 :=
  E.two_torsion_polynomial_disc_ne_zero <| E.coe_Δ' ▸ E.Δ'.IsUnit
#align
  elliptic_curve.two_torsion_polynomial_disc_ne_zero EllipticCurve.two_torsion_polynomial_disc_ne_zero

theorem nonsingular [Nontrivial R] {x y : R} (h : E.Equation x y) : E.Nonsingular x y :=
  E.nonsingular_of_Δ_ne_zero h <| E.coe_Δ' ▸ E.Δ'.NeZero
#align elliptic_curve.nonsingular EllipticCurve.nonsingular

section VariableChange

/-! ### Variable changes -/


variable (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by an admissible linear change of variables
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$.
When `R` is a field, any two Weierstrass equations isomorphic to `E` are related by this. -/
@[simps]
def variableChange : EllipticCurve R :=
  ⟨E.variableChange u r s t, u⁻¹ ^ 12 * E.Δ', by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_Δ', E.variable_change_Δ]⟩
#align elliptic_curve.variable_change EllipticCurve.variableChange

theorem coe_variable_change_Δ' : (↑(E.variableChange u r s t).Δ' : R) = ↑u⁻¹ ^ 12 * E.Δ' := by
  rw [variable_change_Δ', Units.val_mul, Units.val_pow_eq_pow_val]
#align elliptic_curve.coe_variable_change_Δ' EllipticCurve.coe_variable_change_Δ'

theorem coe_inv_variable_change_Δ' : (↑(E.variableChange u r s t).Δ'⁻¹ : R) = u ^ 12 * ↑E.Δ'⁻¹ := by
  rw [variable_change_Δ', mul_inv, inv_pow, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val]
#align elliptic_curve.coe_inv_variable_change_Δ' EllipticCurve.coe_inv_variable_change_Δ'

@[simp]
theorem variable_change_j : (E.variableChange u r s t).j = E.j :=
  by
  rw [j, coe_inv_variable_change_Δ']
  have hu : (u * ↑u⁻¹ : R) ^ 12 = 1 := by rw [u.mul_inv, one_pow]
  linear_combination (norm := (dsimp; ring1)) E.j * hu
#align elliptic_curve.variable_change_j EllipticCurve.variable_change_j

end VariableChange

section BaseChange

/-! ### Base changes -/


variable (A : Type v) [CommRing A] [Algebra R A]

/-- The elliptic curve over `R` base changed to `A`. -/
@[simps]
def baseChange : EllipticCurve A :=
  ⟨E.baseChange A, Units.map (↑(algebraMap R A)) E.Δ', by
    rw [Units.coe_map, [anonymous], coe_Δ', E.base_change_Δ]⟩
#align elliptic_curve.base_change EllipticCurve.baseChange

theorem coe_base_change_Δ' : ↑(E.baseChange A).Δ' = algebraMap R A E.Δ' :=
  rfl
#align elliptic_curve.coe_base_change_Δ' EllipticCurve.coe_base_change_Δ'

theorem coe_inv_base_change_Δ' : ↑(E.baseChange A).Δ'⁻¹ = algebraMap R A ↑E.Δ'⁻¹ :=
  rfl
#align elliptic_curve.coe_inv_base_change_Δ' EllipticCurve.coe_inv_base_change_Δ'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic _private.563546683.map_simp -/
@[simp]
theorem base_change_j : (E.baseChange A).j = algebraMap R A E.j :=
  by
  simp only [j, coe_inv_base_change_Δ', base_change_to_weierstrass_curve, E.base_change_c₄]
  run_tac
    map_simp
#align elliptic_curve.base_change_j EllipticCurve.base_change_j

end BaseChange

end EllipticCurve

