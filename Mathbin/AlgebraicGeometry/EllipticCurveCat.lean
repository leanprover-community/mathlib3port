/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/
import Mathbin.Algebra.CubicDiscriminant
import Mathbin.Tactic.LinearCombination

/-!
# The category of elliptic curves (over a field or a PID)

We give a working definition of elliptic curves which is mathematically accurate
in many cases, and also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category,
whose objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some
axioms (the map is smooth and proper and the fibres are geometrically connected group varieties
of dimension one). In the special case where `S` is `Spec R` for some commutative ring `R`
whose Picard group is trivial (this includes all fields, all principal ideal domains, and many
other commutative rings) then it can be shown (using rather a lot of algebro-geometric machinery)
that every elliptic curve is, up to isomorphism, a projective plane cubic defined by
the equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, with `aᵢ : R`, and such that
the discriminant of the aᵢ is a unit in `R`.

Some more details of the construction can be found on pages 66-69 of
[N. Katz and B. Mazur, *Arithmetic moduli of elliptic curves*][katz_mazur] or pages
53-56 of [P. Deligne, *Courbes elliptiques: formulaire d'après J. Tate*][deligne_formulaire].

## Warning

The definition in this file makes sense for all commutative rings `R`, but it only gives
a type which can be beefed up to a category which is equivalent to the category of elliptic
curves over `Spec R` in the case that `R` has trivial Picard group `Pic R` or, slightly more
generally, when its `12`-torsion is trivial. The issue is that for a general ring `R`, there
might be elliptic curves over `Spec R` in the sense of algebraic geometry which are not
globally defined by a cubic equation valid over the entire base.

## TODO

Define the `R`-points (or even `A`-points if `A` is an `R`-algebra). Care will be needed at infinity
if `R` is not a field. Define the group law on the `R`-points. Prove associativity (hard).
-/


universe u v

/-- The discriminant of an elliptic curve given by the long Weierstrass equation
  `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. If `R` is a field, then this polynomial vanishes iff the
  cubic curve cut out by this equation is singular. Sometimes only defined up to sign in the
  literature; we choose the sign used by the LMFDB. For more discussion, see
  [the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
@[simp]
def EllipticCurveCat.ΔAux {R : Type u} [CommRing R] (a₁ a₂ a₃ a₄ a₆ : R) : R :=
  let b₂ : R := a₁ ^ 2 + 4 * a₂
  let b₄ : R := 2 * a₄ + a₁ * a₃
  let b₆ : R := a₃ ^ 2 + 4 * a₆
  let b₈ : R := a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2
  -b₂ ^ 2 * b₈ - 8 * b₄ ^ 3 - 27 * b₆ ^ 2 + 9 * b₂ * b₄ * b₆
#align EllipticCurve.Δ_aux EllipticCurveCat.ΔAux

/-- The category of elliptic curves over `R` (note that this definition is only mathematically
  correct for certain rings `R` with `Pic(R)[12] = 0`, for example if `R` is a field or a PID). -/
structure EllipticCurveCat (R : Type u) [CommRing R] where
  (a₁ a₂ a₃ a₄ a₆ : R)
  Δ : Rˣ
  Δ_eq : ↑Δ = EllipticCurveCat.ΔAux a₁ a₂ a₃ a₄ a₆
#align EllipticCurve EllipticCurveCat

namespace EllipticCurveCat

instance : Inhabited (EllipticCurveCat ℚ) :=
  ⟨⟨0, 0, 1, -1, 0, ⟨37, 37⁻¹, by norm_num1, by norm_num1⟩, show (37 : ℚ) = _ + _ by norm_num1⟩⟩

variable {R : Type u} [CommRing R] (E : EllipticCurveCat R)

section Quantity

/-! ### Standard quantities -/


/-- The `b₂` coefficient of an elliptic curve. -/
@[simp]
def b₂ : R :=
  E.a₁ ^ 2 + 4 * E.a₂
#align EllipticCurve.b₂ EllipticCurveCat.b₂

/-- The `b₄` coefficient of an elliptic curve. -/
@[simp]
def b₄ : R :=
  2 * E.a₄ + E.a₁ * E.a₃
#align EllipticCurve.b₄ EllipticCurveCat.b₄

/-- The `b₆` coefficient of an elliptic curve. -/
@[simp]
def b₆ : R :=
  E.a₃ ^ 2 + 4 * E.a₆
#align EllipticCurve.b₆ EllipticCurveCat.b₆

/-- The `b₈` coefficient of an elliptic curve. -/
@[simp]
def b₈ : R :=
  E.a₁ ^ 2 * E.a₆ + 4 * E.a₂ * E.a₆ - E.a₁ * E.a₃ * E.a₄ + E.a₂ * E.a₃ ^ 2 - E.a₄ ^ 2
#align EllipticCurve.b₈ EllipticCurveCat.b₈

theorem b_relation : 4 * E.b₈ = E.b₂ * E.b₆ - E.b₄ ^ 2 := by
  simp
  ring1
#align EllipticCurve.b_relation EllipticCurveCat.b_relation

/-- The `c₄` coefficient of an elliptic curve. -/
@[simp]
def c₄ : R :=
  E.b₂ ^ 2 - 24 * E.b₄
#align EllipticCurve.c₄ EllipticCurveCat.c₄

/-- The `c₆` coefficient of an elliptic curve. -/
@[simp]
def c₆ : R :=
  -E.b₂ ^ 3 + 36 * E.b₂ * E.b₄ - 216 * E.b₆
#align EllipticCurve.c₆ EllipticCurveCat.c₆

@[simp]
theorem coe_Δ : ↑E.Δ = -E.b₂ ^ 2 * E.b₈ - 8 * E.b₄ ^ 3 - 27 * E.b₆ ^ 2 + 9 * E.b₂ * E.b₄ * E.b₆ :=
  E.Δ_eq
#align EllipticCurve.coe_Δ EllipticCurveCat.coe_Δ

theorem c_relation : 1728 * ↑E.Δ = E.c₄ ^ 3 - E.c₆ ^ 2 := by
  simp
  ring1
#align EllipticCurve.c_relation EllipticCurveCat.c_relation

/-- The j-invariant of an elliptic curve, which is invariant under isomorphisms over `R`. -/
@[simp]
def j : R :=
  ↑E.Δ⁻¹ * E.c₄ ^ 3
#align EllipticCurve.j EllipticCurveCat.j

end Quantity

section TorsionPolynomial

/-! ### `2`-torsion polynomials -/


/-- The polynomial whose roots over a splitting field of `R` are the `2`-torsion points of the
  elliptic curve when `R` is a field of characteristic different from `2`, and whose discriminant
  happens to be a multiple of the discriminant of the elliptic curve. -/
def twoTorsionPolynomial : Cubic R :=
  ⟨4, E.b₂, 2 * E.b₄, E.b₆⟩
#align EllipticCurve.two_torsion_polynomial EllipticCurveCat.twoTorsionPolynomial

theorem twoTorsionPolynomial.disc_eq : E.twoTorsionPolynomial.disc = 16 * E.Δ := by
  simp only [two_torsion_polynomial, Cubic.disc, coe_Δ, b₂, b₄, b₆, b₈]
  ring1
#align EllipticCurve.two_torsion_polynomial.disc_eq EllipticCurveCat.twoTorsionPolynomial.disc_eq

theorem twoTorsionPolynomial.disc_ne_zero [Nontrivial R] [Invertible (2 : R)] :
    E.twoTorsionPolynomial.disc ≠ 0 := fun hdisc =>
  E.Δ.NeZero <|
    (is_unit_of_invertible <| 2 ^ 4).mul_left_cancel <| by
      linear_combination (norm := ring1) hdisc - two_torsion_polynomial.disc_eq E
#align
  EllipticCurve.two_torsion_polynomial.disc_ne_zero EllipticCurveCat.twoTorsionPolynomial.disc_ne_zero

end TorsionPolynomial

section BaseChange

/-! ### Base changes -/


variable (A : Type v) [CommRing A] [Algebra R A]

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def simp_map : tactic Unit :=
  sorry
#align EllipticCurve.simp_map EllipticCurve.simp_map

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic _private.3257942883.simp_map -/
/-- The elliptic curve over `R` base changed to `A`. -/
@[simps]
def baseChange : EllipticCurveCat
      A where 
  a₁ := algebraMap R A E.a₁
  a₂ := algebraMap R A E.a₂
  a₃ := algebraMap R A E.a₃
  a₄ := algebraMap R A E.a₄
  a₆ := algebraMap R A E.a₆
  Δ := Units.map (↑(algebraMap R A)) E.Δ
  Δ_eq := by 
    simp only [Units.coe_map, RingHom.coe_monoid_hom, Δ_eq, Δ_aux]
    run_tac
      simp_map
#align EllipticCurve.base_change EllipticCurveCat.baseChange

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic _private.3257942883.simp_map -/
@[simp]
theorem base_change_b₂ : (E.base_change A).b₂ = algebraMap R A E.b₂ := by
  simp only [b₂, base_change_a₁, base_change_a₂]
  run_tac
    simp_map
#align EllipticCurve.base_change_b₂ EllipticCurveCat.base_change_b₂

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic _private.3257942883.simp_map -/
@[simp]
theorem base_change_b₄ : (E.base_change A).b₄ = algebraMap R A E.b₄ := by
  simp only [b₄, base_change_a₁, base_change_a₃, base_change_a₄]
  run_tac
    simp_map
#align EllipticCurve.base_change_b₄ EllipticCurveCat.base_change_b₄

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic _private.3257942883.simp_map -/
@[simp]
theorem base_change_b₆ : (E.base_change A).b₆ = algebraMap R A E.b₆ := by
  simp only [b₆, base_change_a₃, base_change_a₆]
  run_tac
    simp_map
#align EllipticCurve.base_change_b₆ EllipticCurveCat.base_change_b₆

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic _private.3257942883.simp_map -/
@[simp]
theorem base_change_b₈ : (E.base_change A).b₈ = algebraMap R A E.b₈ := by
  simp only [b₈, base_change_a₁, base_change_a₂, base_change_a₃, base_change_a₄, base_change_a₆]
  run_tac
    simp_map
#align EllipticCurve.base_change_b₈ EllipticCurveCat.base_change_b₈

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic _private.3257942883.simp_map -/
@[simp]
theorem base_change_c₄ : (E.base_change A).c₄ = algebraMap R A E.c₄ := by
  simp only [c₄, base_change_b₂, base_change_b₄]
  run_tac
    simp_map
#align EllipticCurve.base_change_c₄ EllipticCurveCat.base_change_c₄

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic _private.3257942883.simp_map -/
@[simp]
theorem base_change_c₆ : (E.base_change A).c₆ = algebraMap R A E.c₆ := by
  simp only [c₆, base_change_b₂, base_change_b₄, base_change_b₆]
  run_tac
    simp_map
#align EllipticCurve.base_change_c₆ EllipticCurveCat.base_change_c₆

theorem base_change_Δ_coe : ↑(E.base_change A).Δ = algebraMap R A E.Δ :=
  rfl
#align EllipticCurve.base_change_Δ_coe EllipticCurveCat.base_change_Δ_coe

theorem base_change_Δ_inv_coe : ↑(E.base_change A).Δ⁻¹ = algebraMap R A ↑E.Δ⁻¹ :=
  rfl
#align EllipticCurve.base_change_Δ_inv_coe EllipticCurveCat.base_change_Δ_inv_coe

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic _private.3257942883.simp_map -/
@[simp]
theorem base_change_j : (E.base_change A).j = algebraMap R A E.j := by
  simp only [j, base_change_c₄, base_change_Δ_inv_coe]
  run_tac
    simp_map
#align EllipticCurve.base_change_j EllipticCurveCat.base_change_j

end BaseChange

section VariableChange

/-! ### Variable changes -/


variable (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by an admissible linear change of variables
  `(x, y) ↦ (u²x + r, u³y + u²sx + t)` for some `u ∈ Rˣ` and some `r, s, t ∈ R`.
  When `R` is a field, any two isomorphic long Weierstrass equations are related by this. -/
@[simps]
def variableChange : EllipticCurveCat
      R where 
  a₁ := ↑u⁻¹ * (E.a₁ + 2 * s)
  a₂ := ↑u⁻¹ ^ 2 * (E.a₂ - s * E.a₁ + 3 * r - s ^ 2)
  a₃ := ↑u⁻¹ ^ 3 * (E.a₃ + r * E.a₁ + 2 * t)
  a₄ := ↑u⁻¹ ^ 4 * (E.a₄ - s * E.a₃ + 2 * r * E.a₂ - (t + r * s) * E.a₁ + 3 * r ^ 2 - 2 * s * t)
  a₆ := ↑u⁻¹ ^ 6 * (E.a₆ + r * E.a₄ + r ^ 2 * E.a₂ + r ^ 3 - t * E.a₃ - t ^ 2 - r * t * E.a₁)
  Δ := u⁻¹ ^ 12 * E.Δ
  Δ_eq := by 
    simp [-inv_pow]
    ring1
#align EllipticCurve.variable_change EllipticCurveCat.variableChange

@[simp]
theorem variable_change_b₂ : (E.variableChange u r s t).b₂ = ↑u⁻¹ ^ 2 * (E.b₂ + 12 * r) := by
  simp only [b₂, variable_change_a₁, variable_change_a₂]
  ring1
#align EllipticCurve.variable_change_b₂ EllipticCurveCat.variable_change_b₂

@[simp]
theorem variable_change_b₄ :
    (E.variableChange u r s t).b₄ = ↑u⁻¹ ^ 4 * (E.b₄ + r * E.b₂ + 6 * r ^ 2) := by
  simp only [b₂, b₄, variable_change_a₁, variable_change_a₃, variable_change_a₄]
  ring1
#align EllipticCurve.variable_change_b₄ EllipticCurveCat.variable_change_b₄

@[simp]
theorem variable_change_b₆ :
    (E.variableChange u r s t).b₆ = ↑u⁻¹ ^ 6 * (E.b₆ + 2 * r * E.b₄ + r ^ 2 * E.b₂ + 4 * r ^ 3) :=
  by 
  simp only [b₂, b₄, b₆, variable_change_a₃, variable_change_a₆]
  ring1
#align EllipticCurve.variable_change_b₆ EllipticCurveCat.variable_change_b₆

@[simp]
theorem variable_change_b₈ :
    (E.variableChange u r s t).b₈ =
      ↑u⁻¹ ^ 8 * (E.b₈ + 3 * r * E.b₆ + 3 * r ^ 2 * E.b₄ + r ^ 3 * E.b₂ + 3 * r ^ 4) :=
  by
  simp only [b₂, b₄, b₆, b₈, variable_change_a₁, variable_change_a₂, variable_change_a₃,
    variable_change_a₄, variable_change_a₆]
  ring1
#align EllipticCurve.variable_change_b₈ EllipticCurveCat.variable_change_b₈

@[simp]
theorem variable_change_c₄ : (E.variableChange u r s t).c₄ = ↑u⁻¹ ^ 4 * E.c₄ := by
  simp only [c₄, variable_change_b₂, variable_change_b₄]
  ring1
#align EllipticCurve.variable_change_c₄ EllipticCurveCat.variable_change_c₄

@[simp]
theorem variable_change_c₆ : (E.variableChange u r s t).c₆ = ↑u⁻¹ ^ 6 * E.c₆ := by
  simp only [c₆, variable_change_b₂, variable_change_b₄, variable_change_b₆]
  ring1
#align EllipticCurve.variable_change_c₆ EllipticCurveCat.variable_change_c₆

theorem variable_change_Δ_coe : (↑(E.variableChange u r s t).Δ : R) = ↑u⁻¹ ^ 12 * E.Δ := by
  rw [variable_change_Δ, Units.val_mul, Units.coe_pow]
#align EllipticCurve.variable_change_Δ_coe EllipticCurveCat.variable_change_Δ_coe

theorem variable_change_Δ_inv_coe : (↑(E.variableChange u r s t).Δ⁻¹ : R) = u ^ 12 * ↑E.Δ⁻¹ := by
  rw [variable_change_Δ, mul_inv, inv_pow, inv_inv, Units.val_mul, Units.coe_pow]
#align EllipticCurve.variable_change_Δ_inv_coe EllipticCurveCat.variable_change_Δ_inv_coe

@[simp]
theorem variable_change_j : (E.variableChange u r s t).j = E.j := by
  simp only [b₂, b₄, c₄, j, variable_change_c₄, variable_change_Δ, mul_inv, inv_pow, inv_inv,
    Units.val_mul, u.coe_pow]
  have hu : (u * ↑u⁻¹ : R) ^ 12 = 1 := by rw [u.mul_inv, one_pow]
  linear_combination (norm := ring1)
    ↑E.Δ⁻¹ * ((E.a₁ ^ 2 + 4 * E.a₂) ^ 2 - 24 * (2 * E.a₄ + E.a₁ * E.a₃)) ^ 3 * hu
#align EllipticCurve.variable_change_j EllipticCurveCat.variable_change_j

end VariableChange

end EllipticCurveCat

