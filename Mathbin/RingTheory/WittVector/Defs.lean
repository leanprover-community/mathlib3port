/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.RingTheory.WittVector.StructurePolynomial

/-!
# Witt vectors

In this file we define the type of `p`-typical Witt vectors and ring operations on it.
The ring axioms are verified in `ring_theory/witt_vector/basic.lean`.

For a fixed commutative ring `R` and prime `p`,
a Witt vector `x : π R` is an infinite sequence `β β R` of elements of `R`.
However, the ring operations `+` and `*` are not defined in the obvious component-wise way.
Instead, these operations are defined via certain polynomials
using the machinery in `structure_polynomial.lean`.
The `n`th value of the sum of two Witt vectors can depend on the `0`-th through `n`th values
of the summands. This effectively simulates a βcarryingβ operation.

## Main definitions

* `witt_vector p R`: the type of `p`-typical Witt vectors with coefficients in `R`.
* `witt_vector.coeff x n`: projects the `n`th value of the Witt vector `x`.

## Notation

We use notation `π R`, entered `\bbW`, for the Witt vectors over `R`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


noncomputable section

-- ./././Mathport/Syntax/Translate/Basic.lean:1474:34: infer kinds are unsupported in Lean 4: mk []
/-- `witt_vector p R` is the ring of `p`-typical Witt vectors over the commutative ring `R`,
where `p` is a prime number.

If `p` is invertible in `R`, this ring is isomorphic to `β β R` (the product of `β` copies of `R`).
If `R` is a ring of characteristic `p`, then `witt_vector p R` is a ring of characteristic `0`.
The canonical example is `witt_vector p (zmod p)`,
which is isomorphic to the `p`-adic integers `β€_[p]`. -/
structure WittVector (p : β) (R : Type _) where mk ::
  coeff : β β R

variable {p : β}

-- mathport name: Β«exprπΒ»
/- We cannot make this `localized` notation, because the `p` on the RHS doesn't occur on the left
Hiding the `p` in the notation is very convenient, so we opt for repeating the `local notation`
in other files that use Witt vectors. -/
local notation "π" => WittVector p

-- type as `\bbW`
namespace WittVector

variable (p) {R : Type _}

/-- Construct a Witt vector `mk p x : π R` from a sequence `x` of elements of `R`. -/
add_decl_doc WittVector.mk

/-- `x.coeff n` is the `n`th coefficient of the Witt vector `x`.

This concept does not have a standard name in the literature.
-/
add_decl_doc WittVector.coeff

@[ext]
theorem ext {x y : π R} (h : β n, x.coeff n = y.coeff n) : x = y := by
  cases x
  cases y
  simp only at h
  simp [β Function.funext_iffβ, β h]

theorem ext_iff {x y : π R} : x = y β β n, x.coeff n = y.coeff n :=
  β¨fun h n => by
    rw [h], extβ©

theorem coeff_mk (x : β β R) : (mk p x).coeff = x :=
  rfl

/- These instances are not needed for the rest of the development,
but it is interesting to establish early on that `witt_vector p` is a lawful functor. -/
instance : Functor (WittVector p) where
  map := fun Ξ± Ξ² f v => mk p (f β v.coeff)
  mapConst := fun Ξ± Ξ² a v => mk p fun _ => a

instance : IsLawfulFunctor (WittVector p) where
  map_const_eq := fun Ξ± Ξ² => rfl
  id_map := fun Ξ± β¨v, _β© => rfl
  comp_map := fun Ξ± Ξ² Ξ³ f g v => rfl

variable (p) [hp : Fact p.Prime] [CommRingβ R]

include hp

open MvPolynomial

section RingOperations

/-- The polynomials used for defining the element `0` of the ring of Witt vectors. -/
def wittZero : β β MvPolynomial (Finβ 0 Γ β) β€ :=
  wittStructureInt p 0

/-- The polynomials used for defining the element `1` of the ring of Witt vectors. -/
def wittOne : β β MvPolynomial (Finβ 0 Γ β) β€ :=
  wittStructureInt p 1

/-- The polynomials used for defining the addition of the ring of Witt vectors. -/
def wittAdd : β β MvPolynomial (Finβ 2 Γ β) β€ :=
  wittStructureInt p (x 0 + x 1)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittNsmul (n : β) : β β MvPolynomial (Finβ 1 Γ β) β€ :=
  wittStructureInt p (n β’ x 0)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittZsmul (n : β€) : β β MvPolynomial (Finβ 1 Γ β) β€ :=
  wittStructureInt p (n β’ x 0)

/-- The polynomials used for describing the subtraction of the ring of Witt vectors. -/
def wittSub : β β MvPolynomial (Finβ 2 Γ β) β€ :=
  wittStructureInt p (x 0 - x 1)

/-- The polynomials used for defining the multiplication of the ring of Witt vectors. -/
def wittMul : β β MvPolynomial (Finβ 2 Γ β) β€ :=
  wittStructureInt p (x 0 * x 1)

/-- The polynomials used for defining the negation of the ring of Witt vectors. -/
def wittNeg : β β MvPolynomial (Finβ 1 Γ β) β€ :=
  wittStructureInt p (-x 0)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittPow (n : β) : β β MvPolynomial (Finβ 1 Γ β) β€ :=
  wittStructureInt p (x 0 ^ n)

variable {p}

omit hp

/-- An auxiliary definition used in `witt_vector.eval`.
Evaluates a polynomial whose variables come from the disjoint union of `k` copies of `β`,
with a curried evaluation `x`.
This can be defined more generally but we use only a specific instance here. -/
def peval {k : β} (Ο : MvPolynomial (Finβ k Γ β) β€) (x : Finβ k β β β R) : R :=
  aeval (Function.uncurry x) Ο

/-- Let `Ο` be a family of polynomials, indexed by natural numbers, whose variables come from the
disjoint union of `k` copies of `β`, and let `xα΅’` be a Witt vector for `0 β€ i < k`.

`eval Ο x` evaluates `Ο` mapping the variable `X_(i, n)` to the `n`th coefficient of `xα΅’`.

Instantiating `Ο` with certain polynomials defined in `structure_polynomial.lean` establishes the
ring operations on `π R`. For example, `witt_vector.witt_add` is such a `Ο` with `k = 2`;
evaluating this at `(xβ, xβ)` gives us the sum of two Witt vectors `xβ + xβ`.
-/
def eval {k : β} (Ο : β β MvPolynomial (Finβ k Γ β) β€) (x : Finβ k β π R) : π R :=
  (mk p) fun n => (peval (Ο n)) fun i => (x i).coeff

variable (R) [Fact p.Prime]

instance : Zero (π R) :=
  β¨eval (wittZero p) ![]β©

instance : Inhabited (π R) :=
  β¨0β©

instance : One (π R) :=
  β¨eval (wittOne p) ![]β©

instance : Add (π R) :=
  β¨fun x y => eval (wittAdd p) ![x, y]β©

instance : Sub (π R) :=
  β¨fun x y => eval (wittSub p) ![x, y]β©

instance hasNatScalar : HasSmul β (π R) :=
  β¨fun n x => eval (wittNsmul p n) ![x]β©

instance hasIntScalar : HasSmul β€ (π R) :=
  β¨fun n x => eval (wittZsmul p n) ![x]β©

instance : Mul (π R) :=
  β¨fun x y => eval (wittMul p) ![x, y]β©

instance : Neg (π R) :=
  β¨fun x => eval (wittNeg p) ![x]β©

instance hasNatPow : Pow (π R) β :=
  β¨fun x n => eval (wittPow p n) ![x]β©

instance : HasNatCast (π R) :=
  β¨Nat.unaryCastβ©

instance : HasIntCast (π R) :=
  β¨Int.castDefβ©

end RingOperations

section WittStructureSimplifications

@[simp]
theorem witt_zero_eq_zero (n : β) : wittZero p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom β) Int.cast_injective
  simp only [β witt_zero, β wittStructureRat, β bindβ, β aeval_zero', β constant_coeff_X_in_terms_of_W, β
    RingHom.map_zero, β AlgHom.map_zero, β map_witt_structure_int]

@[simp]
theorem witt_one_zero_eq_one : wittOne p 0 = 1 := by
  apply MvPolynomial.map_injective (Int.castRingHom β) Int.cast_injective
  simp only [β witt_one, β wittStructureRat, β X_in_terms_of_W_zero, β AlgHom.map_one, β RingHom.map_one, β
    bindβ_X_right, β map_witt_structure_int]

@[simp]
theorem witt_one_pos_eq_zero (n : β) (hn : 0 < n) : wittOne p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom β) Int.cast_injective
  simp only [β witt_one, β wittStructureRat, β RingHom.map_zero, β AlgHom.map_one, β RingHom.map_one, β
    map_witt_structure_int]
  revert hn
  apply Nat.strong_induction_onβ n
  clear n
  intro n IH hn
  rw [X_in_terms_of_W_eq]
  simp only [β AlgHom.map_mul, β AlgHom.map_sub, β AlgHom.map_sum, β AlgHom.map_pow, β bindβ_X_right, β bindβ_C_right]
  rw [sub_mul, one_mulβ]
  rw [Finset.sum_eq_single 0]
  Β· simp only [β inv_of_eq_inv, β one_mulβ, β inv_pow, β tsub_zero, β RingHom.map_one, β pow_zeroβ]
    simp only [β one_pow, β one_mulβ, β X_in_terms_of_W_zero, β sub_self, β bindβ_X_right]
    
  Β· intro i hin hi0
    rw [Finset.mem_range] at hin
    rw [IH _ hin (Nat.pos_of_ne_zeroβ hi0), zero_pow (pow_pos hp.1.Pos _), mul_zero]
    
  Β· rw [Finset.mem_range]
    intro
    contradiction
    

@[simp]
theorem witt_add_zero : wittAdd p 0 = x (0, 0) + x (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom β) Int.cast_injective
  simp only [β witt_add, β wittStructureRat, β AlgHom.map_add, β RingHom.map_add, β rename_X, β X_in_terms_of_W_zero, β
    map_X, β witt_polynomial_zero, β bindβ_X_right, β map_witt_structure_int]

@[simp]
theorem witt_sub_zero : wittSub p 0 = x (0, 0) - x (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom β) Int.cast_injective
  simp only [β witt_sub, β wittStructureRat, β AlgHom.map_sub, β RingHom.map_sub, β rename_X, β X_in_terms_of_W_zero, β
    map_X, β witt_polynomial_zero, β bindβ_X_right, β map_witt_structure_int]

@[simp]
theorem witt_mul_zero : wittMul p 0 = x (0, 0) * x (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom β) Int.cast_injective
  simp only [β witt_mul, β wittStructureRat, β rename_X, β X_in_terms_of_W_zero, β map_X, β witt_polynomial_zero, β
    RingHom.map_mul, β bindβ_X_right, β AlgHom.map_mul, β map_witt_structure_int]

@[simp]
theorem witt_neg_zero : wittNeg p 0 = -x (0, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom β) Int.cast_injective
  simp only [β witt_neg, β wittStructureRat, β rename_X, β X_in_terms_of_W_zero, β map_X, β witt_polynomial_zero, β
    RingHom.map_neg, β AlgHom.map_neg, β bindβ_X_right, β map_witt_structure_int]

@[simp]
theorem constant_coeff_witt_add (n : β) : constantCoeff (wittAdd p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [β add_zeroβ, β RingHom.map_add, β constant_coeff_X]

@[simp]
theorem constant_coeff_witt_sub (n : β) : constantCoeff (wittSub p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [β sub_zero, β RingHom.map_sub, β constant_coeff_X]

@[simp]
theorem constant_coeff_witt_mul (n : β) : constantCoeff (wittMul p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [β mul_zero, β RingHom.map_mul, β constant_coeff_X]

@[simp]
theorem constant_coeff_witt_neg (n : β) : constantCoeff (wittNeg p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [β neg_zero, β RingHom.map_neg, β constant_coeff_X]

@[simp]
theorem constant_coeff_witt_nsmul (m : β) (n : β) : constantCoeff (wittNsmul p m n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [β smul_zero, β map_nsmul, β constant_coeff_X]

@[simp]
theorem constant_coeff_witt_zsmul (z : β€) (n : β) : constantCoeff (wittZsmul p z n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [β smul_zero, β map_zsmul, β constant_coeff_X]

end WittStructureSimplifications

section Coeff

variable (p R)

@[simp]
theorem zero_coeff (n : β) : (0 : π R).coeff n = 0 :=
  show (aeval _ (wittZero p n) : R) = 0 by
    simp only [β witt_zero_eq_zero, β AlgHom.map_zero]

@[simp]
theorem one_coeff_zero : (1 : π R).coeff 0 = 1 :=
  show (aeval _ (wittOne p 0) : R) = 1 by
    simp only [β witt_one_zero_eq_one, β AlgHom.map_one]

@[simp]
theorem one_coeff_eq_of_pos (n : β) (hn : 0 < n) : coeff (1 : π R) n = 0 :=
  show (aeval _ (wittOne p n) : R) = 0 by
    simp only [β hn, β witt_one_pos_eq_zero, β AlgHom.map_zero]

variable {p R}

omit hp

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
@[simp]
theorem v2_coeff {p' R'} (x y : WittVector p' R') (i : Finβ 2) : (![x, y] i).coeff = ![x.coeff, y.coeff] i := by
  fin_cases i <;> simp

include hp

theorem add_coeff (x y : π R) (n : β) : (x + y).coeff n = peval (wittAdd p n) ![x.coeff, y.coeff] := by
  simp [β (Β· + Β·), β eval]

theorem sub_coeff (x y : π R) (n : β) : (x - y).coeff n = peval (wittSub p n) ![x.coeff, y.coeff] := by
  simp [β Sub.sub, β eval]

theorem mul_coeff (x y : π R) (n : β) : (x * y).coeff n = peval (wittMul p n) ![x.coeff, y.coeff] := by
  simp [β (Β· * Β·), β eval]

theorem neg_coeff (x : π R) (n : β) : (-x).coeff n = peval (wittNeg p n) ![x.coeff] := by
  simp [β Neg.neg, β eval, β Matrix.cons_fin_one]

theorem nsmul_coeff (m : β) (x : π R) (n : β) : (m β’ x).coeff n = peval (wittNsmul p m n) ![x.coeff] := by
  simp [β HasSmul.smul, β eval, β Matrix.cons_fin_one]

theorem zsmul_coeff (m : β€) (x : π R) (n : β) : (m β’ x).coeff n = peval (wittZsmul p m n) ![x.coeff] := by
  simp [β HasSmul.smul, β eval, β Matrix.cons_fin_one]

theorem pow_coeff (m : β) (x : π R) (n : β) : (x ^ m).coeff n = peval (wittPow p m n) ![x.coeff] := by
  simp [β Pow.pow, β eval, β Matrix.cons_fin_one]

theorem add_coeff_zero (x y : π R) : (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  simp [β add_coeff, β peval]

theorem mul_coeff_zero (x y : π R) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  simp [β mul_coeff, β peval]

end Coeff

theorem witt_add_vars (n : β) : (wittAdd p n).vars β Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_sub_vars (n : β) : (wittSub p n).vars β Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_mul_vars (n : β) : (wittMul p n).vars β Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_neg_vars (n : β) : (wittNeg p n).vars β Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_nsmul_vars (m : β) (n : β) : (wittNsmul p m n).vars β Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_zsmul_vars (m : β€) (n : β) : (wittZsmul p m n).vars β Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_pow_vars (m : β) (n : β) : (wittPow p m n).vars β Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

end WittVector

