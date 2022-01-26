import Mathbin.RingTheory.WittVector.StructurePolynomial

/-!
# Witt vectors

In this file we define the type of `p`-typical Witt vectors and ring operations on it.
The ring axioms are verified in `ring_theory/witt_vector/basic.lean`.

For a fixed commutative ring `R` and prime `p`,
a Witt vector `x : 𝕎 R` is an infinite sequence `ℕ → R` of elements of `R`.
However, the ring operations `+` and `*` are not defined in the obvious component-wise way.
Instead, these operations are defined via certain polynomials
using the machinery in `structure_polynomial.lean`.
The `n`th value of the sum of two Witt vectors can depend on the `0`-th through `n`th values
of the summands. This effectively simulates a “carrying” operation.

## Main definitions

* `witt_vector p R`: the type of `p`-typical Witt vectors with coefficients in `R`.
* `witt_vector.coeff x n`: projects the `n`th value of the Witt vector `x`.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


noncomputable section

/-- `witt_vector p R` is the ring of `p`-typical Witt vectors over the commutative ring `R`,
where `p` is a prime number.

If `p` is invertible in `R`, this ring is isomorphic to `ℕ → R` (the product of `ℕ` copies of `R`).
If `R` is a ring of characteristic `p`, then `witt_vector p R` is a ring of characteristic `0`.
The canonical example is `witt_vector p (zmod p)`,
which is isomorphic to the `p`-adic integers `ℤ_[p]`. -/
structure WittVector (p : ℕ) (R : Type _) where mk {} ::
  coeff : ℕ → R

variable {p : ℕ}

local notation "𝕎" => WittVector p

namespace WittVector

variable (p) {R : Type _}

/-- Construct a Witt vector `mk p x : 𝕎 R` from a sequence `x` of elements of `R`. -/
add_decl_doc WittVector.mk

/-- `x.coeff n` is the `n`th coefficient of the Witt vector `x`.

This concept does not have a standard name in the literature.
-/
add_decl_doc WittVector.coeff

@[ext]
theorem ext {x y : 𝕎 R} (h : ∀ n, x.coeff n = y.coeff n) : x = y := by
  cases x
  cases y
  simp only at h
  simp [Function.funext_iffₓ, h]

theorem ext_iff {x y : 𝕎 R} : x = y ↔ ∀ n, x.coeff n = y.coeff n :=
  ⟨fun h n => by
    rw [h], ext⟩

theorem coeff_mk (x : ℕ → R) : (mk p x).coeff = x :=
  rfl

instance : Functor (WittVector p) where
  map := fun α β f v => mk p (f ∘ v.coeff)
  mapConst := fun α β a v => mk p fun _ => a

instance : IsLawfulFunctor (WittVector p) where
  map_const_eq := fun α β => rfl
  id_map := fun α ⟨v, _⟩ => rfl
  comp_map := fun α β γ f g v => rfl

variable (p) [hp : Fact p.prime] [CommRingₓ R]

include hp

open MvPolynomial

section RingOperations

/-- The polynomials used for defining the element `0` of the ring of Witt vectors. -/
def witt_zero : ℕ → MvPolynomial (Finₓ 0 × ℕ) ℤ :=
  wittStructureInt p 0

/-- The polynomials used for defining the element `1` of the ring of Witt vectors. -/
def witt_one : ℕ → MvPolynomial (Finₓ 0 × ℕ) ℤ :=
  wittStructureInt p 1

/-- The polynomials used for defining the addition of the ring of Witt vectors. -/
def witt_add : ℕ → MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 + X 1)

/-- The polynomials used for describing the subtraction of the ring of Witt vectors. -/
def witt_sub : ℕ → MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 - X 1)

/-- The polynomials used for defining the multiplication of the ring of Witt vectors. -/
def witt_mul : ℕ → MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 * X 1)

/-- The polynomials used for defining the negation of the ring of Witt vectors. -/
def witt_neg : ℕ → MvPolynomial (Finₓ 1 × ℕ) ℤ :=
  wittStructureInt p (-X 0)

variable {p}

omit hp

/-- An auxiliary definition used in `witt_vector.eval`.
Evaluates a polynomial whose variables come from the disjoint union of `k` copies of `ℕ`,
with a curried evaluation `x`.
This can be defined more generally but we use only a specific instance here. -/
def peval {k : ℕ} (φ : MvPolynomial (Finₓ k × ℕ) ℤ) (x : Finₓ k → ℕ → R) : R :=
  aeval (Function.uncurry x) φ

/-- Let `φ` be a family of polynomials, indexed by natural numbers, whose variables come from the
disjoint union of `k` copies of `ℕ`, and let `xᵢ` be a Witt vector for `0 ≤ i < k`.

`eval φ x` evaluates `φ` mapping the variable `X_(i, n)` to the `n`th coefficient of `xᵢ`.

Instantiating `φ` with certain polynomials defined in `structure_polynomial.lean` establishes the
ring operations on `𝕎 R`. For example, `witt_vector.witt_add` is such a `φ` with `k = 2`;
evaluating this at `(x₀, x₁)` gives us the sum of two Witt vectors `x₀ + x₁`.
-/
def eval {k : ℕ} (φ : ℕ → MvPolynomial (Finₓ k × ℕ) ℤ) (x : Finₓ k → 𝕎 R) : 𝕎 R :=
  (mk p) fun n => (peval (φ n)) fun i => (x i).coeff

variable (R) [Fact p.prime]

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
instance : Zero (𝕎 R) :=
  ⟨eval (witt_zero p)
      («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")⟩

instance : Inhabited (𝕎 R) :=
  ⟨0⟩

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
instance : One (𝕎 R) :=
  ⟨eval (witt_one p)
      («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")⟩

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
instance : Add (𝕎 R) :=
  ⟨fun x y =>
    eval (witt_add p)
      («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")⟩

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
instance : Sub (𝕎 R) :=
  ⟨fun x y =>
    eval (witt_sub p)
      («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")⟩

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
instance : Mul (𝕎 R) :=
  ⟨fun x y =>
    eval (witt_mul p)
      («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")⟩

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
instance : Neg (𝕎 R) :=
  ⟨fun x =>
    eval (witt_neg p)
      («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")⟩

end RingOperations

section WittStructureSimplifications

@[simp]
theorem witt_zero_eq_zero (n : ℕ) : witt_zero p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [witt_zero, wittStructureRat, bind₁, aeval_zero', constant_coeff_X_in_terms_of_W, RingHom.map_zero,
    AlgHom.map_zero, map_witt_structure_int]

@[simp]
theorem witt_one_zero_eq_one : witt_one p 0 = 1 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [witt_one, wittStructureRat, X_in_terms_of_W_zero, AlgHom.map_one, RingHom.map_one, bind₁_X_right,
    map_witt_structure_int]

@[simp]
theorem witt_one_pos_eq_zero (n : ℕ) (hn : 0 < n) : witt_one p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [witt_one, wittStructureRat, RingHom.map_zero, AlgHom.map_one, RingHom.map_one, map_witt_structure_int]
  revert hn
  apply Nat.strong_induction_onₓ n
  clear n
  intro n IH hn
  rw [X_in_terms_of_W_eq]
  simp only [AlgHom.map_mul, AlgHom.map_sub, AlgHom.map_sum, AlgHom.map_pow, bind₁_X_right, bind₁_C_right]
  rw [sub_mul, one_mulₓ]
  rw [Finset.sum_eq_single 0]
  · simp only [inv_of_eq_inv, one_mulₓ, inv_pow₀, tsub_zero, RingHom.map_one, pow_zeroₓ]
    simp only [one_pow, one_mulₓ, X_in_terms_of_W_zero, sub_self, bind₁_X_right]
    
  · intro i hin hi0
    rw [Finset.mem_range] at hin
    rw [IH _ hin (Nat.pos_of_ne_zeroₓ hi0), zero_pow (pow_pos hp.1.Pos _), mul_zero]
    
  · rw [Finset.mem_range]
    intro
    contradiction
    

@[simp]
theorem witt_add_zero : witt_add p 0 = X (0, 0) + X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [witt_add, wittStructureRat, AlgHom.map_add, RingHom.map_add, rename_X, X_in_terms_of_W_zero, map_X,
    witt_polynomial_zero, bind₁_X_right, map_witt_structure_int]

@[simp]
theorem witt_sub_zero : witt_sub p 0 = X (0, 0) - X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [witt_sub, wittStructureRat, AlgHom.map_sub, RingHom.map_sub, rename_X, X_in_terms_of_W_zero, map_X,
    witt_polynomial_zero, bind₁_X_right, map_witt_structure_int]

@[simp]
theorem witt_mul_zero : witt_mul p 0 = X (0, 0) * X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [witt_mul, wittStructureRat, rename_X, X_in_terms_of_W_zero, map_X, witt_polynomial_zero, RingHom.map_mul,
    bind₁_X_right, AlgHom.map_mul, map_witt_structure_int]

@[simp]
theorem witt_neg_zero : witt_neg p 0 = -X (0, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [witt_neg, wittStructureRat, rename_X, X_in_terms_of_W_zero, map_X, witt_polynomial_zero, RingHom.map_neg,
    AlgHom.map_neg, bind₁_X_right, map_witt_structure_int]

@[simp]
theorem constant_coeff_witt_add (n : ℕ) : constant_coeff (witt_add p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [add_zeroₓ, RingHom.map_add, constant_coeff_X]

@[simp]
theorem constant_coeff_witt_sub (n : ℕ) : constant_coeff (witt_sub p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [sub_zero, RingHom.map_sub, constant_coeff_X]

@[simp]
theorem constant_coeff_witt_mul (n : ℕ) : constant_coeff (witt_mul p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [mul_zero, RingHom.map_mul, constant_coeff_X]

@[simp]
theorem constant_coeff_witt_neg (n : ℕ) : constant_coeff (witt_neg p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [neg_zero, RingHom.map_neg, constant_coeff_X]

end WittStructureSimplifications

section Coeff

variable (p R)

@[simp]
theorem zero_coeff (n : ℕ) : (0 : 𝕎 R).coeff n = 0 :=
  show (aeval _ (witt_zero p n) : R) = 0 by
    simp only [witt_zero_eq_zero, AlgHom.map_zero]

@[simp]
theorem one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1 :=
  show (aeval _ (witt_one p 0) : R) = 1 by
    simp only [witt_one_zero_eq_one, AlgHom.map_one]

@[simp]
theorem one_coeff_eq_of_pos (n : ℕ) (hn : 0 < n) : coeff (1 : 𝕎 R) n = 0 :=
  show (aeval _ (witt_one p n) : R) = 0 by
    simp only [hn, witt_one_pos_eq_zero, AlgHom.map_zero]

variable {p R}

omit hp

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
@[simp]
theorem v2_coeff {p' R'} (x y : WittVector p' R') (i : Finₓ 2) :
    ((«expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»") i).coeff =
      («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»") i :=
  by
  fin_cases i <;> simp

include hp

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
theorem add_coeff (x y : 𝕎 R) (n : ℕ) :
    (x + y).coeff n =
      peval (witt_add p n)
        («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»") :=
  by
  simp [· + ·, eval]

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
theorem sub_coeff (x y : 𝕎 R) (n : ℕ) :
    (x - y).coeff n =
      peval (witt_sub p n)
        («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»") :=
  by
  simp [Sub.sub, eval]

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
theorem mul_coeff (x y : 𝕎 R) (n : ℕ) :
    (x * y).coeff n =
      peval (witt_mul p n)
        («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»") :=
  by
  simp [· * ·, eval]

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
theorem neg_coeff (x : 𝕎 R) (n : ℕ) :
    (-x).coeff n =
      peval (witt_neg p n)
        («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»") :=
  by
  simp [Neg.neg, eval, Matrix.cons_fin_one]

theorem add_coeff_zero (x y : 𝕎 R) : (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  simp [add_coeff, peval]

theorem mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  simp [mul_coeff, peval]

end Coeff

theorem witt_add_vars (n : ℕ) : (witt_add p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_sub_vars (n : ℕ) : (witt_sub p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_mul_vars (n : ℕ) : (witt_mul p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_neg_vars (n : ℕ) : (witt_neg p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

end WittVector

