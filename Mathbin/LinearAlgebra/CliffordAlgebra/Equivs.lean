import Mathbin.Algebra.QuaternionBasis
import Mathbin.Data.Complex.Module
import Mathbin.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Other constructions isomorphic to Clifford Algebras

This file contains isomorphisms showing that other types are equivalent to some `clifford_algebra`.

## Rings

* `clifford_algebra_ring.equiv`: any ring is equivalent to a `clifford_algebra` over a
  zero-dimensional vector space.

## Complex numbers

* `clifford_algebra_complex.equiv`: the `complex` numbers are equivalent as an `ℝ`-algebra to a
  `clifford_algebra` over a one-dimensional vector space with a quadratic form that satisfies
  `Q (ι Q 1) = -1`.
* `clifford_algebra_complex.to_complex`: the forward direction of this equiv
* `clifford_algebra_complex.of_complex`: the reverse direction of this equiv

We show additionally that this equivalence sends `complex.conj` to `clifford_algebra.involute` and
vice-versa:

* `clifford_algebra_complex.to_complex_involute`
* `clifford_algebra_complex.of_complex_conj`

Note that in this algebra `clifford_algebra.reverse` is the identity and so the clifford conjugate
is the same as `clifford_algebra.involute`.

## Quaternion algebras

* `clifford_algebra_quaternion.equiv`: a `quaternion_algebra` over `R` is equivalent as an
  `R`-algebra to a clifford algebra over `R × R`, sending `i` to `(0, 1)` and `j` to `(1, 0)`.
* `clifford_algebra_quaternion.to_quaternion`: the forward direction of this equiv
* `clifford_algebra_quaternion.of_quaternion`: the reverse direction of this equiv

We show additionally that this equivalence sends `quaternion_algebra.conj` to the clifford conjugate
and vice-versa:

* `clifford_algebra_quaternion.to_quaternion_involute_reverse`
* `clifford_algebra_quaternion.of_quaternion_conj`

-/


open CliffordAlgebra

/-! ### The clifford algebra isomorphic to a ring -/


namespace CliffordAlgebraRing

open_locale ComplexConjugate

variable {R : Type _} [CommRingₓ R]

@[simp]
theorem ι_eq_zero : ι (0 : QuadraticForm R Unit) = 0 :=
  Subsingleton.elimₓ _ _

/--  Since the vector space is empty the ring is commutative. -/
instance : CommRingₓ (CliffordAlgebra (0 : QuadraticForm R Unit)) :=
  { CliffordAlgebra.ring _ with
    mul_comm := fun x y => by
      induction x using CliffordAlgebra.induction
      case h_grade0 r =>
        apply Algebra.commutes
      case h_grade1 x =>
        simp
      case h_add x₁ x₂ hx₁ hx₂ =>
        rw [mul_addₓ, add_mulₓ, hx₁, hx₂]
      case h_mul x₁ x₂ hx₁ hx₂ =>
        rw [mul_assocₓ, hx₂, ← mul_assocₓ, hx₁, ← mul_assocₓ] }

theorem reverse_apply (x : CliffordAlgebra (0 : QuadraticForm R Unit)) : x.reverse = x := by
  induction x using CliffordAlgebra.induction
  case h_grade0 r =>
    exact reverse.commutes _
  case h_grade1 x =>
    rw [ι_eq_zero, LinearMap.zero_apply, reverse.map_zero]
  case h_mul x₁ x₂ hx₁ hx₂ =>
    rw [reverse.map_mul, mul_commₓ, hx₁, hx₂]
  case h_add x₁ x₂ hx₁ hx₂ =>
    rw [reverse.map_add, hx₁, hx₂]

@[simp]
theorem reverse_eq_id : (reverse : CliffordAlgebra (0 : QuadraticForm R Unit) →ₗ[R] _) = LinearMap.id :=
  LinearMap.ext reverse_apply

@[simp]
theorem involute_eq_id : (involute : CliffordAlgebra (0 : QuadraticForm R Unit) →ₐ[R] _) = AlgHom.id R _ := by
  ext
  simp

/--  The clifford algebra over a 0-dimensional vector space is isomorphic to its scalars. -/
protected def Equivₓ : CliffordAlgebra (0 : QuadraticForm R Unit) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom
    (CliffordAlgebra.lift (0 : QuadraticForm R Unit) $
      ⟨0, fun m : Unit => (zero_mul (0 : R)).trans (algebraMap R _).map_zero.symm⟩)
    (Algebra.ofId R _)
    (by
      ext x
      exact AlgHom.commutes _ x)
    (by
      ext : 1
      rw [ι_eq_zero, LinearMap.comp_zero, LinearMap.comp_zero])

end CliffordAlgebraRing

/-! ### The clifford algebra isomorphic to the complex numbers -/


namespace CliffordAlgebraComplex

open_locale ComplexConjugate

/--  The quadratic form sending elements to the negation of their square. -/
def Q : QuadraticForm ℝ ℝ :=
  -QuadraticForm.linMulLin LinearMap.id LinearMap.id

@[simp]
theorem Q_apply (r : ℝ) : Q r = -r*r :=
  rfl

/--  Intermediate result for `clifford_algebra_complex.equiv`: clifford algebras over
`clifford_algebra_complex.Q` above can be converted to `ℂ`. -/
def to_complex : CliffordAlgebra Q →ₐ[ℝ] ℂ :=
  CliffordAlgebra.lift Q
    ⟨LinearMap.toSpanSingleton _ _ Complex.i, fun r => by
      dsimp [LinearMap.toSpanSingleton, LinearMap.id]
      rw [mul_mul_mul_commₓ]
      simp ⟩

@[simp]
theorem to_complex_ι (r : ℝ) : to_complex (ι Q r) = r • Complex.i :=
  CliffordAlgebra.lift_ι_apply _ _ r

/--  `clifford_algebra.involute` is analogous to `complex.conj`. -/
@[simp]
theorem to_complex_involute (c : CliffordAlgebra Q) : to_complex c.involute = conj (to_complex c) := by
  have : to_complex (involute (ι Q 1)) = conj (to_complex (ι Q 1)) := by
    simp only [involute_ι, to_complex_ι, AlgHom.map_neg, one_smul, Complex.conj_I]
  suffices to_complex.comp involute = complex.conj_ae.to_alg_hom.comp to_complex by
    exact AlgHom.congr_fun this c
  ext : 2
  exact this

/--  Intermediate result for `clifford_algebra_complex.equiv`: `ℂ` can be converted to
`clifford_algebra_complex.Q` above can be converted to. -/
def of_complex : ℂ →ₐ[ℝ] CliffordAlgebra Q :=
  Complex.lift
    ⟨CliffordAlgebra.ι Q 1, by
      rw [CliffordAlgebra.ι_sq_scalar, Q_apply, one_mulₓ, RingHom.map_neg, RingHom.map_one]⟩

@[simp]
theorem of_complex_I : of_complex Complex.i = ι Q 1 :=
  Complex.lift_aux_apply_I _ _

@[simp]
theorem to_complex_comp_of_complex : to_complex.comp of_complex = AlgHom.id ℝ ℂ := by
  ext1
  dsimp only [AlgHom.comp_apply, Subtype.coe_mk, AlgHom.id_apply]
  rw [of_complex_I, to_complex_ι, one_smul]

@[simp]
theorem to_complex_of_complex (c : ℂ) : to_complex (of_complex c) = c :=
  AlgHom.congr_fun to_complex_comp_of_complex c

@[simp]
theorem of_complex_comp_to_complex : of_complex.comp to_complex = AlgHom.id ℝ (CliffordAlgebra Q) := by
  ext
  dsimp only [LinearMap.comp_apply, Subtype.coe_mk, AlgHom.id_apply, AlgHom.to_linear_map_apply, AlgHom.comp_apply]
  rw [to_complex_ι, one_smul, of_complex_I]

@[simp]
theorem of_complex_to_complex (c : CliffordAlgebra Q) : of_complex (to_complex c) = c :=
  AlgHom.congr_fun of_complex_comp_to_complex c

/--  The clifford algebras over `clifford_algebra_complex.Q` is isomorphic as an `ℝ`-algebra to
`ℂ`. -/
@[simps]
protected def Equivₓ : CliffordAlgebra Q ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofAlgHom to_complex of_complex to_complex_comp_of_complex of_complex_comp_to_complex

/--  The clifford algebra is commutative since it is isomorphic to the complex numbers.

TODO: prove this is true for all `clifford_algebra`s over a 1-dimensional vector space. -/
instance : CommRingₓ (CliffordAlgebra Q) :=
  { CliffordAlgebra.ring _ with
    mul_comm := fun x y =>
      CliffordAlgebraComplex.equiv.Injective $ by
        rw [AlgEquiv.map_mul, mul_commₓ, AlgEquiv.map_mul] }

/--  `reverse` is a no-op over `clifford_algebra_complex.Q`. -/
theorem reverse_apply (x : CliffordAlgebra Q) : x.reverse = x := by
  induction x using CliffordAlgebra.induction
  case h_grade0 r =>
    exact reverse.commutes _
  case h_grade1 x =>
    rw [reverse_ι]
  case h_mul x₁ x₂ hx₁ hx₂ =>
    rw [reverse.map_mul, mul_commₓ, hx₁, hx₂]
  case h_add x₁ x₂ hx₁ hx₂ =>
    rw [reverse.map_add, hx₁, hx₂]

@[simp]
theorem reverse_eq_id : (reverse : CliffordAlgebra Q →ₗ[ℝ] _) = LinearMap.id :=
  LinearMap.ext reverse_apply

/--  `complex.conj` is analogous to `clifford_algebra.involute`. -/
@[simp]
theorem of_complex_conj (c : ℂ) : of_complex (conj c) = (of_complex c).involute :=
  CliffordAlgebraComplex.equiv.Injective $ by
    rw [equiv_apply, equiv_apply, to_complex_involute, to_complex_of_complex, to_complex_of_complex]

attribute [protected] Q

end CliffordAlgebraComplex

/-! ### The clifford algebra isomorphic to the quaternions -/


namespace CliffordAlgebraQuaternion

open_locale Quaternion

open QuaternionAlgebra

variable {R : Type _} [CommRingₓ R] (c₁ c₂ : R)

/--  `Q c₁ c₂` is a quadratic form over `R × R` such that `clifford_algebra (Q c₁ c₂)` is isomorphic
as an `R`-algebra to `ℍ[R,c₁,c₂]`. -/
def Q : QuadraticForm R (R × R) :=
  (c₁ •
      QuadraticForm.linMulLin (LinearMap.fst _ _ _)
        (LinearMap.fst _ _ _))+c₂ • QuadraticForm.linMulLin (LinearMap.snd _ _ _) (LinearMap.snd _ _ _)

@[simp]
theorem Q_apply (v : R × R) : Q c₁ c₂ v = (c₁*v.1*v.1)+c₂*v.2*v.2 :=
  rfl

/--  The quaternion basis vectors within the algebra. -/
@[simps i j k]
def quaternion_basis : QuaternionAlgebra.Basis (CliffordAlgebra (Q c₁ c₂)) c₁ c₂ :=
  { i := ι (Q c₁ c₂) (1, 0), j := ι (Q c₁ c₂) (0, 1), k := ι (Q c₁ c₂) (1, 0)*ι (Q c₁ c₂) (0, 1),
    i_mul_i := by
      rw [ι_sq_scalar, Q_apply, ← Algebra.algebra_map_eq_smul_one]
      simp ,
    j_mul_j := by
      rw [ι_sq_scalar, Q_apply, ← Algebra.algebra_map_eq_smul_one]
      simp ,
    i_mul_j := rfl,
    j_mul_i := by
      rw [eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, QuadraticForm.polar]
      simp }

variable {c₁ c₂}

/--  Intermediate result of `clifford_algebra_quaternion.equiv`: clifford algebras over
`clifford_algebra_quaternion.Q` can be converted to `ℍ[R,c₁,c₂]`. -/
def to_quaternion : CliffordAlgebra (Q c₁ c₂) →ₐ[R] ℍ[R,c₁,c₂] :=
  CliffordAlgebra.lift (Q c₁ c₂)
    ⟨{ toFun := fun v => (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]),
        map_add' := fun v₁ v₂ => by
          simp ,
        map_smul' := fun r v => by
          ext <;> simp },
      fun v => by
      dsimp
      ext
      all_goals
        dsimp
        ring⟩

@[simp]
theorem to_quaternion_ι (v : R × R) : to_quaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/--  The "clifford conjugate" (aka `involute ∘ reverse = reverse ∘ involute`) maps to the quaternion
conjugate. -/
theorem to_quaternion_involute_reverse (c : CliffordAlgebra (Q c₁ c₂)) :
    to_quaternion (involute (reverse c)) = QuaternionAlgebra.conj (to_quaternion c) := by
  induction c using CliffordAlgebra.induction
  case h_grade0 r =>
    simp only [reverse.commutes, AlgHom.commutes, QuaternionAlgebra.coe_algebra_map, QuaternionAlgebra.conj_coe]
  case h_grade1 x =>
    rw [reverse_ι, involute_ι, to_quaternion_ι, AlgHom.map_neg, to_quaternion_ι, QuaternionAlgebra.neg_mk, conj_mk,
      neg_zero]
  case h_mul x₁ x₂ hx₁ hx₂ =>
    simp only [reverse.map_mul, AlgHom.map_mul, hx₁, hx₂, QuaternionAlgebra.conj_mul]
  case h_add x₁ x₂ hx₁ hx₂ =>
    simp only [reverse.map_add, AlgHom.map_add, hx₁, hx₂, QuaternionAlgebra.conj_add]

/--  Map a quaternion into the clifford algebra. -/
def of_quaternion : ℍ[R,c₁,c₂] →ₐ[R] CliffordAlgebra (Q c₁ c₂) :=
  (quaternion_basis c₁ c₂).liftHom

@[simp]
theorem of_quaternion_mk (a₁ a₂ a₃ a₄ : R) :
    of_quaternion (⟨a₁, a₂, a₃, a₄⟩ : ℍ[R,c₁,c₂]) =
      ((algebraMap R _
              a₁+a₂ • ι (Q c₁ c₂) (1, 0))+a₃ • ι (Q c₁ c₂) (0, 1))+a₄ • ι (Q c₁ c₂) (1, 0)*ι (Q c₁ c₂) (0, 1) :=
  rfl

@[simp]
theorem of_quaternion_comp_to_quaternion : of_quaternion.comp to_quaternion = AlgHom.id R (CliffordAlgebra (Q c₁ c₂)) :=
  by
  ext : 1
  dsimp
  ext
  all_goals
    dsimp
    rw [to_quaternion_ι]
    dsimp
    simp only [to_quaternion_ι, zero_smul, one_smul, zero_addₓ, add_zeroₓ, RingHom.map_zero]

@[simp]
theorem of_quaternion_to_quaternion (c : CliffordAlgebra (Q c₁ c₂)) : of_quaternion (to_quaternion c) = c :=
  AlgHom.congr_fun (of_quaternion_comp_to_quaternion : _ = AlgHom.id R (CliffordAlgebra (Q c₁ c₂))) c

@[simp]
theorem to_quaternion_comp_of_quaternion : to_quaternion.comp of_quaternion = AlgHom.id R ℍ[R,c₁,c₂] := by
  apply quaternion_algebra.lift.symm.injective
  ext1 <;> dsimp [QuaternionAlgebra.Basis.lift] <;> simp

@[simp]
theorem to_quaternion_of_quaternion (q : ℍ[R,c₁,c₂]) : to_quaternion (of_quaternion q) = q :=
  AlgHom.congr_fun (to_quaternion_comp_of_quaternion : _ = AlgHom.id R ℍ[R,c₁,c₂]) q

/--  The clifford algebra over `clifford_algebra_quaternion.Q c₁ c₂` is isomorphic as an `R`-algebra
to `ℍ[R,c₁,c₂]`. -/
@[simps]
protected def Equivₓ : CliffordAlgebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,c₂] :=
  AlgEquiv.ofAlgHom to_quaternion of_quaternion to_quaternion_comp_of_quaternion of_quaternion_comp_to_quaternion

/--  The quaternion conjugate maps to the "clifford conjugate" (aka
`involute ∘ reverse = reverse ∘ involute`). -/
@[simp]
theorem of_quaternion_conj (q : ℍ[R,c₁,c₂]) : of_quaternion q.conj = (of_quaternion q).reverse.involute :=
  CliffordAlgebraQuaternion.equiv.Injective $ by
    rw [equiv_apply, equiv_apply, to_quaternion_involute_reverse, to_quaternion_of_quaternion,
      to_quaternion_of_quaternion]

attribute [protected] Q

end CliffordAlgebraQuaternion

