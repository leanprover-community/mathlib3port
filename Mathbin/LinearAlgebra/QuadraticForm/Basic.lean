/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathbin.Algebra.Invertible
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.LinearAlgebra.Matrix.BilinearForm

/-!
# Quadratic forms

This file defines quadratic forms over a `R`-module `M`.
A quadratic form is a map `Q : M → R` such that
  (`to_fun_smul`) `Q (a • x) = a * a * Q x`
  (`polar_...`) The map `polar Q := λ x y, Q (x + y) - Q x - Q y` is bilinear.
They come with a scalar multiplication, `(a • Q) x = Q (a • x) = a * a * Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

 * `quadratic_form.associated`: associated bilinear form
 * `quadratic_form.pos_def`: positive definite quadratic forms
 * `quadratic_form.anisotropic`: anisotropic quadratic forms
 * `quadratic_form.discr`: discriminant of a quadratic form

## Main statements

 * `quadratic_form.associated_left_inverse`,
 * `quadratic_form.associated_right_inverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic forms and symmetric
  bilinear forms
 * `bilin_form.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear form `B`.

## Notation

In this file, the variable `R` is used when a `ring` structure is sufficient and
`R₁` is used when specifically a `comm_ring` is required. This allows us to keep
`[module R M]` and `[module R₁ M]` assumptions in the variables without
confusion between `*` from `ring` and `*` from `comm_ring`.

The variable `S` is used when `R` itself has a `•` action.

## References

 * https://en.wikipedia.org/wiki/Quadratic_form
 * https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic form, homogeneous polynomial, quadratic polynomial
-/


universe u v w

variable {S : Type _}

variable {R : Type _} {M : Type _} [AddCommGroupₓ M] [Ringₓ R]

variable {R₁ : Type _} [CommRingₓ R₁]

namespace QuadraticForm

/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.d

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar (f : M → R) (x y : M) :=
  f (x + y) - f x - f y

theorem polar_add (f g : M → R) (x y : M) : polar (f + g) x y = polar f x y + polar g x y := by
  simp only [polar, Pi.add_apply]
  abel

theorem polar_neg (f : M → R) (x y : M) : polar (-f) x y = -polar f x y := by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]

theorem polar_smul [Monoidₓ S] [DistribMulAction S R] (f : M → R) (s : S) (x y : M) :
    polar (s • f) x y = s • polar f x y := by
  simp only [polar, Pi.smul_apply, smul_sub]

theorem polar_comm (f : M → R) (x y : M) : polar f x y = polar f y x := by
  rw [polar, polar, add_commₓ, sub_sub, sub_sub, add_commₓ (f x) (f y)]

theorem polar_comp {F : Type _} [Ringₓ S] [AddMonoidHomClass F R S] (f : M → R) (g : F) (x y : M) :
    polar (g ∘ f) x y = g (polar f x y) := by
  simp only [polar, Pi.smul_apply, Function.comp_applyₓ, map_sub]

end QuadraticForm

variable [Module R M] [Module R₁ M]

open QuadraticForm

/-- A quadratic form over a module.

Note we only need the left lemmas about `quadratic_form.polar` as the right lemmas follow from
`quadratic_form.polar_comm`. -/
structure QuadraticForm (R : Type u) (M : Type v) [Ringₓ R] [AddCommGroupₓ M] [Module R M] where
  toFun : M → R
  to_fun_smul : ∀ a : R x : M, to_fun (a • x) = a * a * to_fun x
  polar_add_left' : ∀ x x' y : M, polar to_fun (x + x') y = polar to_fun x y + polar to_fun x' y
  polar_smul_left' : ∀ a : R x y : M, polar to_fun (a • x) y = a • polar to_fun x y

namespace QuadraticForm

variable {Q Q' : QuadraticForm R M}

section FunLike

instance funLike : FunLike (QuadraticForm R M) M fun _ => R where
  coe := toFun
  coe_injective' := fun x y h => by
    cases x <;> cases y <;> congr

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : CoeFun (QuadraticForm R M) fun _ => M → R :=
  ⟨toFun⟩

/-- The `simp` normal form for a quadratic form is `coe_fn`, not `to_fun`. -/
@[simp]
theorem to_fun_eq_coe : Q.toFun = ⇑Q :=
  rfl

@[ext]
theorem ext (H : ∀ x : M, Q x = Q' x) : Q = Q' :=
  FunLike.ext _ _ H

theorem congr_fun (h : Q = Q') (x : M) : Q x = Q' x :=
  FunLike.congr_fun h _

theorem ext_iff : Q = Q' ↔ ∀ x, Q x = Q' x :=
  FunLike.ext_iff

/-- Copy of a `quadratic_form` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (Q : QuadraticForm R M) (Q' : M → R) (h : Q' = ⇑Q) : QuadraticForm R M where
  toFun := Q'
  to_fun_smul := h.symm ▸ Q.to_fun_smul
  polar_add_left' := h.symm ▸ Q.polar_add_left'
  polar_smul_left' := h.symm ▸ Q.polar_smul_left'

end FunLike

theorem map_smul (a : R) (x : M) : Q (a • x) = a * a * Q x :=
  Q.to_fun_smul a x

theorem map_add_self (x : M) : Q (x + x) = 4 * Q x := by
  rw [← one_smul R x, ← add_smul, map_smul]
  norm_num

@[simp]
theorem map_zero : Q 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_mul]

instance zeroHomClass : ZeroHomClass (QuadraticForm R M) M R :=
  { QuadraticForm.funLike with map_zero := fun _ => map_zero }

@[simp]
theorem map_neg (x : M) : Q (-x) = Q x := by
  rw [← @neg_one_smul R _ _ _ _ x, map_smul, neg_one_mul, neg_negₓ, one_mulₓ]

theorem map_sub (x y : M) : Q (x - y) = Q (y - x) := by
  rw [← neg_sub, map_neg]

@[simp]
theorem polar_zero_left (y : M) : polar Q 0 y = 0 := by
  simp only [polar, zero_addₓ, QuadraticForm.map_zero, sub_zero, sub_self]

@[simp]
theorem polar_add_left (x x' y : M) : polar Q (x + x') y = polar Q x y + polar Q x' y :=
  Q.polar_add_left' x x' y

@[simp]
theorem polar_smul_left (a : R) (x y : M) : polar Q (a • x) y = a * polar Q x y :=
  Q.polar_smul_left' a x y

@[simp]
theorem polar_neg_left (x y : M) : polar Q (-x) y = -polar Q x y := by
  rw [← neg_one_smul R x, polar_smul_left, neg_one_mul]

@[simp]
theorem polar_sub_left (x x' y : M) : polar Q (x - x') y = polar Q x y - polar Q x' y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_left, polar_neg_left]

@[simp]
theorem polar_zero_right (y : M) : polar Q y 0 = 0 := by
  simp only [add_zeroₓ, polar, QuadraticForm.map_zero, sub_self]

@[simp]
theorem polar_add_right (x y y' : M) : polar Q x (y + y') = polar Q x y + polar Q x y' := by
  rw [polar_comm Q x, polar_comm Q x, polar_comm Q x, polar_add_left]

@[simp]
theorem polar_smul_right (a : R) (x y : M) : polar Q x (a • y) = a * polar Q x y := by
  rw [polar_comm Q x, polar_comm Q x, polar_smul_left]

@[simp]
theorem polar_neg_right (x y : M) : polar Q x (-y) = -polar Q x y := by
  rw [← neg_one_smul R y, polar_smul_right, neg_one_mul]

@[simp]
theorem polar_sub_right (x y y' : M) : polar Q x (y - y') = polar Q x y - polar Q x y' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_right, polar_neg_right]

@[simp]
theorem polar_self (x : M) : polar Q x x = 2 * Q x := by
  rw [polar, map_add_self, sub_sub, sub_eq_iff_eq_add, ← two_mul, ← two_mul, ← mul_assoc]
  norm_num

section OfTower

variable [CommSemiringₓ S] [Algebra S R] [Module S M] [IsScalarTower S R M]

variable (Q)

theorem map_smul_of_tower (a : S) (x : M) : Q (a • x) = (a * a) • Q x := by
  rw [← IsScalarTower.algebra_map_smul R a x, map_smul, ← RingHom.map_mul, Algebra.smul_def]

@[simp]
theorem polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  rw [← IsScalarTower.algebra_map_smul R a x, polar_smul_left, Algebra.smul_def]

@[simp]
theorem polar_smul_right_of_tower (a : S) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [← IsScalarTower.algebra_map_smul R a y, polar_smul_right, Algebra.smul_def]

end OfTower

section HasScalar

variable [Monoidₓ S] [DistribMulAction S R] [SmulCommClass S R R]

/-- `quadratic_form R M` inherits the scalar action from any algebra over `R`.

When `R` is commutative, this provides an `R`-action via `algebra.id`. -/
instance : HasScalar S (QuadraticForm R M) :=
  ⟨fun a Q =>
    { toFun := a • Q,
      to_fun_smul := fun b x => by
        rw [Pi.smul_apply, map_smul, Pi.smul_apply, mul_smul_comm],
      polar_add_left' := fun x x' y => by
        simp only [polar_smul, polar_add_left, smul_add],
      polar_smul_left' := fun b x y => by
        simp only [polar_smul, polar_smul_left, ← mul_smul_comm, smul_eq_mul] }⟩

@[simp]
theorem coe_fn_smul (a : S) (Q : QuadraticForm R M) : ⇑(a • Q) = a • Q :=
  rfl

@[simp]
theorem smul_apply (a : S) (Q : QuadraticForm R M) (x : M) : (a • Q) x = a • Q x :=
  rfl

end HasScalar

instance : Zero (QuadraticForm R M) :=
  ⟨{ toFun := fun x => 0,
      to_fun_smul := fun a x => by
        simp only [mul_zero],
      polar_add_left' := fun x x' y => by
        simp only [add_zeroₓ, polar, sub_self],
      polar_smul_left' := fun a x y => by
        simp only [polar, smul_zero, sub_self] }⟩

@[simp]
theorem coe_fn_zero : ⇑(0 : QuadraticForm R M) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : M) : (0 : QuadraticForm R M) x = 0 :=
  rfl

instance : Inhabited (QuadraticForm R M) :=
  ⟨0⟩

instance : Add (QuadraticForm R M) :=
  ⟨fun Q Q' =>
    { toFun := Q + Q',
      to_fun_smul := fun a x => by
        simp only [Pi.add_apply, map_smul, mul_addₓ],
      polar_add_left' := fun x x' y => by
        simp only [polar_add, polar_add_left, add_assocₓ, add_left_commₓ],
      polar_smul_left' := fun a x y => by
        simp only [polar_add, smul_eq_mul, mul_addₓ, polar_smul_left] }⟩

@[simp]
theorem coe_fn_add (Q Q' : QuadraticForm R M) : ⇑(Q + Q') = Q + Q' :=
  rfl

@[simp]
theorem add_apply (Q Q' : QuadraticForm R M) (x : M) : (Q + Q') x = Q x + Q' x :=
  rfl

instance : Neg (QuadraticForm R M) :=
  ⟨fun Q =>
    { toFun := -Q,
      to_fun_smul := fun a x => by
        simp only [Pi.neg_apply, map_smul, mul_neg],
      polar_add_left' := fun x x' y => by
        simp only [polar_neg, polar_add_left, neg_add],
      polar_smul_left' := fun a x y => by
        simp only [polar_neg, polar_smul_left, mul_neg, smul_eq_mul] }⟩

@[simp]
theorem coe_fn_neg (Q : QuadraticForm R M) : ⇑(-Q) = -Q :=
  rfl

@[simp]
theorem neg_apply (Q : QuadraticForm R M) (x : M) : (-Q) x = -Q x :=
  rfl

instance : Sub (QuadraticForm R M) :=
  ⟨fun Q Q' => (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _)⟩

@[simp]
theorem coe_fn_sub (Q Q' : QuadraticForm R M) : ⇑(Q - Q') = Q - Q' :=
  rfl

@[simp]
theorem sub_apply (Q Q' : QuadraticForm R M) (x : M) : (Q - Q') x = Q x - Q' x :=
  rfl

instance : AddCommGroupₓ (QuadraticForm R M) :=
  FunLike.coe_injective.AddCommGroup _ coe_fn_zero coe_fn_add coe_fn_neg coe_fn_sub (fun _ _ => coe_fn_smul _ _)
    fun _ _ => coe_fn_smul _ _

/-- `@coe_fn (quadratic_form R M)` as an `add_monoid_hom`.

This API mirrors `add_monoid_hom.coe_fn`. -/
@[simps apply]
def coeFnAddMonoidHom : QuadraticForm R M →+ M → R where
  toFun := coeFn
  map_zero' := coe_fn_zero
  map_add' := coe_fn_add

/-- Evaluation on a particular element of the module `M` is an additive map over quadratic forms. -/
@[simps apply]
def evalAddMonoidHom (m : M) : QuadraticForm R M →+ R :=
  (Pi.evalAddMonoidHom _ m).comp coeFnAddMonoidHom

section Sum

open BigOperators

@[simp]
theorem coe_fn_sum {ι : Type _} (Q : ι → QuadraticForm R M) (s : Finset ι) : ⇑(∑ i in s, Q i) = ∑ i in s, Q i :=
  (coeFnAddMonoidHom : _ →+ M → R).map_sum Q s

@[simp]
theorem sum_apply {ι : Type _} (Q : ι → QuadraticForm R M) (s : Finset ι) (x : M) :
    (∑ i in s, Q i) x = ∑ i in s, Q i x :=
  (evalAddMonoidHom x : _ →+ R).map_sum Q s

end Sum

instance [Monoidₓ S] [DistribMulAction S R] [SmulCommClass S R R] : DistribMulAction S (QuadraticForm R M) where
  mul_smul := fun a b Q =>
    ext fun x => by
      simp only [smul_apply, mul_smul]
  one_smul := fun Q =>
    ext fun x => by
      simp only [QuadraticForm.smul_apply, one_smul]
  smul_add := fun a Q Q' => by
    ext
    simp only [add_apply, smul_apply, smul_add]
  smul_zero := fun a => by
    ext
    simp only [zero_apply, smul_apply, smul_zero]

instance [Semiringₓ S] [Module S R] [SmulCommClass S R R] : Module S (QuadraticForm R M) where
  zero_smul := fun Q => by
    ext
    simp only [zero_apply, smul_apply, zero_smul]
  add_smul := fun a b Q => by
    ext
    simp only [add_apply, smul_apply, add_smul]

section Comp

variable {N : Type v} [AddCommGroupₓ N] [Module R N]

/-- Compose the quadratic form with a linear function. -/
def comp (Q : QuadraticForm R N) (f : M →ₗ[R] N) : QuadraticForm R M where
  toFun := fun x => Q (f x)
  to_fun_smul := fun a x => by
    simp only [map_smul, f.map_smul]
  polar_add_left' := fun x x' y => by
    convert polar_add_left (f x) (f x') (f y) using 1 <;> simp only [polar, f.map_add]
  polar_smul_left' := fun a x y => by
    convert polar_smul_left a (f x) (f y) using 1 <;> simp only [polar, f.map_smul, f.map_add, smul_eq_mul]

@[simp]
theorem comp_apply (Q : QuadraticForm R N) (f : M →ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
  rfl

/-- Compose a quadratic form with a linear function on the left. -/
@[simps (config := { simpRhs := true })]
def _root_.linear_map.comp_quadratic_form {S : Type _} [CommRingₓ S] [Algebra S R] [Module S M] [IsScalarTower S R M]
    (f : R →ₗ[S] S) (Q : QuadraticForm R M) : QuadraticForm S M where
  toFun := f ∘ Q
  to_fun_smul := fun b x => by
    rw [Function.comp_applyₓ, Q.map_smul_of_tower b x, f.map_smul, smul_eq_mul]
  polar_add_left' := fun x x' y => by
    simp only [polar_comp, f.map_add, polar_add_left]
  polar_smul_left' := fun b x y => by
    simp only [polar_comp, f.map_smul, polar_smul_left_of_tower]

end Comp

section CommRingₓ

/-- The product of linear forms is a quadratic form. -/
def linMulLin (f g : M →ₗ[R₁] R₁) : QuadraticForm R₁ M where
  toFun := f * g
  to_fun_smul := fun a x => by
    simp only [smul_eq_mul, RingHom.id_apply, Pi.mul_apply, LinearMap.map_smulₛₗ]
    ring
  polar_add_left' := fun x x' y => by
    simp only [polar, Pi.mul_apply, LinearMap.map_add]
    ring
  polar_smul_left' := fun a x y => by
    simp only [polar, Pi.mul_apply, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
    ring

@[simp]
theorem lin_mul_lin_apply (f g : M →ₗ[R₁] R₁) x : linMulLin f g x = f x * g x :=
  rfl

@[simp]
theorem add_lin_mul_lin (f g h : M →ₗ[R₁] R₁) : linMulLin (f + g) h = linMulLin f h + linMulLin g h :=
  ext fun x => add_mulₓ _ _ _

@[simp]
theorem lin_mul_lin_add (f g h : M →ₗ[R₁] R₁) : linMulLin f (g + h) = linMulLin f g + linMulLin f h :=
  ext fun x => mul_addₓ _ _ _

variable {N : Type v} [AddCommGroupₓ N] [Module R₁ N]

@[simp]
theorem lin_mul_lin_comp (f g : M →ₗ[R₁] R₁) (h : N →ₗ[R₁] M) :
    (linMulLin f g).comp h = linMulLin (f.comp h) (g.comp h) :=
  rfl

variable {n : Type _}

/-- `sq` is the quadratic form mapping the vector `x : R₁` to `x * x` -/
@[simps]
def sq : QuadraticForm R₁ R₁ :=
  linMulLin LinearMap.id LinearMap.id

/-- `proj i j` is the quadratic form mapping the vector `x : n → R₁` to `x i * x j` -/
def proj (i j : n) : QuadraticForm R₁ (n → R₁) :=
  linMulLin (@LinearMap.proj _ _ _ (fun _ => R₁) _ _ i) (@LinearMap.proj _ _ _ (fun _ => R₁) _ _ j)

@[simp]
theorem proj_apply (i j : n) (x : n → R₁) : proj i j x = x i * x j :=
  rfl

end CommRingₓ

end QuadraticForm

/-!
### Associated bilinear forms

Over a commutative ring with an inverse of 2, the theory of quadratic forms is
basically identical to that of symmetric bilinear forms. The map from quadratic
forms to bilinear forms giving this identification is called the `associated`
quadratic form.
-/


variable {B : BilinForm R M}

namespace BilinForm

open QuadraticForm

theorem polar_to_quadratic_form (x y : M) : polar (fun x => B x x) x y = B x y + B y x := by
  simp only [add_assocₓ, add_sub_cancel', add_right, polar, add_left_injₓ, add_neg_cancel_left, add_left,
    sub_eq_add_neg _ (B y y), add_commₓ (B y x) _]

/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def toQuadraticForm (B : BilinForm R M) : QuadraticForm R M where
  toFun := fun x => B x x
  to_fun_smul := fun a x => by
    simp only [mul_assoc, smul_right, smul_left]
  polar_add_left' := fun x x' y => by
    simp only [add_assocₓ, add_right, add_left_injₓ, polar_to_quadratic_form, add_left, add_left_commₓ]
  polar_smul_left' := fun a x y => by
    simp only [smul_add, add_left_injₓ, polar_to_quadratic_form, smul_right, smul_eq_mul, smul_left, smul_right,
      mul_addₓ]

@[simp]
theorem to_quadratic_form_apply (B : BilinForm R M) (x : M) : B.toQuadraticForm x = B x x :=
  rfl

section

variable (R M)

@[simp]
theorem to_quadratic_form_zero : (0 : BilinForm R M).toQuadraticForm = 0 :=
  rfl

end

end BilinForm

namespace QuadraticForm

open BilinForm

section AssociatedHom

variable (S) [CommSemiringₓ S] [Algebra S R]

variable [Invertible (2 : R)] {B₁ : BilinForm R M}

/-- `associated_hom` is the map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative subring of `R`.

Over a commutative ring, use `associated`, which gives an `R`-linear map.  Over a general ring with
no nontrivial distinguished commutative subring, use `associated'`, which gives an additive
homomorphism (or more precisely a `ℤ`-linear map.) -/
def associatedHom : QuadraticForm R M →ₗ[S] BilinForm R M where
  toFun := fun Q =>
    ((· • ·) : Submonoid.center R → BilinForm R M → BilinForm R M)
      ⟨⅟ 2, fun x => (Commute.one_right x).bit0_right.inv_of_right⟩
      { bilin := polar Q, bilin_add_left := polar_add_left, bilin_smul_left := polar_smul_left,
        bilin_add_right := polar_add_right, bilin_smul_right := polar_smul_right }
  map_add' := fun Q Q' => by
    ext
    simp only [BilinForm.add_apply, BilinForm.smul_apply, coe_fn_mk, polar_add, coe_fn_add, smul_add]
  map_smul' := fun s Q => by
    ext
    simp only [RingHom.id_apply, polar_smul, smul_comm s, coe_fn_mk, coe_fn_smul, BilinForm.smul_apply]

variable (Q : QuadraticForm R M) (S)

@[simp]
theorem associated_apply (x y : M) : associatedHom S Q x y = ⅟ 2 * (Q (x + y) - Q x - Q y) :=
  rfl

theorem associated_is_symm : (associatedHom S Q).IsSymm := fun x y => by
  simp only [associated_apply, add_commₓ, add_left_commₓ, sub_eq_add_neg]

@[simp]
theorem associated_comp {N : Type v} [AddCommGroupₓ N] [Module R N] (f : N →ₗ[R] M) :
    associatedHom S (Q.comp f) = (associatedHom S Q).comp f f := by
  ext
  simp only [QuadraticForm.comp_apply, BilinForm.comp_apply, associated_apply, LinearMap.map_add]

theorem associated_to_quadratic_form (B : BilinForm R M) (x y : M) :
    associatedHom S B.toQuadraticForm x y = ⅟ 2 * (B x y + B y x) := by
  simp only [associated_apply, ← polar_to_quadratic_form, polar, to_quadratic_form_apply]

theorem associated_left_inverse (h : B₁.IsSymm) : associatedHom S B₁.toQuadraticForm = B₁ :=
  BilinForm.ext fun x y => by
    rw [associated_to_quadratic_form, is_symm.eq h x y, ← two_mul, ← mul_assoc, inv_of_mul_self, one_mulₓ]

theorem to_quadratic_form_associated : (associatedHom S Q).toQuadraticForm = Q :=
  QuadraticForm.ext fun x =>
    calc
      (associatedHom S Q).toQuadraticForm x = ⅟ 2 * (Q x + Q x) := by
        simp only [add_assocₓ, add_sub_cancel', one_mulₓ, to_quadratic_form_apply, add_mulₓ, associated_apply,
          map_add_self, bit0]
      _ = Q x := by
        rw [← two_mul (Q x), ← mul_assoc, inv_of_mul_self, one_mulₓ]
      

-- note: usually `right_inverse` lemmas are named the other way around, but this is consistent
-- with historical naming in this file.
theorem associated_right_inverse :
    Function.RightInverse (associatedHom S) (BilinForm.toQuadraticForm : _ → QuadraticForm R M) := fun Q =>
  to_quadratic_form_associated S Q

theorem associated_eq_self_apply (x : M) : associatedHom S Q x x = Q x := by
  rw [associated_apply, map_add_self]
  suffices ⅟ 2 * (2 * Q x) = Q x by
    convert this
    simp only [bit0, add_mulₓ, one_mulₓ]
    abel
  simp only [← mul_assoc, one_mulₓ, inv_of_mul_self]

/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
abbrev associated' : QuadraticForm R M →ₗ[ℤ] BilinForm R M :=
  associatedHom ℤ

/-- Symmetric bilinear forms can be lifted to quadratic forms -/
instance : CanLift (BilinForm R M) (QuadraticForm R M) where
  coe := associatedHom ℕ
  cond := BilinForm.IsSymm
  prf := fun B hB => ⟨B.toQuadraticForm, associated_left_inverse _ hB⟩

/-- There exists a non-null vector with respect to any quadratic form `Q` whose associated
bilinear form is non-zero, i.e. there exists `x` such that `Q x ≠ 0`. -/
theorem exists_quadratic_form_ne_zero {Q : QuadraticForm R M} (hB₁ : Q.associated' ≠ 0) : ∃ x, Q x ≠ 0 := by
  rw [← not_forall]
  intro h
  apply hB₁
  rw [(QuadraticForm.ext h : Q = 0), LinearMap.map_zero]

end AssociatedHom

section Associated

variable [Invertible (2 : R₁)]

/-- `associated` is the linear map that sends a quadratic form over a commutative ring to its
associated symmetric bilinear form. -/
-- Note:  When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associated_hom` and place it in the previous section.
abbrev associated : QuadraticForm R₁ M →ₗ[R₁] BilinForm R₁ M :=
  associatedHom R₁

@[simp]
theorem associated_lin_mul_lin (f g : M →ₗ[R₁] R₁) :
    (linMulLin f g).Associated = ⅟ (2 : R₁) • (BilinForm.linMulLin f g + BilinForm.linMulLin g f) := by
  ext
  simp only [smul_add, Algebra.id.smul_eq_mul, BilinForm.lin_mul_lin_apply, QuadraticForm.lin_mul_lin_apply,
    BilinForm.smul_apply, associated_apply, BilinForm.add_apply, LinearMap.map_add]
  ring

end Associated

section Anisotropic

/-- An anisotropic quadratic form is zero only on zero vectors. -/
def Anisotropic (Q : QuadraticForm R M) : Prop :=
  ∀ x, Q x = 0 → x = 0

-- ././Mathport/Syntax/Translate/Basic.lean:597:2: warning: expanding binder collection (x «expr ≠ » 0)
theorem not_anisotropic_iff_exists (Q : QuadraticForm R M) : ¬Anisotropic Q ↔ ∃ (x : _)(_ : x ≠ 0), Q x = 0 := by
  simp only [anisotropic, not_forall, exists_prop, and_comm]

theorem Anisotropic.eq_zero_iff {Q : QuadraticForm R M} (h : Anisotropic Q) {x : M} : Q x = 0 ↔ x = 0 :=
  ⟨h x, fun h => h.symm ▸ map_zero⟩

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
theorem nondegenerate_of_anisotropic [Invertible (2 : R)] (Q : QuadraticForm R M) (hB : Q.Anisotropic) :
    Q.associated'.Nondegenerate := by
  intro x hx
  refine' hB _ _
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm

end Anisotropic

section PosDef

variable {R₂ : Type u} [OrderedRing R₂] [Module R₂ M] {Q₂ : QuadraticForm R₂ M}

-- ././Mathport/Syntax/Translate/Basic.lean:597:2: warning: expanding binder collection (x «expr ≠ » 0)
/-- A positive definite quadratic form is positive on nonzero vectors. -/
def PosDef (Q₂ : QuadraticForm R₂ M) : Prop :=
  ∀ x _ : x ≠ 0, 0 < Q₂ x

theorem PosDef.smul {R} [LinearOrderedCommRing R] [Module R M] {Q : QuadraticForm R M} (h : PosDef Q) {a : R}
    (a_pos : 0 < a) : PosDef (a • Q) := fun x hx => mul_pos a_pos (h x hx)

variable {n : Type _}

theorem PosDef.nonneg {Q : QuadraticForm R₂ M} (hQ : PosDef Q) (x : M) : 0 ≤ Q x :=
  (eq_or_ne x 0).elim (fun h => h.symm ▸ map_zero.symm.le) fun h => (hQ _ h).le

theorem PosDef.anisotropic {Q : QuadraticForm R₂ M} (hQ : Q.PosDef) : Q.Anisotropic := fun x hQx =>
  Classical.by_contradiction fun hx =>
    lt_irreflₓ (0 : R₂) <| by
      have := hQ _ hx
      rw [hQx] at this
      exact this

theorem pos_def_of_nonneg {Q : QuadraticForm R₂ M} (h : ∀ x, 0 ≤ Q x) (h0 : Q.Anisotropic) : PosDef Q := fun x hx =>
  lt_of_le_of_neₓ (h x) (Ne.symm fun hQx => hx <| h0 _ hQx)

theorem pos_def_iff_nonneg {Q : QuadraticForm R₂ M} : PosDef Q ↔ (∀ x, 0 ≤ Q x) ∧ Q.Anisotropic :=
  ⟨fun h => ⟨h.Nonneg, h.Anisotropic⟩, fun ⟨n, a⟩ => pos_def_of_nonneg n a⟩

theorem PosDef.add (Q Q' : QuadraticForm R₂ M) (hQ : PosDef Q) (hQ' : PosDef Q') : PosDef (Q + Q') := fun x hx =>
  add_pos (hQ x hx) (hQ' x hx)

theorem lin_mul_lin_self_pos_def {R} [LinearOrderedCommRing R] [Module R M] (f : M →ₗ[R] R) (hf : LinearMap.ker f = ⊥) :
    PosDef (linMulLin f f) := fun x hx =>
  mul_self_pos.2 fun h =>
    hx
      (LinearMap.ker_eq_bot.mp hf
        (by
          rw [h, LinearMap.map_zero]))

end PosDef

end QuadraticForm

section

/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/


variable {n : Type w} [Fintype n] [DecidableEq n]

/-- `M.to_quadratic_form` is the map `λ x, col x ⬝ M ⬝ row x` as a quadratic form. -/
def Matrix.toQuadraticForm' (M : Matrix n n R₁) : QuadraticForm R₁ (n → R₁) :=
  M.toBilin'.toQuadraticForm

variable [Invertible (2 : R₁)]

/-- A matrix representation of the quadratic form. -/
def QuadraticForm.toMatrix' (Q : QuadraticForm R₁ (n → R₁)) : Matrix n n R₁ :=
  Q.Associated.toMatrix'

open QuadraticForm

theorem QuadraticForm.to_matrix'_smul (a : R₁) (Q : QuadraticForm R₁ (n → R₁)) : (a • Q).toMatrix' = a • Q.toMatrix' :=
  by
  simp only [to_matrix', LinearEquiv.map_smul, LinearMap.map_smul]

end

namespace QuadraticForm

variable {n : Type w} [Fintype n]

variable [DecidableEq n] [Invertible (2 : R₁)]

variable {m : Type w} [DecidableEq m] [Fintype m]

open Matrix

@[simp]
theorem to_matrix'_comp (Q : QuadraticForm R₁ (m → R₁)) (f : (n → R₁) →ₗ[R₁] m → R₁) :
    (Q.comp f).toMatrix' = f.toMatrix'ᵀ ⬝ Q.toMatrix' ⬝ f.toMatrix' := by
  ext
  simp only [QuadraticForm.associated_comp, BilinForm.to_matrix'_comp, to_matrix']

section Discriminant

variable {Q : QuadraticForm R₁ (n → R₁)}

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : QuadraticForm R₁ (n → R₁)) : R₁ :=
  Q.toMatrix'.det

theorem discr_smul (a : R₁) : (a • Q).discr = a ^ Fintype.card n * Q.discr := by
  simp only [discr, to_matrix'_smul, Matrix.det_smul]

theorem discr_comp (f : (n → R₁) →ₗ[R₁] n → R₁) : (Q.comp f).discr = f.toMatrix'.det * f.toMatrix'.det * Q.discr := by
  simp only [Matrix.det_transpose, mul_left_commₓ, QuadraticForm.to_matrix'_comp, mul_comm, Matrix.det_mul, discr]

end Discriminant

end QuadraticForm

namespace QuadraticForm

end QuadraticForm

namespace BilinForm

/-- A bilinear form is nondegenerate if the quadratic form it is associated with is anisotropic. -/
theorem nondegenerate_of_anisotropic {B : BilinForm R M} (hB : B.toQuadraticForm.Anisotropic) : B.Nondegenerate :=
  fun x hx => hB _ (hx x)

/-- There exists a non-null vector with respect to any symmetric, nonzero bilinear form `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
theorem exists_bilin_form_self_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R M} (hB₁ : B ≠ 0) (hB₂ : B.IsSymm) :
    ∃ x, ¬B.IsOrtho x x := by
  lift B to QuadraticForm R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticForm.exists_quadratic_form_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply ℕ x ▸ h)⟩

open FiniteDimensional

variable {V : Type u} {K : Type v} [Field K] [AddCommGroupₓ V] [Module K V]

variable [FiniteDimensional K V]

/-- Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`. -/
theorem exists_orthogonal_basis [hK : Invertible (2 : K)] {B : BilinForm K V} (hB₂ : B.IsSymm) :
    ∃ v : Basis (Finₓ (finrank K V)) K V, B.IsOrtho v := by
  induction' hd : finrank K V with d ih generalizing V
  · exact ⟨basisOfFinrankZero hd, fun _ _ _ => zero_left _⟩
    
  have := finrank_pos_iff.1 (hd.symm ▸ Nat.succ_posₓ d : 0 < finrank K V)
  -- either the bilinear form is trivial or we can pick a non-null `x`
  obtain rfl | hB₁ := eq_or_ne B 0
  · let b := FiniteDimensional.finBasis K V
    rw [hd] at b
    refine' ⟨b, fun i j hij => rfl⟩
    
  obtain ⟨x, hx⟩ := exists_bilin_form_self_ne_zero hB₁ hB₂
  rw [← Submodule.finrank_add_eq_of_is_compl (is_compl_span_singleton_orthogonal hx).symm,
    finrank_span_singleton (ne_zero_of_not_is_ortho_self x hx)] at hd
  let B' := B.restrict (B.orthogonal <| K∙x)
  obtain ⟨v', hv₁⟩ := ih (B.restrict_symm hB₂ _ : B'.is_symm) (Nat.succ.injₓ hd)
  -- concatenate `x` with the basis obtained by induction
  let b :=
    Basis.mkFinCons x v'
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc, Submodule.neg_mem_iff] at hy
        have := (is_compl_span_singleton_orthogonal hx).Disjoint
        rw [Submodule.disjoint_def] at this
        have := this (c • x) (Submodule.smul_mem _ _ <| Submodule.mem_span_singleton_self _) hy
        exact (smul_eq_zero.1 this).resolve_right fun h => hx <| h.symm ▸ zero_left _)
      (by
        intro y
        refine' ⟨-B x y / B x x, fun z hz => _⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        rw [is_ortho, smul_left, add_right, smul_right, div_mul_cancel _ hx, add_neg_selfₓ, mul_zero])
  refine' ⟨b, _⟩
  · rw [Basis.coe_mk_fin_cons]
    intro j i
    refine' Finₓ.cases _ (fun i => _) i <;>
      refine' Finₓ.cases _ (fun j => _) j <;>
        intro hij <;> simp only [Function.onFun, Finₓ.cons_zero, Finₓ.cons_succ, Function.comp_applyₓ]
    · exact (hij rfl).elim
      
    · rw [is_ortho, hB₂]
      exact (v' j).Prop _ (Submodule.mem_span_singleton_self x)
      
    · exact (v' i).Prop _ (Submodule.mem_span_singleton_self x)
      
    · exact hv₁ _ _ (ne_of_apply_ne _ hij)
      
    

end BilinForm

namespace QuadraticForm

open BigOperators

open Finset BilinForm

variable {M₁ : Type _} [AddCommGroupₓ M₁] [Module R M₁]

variable {ι : Type _} [Fintype ι] {v : Basis ι R M}

/-- Given a quadratic form `Q` and a basis, `basis_repr` is the basis representation of `Q`. -/
noncomputable def basisRepr (Q : QuadraticForm R M) (v : Basis ι R M) : QuadraticForm R (ι → R) :=
  Q.comp v.equivFun.symm

@[simp]
theorem basis_repr_apply (Q : QuadraticForm R M) (w : ι → R) : Q.basis_repr v w = Q (∑ i : ι, w i • v i) := by
  rw [← v.equiv_fun_symm_apply]
  rfl

section

variable (R₁)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R₁` or
`[algebra S R₁]`, although this is stated more generally. -/
def weightedSumSquares [Monoidₓ S] [DistribMulAction S R₁] [SmulCommClass S R₁ R₁] (w : ι → S) :
    QuadraticForm R₁ (ι → R₁) :=
  ∑ i : ι, w i • proj i i

end

@[simp]
theorem weighted_sum_squares_apply [Monoidₓ S] [DistribMulAction S R₁] [SmulCommClass S R₁ R₁] (w : ι → S)
    (v : ι → R₁) : weightedSumSquares R₁ w v = ∑ i : ι, w i • (v i * v i) :=
  QuadraticForm.sum_apply _ _ _

/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
theorem basis_repr_eq_of_is_Ortho [Invertible (2 : R₁)] (Q : QuadraticForm R₁ M) (v : Basis ι R₁ M)
    (hv₂ : (associated Q).IsOrtho v) : Q.basis_repr v = weightedSumSquares _ fun i => Q (v i) := by
  ext w
  rw [basis_repr_apply, ← @associated_eq_self_apply R₁, sum_left, weighted_sum_squares_apply]
  refine' sum_congr rfl fun j hj => _
  rw [← @associated_eq_self_apply R₁, sum_right, sum_eq_single_of_mem j hj]
  · rw [smul_left, smul_right, smul_eq_mul]
    ring
    
  · intro i _ hij
    rw [smul_left, smul_right, show associated_hom R₁ Q (v j) (v i) = 0 from hv₂ j i hij.symm, mul_zero, mul_zero]
    

end QuadraticForm

