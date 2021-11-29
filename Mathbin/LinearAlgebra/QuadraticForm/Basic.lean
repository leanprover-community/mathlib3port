import Mathbin.Algebra.Invertible 
import Mathbin.LinearAlgebra.Matrix.Determinant 
import Mathbin.LinearAlgebra.BilinearForm

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

variable{S : Type _}

variable{R : Type _}{M : Type _}[AddCommGroupₓ M][Ringₓ R]

variable{R₁ : Type _}[CommRingₓ R₁]

namespace QuadraticForm

/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.d

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar (f : M → R) (x y : M) :=
  f (x+y) - f x - f y

theorem polar_add (f g : M → R) (x y : M) : polar (f+g) x y = polar f x y+polar g x y :=
  by 
    simp only [polar, Pi.add_apply]
    abel

theorem polar_neg (f : M → R) (x y : M) : polar (-f) x y = -polar f x y :=
  by 
    simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]

theorem polar_smul [Monoidₓ S] [DistribMulAction S R] (f : M → R) (s : S) (x y : M) :
  polar (s • f) x y = s • polar f x y :=
  by 
    simp only [polar, Pi.smul_apply, smul_sub]

theorem polar_comm (f : M → R) (x y : M) : polar f x y = polar f y x :=
  by 
    rw [polar, polar, add_commₓ, sub_sub, sub_sub, add_commₓ (f x) (f y)]

end QuadraticForm

variable[Module R M][Module R₁ M]

open QuadraticForm

/-- A quadratic form over a module. -/
structure QuadraticForm(R : Type u)(M : Type v)[Ringₓ R][AddCommGroupₓ M][Module R M] where 
  toFun : M → R 
  to_fun_smul : ∀ (a : R) (x : M), to_fun (a • x) = (a*a)*to_fun x 
  polar_add_left' : ∀ (x x' y : M), polar to_fun (x+x') y = polar to_fun x y+polar to_fun x' y 
  polar_smul_left' : ∀ (a : R) (x y : M), polar to_fun (a • x) y = a • polar to_fun x y 
  polar_add_right' : ∀ (x y y' : M), polar to_fun x (y+y') = polar to_fun x y+polar to_fun x y' 
  polar_smul_right' : ∀ (a : R) (x y : M), polar to_fun x (a • y) = a • polar to_fun x y

namespace QuadraticForm

variable{Q : QuadraticForm R M}

instance  : CoeFun (QuadraticForm R M) fun _ => M → R :=
  ⟨to_fun⟩

/-- The `simp` normal form for a quadratic form is `coe_fn`, not `to_fun`. -/
@[simp]
theorem to_fun_eq_apply : Q.to_fun = «expr⇑ » Q :=
  rfl

theorem map_smul (a : R) (x : M) : Q (a • x) = (a*a)*Q x :=
  Q.to_fun_smul a x

theorem map_add_self (x : M) : Q (x+x) = 4*Q x :=
  by 
    rw [←one_smul R x, ←add_smul, map_smul]
    normNum

@[simp]
theorem map_zero : Q 0 = 0 :=
  by 
    rw [←@zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_mul]

@[simp]
theorem map_neg (x : M) : Q (-x) = Q x :=
  by 
    rw [←@neg_one_smul R _ _ _ _ x, map_smul, neg_one_mul, neg_negₓ, one_mulₓ]

theorem map_sub (x y : M) : Q (x - y) = Q (y - x) :=
  by 
    rw [←neg_sub, map_neg]

@[simp]
theorem polar_zero_left (y : M) : polar Q 0 y = 0 :=
  by 
    simp only [polar, zero_addₓ, QuadraticForm.map_zero, sub_zero, sub_self]

@[simp]
theorem polar_add_left (x x' y : M) : polar Q (x+x') y = polar Q x y+polar Q x' y :=
  Q.polar_add_left' x x' y

@[simp]
theorem polar_smul_left (a : R) (x y : M) : polar Q (a • x) y = a*polar Q x y :=
  Q.polar_smul_left' a x y

@[simp]
theorem polar_neg_left (x y : M) : polar Q (-x) y = -polar Q x y :=
  by 
    rw [←neg_one_smul R x, polar_smul_left, neg_one_mul]

@[simp]
theorem polar_sub_left (x x' y : M) : polar Q (x - x') y = polar Q x y - polar Q x' y :=
  by 
    rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_left, polar_neg_left]

@[simp]
theorem polar_zero_right (y : M) : polar Q y 0 = 0 :=
  by 
    simp only [add_zeroₓ, polar, QuadraticForm.map_zero, sub_self]

@[simp]
theorem polar_add_right (x y y' : M) : polar Q x (y+y') = polar Q x y+polar Q x y' :=
  Q.polar_add_right' x y y'

@[simp]
theorem polar_smul_right (a : R) (x y : M) : polar Q x (a • y) = a*polar Q x y :=
  Q.polar_smul_right' a x y

@[simp]
theorem polar_neg_right (x y : M) : polar Q x (-y) = -polar Q x y :=
  by 
    rw [←neg_one_smul R y, polar_smul_right, neg_one_mul]

@[simp]
theorem polar_sub_right (x y y' : M) : polar Q x (y - y') = polar Q x y - polar Q x y' :=
  by 
    rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_right, polar_neg_right]

@[simp]
theorem polar_self (x : M) : polar Q x x = 2*Q x :=
  by 
    rw [polar, map_add_self, sub_sub, sub_eq_iff_eq_add, ←two_mul, ←two_mul, ←mul_assocₓ]
    normNum

section OfTower

variable[CommSemiringₓ S][Algebra S R][Module S M][IsScalarTower S R M]

@[simp]
theorem polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar Q x y :=
  by 
    rw [←IsScalarTower.algebra_map_smul R a x, polar_smul_left, Algebra.smul_def]

@[simp]
theorem polar_smul_right_of_tower (a : S) (x y : M) : polar Q x (a • y) = a • polar Q x y :=
  by 
    rw [←IsScalarTower.algebra_map_smul R a y, polar_smul_right, Algebra.smul_def]

end OfTower

variable{Q' : QuadraticForm R M}

@[ext]
theorem ext (H : ∀ (x : M), Q x = Q' x) : Q = Q' :=
  by 
    cases Q 
    cases Q' 
    congr 
    funext 
    apply H

theorem congr_funₓ (h : Q = Q') (x : M) : Q x = Q' x :=
  h ▸ rfl

theorem ext_iff : Q = Q' ↔ ∀ x, Q x = Q' x :=
  ⟨congr_funₓ, ext⟩

instance  : HasZero (QuadraticForm R M) :=
  ⟨{ toFun := fun x => 0,
      to_fun_smul :=
        fun a x =>
          by 
            simp only [mul_zero],
      polar_add_left' :=
        fun x x' y =>
          by 
            simp only [add_zeroₓ, polar, sub_self],
      polar_smul_left' :=
        fun a x y =>
          by 
            simp only [polar, smul_zero, sub_self],
      polar_add_right' :=
        fun x y y' =>
          by 
            simp only [add_zeroₓ, polar, sub_self],
      polar_smul_right' :=
        fun a x y =>
          by 
            simp only [polar, smul_zero, sub_self] }⟩

@[simp]
theorem coe_fn_zero : «expr⇑ » (0 : QuadraticForm R M) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : M) : (0 : QuadraticForm R M) x = 0 :=
  rfl

instance  : Inhabited (QuadraticForm R M) :=
  ⟨0⟩

instance  : Add (QuadraticForm R M) :=
  ⟨fun Q Q' =>
      { toFun := Q+Q',
        to_fun_smul :=
          fun a x =>
            by 
              simp only [Pi.add_apply, map_smul, mul_addₓ],
        polar_add_left' :=
          fun x x' y =>
            by 
              simp only [polar_add, polar_add_left, add_assocₓ, add_left_commₓ],
        polar_smul_left' :=
          fun a x y =>
            by 
              simp only [polar_add, smul_eq_mul, mul_addₓ, polar_smul_left],
        polar_add_right' :=
          fun x y y' =>
            by 
              simp only [polar_add, polar_add_right, add_assocₓ, add_left_commₓ],
        polar_smul_right' :=
          fun a x y =>
            by 
              simp only [polar_add, smul_eq_mul, mul_addₓ, polar_smul_right] }⟩

@[simp]
theorem coe_fn_add (Q Q' : QuadraticForm R M) : «expr⇑ » (Q+Q') = Q+Q' :=
  rfl

@[simp]
theorem add_apply (Q Q' : QuadraticForm R M) (x : M) : (Q+Q') x = Q x+Q' x :=
  rfl

instance  : Neg (QuadraticForm R M) :=
  ⟨fun Q =>
      { toFun := -Q,
        to_fun_smul :=
          fun a x =>
            by 
              simp only [Pi.neg_apply, map_smul, mul_neg_eq_neg_mul_symm],
        polar_add_left' :=
          fun x x' y =>
            by 
              simp only [polar_neg, polar_add_left, neg_add],
        polar_smul_left' :=
          fun a x y =>
            by 
              simp only [polar_neg, polar_smul_left, mul_neg_eq_neg_mul_symm, smul_eq_mul],
        polar_add_right' :=
          fun x y y' =>
            by 
              simp only [polar_neg, polar_add_right, neg_add],
        polar_smul_right' :=
          fun a x y =>
            by 
              simp only [polar_neg, polar_smul_right, mul_neg_eq_neg_mul_symm, smul_eq_mul] }⟩

@[simp]
theorem coe_fn_neg (Q : QuadraticForm R M) : «expr⇑ » (-Q) = -Q :=
  rfl

@[simp]
theorem neg_apply (Q : QuadraticForm R M) (x : M) : (-Q) x = -Q x :=
  rfl

instance  : AddCommGroupₓ (QuadraticForm R M) :=
  { add := ·+·, zero := 0, neg := Neg.neg,
    add_comm :=
      fun Q Q' =>
        by 
          ext 
          simp only [add_apply, add_commₓ],
    add_assoc :=
      fun Q Q' Q'' =>
        by 
          ext 
          simp only [add_apply, add_assocₓ],
    add_left_neg :=
      fun Q =>
        by 
          ext 
          simp only [add_apply, neg_apply, zero_apply, add_left_negₓ],
    add_zero :=
      fun Q =>
        by 
          ext 
          simp only [zero_apply, add_apply, add_zeroₓ],
    zero_add :=
      fun Q =>
        by 
          ext 
          simp only [zero_apply, add_apply, zero_addₓ] }

@[simp]
theorem coe_fn_sub (Q Q' : QuadraticForm R M) : «expr⇑ » (Q - Q') = Q - Q' :=
  by 
    simp only [QuadraticForm.coe_fn_neg, add_left_injₓ, QuadraticForm.coe_fn_add, sub_eq_add_neg]

@[simp]
theorem sub_apply (Q Q' : QuadraticForm R M) (x : M) : (Q - Q') x = Q x - Q' x :=
  by 
    simp only [QuadraticForm.neg_apply, add_left_injₓ, QuadraticForm.add_apply, sub_eq_add_neg]

/-- `@coe_fn (quadratic_form R M)` as an `add_monoid_hom`.

This API mirrors `add_monoid_hom.coe_fn`. -/
@[simps apply]
def coe_fn_add_monoid_hom : QuadraticForm R M →+ M → R :=
  { toFun := coeFn, map_zero' := coe_fn_zero, map_add' := coe_fn_add }

/-- Evaluation on a particular element of the module `M` is an additive map over quadratic forms. -/
@[simps apply]
def eval_add_monoid_hom (m : M) : QuadraticForm R M →+ R :=
  (Pi.evalAddMonoidHom _ m).comp coe_fn_add_monoid_hom

section Sum

open_locale BigOperators

@[simp]
theorem coe_fn_sum {ι : Type _} (Q : ι → QuadraticForm R M) (s : Finset ι) : «expr⇑ » (∑i in s, Q i) = ∑i in s, Q i :=
  (coe_fn_add_monoid_hom : _ →+ M → R).map_sum Q s

@[simp]
theorem sum_apply {ι : Type _} (Q : ι → QuadraticForm R M) (s : Finset ι) (x : M) : (∑i in s, Q i) x = ∑i in s, Q i x :=
  (eval_add_monoid_hom x : _ →+ R).map_sum Q s

end Sum

section HasScalar

variable[Monoidₓ S][DistribMulAction S R][SmulCommClass S R R]

/-- `quadratic_form R M` inherits the scalar action from any algebra over `R`.

When `R` is commutative, this provides an `R`-action via `algebra.id`. -/
instance  : HasScalar S (QuadraticForm R M) :=
  ⟨fun a Q =>
      { toFun := a • Q,
        to_fun_smul :=
          fun b x =>
            by 
              rw [Pi.smul_apply, map_smul, Pi.smul_apply, mul_smul_comm],
        polar_add_left' :=
          fun x x' y =>
            by 
              simp only [polar_smul, polar_add_left, smul_add],
        polar_smul_left' :=
          fun b x y =>
            by 
              simp only [polar_smul, polar_smul_left, ←mul_smul_comm, smul_eq_mul],
        polar_add_right' :=
          fun x y y' =>
            by 
              simp only [polar_smul, polar_add_right, smul_add],
        polar_smul_right' :=
          fun b x y =>
            by 
              simp only [polar_smul, polar_smul_right, ←mul_smul_comm, smul_eq_mul] }⟩

@[simp]
theorem coe_fn_smul (a : S) (Q : QuadraticForm R M) : «expr⇑ » (a • Q) = a • Q :=
  rfl

@[simp]
theorem smul_apply (a : S) (Q : QuadraticForm R M) (x : M) : (a • Q) x = a • Q x :=
  rfl

instance  : DistribMulAction S (QuadraticForm R M) :=
  { mul_smul :=
      fun a b Q =>
        ext
          fun x =>
            by 
              simp only [smul_apply, mul_smul],
    one_smul :=
      fun Q =>
        ext
          fun x =>
            by 
              simp only [QuadraticForm.smul_apply, one_smul],
    smul_add :=
      fun a Q Q' =>
        by 
          ext 
          simp only [add_apply, smul_apply, smul_add],
    smul_zero :=
      fun a =>
        by 
          ext 
          simp only [zero_apply, smul_apply, smul_zero] }

end HasScalar

section Module

instance  [Semiringₓ S] [Module S R] [SmulCommClass S R R] : Module S (QuadraticForm R M) :=
  { zero_smul :=
      fun Q =>
        by 
          ext 
          simp only [zero_apply, smul_apply, zero_smul],
    add_smul :=
      fun a b Q =>
        by 
          ext 
          simp only [add_apply, smul_apply, add_smul] }

end Module

section Comp

variable{N : Type v}[AddCommGroupₓ N][Module R N]

/-- Compose the quadratic form with a linear function. -/
def comp (Q : QuadraticForm R N) (f : M →ₗ[R] N) : QuadraticForm R M :=
  { toFun := fun x => Q (f x),
    to_fun_smul :=
      fun a x =>
        by 
          simp only [map_smul, f.map_smul],
    polar_add_left' :=
      fun x x' y =>
        by 
          convert polar_add_left (f x) (f x') (f y) using 1 <;> simp only [polar, f.map_add],
    polar_smul_left' :=
      fun a x y =>
        by 
          convert polar_smul_left a (f x) (f y) using 1 <;> simp only [polar, f.map_smul, f.map_add, smul_eq_mul],
    polar_add_right' :=
      fun x y y' =>
        by 
          convert polar_add_right (f x) (f y) (f y') using 1 <;> simp only [polar, f.map_add],
    polar_smul_right' :=
      fun a x y =>
        by 
          convert polar_smul_right a (f x) (f y) using 1 <;> simp only [polar, f.map_smul, f.map_add, smul_eq_mul] }

@[simp]
theorem comp_apply (Q : QuadraticForm R N) (f : M →ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
  rfl

end Comp

section CommRingₓ

/-- Create a quadratic form in a commutative ring by proving only one side of the bilinearity. -/
def mk_left (f : M → R₁) (to_fun_smul : ∀ a x, f (a • x) = (a*a)*f x)
  (polar_add_left : ∀ x x' y, polar f (x+x') y = polar f x y+polar f x' y)
  (polar_smul_left : ∀ a x y, polar f (a • x) y = a*polar f x y) : QuadraticForm R₁ M :=
  { toFun := f, to_fun_smul, polar_add_left' := polar_add_left, polar_smul_left' := polar_smul_left,
    polar_add_right' :=
      fun x y y' =>
        by 
          rw [polar_comm, polar_add_left, polar_comm f y x, polar_comm f y' x],
    polar_smul_right' :=
      fun a x y =>
        by 
          rw [polar_comm, polar_smul_left, polar_comm f y x, smul_eq_mul] }

/-- The product of linear forms is a quadratic form. -/
def lin_mul_lin (f g : M →ₗ[R₁] R₁) : QuadraticForm R₁ M :=
  mk_left (f*g)
    (fun a x =>
      by 
        simp only [smul_eq_mul, RingHom.id_apply, Pi.mul_apply, LinearMap.map_smulₛₗ]
        ring)
    (fun x x' y =>
      by 
        simp only [polar, Pi.mul_apply, LinearMap.map_add]
        ring)
    fun a x y =>
      by 
        simp only [polar, Pi.mul_apply, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
        ring

@[simp]
theorem lin_mul_lin_apply (f g : M →ₗ[R₁] R₁) x : lin_mul_lin f g x = f x*g x :=
  rfl

@[simp]
theorem add_lin_mul_lin (f g h : M →ₗ[R₁] R₁) : lin_mul_lin (f+g) h = lin_mul_lin f h+lin_mul_lin g h :=
  ext fun x => add_mulₓ _ _ _

@[simp]
theorem lin_mul_lin_add (f g h : M →ₗ[R₁] R₁) : lin_mul_lin f (g+h) = lin_mul_lin f g+lin_mul_lin f h :=
  ext fun x => mul_addₓ _ _ _

variable{N : Type v}[AddCommGroupₓ N][Module R₁ N]

@[simp]
theorem lin_mul_lin_comp (f g : M →ₗ[R₁] R₁) (h : N →ₗ[R₁] M) :
  (lin_mul_lin f g).comp h = lin_mul_lin (f.comp h) (g.comp h) :=
  rfl

variable{n : Type _}

/-- `proj i j` is the quadratic form mapping the vector `x : n → R₁` to `x i * x j` -/
def proj (i j : n) : QuadraticForm R₁ (n → R₁) :=
  lin_mul_lin (@LinearMap.proj _ _ _ (fun _ => R₁) _ _ i) (@LinearMap.proj _ _ _ (fun _ => R₁) _ _ j)

@[simp]
theorem proj_apply (i j : n) (x : n → R₁) : proj i j x = x i*x j :=
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


variable{B : BilinForm R M}

namespace BilinForm

open QuadraticForm

theorem polar_to_quadratic_form (x y : M) : polar (fun x => B x x) x y = B x y+B y x :=
  by 
    simp only [add_assocₓ, add_sub_cancel', add_right, polar, add_left_injₓ, add_neg_cancel_left, add_left,
      sub_eq_add_neg _ (B y y), add_commₓ (B y x) _]

/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def to_quadratic_form (B : BilinForm R M) : QuadraticForm R M :=
  ⟨fun x => B x x,
    fun a x =>
      by 
        simp only [mul_assocₓ, smul_right, smul_left],
    fun x x' y =>
      by 
        simp only [add_assocₓ, add_right, add_left_injₓ, polar_to_quadratic_form, add_left, add_left_commₓ],
    fun a x y =>
      by 
        simp only [smul_add, add_left_injₓ, polar_to_quadratic_form, smul_right, smul_eq_mul, smul_left, smul_right,
          mul_addₓ],
    fun x y y' =>
      by 
        simp only [add_assocₓ, add_right, add_left_injₓ, polar_to_quadratic_form, add_left, add_left_commₓ],
    fun a x y =>
      by 
        simp only [smul_add, add_left_injₓ, polar_to_quadratic_form, smul_right, smul_eq_mul, smul_left, smul_right,
          mul_addₓ]⟩

@[simp]
theorem to_quadratic_form_apply (B : BilinForm R M) (x : M) : B.to_quadratic_form x = B x x :=
  rfl

section 

variable(R M)

@[simp]
theorem to_quadratic_form_zero : (0 : BilinForm R M).toQuadraticForm = 0 :=
  rfl

end 

end BilinForm

namespace QuadraticForm

open BilinForm

section AssociatedHom

variable(S)[CommSemiringₓ S][Algebra S R]

variable[Invertible (2 : R)]{B₁ : BilinForm R M}

-- error in LinearAlgebra.QuadraticForm.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `associated_hom` is the map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative subring of `R`.

Over a commutative ring, use `associated`, which gives an `R`-linear map.  Over a general ring with
no nontrivial distinguished commutative subring, use `associated'`, which gives an additive
homomorphism (or more precisely a `ℤ`-linear map.) -/
def associated_hom : «expr →ₗ[ ] »(quadratic_form R M, S, bilin_form R M) :=
{ to_fun := λ
  Q, { bilin := λ x y, «expr * »(«expr⅟»() 2, polar Q x y),
    bilin_add_left := λ x y z, by rw ["[", "<-", expr mul_add, ",", expr polar_add_left, "]"] [],
    bilin_smul_left := λ x y z, begin
      have [ident htwo] [":", expr «expr = »(«expr * »(x, «expr⅟»() 2), «expr * »(«expr⅟»() 2, x))] [":=", expr (commute.one_right x).bit0_right.inv_of_right],
      simp [] [] ["only"] ["[", expr polar_smul_left, ",", "<-", expr mul_assoc, ",", expr htwo, "]"] [] []
    end,
    bilin_add_right := λ x y z, by rw ["[", "<-", expr mul_add, ",", expr polar_add_right, "]"] [],
    bilin_smul_right := λ x y z, begin
      have [ident htwo] [":", expr «expr = »(«expr * »(x, «expr⅟»() 2), «expr * »(«expr⅟»() 2, x))] [":=", expr (commute.one_right x).bit0_right.inv_of_right],
      simp [] [] ["only"] ["[", expr polar_smul_right, ",", "<-", expr mul_assoc, ",", expr htwo, "]"] [] []
    end },
  map_add' := λ Q Q', by { ext [] [] [],
    simp [] [] ["only"] ["[", expr bilin_form.add_apply, ",", expr coe_fn_mk, ",", expr polar_add, ",", expr coe_fn_add, ",", expr mul_add, "]"] [] [] },
  map_smul' := λ s Q, by { ext [] [] [],
    simp [] [] ["only"] ["[", expr ring_hom.id_apply, ",", expr polar_smul, ",", expr algebra.mul_smul_comm, ",", expr coe_fn_mk, ",", expr coe_fn_smul, ",", expr bilin_form.smul_apply, "]"] [] [] } }

variable(Q : QuadraticForm R M)(S)

@[simp]
theorem associated_apply (x y : M) : associated_hom S Q x y = ⅟ 2*Q (x+y) - Q x - Q y :=
  rfl

theorem associated_is_symm : (associated_hom S Q).IsSymm :=
  fun x y =>
    by 
      simp only [associated_apply, add_commₓ, add_left_commₓ, sub_eq_add_neg]

@[simp]
theorem associated_comp {N : Type v} [AddCommGroupₓ N] [Module R N] (f : N →ₗ[R] M) :
  associated_hom S (Q.comp f) = (associated_hom S Q).comp f f :=
  by 
    ext 
    simp only [QuadraticForm.comp_apply, BilinForm.comp_apply, associated_apply, LinearMap.map_add]

theorem associated_to_quadratic_form (B : BilinForm R M) (x y : M) :
  associated_hom S B.to_quadratic_form x y = ⅟ 2*B x y+B y x :=
  by 
    simp only [associated_apply, ←polar_to_quadratic_form, polar, to_quadratic_form_apply]

theorem associated_left_inverse (h : B₁.is_symm) : associated_hom S B₁.to_quadratic_form = B₁ :=
  BilinForm.ext$
    fun x y =>
      by 
        rw [associated_to_quadratic_form, is_symm.eq h x y, ←two_mul, ←mul_assocₓ, inv_of_mul_self, one_mulₓ]

theorem to_quadratic_form_associated : (associated_hom S Q).toQuadraticForm = Q :=
  QuadraticForm.ext$
    fun x =>
      calc (associated_hom S Q).toQuadraticForm x = ⅟ 2*Q x+Q x :=
        by 
          simp only [add_assocₓ, add_sub_cancel', one_mulₓ, to_quadratic_form_apply, add_mulₓ, associated_apply,
            map_add_self, bit0]
        _ = Q x :=
        by 
          rw [←two_mul (Q x), ←mul_assocₓ, inv_of_mul_self, one_mulₓ]
        

theorem associated_right_inverse :
  Function.RightInverse (associated_hom S) (BilinForm.toQuadraticForm : _ → QuadraticForm R M) :=
  fun Q => to_quadratic_form_associated S Q

theorem associated_eq_self_apply (x : M) : associated_hom S Q x x = Q x :=
  by 
    rw [associated_apply, map_add_self]
    suffices  : (⅟ 2*2*Q x) = Q x
    ·
      convert this 
      simp only [bit0, add_mulₓ, one_mulₓ]
      abel 
    simp only [←mul_assocₓ, one_mulₓ, inv_of_mul_self]

/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
abbrev associated' : QuadraticForm R M →ₗ[ℤ] BilinForm R M :=
  associated_hom ℤ

/-- Symmetric bilinear forms can be lifted to quadratic forms -/
instance  : CanLift (BilinForm R M) (QuadraticForm R M) :=
  { coe := associated_hom ℕ, cond := BilinForm.IsSymm,
    prf := fun B hB => ⟨B.to_quadratic_form, associated_left_inverse _ hB⟩ }

/-- There exists a non-null vector with respect to any quadratic form `Q` whose associated
bilinear form is non-zero, i.e. there exists `x` such that `Q x ≠ 0`. -/
theorem exists_quadratic_form_ne_zero {Q : QuadraticForm R M} (hB₁ : Q.associated' ≠ 0) : ∃ x, Q x ≠ 0 :=
  by 
    rw [←not_forall]
    intro h 
    apply hB₁ 
    rw [(QuadraticForm.ext h : Q = 0), LinearMap.map_zero]

end AssociatedHom

section Associated

variable[Invertible (2 : R₁)]

/-- `associated` is the linear map that sends a quadratic form over a commutative ring to its
associated symmetric bilinear form. -/
abbrev Associated : QuadraticForm R₁ M →ₗ[R₁] BilinForm R₁ M :=
  associated_hom R₁

@[simp]
theorem associated_lin_mul_lin (f g : M →ₗ[R₁] R₁) :
  (lin_mul_lin f g).Associated = ⅟ (2 : R₁) • BilinForm.linMulLin f g+BilinForm.linMulLin g f :=
  by 
    ext 
    simp only [smul_add, Algebra.id.smul_eq_mul, BilinForm.lin_mul_lin_apply, QuadraticForm.lin_mul_lin_apply,
      BilinForm.smul_apply, associated_apply, BilinForm.add_apply, LinearMap.map_add]
    ring

end Associated

section Anisotropic

/-- An anisotropic quadratic form is zero only on zero vectors. -/
def anisotropic (Q : QuadraticForm R M) : Prop :=
  ∀ x, Q x = 0 → x = 0

theorem not_anisotropic_iff_exists (Q : QuadraticForm R M) : ¬anisotropic Q ↔ ∃ (x : _)(_ : x ≠ 0), Q x = 0 :=
  by 
    simp only [anisotropic, not_forall, exists_prop, and_comm]

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
theorem nondegenerate_of_anisotropic [Invertible (2 : R)] (Q : QuadraticForm R M) (hB : Q.anisotropic) :
  Q.associated'.nondegenerate :=
  by 
    intro x hx 
    refine' hB _ _ 
    rw [←hx x]
    exact (associated_eq_self_apply _ _ x).symm

end Anisotropic

section PosDef

variable{R₂ : Type u}[OrderedRing R₂][Module R₂ M]{Q₂ : QuadraticForm R₂ M}

/-- A positive definite quadratic form is positive on nonzero vectors. -/
def pos_def (Q₂ : QuadraticForm R₂ M) : Prop :=
  ∀ x (_ : x ≠ 0), 0 < Q₂ x

theorem pos_def.smul {R} [LinearOrderedCommRing R] [Module R M] {Q : QuadraticForm R M} (h : pos_def Q) {a : R}
  (a_pos : 0 < a) : pos_def (a • Q) :=
  fun x hx => mul_pos a_pos (h x hx)

variable{n : Type _}

theorem pos_def.add (Q Q' : QuadraticForm R₂ M) (hQ : pos_def Q) (hQ' : pos_def Q') : pos_def (Q+Q') :=
  fun x hx => add_pos (hQ x hx) (hQ' x hx)

theorem lin_mul_lin_self_pos_def {R} [LinearOrderedCommRing R] [Module R M] (f : M →ₗ[R] R) (hf : LinearMap.ker f = ⊥) :
  pos_def (lin_mul_lin f f) :=
  fun x hx =>
    mul_self_pos
      fun h =>
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


variable{n : Type w}[Fintype n][DecidableEq n]

/-- `M.to_quadratic_form` is the map `λ x, col x ⬝ M ⬝ row x` as a quadratic form. -/
def Matrix.toQuadraticForm' (M : Matrix n n R₁) : QuadraticForm R₁ (n → R₁) :=
  M.to_bilin'.to_quadratic_form

variable[Invertible (2 : R₁)]

/-- A matrix representation of the quadratic form. -/
def QuadraticForm.toMatrix' (Q : QuadraticForm R₁ (n → R₁)) : Matrix n n R₁ :=
  Q.associated.to_matrix'

open QuadraticForm

theorem QuadraticForm.to_matrix'_smul (a : R₁) (Q : QuadraticForm R₁ (n → R₁)) : (a • Q).toMatrix' = a • Q.to_matrix' :=
  by 
    simp only [to_matrix', LinearEquiv.map_smul, LinearMap.map_smul]

end 

namespace QuadraticForm

variable{n : Type w}[Fintype n]

variable[DecidableEq n][Invertible (2 : R₁)]

variable{m : Type w}[DecidableEq m][Fintype m]

open_locale Matrix

@[simp]
theorem to_matrix'_comp (Q : QuadraticForm R₁ (m → R₁)) (f : (n → R₁) →ₗ[R₁] m → R₁) :
  (Q.comp f).toMatrix' = (f.to_matrix')ᵀ ⬝ Q.to_matrix' ⬝ f.to_matrix' :=
  by 
    ext 
    simp only [QuadraticForm.associated_comp, BilinForm.to_matrix'_comp, to_matrix']

section Discriminant

variable{Q : QuadraticForm R₁ (n → R₁)}

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : QuadraticForm R₁ (n → R₁)) : R₁ :=
  Q.to_matrix'.det

theorem discr_smul (a : R₁) : (a • Q).discr = (a^Fintype.card n)*Q.discr :=
  by 
    simp only [discr, to_matrix'_smul, Matrix.det_smul]

theorem discr_comp (f : (n → R₁) →ₗ[R₁] n → R₁) : (Q.comp f).discr = (f.to_matrix'.det*f.to_matrix'.det)*Q.discr :=
  by 
    simp only [Matrix.det_transpose, mul_left_commₓ, QuadraticForm.to_matrix'_comp, mul_commₓ, Matrix.det_mul, discr]

end Discriminant

end QuadraticForm

namespace QuadraticForm

variable{M₁ : Type _}{M₂ : Type _}{M₃ : Type _}

variable[AddCommGroupₓ M₁][AddCommGroupₓ M₂][AddCommGroupₓ M₃]

variable[Module R M₁][Module R M₂][Module R M₃]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
@[nolint has_inhabited_instance]
structure isometry(Q₁ : QuadraticForm R M₁)(Q₂ : QuadraticForm R M₂) extends M₁ ≃ₗ[R] M₂ where 
  map_app' : ∀ m, Q₂ (to_fun m) = Q₁ m

/-- Two quadratic forms over a ring `R` are equivalent
if there exists an isometry between them:
a linear equivalence that transforms one quadratic form into the other. -/
def equivalent (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :=
  Nonempty (Q₁.isometry Q₂)

namespace Isometry

variable{Q₁ : QuadraticForm R M₁}{Q₂ : QuadraticForm R M₂}{Q₃ : QuadraticForm R M₃}

instance  : Coe (Q₁.isometry Q₂) (M₁ ≃ₗ[R] M₂) :=
  ⟨isometry.to_linear_equiv⟩

@[simp]
theorem to_linear_equiv_eq_coe (f : Q₁.isometry Q₂) : f.to_linear_equiv = f :=
  rfl

instance  : CoeFun (Q₁.isometry Q₂) fun _ => M₁ → M₂ :=
  ⟨fun f => «expr⇑ » (f : M₁ ≃ₗ[R] M₂)⟩

@[simp]
theorem coe_to_linear_equiv (f : Q₁.isometry Q₂) : «expr⇑ » (f : M₁ ≃ₗ[R] M₂) = f :=
  rfl

@[simp]
theorem map_app (f : Q₁.isometry Q₂) (m : M₁) : Q₂ (f m) = Q₁ m :=
  f.map_app' m

/-- The identity isometry from a quadratic form to itself. -/
@[refl]
def refl (Q : QuadraticForm R M) : Q.isometry Q :=
  { LinearEquiv.refl R M with map_app' := fun m => rfl }

/-- The inverse isometry of an isometry between two quadratic forms. -/
@[symm]
def symm (f : Q₁.isometry Q₂) : Q₂.isometry Q₁ :=
  { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' :=
      by 
        intro m 
        rw [←f.map_app]
        congr 
        exact f.to_linear_equiv.apply_symm_apply m }

/-- The composition of two isometries between quadratic forms. -/
@[trans]
def trans (f : Q₁.isometry Q₂) (g : Q₂.isometry Q₃) : Q₁.isometry Q₃ :=
  { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' :=
      by 
        intro m 
        rw [←f.map_app, ←g.map_app]
        rfl }

end Isometry

namespace Equivalent

variable{Q₁ : QuadraticForm R M₁}{Q₂ : QuadraticForm R M₂}{Q₃ : QuadraticForm R M₃}

@[refl]
theorem refl (Q : QuadraticForm R M) : Q.equivalent Q :=
  ⟨isometry.refl Q⟩

@[symm]
theorem symm (h : Q₁.equivalent Q₂) : Q₂.equivalent Q₁ :=
  h.elim$ fun f => ⟨f.symm⟩

@[trans]
theorem trans (h : Q₁.equivalent Q₂) (h' : Q₂.equivalent Q₃) : Q₁.equivalent Q₃ :=
  h'.elim$ h.elim$ fun f g => ⟨f.trans g⟩

end Equivalent

end QuadraticForm

namespace BilinForm

/-- A bilinear form is nondegenerate if the quadratic form it is associated with is anisotropic. -/
theorem nondegenerate_of_anisotropic {B : BilinForm R M} (hB : B.to_quadratic_form.anisotropic) : B.nondegenerate :=
  fun x hx => hB _ (hx x)

/-- There exists a non-null vector with respect to any symmetric, nonzero bilinear form `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
theorem exists_bilin_form_self_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R M} (hB₁ : B ≠ 0) (hB₂ : B.is_symm) :
  ∃ x, ¬B.is_ortho x x :=
  by 
    lift B to QuadraticForm R M using hB₂ with Q 
    obtain ⟨x, hx⟩ := QuadraticForm.exists_quadratic_form_ne_zero hB₁ 
    exact ⟨x, fun h => hx (Q.associated_eq_self_apply ℕ x ▸ h)⟩

open FiniteDimensional

variable{V : Type u}{K : Type v}[Field K][AddCommGroupₓ V][Module K V]

variable[FiniteDimensional K V]

-- error in LinearAlgebra.QuadraticForm.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`. -/
theorem exists_orthogonal_basis
[hK : invertible (2 : K)]
{B : bilin_form K V}
(hB₂ : B.is_symm) : «expr∃ , »((v : basis (fin (finrank K V)) K V), B.is_Ortho v) :=
begin
  tactic.unfreeze_local_instances,
  induction [expr hd, ":", expr finrank K V] [] ["with", ident d, ident ih] ["generalizing", ident V],
  { exact [expr ⟨basis_of_finrank_zero hd, λ _ _ _, zero_left _⟩] },
  haveI [] [] [":=", expr finrank_pos_iff.1 («expr ▸ »(hd.symm, nat.succ_pos d) : «expr < »(0, finrank K V))],
  obtain [ident rfl, "|", ident hB₁, ":=", expr eq_or_ne B 0],
  { let [ident b] [] [":=", expr finite_dimensional.fin_basis K V],
    rw [expr hd] ["at", ident b],
    refine [expr ⟨b, λ i j hij, rfl⟩] },
  obtain ["⟨", ident x, ",", ident hx, "⟩", ":=", expr exists_bilin_form_self_ne_zero hB₁ hB₂],
  rw ["[", "<-", expr submodule.finrank_add_eq_of_is_compl (is_compl_span_singleton_orthogonal hx).symm, ",", expr finrank_span_singleton (ne_zero_of_not_is_ortho_self x hx), "]"] ["at", ident hd],
  let [ident B'] [] [":=", expr B.restrict «expr $ »(B.orthogonal, «expr ∙ »(K, x))],
  obtain ["⟨", ident v', ",", ident hv₁, "⟩", ":=", expr ih (B.restrict_symm hB₂ _ : B'.is_symm) (nat.succ.inj hd)],
  let [ident b] [] [":=", expr basis.mk_fin_cons x v' (begin
      rintros [ident c, ident y, ident hy, ident hc],
      rw [expr add_eq_zero_iff_neg_eq] ["at", ident hc],
      rw ["[", "<-", expr hc, ",", expr submodule.neg_mem_iff, "]"] ["at", ident hy],
      have [] [] [":=", expr (is_compl_span_singleton_orthogonal hx).disjoint],
      rw [expr submodule.disjoint_def] ["at", ident this],
      have [] [] [":=", expr this «expr • »(c, x) «expr $ »(submodule.smul_mem _ _, submodule.mem_span_singleton_self _) hy],
      exact [expr (smul_eq_zero.1 this).resolve_right (λ h, «expr $ »(hx, «expr ▸ »(h.symm, zero_left _)))]
    end) (begin
      intro [ident y],
      refine [expr ⟨«expr / »(«expr- »(B x y), B x x), λ z hz, _⟩],
      obtain ["⟨", ident c, ",", ident rfl, "⟩", ":=", expr submodule.mem_span_singleton.1 hz],
      rw ["[", expr is_ortho, ",", expr smul_left, ",", expr add_right, ",", expr smul_right, ",", expr div_mul_cancel _ hx, ",", expr add_neg_self, ",", expr mul_zero, "]"] []
    end)],
  refine [expr ⟨b, _⟩],
  { rw [expr basis.coe_mk_fin_cons] [],
    intros [ident j, ident i],
    refine [expr fin.cases _ (λ
      i, _) i]; refine [expr fin.cases _ (λ
      j, _) j]; intro [ident hij]; simp [] [] ["only"] ["[", expr function.on_fun, ",", expr fin.cons_zero, ",", expr fin.cons_succ, ",", expr function.comp_apply, "]"] [] [],
    { exact [expr (hij rfl).elim] },
    { rw ["[", expr is_ortho, ",", expr hB₂, "]"] [],
      exact [expr (v' j).prop _ (submodule.mem_span_singleton_self x)] },
    { exact [expr (v' i).prop _ (submodule.mem_span_singleton_self x)] },
    { exact [expr hv₁ _ _ (ne_of_apply_ne _ hij)] } }
end

end BilinForm

namespace QuadraticForm

open_locale BigOperators

open Finset BilinForm

variable{M₁ : Type _}[AddCommGroupₓ M₁][Module R M₁]

variable{ι : Type _}[Fintype ι]{v : Basis ι R M}

/-- A quadratic form composed with a `linear_equiv` is isometric to itself. -/
def isometry_of_comp_linear_equiv (Q : QuadraticForm R M) (f : M₁ ≃ₗ[R] M) : Q.isometry (Q.comp (f : M₁ →ₗ[R] M)) :=
  { f.symm with
    map_app' :=
      by 
        intro 
        simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.to_fun_eq_coe, LinearEquiv.apply_symm_apply,
          f.apply_symm_apply] }

/-- Given a quadratic form `Q` and a basis, `basis_repr` is the basis representation of `Q`. -/
noncomputable def basis_repr (Q : QuadraticForm R M) (v : Basis ι R M) : QuadraticForm R (ι → R) :=
  Q.comp v.equiv_fun.symm

@[simp]
theorem basis_repr_apply (Q : QuadraticForm R M) (w : ι → R) : Q.basis_repr v w = Q (∑i : ι, w i • v i) :=
  by 
    rw [←v.equiv_fun_symm_apply]
    rfl

/-- A quadratic form is isometric to its bases representations. -/
noncomputable def isometry_basis_repr (Q : QuadraticForm R M) (v : Basis ι R M) : isometry Q (Q.basis_repr v) :=
  isometry_of_comp_linear_equiv Q v.equiv_fun.symm

section 

variable(R₁)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R₁` or
`[algebra S R₁]`, although this is stated more generally. -/
def weighted_sum_squares [Monoidₓ S] [DistribMulAction S R₁] [SmulCommClass S R₁ R₁] (w : ι → S) :
  QuadraticForm R₁ (ι → R₁) :=
  ∑i : ι, w i • proj i i

end 

@[simp]
theorem weighted_sum_squares_apply [Monoidₓ S] [DistribMulAction S R₁] [SmulCommClass S R₁ R₁] (w : ι → S)
  (v : ι → R₁) : weighted_sum_squares R₁ w v = ∑i : ι, w i • v i*v i :=
  QuadraticForm.sum_apply _ _ _

/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
theorem basis_repr_eq_of_is_Ortho [Invertible (2 : R₁)] (Q : QuadraticForm R₁ M) (v : Basis ι R₁ M)
  (hv₂ : (Associated Q).IsOrtho v) : Q.basis_repr v = weighted_sum_squares _ fun i => Q (v i) :=
  by 
    ext w 
    rw [basis_repr_apply, ←@associated_eq_self_apply R₁, sum_left, weighted_sum_squares_apply]
    refine' sum_congr rfl fun j hj => _ 
    rw [←@associated_eq_self_apply R₁, sum_right, sum_eq_single_of_mem j hj]
    ·
      rw [smul_left, smul_right, smul_eq_mul]
      ring
    ·
      intro i _ hij 
      rw [smul_left, smul_right, show associated_hom R₁ Q (v j) (v i) = 0 from hv₂ j i hij.symm, mul_zero, mul_zero]

variable{V : Type _}{K : Type _}[Field K][Invertible (2 : K)]

variable[AddCommGroupₓ V][Module K V]

/-- Given an orthogonal basis, a quadratic form is isometric with a weighted sum of squares. -/
noncomputable def isometry_weighted_sum_squares (Q : QuadraticForm K V)
  (v : Basis (Finₓ (FiniteDimensional.finrank K V)) K V) (hv₁ : (Associated Q).IsOrtho v) :
  Q.isometry (weighted_sum_squares K fun i => Q (v i)) :=
  by 
    let iso := Q.isometry_basis_repr v 
    refine' ⟨iso, fun m => _⟩
    convert iso.map_app m 
    rw [basis_repr_eq_of_is_Ortho _ _ hv₁]

variable[FiniteDimensional K V]

theorem equivalent_weighted_sum_squares (Q : QuadraticForm K V) :
  ∃ w : Finₓ (FiniteDimensional.finrank K V) → K, equivalent Q (weighted_sum_squares K w) :=
  let ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_is_symm _ Q)
  ⟨_, ⟨Q.isometry_weighted_sum_squares v hv₁⟩⟩

-- error in LinearAlgebra.QuadraticForm.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem equivalent_weighted_sum_squares_units_of_nondegenerate'
(Q : quadratic_form K V)
(hQ : (associated Q).nondegenerate) : «expr∃ , »((w : fin (finite_dimensional.finrank K V) → units K), equivalent Q (weighted_sum_squares K w)) :=
begin
  obtain ["⟨", ident v, ",", ident hv₁, "⟩", ":=", expr exists_orthogonal_basis (associated_is_symm _ Q)],
  have [ident hv₂] [] [":=", expr hv₁.not_is_ortho_basis_self_of_nondegenerate hQ],
  simp_rw ["[", expr is_ortho, ",", expr associated_eq_self_apply, "]"] ["at", ident hv₂],
  exact [expr ⟨λ i, units.mk0 _ (hv₂ i), ⟨Q.isometry_weighted_sum_squares v hv₁⟩⟩]
end

end QuadraticForm

