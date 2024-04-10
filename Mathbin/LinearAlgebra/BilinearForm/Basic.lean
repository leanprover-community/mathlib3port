/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import LinearAlgebra.Dual
import LinearAlgebra.FreeModule.Finite.Matrix

#align_import linear_algebra.bilinear_form from "leanprover-community/mathlib"@"38df578a6450a8c5142b3727e3ae894c2300cae0"

/-!
# Bilinear form

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexivive,
symmetric, non-degenerate and alternating bilinear forms. Adjoints of
linear maps with respect to a bilinear form are also introduced.

A bilinear form on an R-(semi)module M, is a function from M x M to R,
that is linear in both arguments. Comments will typically abbreviate
"(semi)module" as just "module", but the definitions should be as general as
possible.

The result that there exists an orthogonal basis with respect to a symmetric,
nondegenerate bilinear form can be found in `quadratic_form.lean` with
`exists_orthogonal_basis`.

## Notations

Given any term B of type bilin_form, due to a coercion, can use
the notation B x y to refer to the function field, ie. B x y = B.bilin x y.

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/


open scoped BigOperators

universe u v w

/-- `bilin_form R M` is the type of `R`-bilinear functions `M → M → R`. -/
structure BilinForm (R : Type _) (M : Type _) [Semiring R] [AddCommMonoid M] [Module R M] where
  bilin : M → M → R
  bilin_add_left : ∀ x y z : M, bilin (x + y) z = bilin x z + bilin y z
  bilin_smul_left : ∀ (a : R) (x y : M), bilin (a • x) y = a * bilin x y
  bilin_add_right : ∀ x y z : M, bilin x (y + z) = bilin x y + bilin x z
  bilin_smul_right : ∀ (a : R) (x y : M), bilin x (a • y) = a * bilin x y
#align bilin_form BilinForm

variable {R : Type _} {M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]

variable {R₁ : Type _} {M₁ : Type _} [Ring R₁] [AddCommGroup M₁] [Module R₁ M₁]

variable {R₂ : Type _} {M₂ : Type _} [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]

variable {R₃ : Type _} {M₃ : Type _} [CommRing R₃] [AddCommGroup M₃] [Module R₃ M₃]

variable {V : Type _} {K : Type _} [Field K] [AddCommGroup V] [Module K V]

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁} {B₂ : BilinForm R₂ M₂}

namespace BilinForm

instance : CoeFun (BilinForm R M) fun _ => M → M → R :=
  ⟨bilin⟩

initialize_simps_projections BilinForm (bilin → apply)

@[simp]
theorem coeFn_mk (f : M → M → R) (h₁ h₂ h₃ h₄) : (BilinForm.mk f h₁ h₂ h₃ h₄ : M → M → R) = f :=
  rfl
#align bilin_form.coe_fn_mk BilinForm.coeFn_mk

#print LinearMap.BilinForm.coeFn_congr /-
theorem LinearMap.BilinForm.coeFn_congr : ∀ {x x' y y' : M}, x = x' → y = y' → B x y = B x' y'
  | _, _, _, _, rfl, rfl => rfl
#align bilin_form.coe_fn_congr LinearMap.BilinForm.coeFn_congr
-/

#print LinearMap.BilinForm.add_left /-
@[simp]
theorem LinearMap.BilinForm.add_left (x y z : M) : B (x + y) z = B x z + B y z :=
  bilin_add_left B x y z
#align bilin_form.add_left LinearMap.BilinForm.add_left
-/

#print LinearMap.BilinForm.smul_left /-
@[simp]
theorem LinearMap.BilinForm.smul_left (a : R) (x y : M) : B (a • x) y = a * B x y :=
  bilin_smul_left B a x y
#align bilin_form.smul_left LinearMap.BilinForm.smul_left
-/

#print LinearMap.BilinForm.add_right /-
@[simp]
theorem LinearMap.BilinForm.add_right (x y z : M) : B x (y + z) = B x y + B x z :=
  bilin_add_right B x y z
#align bilin_form.add_right LinearMap.BilinForm.add_right
-/

#print LinearMap.BilinForm.smul_right /-
@[simp]
theorem LinearMap.BilinForm.smul_right (a : R) (x y : M) : B x (a • y) = a * B x y :=
  bilin_smul_right B a x y
#align bilin_form.smul_right LinearMap.BilinForm.smul_right
-/

#print LinearMap.BilinForm.zero_left /-
@[simp]
theorem LinearMap.BilinForm.zero_left (x : M) : B 0 x = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), smul_left, MulZeroClass.zero_mul]
#align bilin_form.zero_left LinearMap.BilinForm.zero_left
-/

#print LinearMap.BilinForm.zero_right /-
@[simp]
theorem LinearMap.BilinForm.zero_right (x : M) : B x 0 = 0 := by
  rw [← @zero_smul _ _ _ _ _ (0 : M), smul_right, MulZeroClass.zero_mul]
#align bilin_form.zero_right LinearMap.BilinForm.zero_right
-/

#print LinearMap.BilinForm.neg_left /-
@[simp]
theorem LinearMap.BilinForm.neg_left (x y : M₁) : B₁ (-x) y = -B₁ x y := by
  rw [← @neg_one_smul R₁ _ _, smul_left, neg_one_mul]
#align bilin_form.neg_left LinearMap.BilinForm.neg_left
-/

#print LinearMap.BilinForm.neg_right /-
@[simp]
theorem LinearMap.BilinForm.neg_right (x y : M₁) : B₁ x (-y) = -B₁ x y := by
  rw [← @neg_one_smul R₁ _ _, smul_right, neg_one_mul]
#align bilin_form.neg_right LinearMap.BilinForm.neg_right
-/

#print LinearMap.BilinForm.sub_left /-
@[simp]
theorem LinearMap.BilinForm.sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_left, neg_left]
#align bilin_form.sub_left LinearMap.BilinForm.sub_left
-/

#print LinearMap.BilinForm.sub_right /-
@[simp]
theorem LinearMap.BilinForm.sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right, neg_right]
#align bilin_form.sub_right LinearMap.BilinForm.sub_right
-/

variable {D : BilinForm R M} {D₁ : BilinForm R₁ M₁}

#print LinearMap.BilinForm.coe_injective /-
-- TODO: instantiate `fun_like`
theorem LinearMap.BilinForm.coe_injective :
    Function.Injective (coeFn : BilinForm R M → M → M → R) := fun B D h => by cases B; cases D;
  congr
#align bilin_form.coe_injective LinearMap.BilinForm.coe_injective
-/

#print LinearMap.BilinForm.ext /-
@[ext]
theorem LinearMap.BilinForm.ext (H : ∀ x y : M, B x y = D x y) : B = D :=
  LinearMap.BilinForm.coe_injective <| by funext; exact H _ _
#align bilin_form.ext LinearMap.BilinForm.ext
-/

#print LinearMap.BilinForm.congr_fun /-
theorem LinearMap.BilinForm.congr_fun (h : B = D) (x y : M) : B x y = D x y :=
  h ▸ rfl
#align bilin_form.congr_fun LinearMap.BilinForm.congr_fun
-/

#print LinearMap.BilinForm.ext_iff /-
theorem LinearMap.BilinForm.ext_iff : B = D ↔ ∀ x y, B x y = D x y :=
  ⟨LinearMap.BilinForm.congr_fun, LinearMap.BilinForm.ext⟩
#align bilin_form.ext_iff LinearMap.BilinForm.ext_iff
-/

instance : Zero (BilinForm R M)
    where zero :=
    { bilin := fun x y => 0
      bilin_add_left := fun x y z => (add_zero 0).symm
      bilin_smul_left := fun a x y => (MulZeroClass.mul_zero a).symm
      bilin_add_right := fun x y z => (zero_add 0).symm
      bilin_smul_right := fun a x y => (MulZeroClass.mul_zero a).symm }

#print LinearMap.BilinForm.coe_zero /-
@[simp]
theorem LinearMap.BilinForm.coe_zero : ⇑(0 : BilinForm R M) = 0 :=
  rfl
#align bilin_form.coe_zero LinearMap.BilinForm.coe_zero
-/

#print LinearMap.BilinForm.zero_apply /-
@[simp]
theorem LinearMap.BilinForm.zero_apply (x y : M) : (0 : BilinForm R M) x y = 0 :=
  rfl
#align bilin_form.zero_apply LinearMap.BilinForm.zero_apply
-/

variable (B D B₁ D₁)

instance : Add (BilinForm R M)
    where add B D :=
    { bilin := fun x y => B x y + D x y
      bilin_add_left := fun x y z => by rw [add_left, add_left, add_add_add_comm]
      bilin_smul_left := fun a x y => by rw [smul_left, smul_left, mul_add]
      bilin_add_right := fun x y z => by rw [add_right, add_right, add_add_add_comm]
      bilin_smul_right := fun a x y => by rw [smul_right, smul_right, mul_add] }

#print LinearMap.BilinForm.coe_add /-
@[simp]
theorem LinearMap.BilinForm.coe_add : ⇑(B + D) = B + D :=
  rfl
#align bilin_form.coe_add LinearMap.BilinForm.coe_add
-/

#print LinearMap.BilinForm.add_apply /-
@[simp]
theorem LinearMap.BilinForm.add_apply (x y : M) : (B + D) x y = B x y + D x y :=
  rfl
#align bilin_form.add_apply LinearMap.BilinForm.add_apply
-/

/-- `bilin_form R M` inherits the scalar action by `α` on `R` if this is compatible with
multiplication.

When `R` itself is commutative, this provides an `R`-action via `algebra.id`. -/
instance {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] : SMul α (BilinForm R M)
    where smul c B :=
    { bilin := fun x y => c • B x y
      bilin_add_left := fun x y z => by rw [add_left, smul_add]
      bilin_smul_left := fun a x y => by rw [smul_left, ← mul_smul_comm]
      bilin_add_right := fun x y z => by rw [add_right, smul_add]
      bilin_smul_right := fun a x y => by rw [smul_right, ← mul_smul_comm] }

@[simp]
theorem coe_smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    (B : BilinForm R M) : ⇑(a • B) = a • B :=
  rfl
#align bilin_form.coe_smul BilinForm.coe_smul

@[simp]
theorem smul_apply {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    (B : BilinForm R M) (x y : M) : (a • B) x y = a • B x y :=
  rfl
#align bilin_form.smul_apply BilinForm.smul_apply

instance : AddCommMonoid (BilinForm R M) :=
  Function.Injective.addCommMonoid _ LinearMap.BilinForm.coe_injective LinearMap.BilinForm.coe_zero
    LinearMap.BilinForm.coe_add fun n x => coe_smul _ _

instance : Neg (BilinForm R₁ M₁)
    where neg B :=
    { bilin := fun x y => -B x y
      bilin_add_left := fun x y z => by rw [add_left, neg_add]
      bilin_smul_left := fun a x y => by rw [smul_left, mul_neg]
      bilin_add_right := fun x y z => by rw [add_right, neg_add]
      bilin_smul_right := fun a x y => by rw [smul_right, mul_neg] }

#print LinearMap.BilinForm.coe_neg /-
@[simp]
theorem LinearMap.BilinForm.coe_neg : ⇑(-B₁) = -B₁ :=
  rfl
#align bilin_form.coe_neg LinearMap.BilinForm.coe_neg
-/

#print LinearMap.BilinForm.neg_apply /-
@[simp]
theorem LinearMap.BilinForm.neg_apply (x y : M₁) : (-B₁) x y = -B₁ x y :=
  rfl
#align bilin_form.neg_apply LinearMap.BilinForm.neg_apply
-/

instance : Sub (BilinForm R₁ M₁)
    where sub B D :=
    { bilin := fun x y => B x y - D x y
      bilin_add_left := fun x y z => by rw [add_left, add_left, add_sub_add_comm]
      bilin_smul_left := fun a x y => by rw [smul_left, smul_left, mul_sub]
      bilin_add_right := fun x y z => by rw [add_right, add_right, add_sub_add_comm]
      bilin_smul_right := fun a x y => by rw [smul_right, smul_right, mul_sub] }

#print LinearMap.BilinForm.coe_sub /-
@[simp]
theorem LinearMap.BilinForm.coe_sub : ⇑(B₁ - D₁) = B₁ - D₁ :=
  rfl
#align bilin_form.coe_sub LinearMap.BilinForm.coe_sub
-/

#print LinearMap.BilinForm.sub_apply /-
@[simp]
theorem LinearMap.BilinForm.sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
  rfl
#align bilin_form.sub_apply LinearMap.BilinForm.sub_apply
-/

instance : AddCommGroup (BilinForm R₁ M₁) :=
  Function.Injective.addCommGroup _ LinearMap.BilinForm.coe_injective LinearMap.BilinForm.coe_zero
    LinearMap.BilinForm.coe_add LinearMap.BilinForm.coe_neg LinearMap.BilinForm.coe_sub
    (fun n x => coe_smul _ _) fun n x => coe_smul _ _

instance : Inhabited (BilinForm R M) :=
  ⟨0⟩

#print LinearMap.BilinForm.coeFnAddMonoidHom /-
/-- `coe_fn` as an `add_monoid_hom` -/
def LinearMap.BilinForm.coeFnAddMonoidHom : BilinForm R M →+ M → M → R
    where
  toFun := coeFn
  map_zero' := LinearMap.BilinForm.coe_zero
  map_add' := LinearMap.BilinForm.coe_add
#align bilin_form.coe_fn_add_monoid_hom LinearMap.BilinForm.coeFnAddMonoidHom
-/

instance {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] :
    DistribMulAction α (BilinForm R M) :=
  Function.Injective.distribMulAction LinearMap.BilinForm.coeFnAddMonoidHom
    LinearMap.BilinForm.coe_injective coe_smul

instance {α} [Semiring α] [Module α R] [SMulCommClass α R R] : Module α (BilinForm R M) :=
  Function.Injective.module _ LinearMap.BilinForm.coeFnAddMonoidHom
    LinearMap.BilinForm.coe_injective coe_smul

section flip

variable (R₂)

#print LinearMap.BilinForm.flipHomAux /-
/-- Auxiliary construction for the flip of a bilinear form, obtained by exchanging the left and
right arguments. This version is a `linear_map`; it is later upgraded to a `linear_equiv`
in `flip_hom`. -/
def LinearMap.BilinForm.flipHomAux [Algebra R₂ R] : BilinForm R M →ₗ[R₂] BilinForm R M
    where
  toFun A :=
    { bilin := fun i j => A j i
      bilin_add_left := fun x y z => A.bilin_add_right z x y
      bilin_smul_left := fun a x y => A.bilin_smul_right a y x
      bilin_add_right := fun x y z => A.bilin_add_left y z x
      bilin_smul_right := fun a x y => A.bilin_smul_left a y x }
  map_add' A₁ A₂ := by ext; simp
  map_smul' c A := by ext; simp
#align bilin_form.flip_hom_aux LinearMap.BilinForm.flipHomAux
-/

variable {R₂}

#print LinearMap.BilinForm.flip_flip_aux /-
theorem LinearMap.BilinForm.flip_flip_aux [Algebra R₂ R] (A : BilinForm R M) :
    (LinearMap.BilinForm.flipHomAux R₂) (LinearMap.BilinForm.flipHomAux R₂ A) = A := by ext A x y;
  simp [flip_hom_aux]
#align bilin_form.flip_flip_aux LinearMap.BilinForm.flip_flip_aux
-/

variable (R₂)

#print LinearMap.BilinForm.flipHom /-
/-- The flip of a bilinear form, obtained by exchanging the left and right arguments. This is a
less structured version of the equiv which applies to general (noncommutative) rings `R` with a
distinguished commutative subring `R₂`; over a commutative ring use `flip`. -/
def LinearMap.BilinForm.flipHom [Algebra R₂ R] : BilinForm R M ≃ₗ[R₂] BilinForm R M :=
  {
    LinearMap.BilinForm.flipHomAux
      R₂ with
    invFun := LinearMap.BilinForm.flipHomAux R₂
    left_inv := LinearMap.BilinForm.flip_flip_aux
    right_inv := LinearMap.BilinForm.flip_flip_aux }
#align bilin_form.flip_hom LinearMap.BilinForm.flipHom
-/

variable {R₂}

#print LinearMap.BilinForm.flip_apply /-
@[simp]
theorem LinearMap.BilinForm.flip_apply [Algebra R₂ R] (A : BilinForm R M) (x y : M) :
    LinearMap.BilinForm.flipHom R₂ A x y = A y x :=
  rfl
#align bilin_form.flip_apply LinearMap.BilinForm.flip_apply
-/

#print LinearMap.BilinForm.flip_flip /-
theorem LinearMap.BilinForm.flip_flip [Algebra R₂ R] :
    (LinearMap.BilinForm.flipHom R₂).trans (LinearMap.BilinForm.flipHom R₂) =
      LinearEquiv.refl R₂ (BilinForm R M) :=
  by ext A x y; simp
#align bilin_form.flip_flip LinearMap.BilinForm.flip_flip
-/

/-- The flip of a bilinear form over a ring, obtained by exchanging the left and right arguments,
here considered as an `ℕ`-linear equivalence, i.e. an additive equivalence. -/
abbrev flip' : BilinForm R M ≃ₗ[ℕ] BilinForm R M :=
  LinearMap.BilinForm.flipHom ℕ
#align bilin_form.flip' BilinForm.flip'

#print LinearMap.BilinForm.flip /-
/-- The `flip` of a bilinear form over a commutative ring, obtained by exchanging the left and
right arguments. -/
abbrev LinearMap.BilinForm.flip : BilinForm R₂ M₂ ≃ₗ[R₂] BilinForm R₂ M₂ :=
  LinearMap.BilinForm.flipHom R₂
#align bilin_form.flip LinearMap.BilinForm.flip
-/

end flip

section ToLin'

variable [Algebra R₂ R] [Module R₂ M] [IsScalarTower R₂ R M]

#print LinearMap.BilinForm.toLinHomAux₁ /-
/-- Auxiliary definition to define `to_lin_hom`; see below. -/
def LinearMap.BilinForm.toLinHomAux₁ (A : BilinForm R M) (x : M) : M →ₗ[R] R
    where
  toFun y := A x y
  map_add' := A.bilin_add_right x
  map_smul' c := A.bilin_smul_right c x
#align bilin_form.to_lin_hom_aux₁ LinearMap.BilinForm.toLinHomAux₁
-/

#print LinearMap.BilinForm.toLinHomAux₂ /-
/-- Auxiliary definition to define `to_lin_hom`; see below. -/
def LinearMap.BilinForm.toLinHomAux₂ (A : BilinForm R M) : M →ₗ[R₂] M →ₗ[R] R
    where
  toFun := LinearMap.BilinForm.toLinHomAux₁ A
  map_add' x₁ x₂ :=
    LinearMap.ext fun x => by
      simp only [to_lin_hom_aux₁, LinearMap.coe_mk, LinearMap.add_apply, add_left]
  map_smul' c x :=
    LinearMap.ext <| by
      dsimp [to_lin_hom_aux₁]
      intros
      simp only [← algebraMap_smul R c x, Algebra.smul_def, LinearMap.coe_mk, LinearMap.smul_apply,
        smul_left]
#align bilin_form.to_lin_hom_aux₂ LinearMap.BilinForm.toLinHomAux₂
-/

variable (R₂)

#print LinearMap.BilinForm.toLinHom /-
/-- The linear map obtained from a `bilin_form` by fixing the left co-ordinate and evaluating in
the right.
This is the most general version of the construction; it is `R₂`-linear for some distinguished
commutative subsemiring `R₂` of the scalar ring.  Over a semiring with no particular distinguished
such subsemiring, use `to_lin'`, which is `ℕ`-linear.  Over a commutative semiring, use `to_lin`,
which is linear. -/
def LinearMap.BilinForm.toLinHom : BilinForm R M →ₗ[R₂] M →ₗ[R₂] M →ₗ[R] R
    where
  toFun := LinearMap.BilinForm.toLinHomAux₂
  map_add' A₁ A₂ :=
    LinearMap.ext fun x => by
      dsimp only [to_lin_hom_aux₁, to_lin_hom_aux₂]
      apply LinearMap.ext
      intro y
      simp only [to_lin_hom_aux₂, to_lin_hom_aux₁, LinearMap.coe_mk, LinearMap.add_apply, add_apply]
  map_smul' c A := by
    dsimp [to_lin_hom_aux₁, to_lin_hom_aux₂]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [to_lin_hom_aux₂, to_lin_hom_aux₁, LinearMap.coe_mk, LinearMap.smul_apply, smul_apply]
#align bilin_form.to_lin_hom LinearMap.BilinForm.toLinHom
-/

variable {R₂}

#print LinearMap.BilinForm.toLin'_apply /-
@[simp]
theorem LinearMap.BilinForm.toLin'_apply (A : BilinForm R M) (x : M) :
    ⇑(LinearMap.BilinForm.toLinHom R₂ A x) = A x :=
  rfl
#align bilin_form.to_lin'_apply LinearMap.BilinForm.toLin'_apply
-/

/-- The linear map obtained from a `bilin_form` by fixing the left co-ordinate and evaluating in
the right.
Over a commutative semiring, use `to_lin`, which is linear rather than `ℕ`-linear. -/
abbrev toLin' : BilinForm R M →ₗ[ℕ] M →ₗ[ℕ] M →ₗ[R] R :=
  LinearMap.BilinForm.toLinHom ℕ
#align bilin_form.to_lin' BilinForm.toLin'

#print LinearMap.BilinForm.sum_left /-
@[simp]
theorem LinearMap.BilinForm.sum_left {α} (t : Finset α) (g : α → M) (w : M) :
    B (∑ i in t, g i) w = ∑ i in t, B (g i) w :=
  (BilinForm.toLin' B).map_sum₂ t g w
#align bilin_form.sum_left LinearMap.BilinForm.sum_left
-/

#print LinearMap.BilinForm.sum_right /-
@[simp]
theorem LinearMap.BilinForm.sum_right {α} (t : Finset α) (w : M) (g : α → M) :
    B w (∑ i in t, g i) = ∑ i in t, B w (g i) :=
  (BilinForm.toLin' B w).map_sum
#align bilin_form.sum_right LinearMap.BilinForm.sum_right
-/

variable (R₂)

#print LinearMap.BilinForm.toLinHomFlip /-
/-- The linear map obtained from a `bilin_form` by fixing the right co-ordinate and evaluating in
the left.
This is the most general version of the construction; it is `R₂`-linear for some distinguished
commutative subsemiring `R₂` of the scalar ring.  Over semiring with no particular distinguished
such subsemiring, use `to_lin'_flip`, which is `ℕ`-linear.  Over a commutative semiring, use
`to_lin_flip`, which is linear. -/
def LinearMap.BilinForm.toLinHomFlip : BilinForm R M →ₗ[R₂] M →ₗ[R₂] M →ₗ[R] R :=
  (LinearMap.BilinForm.toLinHom R₂).comp (LinearMap.BilinForm.flipHom R₂).toLinearMap
#align bilin_form.to_lin_hom_flip LinearMap.BilinForm.toLinHomFlip
-/

variable {R₂}

#print LinearMap.BilinForm.toLin'Flip_apply /-
@[simp]
theorem LinearMap.BilinForm.toLin'Flip_apply (A : BilinForm R M) (x : M) :
    ⇑(LinearMap.BilinForm.toLinHomFlip R₂ A x) = fun y => A y x :=
  rfl
#align bilin_form.to_lin'_flip_apply LinearMap.BilinForm.toLin'Flip_apply
-/

/-- The linear map obtained from a `bilin_form` by fixing the right co-ordinate and evaluating in
the left.
Over a commutative semiring, use `to_lin_flip`, which is linear rather than `ℕ`-linear. -/
abbrev toLin'Flip : BilinForm R M →ₗ[ℕ] M →ₗ[ℕ] M →ₗ[R] R :=
  LinearMap.BilinForm.toLinHomFlip ℕ
#align bilin_form.to_lin'_flip BilinForm.toLin'Flip

end ToLin'

end BilinForm

section EquivLin

#print LinearMap.toBilinAux /-
/-- A map with two arguments that is linear in both is a bilinear form.

This is an auxiliary definition for the full linear equivalence `linear_map.to_bilin`.
-/
def LinearMap.toBilinAux (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) : BilinForm R₂ M₂
    where
  bilin x y := f x y
  bilin_add_left x y z := (LinearMap.map_add f x y).symm ▸ LinearMap.add_apply (f x) (f y) z
  bilin_smul_left a x y := by rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  bilin_add_right x y z := LinearMap.map_add (f x) y z
  bilin_smul_right a x y := LinearMap.map_smul (f x) a y
#align linear_map.to_bilin_aux LinearMap.toBilinAux
-/

#print LinearMap.BilinForm.toLin /-
/-- Bilinear forms are linearly equivalent to maps with two arguments that are linear in both. -/
def LinearMap.BilinForm.toLin : BilinForm R₂ M₂ ≃ₗ[R₂] M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂ :=
  {
    LinearMap.BilinForm.toLinHom
      R₂ with
    invFun := LinearMap.toBilinAux
    left_inv := fun B => by ext; simp [LinearMap.toBilinAux]
    right_inv := fun B => by ext; simp [LinearMap.toBilinAux] }
#align bilin_form.to_lin LinearMap.BilinForm.toLin
-/

#print LinearMap.toBilin /-
/-- A map with two arguments that is linear in both is linearly equivalent to bilinear form. -/
def LinearMap.toBilin : (M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) ≃ₗ[R₂] BilinForm R₂ M₂ :=
  LinearMap.BilinForm.toLin.symm
#align linear_map.to_bilin LinearMap.toBilin
-/

#print LinearMap.toBilinAux_eq /-
@[simp]
theorem LinearMap.toBilinAux_eq (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) :
    LinearMap.toBilinAux f = LinearMap.toBilin f :=
  rfl
#align linear_map.to_bilin_aux_eq LinearMap.toBilinAux_eq
-/

#print LinearMap.toBilin_symm /-
@[simp]
theorem LinearMap.toBilin_symm :
    (LinearMap.toBilin.symm : BilinForm R₂ M₂ ≃ₗ[R₂] _) = LinearMap.BilinForm.toLin :=
  rfl
#align linear_map.to_bilin_symm LinearMap.toBilin_symm
-/

#print BilinForm.toLin_symm /-
@[simp]
theorem BilinForm.toLin_symm :
    (LinearMap.BilinForm.toLin.symm : _ ≃ₗ[R₂] BilinForm R₂ M₂) = LinearMap.toBilin :=
  LinearMap.toBilin.symm_symm
#align bilin_form.to_lin_symm BilinForm.toLin_symm
-/

#print BilinForm.toLin_apply /-
@[simp, norm_cast]
theorem BilinForm.toLin_apply (x : M₂) : ⇑(LinearMap.BilinForm.toLin B₂ x) = B₂ x :=
  rfl
#align bilin_form.to_lin_apply BilinForm.toLin_apply
-/

end EquivLin

namespace LinearMap

variable {R' : Type _} [CommSemiring R'] [Algebra R' R] [Module R' M] [IsScalarTower R' R M]

#print LinearMap.compBilinForm /-
/-- Apply a linear map on the output of a bilinear form. -/
@[simps]
def compBilinForm (f : R →ₗ[R'] R') (B : BilinForm R M) : BilinForm R' M
    where
  bilin x y := f (B x y)
  bilin_add_left x y z := by rw [LinearMap.BilinForm.add_left, map_add]
  bilin_smul_left r x y := by
    rw [← smul_one_smul R r (_ : M), LinearMap.BilinForm.smul_left, smul_one_mul r (_ : R),
      map_smul, smul_eq_mul]
  bilin_add_right x y z := by rw [LinearMap.BilinForm.add_right, map_add]
  bilin_smul_right r x y := by
    rw [← smul_one_smul R r (_ : M), LinearMap.BilinForm.smul_right, smul_one_mul r (_ : R),
      map_smul, smul_eq_mul]
#align linear_map.comp_bilin_form LinearMap.compBilinForm
-/

end LinearMap

namespace BilinForm

section Comp

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

#print LinearMap.BilinForm.comp /-
/-- Apply a linear map on the left and right argument of a bilinear form. -/
def LinearMap.BilinForm.comp (B : BilinForm R M') (l r : M →ₗ[R] M') : BilinForm R M
    where
  bilin x y := B (l x) (r y)
  bilin_add_left x y z := by rw [LinearMap.map_add, add_left]
  bilin_smul_left x y z := by rw [LinearMap.map_smul, smul_left]
  bilin_add_right x y z := by rw [LinearMap.map_add, add_right]
  bilin_smul_right x y z := by rw [LinearMap.map_smul, smul_right]
#align bilin_form.comp LinearMap.BilinForm.comp
-/

#print LinearMap.BilinForm.compLeft /-
/-- Apply a linear map to the left argument of a bilinear form. -/
def LinearMap.BilinForm.compLeft (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp f LinearMap.id
#align bilin_form.comp_left LinearMap.BilinForm.compLeft
-/

#print LinearMap.BilinForm.compRight /-
/-- Apply a linear map to the right argument of a bilinear form. -/
def LinearMap.BilinForm.compRight (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp LinearMap.id f
#align bilin_form.comp_right LinearMap.BilinForm.compRight
-/

#print LinearMap.BilinForm.comp_comp /-
theorem LinearMap.BilinForm.comp_comp {M'' : Type _} [AddCommMonoid M''] [Module R M'']
    (B : BilinForm R M'') (l r : M →ₗ[R] M') (l' r' : M' →ₗ[R] M'') :
    (B.comp l' r').comp l r = B.comp (l'.comp l) (r'.comp r) :=
  rfl
#align bilin_form.comp_comp LinearMap.BilinForm.comp_comp
-/

#print LinearMap.BilinForm.compLeft_compRight /-
@[simp]
theorem LinearMap.BilinForm.compLeft_compRight (B : BilinForm R M) (l r : M →ₗ[R] M) :
    (B.compLeft l).compRight r = B.comp l r :=
  rfl
#align bilin_form.comp_left_comp_right LinearMap.BilinForm.compLeft_compRight
-/

#print LinearMap.BilinForm.compRight_compLeft /-
@[simp]
theorem LinearMap.BilinForm.compRight_compLeft (B : BilinForm R M) (l r : M →ₗ[R] M) :
    (B.compRight r).compLeft l = B.comp l r :=
  rfl
#align bilin_form.comp_right_comp_left LinearMap.BilinForm.compRight_compLeft
-/

#print LinearMap.BilinForm.comp_apply /-
@[simp]
theorem LinearMap.BilinForm.comp_apply (B : BilinForm R M') (l r : M →ₗ[R] M') (v w) :
    B.comp l r v w = B (l v) (r w) :=
  rfl
#align bilin_form.comp_apply LinearMap.BilinForm.comp_apply
-/

#print LinearMap.BilinForm.compLeft_apply /-
@[simp]
theorem LinearMap.BilinForm.compLeft_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) :
    B.compLeft f v w = B (f v) w :=
  rfl
#align bilin_form.comp_left_apply LinearMap.BilinForm.compLeft_apply
-/

#print LinearMap.BilinForm.compRight_apply /-
@[simp]
theorem LinearMap.BilinForm.compRight_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) :
    B.compRight f v w = B v (f w) :=
  rfl
#align bilin_form.comp_right_apply LinearMap.BilinForm.compRight_apply
-/

#print LinearMap.BilinForm.comp_id_left /-
@[simp]
theorem LinearMap.BilinForm.comp_id_left (B : BilinForm R M) (r : M →ₗ[R] M) :
    B.comp LinearMap.id r = B.compRight r := by ext; rfl
#align bilin_form.comp_id_left LinearMap.BilinForm.comp_id_left
-/

#print LinearMap.BilinForm.comp_id_right /-
@[simp]
theorem LinearMap.BilinForm.comp_id_right (B : BilinForm R M) (l : M →ₗ[R] M) :
    B.comp l LinearMap.id = B.compLeft l := by ext; rfl
#align bilin_form.comp_id_right LinearMap.BilinForm.comp_id_right
-/

#print LinearMap.BilinForm.compLeft_id /-
@[simp]
theorem LinearMap.BilinForm.compLeft_id (B : BilinForm R M) : B.compLeft LinearMap.id = B := by ext;
  rfl
#align bilin_form.comp_left_id LinearMap.BilinForm.compLeft_id
-/

#print LinearMap.BilinForm.compRight_id /-
@[simp]
theorem LinearMap.BilinForm.compRight_id (B : BilinForm R M) : B.compRight LinearMap.id = B := by
  ext; rfl
#align bilin_form.comp_right_id LinearMap.BilinForm.compRight_id
-/

#print LinearMap.BilinForm.comp_id_id /-
-- Shortcut for `comp_id_{left,right}` followed by `comp_{right,left}_id`,
-- has to be declared after the former two to get the right priority
@[simp]
theorem LinearMap.BilinForm.comp_id_id (B : BilinForm R M) : B.comp LinearMap.id LinearMap.id = B :=
  by ext; rfl
#align bilin_form.comp_id_id LinearMap.BilinForm.comp_id_id
-/

#print LinearMap.BilinForm.comp_inj /-
theorem LinearMap.BilinForm.comp_inj (B₁ B₂ : BilinForm R M') {l r : M →ₗ[R] M'}
    (hₗ : Function.Surjective l) (hᵣ : Function.Surjective r) :
    B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ :=
  by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext
    cases' hₗ x with x' hx; subst hx
    cases' hᵣ y with y' hy; subst hy
    rw [← comp_apply, ← comp_apply, h]
  ·-- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h
#align bilin_form.comp_inj LinearMap.BilinForm.comp_inj
-/

end Comp

variable {M₂' M₂'' : Type _}

variable [AddCommMonoid M₂'] [AddCommMonoid M₂''] [Module R₂ M₂'] [Module R₂ M₂'']

section congr

#print LinearMap.BilinForm.congr /-
/-- Apply a linear equivalence on the arguments of a bilinear form. -/
def LinearMap.BilinForm.congr (e : M₂ ≃ₗ[R₂] M₂') : BilinForm R₂ M₂ ≃ₗ[R₂] BilinForm R₂ M₂'
    where
  toFun B := B.comp e.symm e.symm
  invFun B := B.comp e e
  left_inv B :=
    LinearMap.BilinForm.ext fun x y => by
      simp only [comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
  right_inv B :=
    LinearMap.BilinForm.ext fun x y => by
      simp only [comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply]
  map_add' B B' := LinearMap.BilinForm.ext fun x y => by simp only [comp_apply, add_apply]
  map_smul' B B' := LinearMap.BilinForm.ext fun x y => by simp [comp_apply, smul_apply]
#align bilin_form.congr LinearMap.BilinForm.congr
-/

#print LinearMap.BilinForm.congr_apply /-
@[simp]
theorem LinearMap.BilinForm.congr_apply (e : M₂ ≃ₗ[R₂] M₂') (B : BilinForm R₂ M₂) (x y : M₂') :
    LinearMap.BilinForm.congr e B x y = B (e.symm x) (e.symm y) :=
  rfl
#align bilin_form.congr_apply LinearMap.BilinForm.congr_apply
-/

#print LinearMap.BilinForm.congr_symm /-
@[simp]
theorem LinearMap.BilinForm.congr_symm (e : M₂ ≃ₗ[R₂] M₂') :
    (LinearMap.BilinForm.congr e).symm = LinearMap.BilinForm.congr e.symm := by ext B x y;
  simp only [congr_apply, LinearEquiv.symm_symm]; rfl
#align bilin_form.congr_symm LinearMap.BilinForm.congr_symm
-/

#print LinearMap.BilinForm.congr_refl /-
@[simp]
theorem LinearMap.BilinForm.congr_refl :
    LinearMap.BilinForm.congr (LinearEquiv.refl R₂ M₂) = LinearEquiv.refl R₂ _ :=
  LinearEquiv.ext fun B => LinearMap.BilinForm.ext fun x y => rfl
#align bilin_form.congr_refl LinearMap.BilinForm.congr_refl
-/

#print LinearMap.BilinForm.congr_trans /-
theorem LinearMap.BilinForm.congr_trans (e : M₂ ≃ₗ[R₂] M₂') (f : M₂' ≃ₗ[R₂] M₂'') :
    (LinearMap.BilinForm.congr e).trans (LinearMap.BilinForm.congr f) =
      LinearMap.BilinForm.congr (e.trans f) :=
  rfl
#align bilin_form.congr_trans LinearMap.BilinForm.congr_trans
-/

#print LinearMap.BilinForm.congr_congr /-
theorem LinearMap.BilinForm.congr_congr (e : M₂' ≃ₗ[R₂] M₂'') (f : M₂ ≃ₗ[R₂] M₂')
    (B : BilinForm R₂ M₂) :
    LinearMap.BilinForm.congr e (LinearMap.BilinForm.congr f B) =
      LinearMap.BilinForm.congr (f.trans e) B :=
  rfl
#align bilin_form.congr_congr LinearMap.BilinForm.congr_congr
-/

#print LinearMap.BilinForm.congr_comp /-
theorem LinearMap.BilinForm.congr_comp (e : M₂ ≃ₗ[R₂] M₂') (B : BilinForm R₂ M₂)
    (l r : M₂'' →ₗ[R₂] M₂') :
    (LinearMap.BilinForm.congr e B).comp l r =
      B.comp (LinearMap.comp (e.symm : M₂' →ₗ[R₂] M₂) l)
        (LinearMap.comp (e.symm : M₂' →ₗ[R₂] M₂) r) :=
  rfl
#align bilin_form.congr_comp LinearMap.BilinForm.congr_comp
-/

#print LinearMap.BilinForm.comp_congr /-
theorem LinearMap.BilinForm.comp_congr (e : M₂' ≃ₗ[R₂] M₂'') (B : BilinForm R₂ M₂)
    (l r : M₂' →ₗ[R₂] M₂) :
    LinearMap.BilinForm.congr e (B.comp l r) =
      B.comp (l.comp (e.symm : M₂'' →ₗ[R₂] M₂')) (r.comp (e.symm : M₂'' →ₗ[R₂] M₂')) :=
  rfl
#align bilin_form.comp_congr LinearMap.BilinForm.comp_congr
-/

end congr

section LinMulLin

#print LinearMap.BilinForm.linMulLin /-
/-- `lin_mul_lin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
def LinearMap.BilinForm.linMulLin (f g : M₂ →ₗ[R₂] R₂) : BilinForm R₂ M₂
    where
  bilin x y := f x * g y
  bilin_add_left x y z := by rw [LinearMap.map_add, add_mul]
  bilin_smul_left x y z := by rw [LinearMap.map_smul, smul_eq_mul, mul_assoc]
  bilin_add_right x y z := by rw [LinearMap.map_add, mul_add]
  bilin_smul_right x y z := by rw [LinearMap.map_smul, smul_eq_mul, mul_left_comm]
#align bilin_form.lin_mul_lin LinearMap.BilinForm.linMulLin
-/

variable {f g : M₂ →ₗ[R₂] R₂}

#print LinearMap.BilinForm.linMulLin_apply /-
@[simp]
theorem LinearMap.BilinForm.linMulLin_apply (x y) :
    LinearMap.BilinForm.linMulLin f g x y = f x * g y :=
  rfl
#align bilin_form.lin_mul_lin_apply LinearMap.BilinForm.linMulLin_apply
-/

#print LinearMap.BilinForm.linMulLin_comp /-
@[simp]
theorem LinearMap.BilinForm.linMulLin_comp (l r : M₂' →ₗ[R₂] M₂) :
    (LinearMap.BilinForm.linMulLin f g).comp l r =
      LinearMap.BilinForm.linMulLin (f.comp l) (g.comp r) :=
  rfl
#align bilin_form.lin_mul_lin_comp LinearMap.BilinForm.linMulLin_comp
-/

#print LinearMap.BilinForm.linMulLin_compLeft /-
@[simp]
theorem LinearMap.BilinForm.linMulLin_compLeft (l : M₂ →ₗ[R₂] M₂) :
    (LinearMap.BilinForm.linMulLin f g).compLeft l = LinearMap.BilinForm.linMulLin (f.comp l) g :=
  rfl
#align bilin_form.lin_mul_lin_comp_left LinearMap.BilinForm.linMulLin_compLeft
-/

#print LinearMap.BilinForm.linMulLin_compRight /-
@[simp]
theorem LinearMap.BilinForm.linMulLin_compRight (r : M₂ →ₗ[R₂] M₂) :
    (LinearMap.BilinForm.linMulLin f g).compRight r = LinearMap.BilinForm.linMulLin f (g.comp r) :=
  rfl
#align bilin_form.lin_mul_lin_comp_right LinearMap.BilinForm.linMulLin_compRight
-/

end LinMulLin

#print LinearMap.BilinForm.IsOrtho /-
/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `bilin_form.is_Ortho`. -/
def LinearMap.BilinForm.IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0
#align bilin_form.is_ortho LinearMap.BilinForm.IsOrtho
-/

#print LinearMap.BilinForm.isOrtho_def /-
theorem LinearMap.BilinForm.isOrtho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl
#align bilin_form.is_ortho_def LinearMap.BilinForm.isOrtho_def
-/

#print LinearMap.BilinForm.isOrtho_zero_left /-
theorem LinearMap.BilinForm.isOrtho_zero_left (x : M) : LinearMap.BilinForm.IsOrtho B (0 : M) x :=
  LinearMap.BilinForm.zero_left x
#align bilin_form.is_ortho_zero_left LinearMap.BilinForm.isOrtho_zero_left
-/

#print LinearMap.BilinForm.isOrtho_zero_right /-
theorem LinearMap.BilinForm.isOrtho_zero_right (x : M) : LinearMap.BilinForm.IsOrtho B x (0 : M) :=
  LinearMap.BilinForm.zero_right x
#align bilin_form.is_ortho_zero_right LinearMap.BilinForm.isOrtho_zero_right
-/

#print LinearMap.BilinForm.ne_zero_of_not_isOrtho_self /-
theorem LinearMap.BilinForm.ne_zero_of_not_isOrtho_self {B : BilinForm K V} (x : V)
    (hx₁ : ¬B.IsOrtho x x) : x ≠ 0 := fun hx₂ =>
  hx₁ (hx₂.symm ▸ LinearMap.BilinForm.isOrtho_zero_left _)
#align bilin_form.ne_zero_of_not_is_ortho_self LinearMap.BilinForm.ne_zero_of_not_isOrtho_self
-/

#print LinearMap.BilinForm.iIsOrtho /-
/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`bilin_form.is_ortho` -/
def LinearMap.BilinForm.iIsOrtho {n : Type w} (B : BilinForm R M) (v : n → M) : Prop :=
  Pairwise (B.IsOrtho on v)
#align bilin_form.is_Ortho LinearMap.BilinForm.iIsOrtho
-/

#print LinearMap.BilinForm.iIsOrtho_def /-
theorem LinearMap.BilinForm.iIsOrtho_def {n : Type w} {B : BilinForm R M} {v : n → M} :
    B.IsOrthoᵢ v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl
#align bilin_form.is_Ortho_def LinearMap.BilinForm.iIsOrtho_def
-/

section

variable {R₄ M₄ : Type _} [Ring R₄] [IsDomain R₄]

variable [AddCommGroup M₄] [Module R₄ M₄] {G : BilinForm R₄ M₄}

#print LinearMap.BilinForm.isOrtho_smul_left /-
@[simp]
theorem LinearMap.BilinForm.isOrtho_smul_left {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    LinearMap.BilinForm.IsOrtho G (a • x) y ↔ LinearMap.BilinForm.IsOrtho G x y :=
  by
  dsimp only [is_ortho]
  constructor <;> intro H
  · rw [smul_left, mul_eq_zero] at H
    cases H
    · trivial
    · exact H
  · rw [smul_left, H, MulZeroClass.mul_zero]
#align bilin_form.is_ortho_smul_left LinearMap.BilinForm.isOrtho_smul_left
-/

#print LinearMap.BilinForm.isOrtho_smul_right /-
@[simp]
theorem LinearMap.BilinForm.isOrtho_smul_right {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    LinearMap.BilinForm.IsOrtho G x (a • y) ↔ LinearMap.BilinForm.IsOrtho G x y :=
  by
  dsimp only [is_ortho]
  constructor <;> intro H
  · rw [smul_right, mul_eq_zero] at H
    cases H
    · trivial
    · exact H
  · rw [smul_right, H, MulZeroClass.mul_zero]
#align bilin_form.is_ortho_smul_right LinearMap.BilinForm.isOrtho_smul_right
-/

#print LinearMap.BilinForm.linearIndependent_of_iIsOrtho /-
/-- A set of orthogonal vectors `v` with respect to some bilinear form `B` is linearly independent
  if for all `i`, `B (v i) (v i) ≠ 0`. -/
theorem LinearMap.BilinForm.linearIndependent_of_iIsOrtho {n : Type w} {B : BilinForm K V}
    {v : n → V} (hv₁ : B.IsOrthoᵢ v) (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K v :=
  by
  classical
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, zero_left]
  have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) :=
    by
    apply Finset.sum_eq_single_of_mem i hi
    intro j hj hij
    rw [is_Ortho_def.1 hv₁ _ _ hij, MulZeroClass.mul_zero]
  simp_rw [sum_left, smul_left, hsum] at this
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this
#align bilin_form.linear_independent_of_is_Ortho LinearMap.BilinForm.linearIndependent_of_iIsOrtho
-/

end

section Basis

variable {F₂ : BilinForm R₂ M₂}

variable {ι : Type _} (b : Basis ι R₂ M₂)

#print LinearMap.BilinForm.ext_basis /-
/-- Two bilinear forms are equal when they are equal on all basis vectors. -/
theorem LinearMap.BilinForm.ext_basis (h : ∀ i j, B₂ (b i) (b j) = F₂ (b i) (b j)) : B₂ = F₂ :=
  LinearMap.BilinForm.toLin.Injective <| b.ext fun i => b.ext fun j => h i j
#align bilin_form.ext_basis LinearMap.BilinForm.ext_basis
-/

#print LinearMap.BilinForm.sum_repr_mul_repr_mul /-
/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
theorem LinearMap.BilinForm.sum_repr_mul_repr_mul (x y : M₂) :
    ((b.repr x).Sum fun i xi => (b.repr y).Sum fun j yj => xi • yj • B₂ (b i) (b j)) = B₂ x y :=
  by
  conv_rhs => rw [← b.total_repr x, ← b.total_repr y]
  simp_rw [Finsupp.total_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right,
    smul_eq_mul]
#align bilin_form.sum_repr_mul_repr_mul LinearMap.BilinForm.sum_repr_mul_repr_mul
-/

end Basis

/-! ### Reflexivity, symmetry, and alternativity -/


#print LinearMap.BilinForm.IsRefl /-
/-- The proposition that a bilinear form is reflexive -/
def LinearMap.BilinForm.IsRefl (B : BilinForm R M) : Prop :=
  ∀ x y : M, B x y = 0 → B y x = 0
#align bilin_form.is_refl LinearMap.BilinForm.IsRefl
-/

namespace IsRefl

variable (H : B.IsRefl)

#print LinearMap.BilinForm.IsRefl.eq_zero /-
theorem LinearMap.BilinForm.IsRefl.eq_zero : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun x y => H x y
#align bilin_form.is_refl.eq_zero LinearMap.BilinForm.IsRefl.eq_zero
-/

#print LinearMap.BilinForm.IsRefl.ortho_comm /-
theorem LinearMap.BilinForm.IsRefl.ortho_comm {x y : M} :
    LinearMap.BilinForm.IsOrtho B x y ↔ LinearMap.BilinForm.IsOrtho B y x :=
  ⟨LinearMap.BilinForm.IsRefl.eq_zero H, LinearMap.BilinForm.IsRefl.eq_zero H⟩
#align bilin_form.is_refl.ortho_comm LinearMap.BilinForm.IsRefl.ortho_comm
-/

#print LinearMap.BilinForm.IsRefl.neg /-
protected theorem LinearMap.BilinForm.IsRefl.neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) :
    (-B).IsRefl := fun x y => neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp
#align bilin_form.is_refl.neg LinearMap.BilinForm.IsRefl.neg
-/

#print LinearMap.BilinForm.IsRefl.smul /-
protected theorem LinearMap.BilinForm.IsRefl.smul {α} [Semiring α] [Module α R]
    [SMulCommClass α R R] [NoZeroSMulDivisors α R] (a : α) {B : BilinForm R M} (hB : B.IsRefl) :
    (a • B).IsRefl := fun x y h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)
#align bilin_form.is_refl.smul LinearMap.BilinForm.IsRefl.smul
-/

#print LinearMap.BilinForm.IsRefl.groupSMul /-
protected theorem LinearMap.BilinForm.IsRefl.groupSMul {α} [Group α] [DistribMulAction α R]
    [SMulCommClass α R R] (a : α) {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp
#align bilin_form.is_refl.group_smul LinearMap.BilinForm.IsRefl.groupSMul
-/

end IsRefl

#print LinearMap.BilinForm.isRefl_zero /-
@[simp]
theorem LinearMap.BilinForm.isRefl_zero : (0 : BilinForm R M).IsRefl := fun _ _ _ => rfl
#align bilin_form.is_refl_zero LinearMap.BilinForm.isRefl_zero
-/

#print LinearMap.BilinForm.isRefl_neg /-
@[simp]
theorem LinearMap.BilinForm.isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl :=
  ⟨fun h => neg_neg B ▸ h.neg, LinearMap.BilinForm.IsRefl.neg⟩
#align bilin_form.is_refl_neg LinearMap.BilinForm.isRefl_neg
-/

#print LinearMap.BilinForm.IsSymm /-
/-- The proposition that a bilinear form is symmetric -/
def LinearMap.BilinForm.IsSymm (B : BilinForm R M) : Prop :=
  ∀ x y : M, B x y = B y x
#align bilin_form.is_symm LinearMap.BilinForm.IsSymm
-/

namespace IsSymm

variable (H : B.IsSymm)

#print LinearMap.BilinForm.IsSymm.eq /-
protected theorem LinearMap.BilinForm.IsSymm.eq (x y : M) : B x y = B y x :=
  H x y
#align bilin_form.is_symm.eq LinearMap.BilinForm.IsSymm.eq
-/

#print LinearMap.BilinForm.IsSymm.isRefl /-
theorem LinearMap.BilinForm.IsSymm.isRefl : B.IsRefl := fun x y H1 => H x y ▸ H1
#align bilin_form.is_symm.is_refl LinearMap.BilinForm.IsSymm.isRefl
-/

#print LinearMap.BilinForm.IsSymm.ortho_comm /-
theorem LinearMap.BilinForm.IsSymm.ortho_comm {x y : M} :
    LinearMap.BilinForm.IsOrtho B x y ↔ LinearMap.BilinForm.IsOrtho B y x :=
  H.IsRefl.ortho_comm
#align bilin_form.is_symm.ortho_comm LinearMap.BilinForm.IsSymm.ortho_comm
-/

#print LinearMap.BilinForm.IsSymm.add /-
protected theorem LinearMap.BilinForm.IsSymm.add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm)
    (hB₂ : B₂.IsSymm) : (B₁ + B₂).IsSymm := fun x y => (congr_arg₂ (· + ·) (hB₁ x y) (hB₂ x y) : _)
#align bilin_form.is_symm.add LinearMap.BilinForm.IsSymm.add
-/

#print LinearMap.BilinForm.IsSymm.sub /-
protected theorem LinearMap.BilinForm.IsSymm.sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm)
    (hB₂ : B₂.IsSymm) : (B₁ - B₂).IsSymm := fun x y => (congr_arg₂ Sub.sub (hB₁ x y) (hB₂ x y) : _)
#align bilin_form.is_symm.sub LinearMap.BilinForm.IsSymm.sub
-/

#print LinearMap.BilinForm.IsSymm.neg /-
protected theorem LinearMap.BilinForm.IsSymm.neg {B : BilinForm R₁ M₁} (hB : B.IsSymm) :
    (-B).IsSymm := fun x y => congr_arg Neg.neg (hB x y)
#align bilin_form.is_symm.neg LinearMap.BilinForm.IsSymm.neg
-/

#print LinearMap.BilinForm.IsSymm.smul /-
protected theorem LinearMap.BilinForm.IsSymm.smul {α} [Monoid α] [DistribMulAction α R]
    [SMulCommClass α R R] (a : α) {B : BilinForm R M} (hB : B.IsSymm) : (a • B).IsSymm := fun x y =>
  congr_arg ((· • ·) a) (hB x y)
#align bilin_form.is_symm.smul LinearMap.BilinForm.IsSymm.smul
-/

end IsSymm

#print LinearMap.BilinForm.isSymm_zero /-
@[simp]
theorem LinearMap.BilinForm.isSymm_zero : (0 : BilinForm R M).IsSymm := fun _ _ => rfl
#align bilin_form.is_symm_zero LinearMap.BilinForm.isSymm_zero
-/

#print LinearMap.BilinForm.isSymm_neg /-
@[simp]
theorem LinearMap.BilinForm.isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm :=
  ⟨fun h => neg_neg B ▸ h.neg, LinearMap.BilinForm.IsSymm.neg⟩
#align bilin_form.is_symm_neg LinearMap.BilinForm.isSymm_neg
-/

#print LinearMap.BilinForm.isSymm_iff_flip /-
theorem LinearMap.BilinForm.isSymm_iff_flip [Algebra R₂ R] :
    B.IsSymm ↔ LinearMap.BilinForm.flipHom R₂ B = B :=
  by
  constructor
  · intro h
    ext x y
    exact h y x
  · intro h x y
    conv_lhs => rw [← h]
    simp
#align bilin_form.is_symm_iff_flip' LinearMap.BilinForm.isSymm_iff_flip
-/

#print LinearMap.BilinForm.IsAlt /-
/-- The proposition that a bilinear form is alternating -/
def LinearMap.BilinForm.IsAlt (B : BilinForm R M) : Prop :=
  ∀ x : M, B x x = 0
#align bilin_form.is_alt LinearMap.BilinForm.IsAlt
-/

namespace IsAlt

#print LinearMap.BilinForm.IsAlt.self_eq_zero /-
theorem LinearMap.BilinForm.IsAlt.self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 :=
  H x
#align bilin_form.is_alt.self_eq_zero LinearMap.BilinForm.IsAlt.self_eq_zero
-/

#print LinearMap.BilinForm.IsAlt.neg_eq /-
theorem LinearMap.BilinForm.IsAlt.neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x :=
  by
  have H1 : B₁ (x + y) (x + y) = 0 := self_eq_zero H (x + y)
  rw [add_left, add_right, add_right, self_eq_zero H, self_eq_zero H, Ring.zero_add, Ring.add_zero,
    add_eq_zero_iff_neg_eq] at H1
  exact H1
#align bilin_form.is_alt.neg_eq LinearMap.BilinForm.IsAlt.neg_eq
-/

#print LinearMap.BilinForm.IsAlt.isRefl /-
theorem LinearMap.BilinForm.IsAlt.isRefl (H : B₁.IsAlt) : B₁.IsRefl :=
  by
  intro x y h
  rw [← neg_eq H, h, neg_zero]
#align bilin_form.is_alt.is_refl LinearMap.BilinForm.IsAlt.isRefl
-/

#print LinearMap.BilinForm.IsAlt.ortho_comm /-
theorem LinearMap.BilinForm.IsAlt.ortho_comm (H : B₁.IsAlt) {x y : M₁} :
    LinearMap.BilinForm.IsOrtho B₁ x y ↔ LinearMap.BilinForm.IsOrtho B₁ y x :=
  H.IsRefl.ortho_comm
#align bilin_form.is_alt.ortho_comm LinearMap.BilinForm.IsAlt.ortho_comm
-/

#print LinearMap.BilinForm.IsAlt.add /-
protected theorem LinearMap.BilinForm.IsAlt.add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt)
    (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt := fun x =>
  (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) : _).trans <| add_zero _
#align bilin_form.is_alt.add LinearMap.BilinForm.IsAlt.add
-/

#print LinearMap.BilinForm.IsAlt.sub /-
protected theorem LinearMap.BilinForm.IsAlt.sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt)
    (hB₂ : B₂.IsAlt) : (B₁ - B₂).IsAlt := fun x =>
  (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans <| sub_zero _
#align bilin_form.is_alt.sub LinearMap.BilinForm.IsAlt.sub
-/

#print LinearMap.BilinForm.IsAlt.neg /-
protected theorem LinearMap.BilinForm.IsAlt.neg {B : BilinForm R₁ M₁} (hB : B.IsAlt) : (-B).IsAlt :=
  fun x => neg_eq_zero.mpr <| hB x
#align bilin_form.is_alt.neg LinearMap.BilinForm.IsAlt.neg
-/

#print LinearMap.BilinForm.IsAlt.smul /-
protected theorem LinearMap.BilinForm.IsAlt.smul {α} [Monoid α] [DistribMulAction α R]
    [SMulCommClass α R R] (a : α) {B : BilinForm R M} (hB : B.IsAlt) : (a • B).IsAlt := fun x =>
  (congr_arg ((· • ·) a) (hB x)).trans <| smul_zero _
#align bilin_form.is_alt.smul LinearMap.BilinForm.IsAlt.smul
-/

end IsAlt

#print LinearMap.BilinForm.isAlt_zero /-
@[simp]
theorem LinearMap.BilinForm.isAlt_zero : (0 : BilinForm R M).IsAlt := fun _ => rfl
#align bilin_form.is_alt_zero LinearMap.BilinForm.isAlt_zero
-/

#print LinearMap.BilinForm.isAlt_neg /-
@[simp]
theorem LinearMap.BilinForm.isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt :=
  ⟨fun h => neg_neg B ▸ h.neg, LinearMap.BilinForm.IsAlt.neg⟩
#align bilin_form.is_alt_neg LinearMap.BilinForm.isAlt_neg
-/

/-! ### Linear adjoints -/


section LinearAdjoints

variable (B) (F : BilinForm R M)

variable {M' : Type _} [AddCommMonoid M'] [Module R M']

variable (B' : BilinForm R M') (f f' : M →ₗ[R] M') (g g' : M' →ₗ[R] M)

#print LinearMap.BilinForm.IsAdjointPair /-
/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def LinearMap.BilinForm.IsAdjointPair :=
  ∀ ⦃x y⦄, B' (f x) y = B x (g y)
#align bilin_form.is_adjoint_pair LinearMap.BilinForm.IsAdjointPair
-/

variable {B B' B₂ f f' g g'}

#print LinearMap.BilinForm.IsAdjointPair.eq /-
theorem LinearMap.BilinForm.IsAdjointPair.eq (h : LinearMap.BilinForm.IsAdjointPair B B' f g) :
    ∀ {x y}, B' (f x) y = B x (g y) :=
  h
#align bilin_form.is_adjoint_pair.eq LinearMap.BilinForm.IsAdjointPair.eq
-/

#print LinearMap.BilinForm.isAdjointPair_iff_compLeft_eq_compRight /-
theorem LinearMap.BilinForm.isAdjointPair_iff_compLeft_eq_compRight (f g : Module.End R M) :
    LinearMap.BilinForm.IsAdjointPair B F f g ↔ F.compLeft f = B.compRight g :=
  by
  constructor <;> intro h
  · ext x y; rw [comp_left_apply, comp_right_apply]; apply h
  · intro x y; rw [← comp_left_apply, ← comp_right_apply]; rw [h]
#align bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right LinearMap.BilinForm.isAdjointPair_iff_compLeft_eq_compRight
-/

#print LinearMap.BilinForm.isAdjointPair_zero /-
theorem LinearMap.BilinForm.isAdjointPair_zero : LinearMap.BilinForm.IsAdjointPair B B' 0 0 :=
  fun x y => by
  simp only [LinearMap.BilinForm.zero_left, LinearMap.BilinForm.zero_right, LinearMap.zero_apply]
#align bilin_form.is_adjoint_pair_zero LinearMap.BilinForm.isAdjointPair_zero
-/

#print LinearMap.BilinForm.isAdjointPair_id /-
theorem LinearMap.BilinForm.isAdjointPair_id : LinearMap.BilinForm.IsAdjointPair B B 1 1 :=
  fun x y => rfl
#align bilin_form.is_adjoint_pair_id LinearMap.BilinForm.isAdjointPair_id
-/

#print LinearMap.BilinForm.IsAdjointPair.add /-
theorem LinearMap.BilinForm.IsAdjointPair.add (h : LinearMap.BilinForm.IsAdjointPair B B' f g)
    (h' : LinearMap.BilinForm.IsAdjointPair B B' f' g') :
    LinearMap.BilinForm.IsAdjointPair B B' (f + f') (g + g') := fun x y => by
  rw [LinearMap.add_apply, LinearMap.add_apply, add_left, add_right, h, h']
#align bilin_form.is_adjoint_pair.add LinearMap.BilinForm.IsAdjointPair.add
-/

variable {M₁' : Type _} [AddCommGroup M₁'] [Module R₁ M₁']

variable {B₁' : BilinForm R₁ M₁'} {f₁ f₁' : M₁ →ₗ[R₁] M₁'} {g₁ g₁' : M₁' →ₗ[R₁] M₁}

#print LinearMap.BilinForm.IsAdjointPair.sub /-
theorem LinearMap.BilinForm.IsAdjointPair.sub (h : LinearMap.BilinForm.IsAdjointPair B₁ B₁' f₁ g₁)
    (h' : LinearMap.BilinForm.IsAdjointPair B₁ B₁' f₁' g₁') :
    LinearMap.BilinForm.IsAdjointPair B₁ B₁' (f₁ - f₁') (g₁ - g₁') := fun x y => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_left, sub_right, h, h']
#align bilin_form.is_adjoint_pair.sub LinearMap.BilinForm.IsAdjointPair.sub
-/

variable {B₂' : BilinForm R₂ M₂'} {f₂ f₂' : M₂ →ₗ[R₂] M₂'} {g₂ g₂' : M₂' →ₗ[R₂] M₂}

#print LinearMap.BilinForm.IsAdjointPair.smul /-
theorem LinearMap.BilinForm.IsAdjointPair.smul (c : R₂)
    (h : LinearMap.BilinForm.IsAdjointPair B₂ B₂' f₂ g₂) :
    LinearMap.BilinForm.IsAdjointPair B₂ B₂' (c • f₂) (c • g₂) := fun x y => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_left, smul_right, h]
#align bilin_form.is_adjoint_pair.smul LinearMap.BilinForm.IsAdjointPair.smul
-/

variable {M'' : Type _} [AddCommMonoid M''] [Module R M'']

variable (B'' : BilinForm R M'')

#print LinearMap.BilinForm.IsAdjointPair.comp /-
theorem LinearMap.BilinForm.IsAdjointPair.comp {f' : M' →ₗ[R] M''} {g' : M'' →ₗ[R] M'}
    (h : LinearMap.BilinForm.IsAdjointPair B B' f g)
    (h' : LinearMap.BilinForm.IsAdjointPair B' B'' f' g') :
    LinearMap.BilinForm.IsAdjointPair B B'' (f'.comp f) (g.comp g') := fun x y => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h', h]
#align bilin_form.is_adjoint_pair.comp LinearMap.BilinForm.IsAdjointPair.comp
-/

#print LinearMap.BilinForm.IsAdjointPair.mul /-
theorem LinearMap.BilinForm.IsAdjointPair.mul {f g f' g' : Module.End R M}
    (h : LinearMap.BilinForm.IsAdjointPair B B f g)
    (h' : LinearMap.BilinForm.IsAdjointPair B B f' g') :
    LinearMap.BilinForm.IsAdjointPair B B (f * f') (g' * g) := fun x y => by
  rw [LinearMap.mul_apply, LinearMap.mul_apply, h, h']
#align bilin_form.is_adjoint_pair.mul LinearMap.BilinForm.IsAdjointPair.mul
-/

variable (B B' B₁ B₂) (F₂ : BilinForm R₂ M₂)

#print LinearMap.BilinForm.IsPairSelfAdjoint /-
/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def LinearMap.BilinForm.IsPairSelfAdjoint (f : Module.End R M) :=
  LinearMap.BilinForm.IsAdjointPair B F f f
#align bilin_form.is_pair_self_adjoint LinearMap.BilinForm.IsPairSelfAdjoint
-/

#print LinearMap.BilinForm.isPairSelfAdjointSubmodule /-
/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def LinearMap.BilinForm.isPairSelfAdjointSubmodule : Submodule R₂ (Module.End R₂ M₂)
    where
  carrier := {f | LinearMap.BilinForm.IsPairSelfAdjoint B₂ F₂ f}
  zero_mem' := LinearMap.BilinForm.isAdjointPair_zero
  add_mem' f g hf hg := hf.add hg
  smul_mem' c f h := h.smul c
#align bilin_form.is_pair_self_adjoint_submodule LinearMap.BilinForm.isPairSelfAdjointSubmodule
-/

#print LinearMap.BilinForm.mem_isPairSelfAdjointSubmodule /-
@[simp]
theorem LinearMap.BilinForm.mem_isPairSelfAdjointSubmodule (f : Module.End R₂ M₂) :
    f ∈ LinearMap.BilinForm.isPairSelfAdjointSubmodule B₂ F₂ ↔
      LinearMap.BilinForm.IsPairSelfAdjoint B₂ F₂ f :=
  by rfl
#align bilin_form.mem_is_pair_self_adjoint_submodule LinearMap.BilinForm.mem_isPairSelfAdjointSubmodule
-/

#print LinearMap.BilinForm.isPairSelfAdjoint_equiv /-
theorem LinearMap.BilinForm.isPairSelfAdjoint_equiv (e : M₂' ≃ₗ[R₂] M₂) (f : Module.End R₂ M₂) :
    LinearMap.BilinForm.IsPairSelfAdjoint B₂ F₂ f ↔
      LinearMap.BilinForm.IsPairSelfAdjoint (B₂.comp ↑e ↑e) (F₂.comp ↑e ↑e) (e.symm.conj f) :=
  by
  have hₗ : (F₂.comp ↑e ↑e).compLeft (e.symm.conj f) = (F₂.comp_left f).comp ↑e ↑e := by ext;
    simp [LinearEquiv.symm_conj_apply]
  have hᵣ : (B₂.comp ↑e ↑e).compRight (e.symm.conj f) = (B₂.comp_right f).comp ↑e ↑e := by ext;
    simp [LinearEquiv.conj_apply]
  have he : Function.Surjective (⇑(↑e : M₂' →ₗ[R₂] M₂) : M₂' → M₂) := e.surjective
  show LinearMap.BilinForm.IsAdjointPair _ _ _ _ ↔ LinearMap.BilinForm.IsAdjointPair _ _ _ _
  rw [is_adjoint_pair_iff_comp_left_eq_comp_right, is_adjoint_pair_iff_comp_left_eq_comp_right, hᵣ,
    hₗ, comp_inj _ _ he he]
#align bilin_form.is_pair_self_adjoint_equiv LinearMap.BilinForm.isPairSelfAdjoint_equiv
-/

#print LinearMap.BilinForm.IsSelfAdjoint /-
/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def LinearMap.BilinForm.IsSelfAdjoint (f : Module.End R M) :=
  LinearMap.BilinForm.IsAdjointPair B B f f
#align bilin_form.is_self_adjoint LinearMap.BilinForm.IsSelfAdjoint
-/

#print LinearMap.BilinForm.IsSkewAdjoint /-
/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def LinearMap.BilinForm.IsSkewAdjoint (f : Module.End R₁ M₁) :=
  LinearMap.BilinForm.IsAdjointPair B₁ B₁ f (-f)
#align bilin_form.is_skew_adjoint LinearMap.BilinForm.IsSkewAdjoint
-/

#print LinearMap.BilinForm.isSkewAdjoint_iff_neg_self_adjoint /-
theorem LinearMap.BilinForm.isSkewAdjoint_iff_neg_self_adjoint (f : Module.End R₁ M₁) :
    B₁.IsSkewAdjoint f ↔ LinearMap.BilinForm.IsAdjointPair (-B₁) B₁ f f :=
  show (∀ x y, B₁ (f x) y = B₁ x ((-f) y)) ↔ ∀ x y, B₁ (f x) y = (-B₁) x (f y) by
    simp only [LinearMap.neg_apply, LinearMap.BilinForm.neg_apply, LinearMap.BilinForm.neg_right]
#align bilin_form.is_skew_adjoint_iff_neg_self_adjoint LinearMap.BilinForm.isSkewAdjoint_iff_neg_self_adjoint
-/

#print LinearMap.BilinForm.selfAdjointSubmodule /-
/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def LinearMap.BilinForm.selfAdjointSubmodule :=
  LinearMap.BilinForm.isPairSelfAdjointSubmodule B₂ B₂
#align bilin_form.self_adjoint_submodule LinearMap.BilinForm.selfAdjointSubmodule
-/

#print LinearMap.BilinForm.mem_selfAdjointSubmodule /-
@[simp]
theorem LinearMap.BilinForm.mem_selfAdjointSubmodule (f : Module.End R₂ M₂) :
    f ∈ B₂.selfAdjointSubmodule ↔ B₂.IsSelfAdjoint f :=
  Iff.rfl
#align bilin_form.mem_self_adjoint_submodule LinearMap.BilinForm.mem_selfAdjointSubmodule
-/

variable (B₃ : BilinForm R₃ M₃)

#print LinearMap.BilinForm.skewAdjointSubmodule /-
/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def LinearMap.BilinForm.skewAdjointSubmodule :=
  LinearMap.BilinForm.isPairSelfAdjointSubmodule (-B₃) B₃
#align bilin_form.skew_adjoint_submodule LinearMap.BilinForm.skewAdjointSubmodule
-/

#print LinearMap.BilinForm.mem_skewAdjointSubmodule /-
@[simp]
theorem LinearMap.BilinForm.mem_skewAdjointSubmodule (f : Module.End R₃ M₃) :
    f ∈ B₃.skewAdjointSubmodule ↔ B₃.IsSkewAdjoint f := by
  rw [is_skew_adjoint_iff_neg_self_adjoint]; exact Iff.rfl
#align bilin_form.mem_skew_adjoint_submodule LinearMap.BilinForm.mem_skewAdjointSubmodule
-/

end LinearAdjoints

end BilinForm

namespace BilinForm

section Orthogonal

#print LinearMap.BilinForm.orthogonal /-
/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def LinearMap.BilinForm.orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M
    where
  carrier := {m | ∀ n ∈ N, LinearMap.BilinForm.IsOrtho B n m}
  zero_mem' x _ := LinearMap.BilinForm.isOrtho_zero_right x
  add_mem' x y hx hy n hn := by
    rw [is_ortho, add_right, show B n x = 0 from hx n hn, show B n y = 0 from hy n hn, zero_add]
  smul_mem' c x hx n hn := by
    rw [is_ortho, smul_right, show B n x = 0 from hx n hn, MulZeroClass.mul_zero]
#align bilin_form.orthogonal LinearMap.BilinForm.orthogonal
-/

variable {N L : Submodule R M}

#print LinearMap.BilinForm.mem_orthogonal_iff /-
@[simp]
theorem LinearMap.BilinForm.mem_orthogonal_iff {N : Submodule R M} {m : M} :
    m ∈ B.orthogonal N ↔ ∀ n ∈ N, LinearMap.BilinForm.IsOrtho B n m :=
  Iff.rfl
#align bilin_form.mem_orthogonal_iff LinearMap.BilinForm.mem_orthogonal_iff
-/

#print LinearMap.BilinForm.orthogonal_le /-
theorem LinearMap.BilinForm.orthogonal_le (h : N ≤ L) : B.orthogonal L ≤ B.orthogonal N :=
  fun _ hn l hl => hn l (h hl)
#align bilin_form.orthogonal_le LinearMap.BilinForm.orthogonal_le
-/

#print LinearMap.BilinForm.le_orthogonal_orthogonal /-
theorem LinearMap.BilinForm.le_orthogonal_orthogonal (b : B.IsRefl) :
    N ≤ B.orthogonal (B.orthogonal N) := fun n hn m hm => b _ _ (hm n hn)
#align bilin_form.le_orthogonal_orthogonal LinearMap.BilinForm.le_orthogonal_orthogonal
-/

#print LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot /-
-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot {B : BilinForm K V} {x : V}
    (hx : ¬B.IsOrtho x x) : (K ∙ x) ⊓ B.orthogonal (K ∙ x) = ⊥ :=
  by
  rw [← Finset.coe_singleton]
  refine' eq_bot_iff.2 fun y h => _
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩
  have := h.2 x _
  · rw [Finset.sum_singleton] at this ⊢
    suffices hμzero : μ x = 0
    · rw [hμzero, zero_smul, Submodule.mem_bot]
    change B x (μ x • x) = 0 at this; rw [smul_right] at this
    exact Or.elim (zero_eq_mul.mp this.symm) id fun hfalse => False.elim <| hx hfalse
  · rw [Submodule.mem_span] <;> exact fun _ hp => hp <| Finset.mem_singleton_self _
#align bilin_form.span_singleton_inf_orthogonal_eq_bot LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot
-/

#print LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker /-
-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) :
    B.orthogonal (K ∙ x) = (LinearMap.BilinForm.toLin B x).ker :=
  by
  ext y
  simp_rw [mem_orthogonal_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [is_ortho, smul_left, mul_eq_zero]
    exact Or.intro_right _ h
#align bilin_form.orthogonal_span_singleton_eq_to_lin_ker LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker
-/

#print LinearMap.BilinForm.span_singleton_sup_orthogonal_eq_top /-
theorem LinearMap.BilinForm.span_singleton_sup_orthogonal_eq_top {B : BilinForm K V} {x : V}
    (hx : ¬B.IsOrtho x x) : (K ∙ x) ⊔ B.orthogonal (K ∙ x) = ⊤ :=
  by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact LinearMap.span_singleton_sup_ker_eq_top _ hx
#align bilin_form.span_singleton_sup_orthogonal_eq_top LinearMap.BilinForm.span_singleton_sup_orthogonal_eq_top
-/

#print LinearMap.BilinForm.isCompl_span_singleton_orthogonal /-
/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem LinearMap.BilinForm.isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V}
    (hx : ¬B.IsOrtho x x) : IsCompl (K ∙ x) (B.orthogonal <| K ∙ x) :=
  { Disjoint := disjoint_iff.2 <| LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot hx
    Codisjoint := codisjoint_iff.2 <| LinearMap.BilinForm.span_singleton_sup_orthogonal_eq_top hx }
#align bilin_form.is_compl_span_singleton_orthogonal LinearMap.BilinForm.isCompl_span_singleton_orthogonal
-/

end Orthogonal

#print LinearMap.BilinForm.restrict /-
/-- The restriction of a bilinear form on a submodule. -/
@[simps apply]
def LinearMap.BilinForm.restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W
    where
  bilin a b := B a b
  bilin_add_left _ _ _ := LinearMap.BilinForm.add_left _ _ _
  bilin_smul_left _ _ _ := LinearMap.BilinForm.smul_left _ _ _
  bilin_add_right _ _ _ := LinearMap.BilinForm.add_right _ _ _
  bilin_smul_right _ _ _ := LinearMap.BilinForm.smul_right _ _ _
#align bilin_form.restrict LinearMap.BilinForm.restrict
-/

#print LinearMap.BilinForm.IsSymm.restrict /-
/-- The restriction of a symmetric bilinear form on a submodule is also symmetric. -/
theorem LinearMap.BilinForm.IsSymm.restrict (B : BilinForm R M) (b : B.IsSymm) (W : Submodule R M) :
    (B.restrict W).IsSymm := fun x y => b x y
#align bilin_form.restrict_symm LinearMap.BilinForm.IsSymm.restrict
-/

#print LinearMap.BilinForm.Nondegenerate /-
/-- A nondegenerate bilinear form is a bilinear form such that the only element that is orthogonal
to every other element is `0`; i.e., for all nonzero `m` in `M`, there exists `n` in `M` with
`B m n ≠ 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" nondegeneracy condition one could define a "right"
nondegeneracy condition that in the situation described, `B n m ≠ 0`.  This variant definition is
not currently provided in mathlib. In finite dimension either definition implies the other. -/
def LinearMap.BilinForm.Nondegenerate (B : BilinForm R M) : Prop :=
  ∀ m : M, (∀ n : M, B m n = 0) → m = 0
#align bilin_form.nondegenerate LinearMap.BilinForm.Nondegenerate
-/

section

variable (R M)

#print LinearMap.BilinForm.not_nondegenerate_zero /-
/-- In a non-trivial module, zero is not non-degenerate. -/
theorem LinearMap.BilinForm.not_nondegenerate_zero [Nontrivial M] :
    ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h m fun n => rfl)
#align bilin_form.not_nondegenerate_zero LinearMap.BilinForm.not_nondegenerate_zero
-/

end

variable {M₂' : Type _}

variable [AddCommMonoid M₂'] [Module R₂ M₂']

#print LinearMap.BilinForm.Nondegenerate.ne_zero /-
theorem LinearMap.BilinForm.Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M}
    (h : B.Nondegenerate) : B ≠ 0 := fun h0 =>
  LinearMap.BilinForm.not_nondegenerate_zero R M <| h0 ▸ h
#align bilin_form.nondegenerate.ne_zero LinearMap.BilinForm.Nondegenerate.ne_zero
-/

#print LinearMap.BilinForm.Nondegenerate.congr /-
theorem LinearMap.BilinForm.Nondegenerate.congr {B : BilinForm R₂ M₂} (e : M₂ ≃ₗ[R₂] M₂')
    (h : B.Nondegenerate) : (LinearMap.BilinForm.congr e B).Nondegenerate := fun m hm =>
  e.symm.map_eq_zero_iff.1 <|
    h (e.symm m) fun n => (congr_arg _ (e.symm_apply_apply n).symm).trans (hm (e n))
#align bilin_form.nondegenerate.congr LinearMap.BilinForm.Nondegenerate.congr
-/

#print LinearMap.BilinForm.nondegenerate_congr_iff /-
@[simp]
theorem LinearMap.BilinForm.nondegenerate_congr_iff {B : BilinForm R₂ M₂} (e : M₂ ≃ₗ[R₂] M₂') :
    (LinearMap.BilinForm.congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert h.congr e.symm
    rw [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply],
    LinearMap.BilinForm.Nondegenerate.congr e⟩
#align bilin_form.nondegenerate_congr_iff LinearMap.BilinForm.nondegenerate_congr_iff
-/

#print LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot /-
/-- A bilinear form is nondegenerate if and only if it has a trivial kernel. -/
theorem LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot {B : BilinForm R₂ M₂} :
    B.Nondegenerate ↔ B.toLin.ker = ⊥ :=
  by
  rw [LinearMap.ker_eq_bot']
  constructor <;> intro h
  · refine' fun m hm => h _ fun x => _
    rw [← to_lin_apply, hm]; rfl
  · intro m hm; apply h
    ext x; exact hm x
#align bilin_form.nondegenerate_iff_ker_eq_bot LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot
-/

#print LinearMap.BilinForm.Nondegenerate.ker_eq_bot /-
theorem LinearMap.BilinForm.Nondegenerate.ker_eq_bot {B : BilinForm R₂ M₂} (h : B.Nondegenerate) :
    B.toLin.ker = ⊥ :=
  LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mp h
#align bilin_form.nondegenerate.ker_eq_bot LinearMap.BilinForm.Nondegenerate.ker_eq_bot
-/

#print LinearMap.BilinForm.nondegenerateRestrictOfDisjointOrthogonal /-
/-- The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `disjoint W (B.orthogonal W)`. -/
theorem LinearMap.BilinForm.nondegenerateRestrictOfDisjointOrthogonal (B : BilinForm R₁ M₁)
    (b : B.IsRefl) {W : Submodule R₁ M₁} (hW : Disjoint W (B.orthogonal W)) :
    (B.restrict W).Nondegenerate := by
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R₁]
  refine' hW.le_bot ⟨hx, fun y hy => _⟩
  specialize b₁ ⟨y, hy⟩
  rw [restrict_apply, Submodule.coe_mk, Submodule.coe_mk] at b₁
  exact is_ortho_def.mpr (b x y b₁)
#align bilin_form.nondegenerate_restrict_of_disjoint_orthogonal LinearMap.BilinForm.nondegenerateRestrictOfDisjointOrthogonal
-/

#print LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate /-
/-- An orthogonal basis with respect to a nondegenerate bilinear form has no self-orthogonal
elements. -/
theorem LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate {n : Type w}
    [Nontrivial R] {B : BilinForm R M} {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.Nondegenerate)
    (i : n) : ¬B.IsOrtho (v i) (v i) := by
  intro ho
  refine' v.ne_zero i (hB (v i) fun m => _)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, sum_right]
  apply Finset.sum_eq_zero
  rintro j -
  rw [smul_right]
  convert MulZeroClass.mul_zero _ using 2
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij
#align bilin_form.is_Ortho.not_is_ortho_basis_self_of_nondegenerate LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
-/

#print LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self /-
/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is nondegenerate
iff the basis has no elements which are self-orthogonal. -/
theorem LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self {n : Type w}
    [Nontrivial R] [NoZeroDivisors R] (B : BilinForm R M) (v : Basis n R M) (hO : B.IsOrthoᵢ v) :
    B.Nondegenerate ↔ ∀ i, ¬B.IsOrtho (v i) (v i) :=
  by
  refine' ⟨hO.not_is_ortho_basis_self_of_nondegenerate, fun ho m hB => _⟩
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, sum_left, smul_left] at hB
  rw [Finset.sum_eq_single i] at hB
  · exact eq_zero_of_ne_zero_of_mul_right_eq_zero (ho i) hB
  · intro j hj hij; convert MulZeroClass.mul_zero _ using 2; exact hO hij
  · intro hi; convert MulZeroClass.zero_mul _ using 2; exact finsupp.not_mem_support_iff.mp hi
#align bilin_form.is_Ortho.nondegenerate_iff_not_is_ortho_basis_self LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self
-/

section

#print LinearMap.BilinForm.toLin_restrict_ker_eq_inf_orthogonal /-
theorem LinearMap.BilinForm.toLin_restrict_ker_eq_inf_orthogonal (B : BilinForm K V)
    (W : Subspace K V) (b : B.IsRefl) :
    (B.toLin.domRestrict W).ker.map W.Subtype = (W ⊓ B.orthogonal ⊤ : Subspace K V) :=
  by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    erw [LinearMap.mem_ker] at hker
    constructor
    · simp [hx]
    · intro y _
      rw [is_ortho, b]
      change (B.to_lin.dom_restrict W) ⟨x, hx⟩ y = 0
      rw [hker]; rfl
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    refine' ⟨⟨x, hx.1⟩, _, rfl⟩
    ext y; change B x y = 0
    rw [b]
    exact hx.2 _ Submodule.mem_top
#align bilin_form.to_lin_restrict_ker_eq_inf_orthogonal LinearMap.BilinForm.toLin_restrict_ker_eq_inf_orthogonal
-/

#print LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal /-
theorem LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : BilinForm K V)
    (W : Subspace K V) : (B.toLin.domRestrict W).range.dualCoannihilator = B.orthogonal W :=
  by
  ext x; constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dualCoannihilator] at hx
    refine' hx (B.to_lin.dom_restrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [Submodule.mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw
#align bilin_form.to_lin_restrict_range_dual_coannihilator_eq_orthogonal LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal
-/

variable [FiniteDimensional K V]

open FiniteDimensional

#print LinearMap.BilinForm.finrank_add_finrank_orthogonal /-
theorem LinearMap.BilinForm.finrank_add_finrank_orthogonal {B : BilinForm K V} {W : Subspace K V}
    (b₁ : B.IsRefl) :
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.orthogonal ⊤ : Subspace K V) :=
  by
  rw [← to_lin_restrict_ker_eq_inf_orthogonal _ _ b₁, ←
    to_lin_restrict_range_dual_coannihilator_eq_orthogonal _ _, submodule.finrank_map_subtype_eq]
  conv_rhs =>
    rw [←
      @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (B.to_lin.dom_restrict W).range,
      add_comm, ← add_assoc, add_comm (finrank K ↥(B.to_lin.dom_restrict W).ker),
      LinearMap.finrank_range_add_finrank_ker]
#align bilin_form.finrank_add_finrank_orthogonal LinearMap.BilinForm.finrank_add_finrank_orthogonal
-/

#print LinearMap.BilinForm.restrict_nondegenerate_of_isCompl_orthogonal /-
/-- A subspace is complement to its orthogonal complement with respect to some
reflexive bilinear form if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem LinearMap.BilinForm.restrict_nondegenerate_of_isCompl_orthogonal {B : BilinForm K V}
    {W : Subspace K V} (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) :
    IsCompl W (B.orthogonal W) :=
  by
  have : W ⊓ B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Submodule.mem_inf.1 hx
    refine' Subtype.mk_eq_mk.1 (b₂ ⟨x, hx₁⟩ _)
    rintro ⟨n, hn⟩
    rw [restrict_apply, Submodule.coe_mk, Submodule.coe_mk, b₁]
    exact hx₂ n hn
  refine' IsCompl.of_eq this (eq_top_of_finrank_eq <| (Submodule.finrank_le _).antisymm _)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K V, ← this, Submodule.finrank_sup_add_finrank_inf_eq,
    finrank_add_finrank_orthogonal b₁]
  exact le_self_add
#align bilin_form.restrict_nondegenerate_of_is_compl_orthogonal LinearMap.BilinForm.restrict_nondegenerate_of_isCompl_orthogonal
-/

#print LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal /-
/-- A subspace is complement to its orthogonal complement with respect to some reflexive bilinear
form if and only if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal {B : BilinForm K V}
    {W : Subspace K V} (b₁ : B.IsRefl) :
    (B.restrict W).Nondegenerate ↔ IsCompl W (B.orthogonal W) :=
  ⟨fun b₂ => LinearMap.BilinForm.restrict_nondegenerate_of_isCompl_orthogonal b₁ b₂, fun h =>
    B.nondegenerateRestrictOfDisjointOrthogonal b₁ h.1⟩
#align bilin_form.restrict_nondegenerate_iff_is_compl_orthogonal LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
-/

#print LinearMap.BilinForm.toDual /-
/-- Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B.to_dual` is
the linear equivalence between a vector space and its dual with the underlying linear map
`B.to_lin`. -/
noncomputable def LinearMap.BilinForm.toDual (B : BilinForm K V) (b : B.Nondegenerate) :
    V ≃ₗ[K] Module.Dual K V :=
  B.toLin.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm
#align bilin_form.to_dual LinearMap.BilinForm.toDual
-/

#print LinearMap.BilinForm.toDual_def /-
theorem LinearMap.BilinForm.toDual_def {B : BilinForm K V} (b : B.Nondegenerate) {m n : V} :
    B.toDual b m n = B m n :=
  rfl
#align bilin_form.to_dual_def LinearMap.BilinForm.toDual_def
-/

section DualBasis

variable {ι : Type _} [DecidableEq ι] [Fintype ι]

#print LinearMap.BilinForm.dualBasis /-
/-- The `B`-dual basis `B.dual_basis hB b` to a finite basis `b` satisfies
`B (B.dual_basis hB b i) (b j) = B (b i) (B.dual_basis hB b j) = if i = j then 1 else 0`,
where `B` is a nondegenerate (symmetric) bilinear form and `b` is a finite basis. -/
noncomputable def LinearMap.BilinForm.dualBasis (B : BilinForm K V) (hB : B.Nondegenerate)
    (b : Basis ι K V) : Basis ι K V :=
  b.dualBasis.map (B.toDual hB).symm
#align bilin_form.dual_basis LinearMap.BilinForm.dualBasis
-/

#print LinearMap.BilinForm.dualBasis_repr_apply /-
@[simp]
theorem LinearMap.BilinForm.dualBasis_repr_apply (B : BilinForm K V) (hB : B.Nondegenerate)
    (b : Basis ι K V) (x i) : (B.dualBasis hB b).repr x i = B x (b i) := by
  rw [dual_basis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, to_dual_def]
#align bilin_form.dual_basis_repr_apply LinearMap.BilinForm.dualBasis_repr_apply
-/

#print LinearMap.BilinForm.apply_dualBasis_left /-
theorem LinearMap.BilinForm.apply_dualBasis_left (B : BilinForm K V) (hB : B.Nondegenerate)
    (b : Basis ι K V) (i j) : B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  rw [dual_basis, Basis.map_apply, Basis.coe_dualBasis, ← to_dual_def hB,
    LinearEquiv.apply_symm_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
#align bilin_form.apply_dual_basis_left LinearMap.BilinForm.apply_dualBasis_left
-/

#print LinearMap.BilinForm.apply_dualBasis_right /-
theorem LinearMap.BilinForm.apply_dualBasis_right (B : BilinForm K V) (hB : B.Nondegenerate)
    (sym : B.IsSymm) (b : Basis ι K V) (i j) :
    B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by rw [Sym, apply_dual_basis_left]
#align bilin_form.apply_dual_basis_right LinearMap.BilinForm.apply_dualBasis_right
-/

end DualBasis

end

/-! We note that we cannot use `bilin_form.restrict_nondegenerate_iff_is_compl_orthogonal` for the
lemma below since the below lemma does not require `V` to be finite dimensional. However,
`bilin_form.restrict_nondegenerate_iff_is_compl_orthogonal` does not require `B` to be nondegenerate
on the whole space. -/


#print LinearMap.BilinForm.restrictOrthogonalSpanSingletonNondegenerate /-
/-- The restriction of a reflexive, non-degenerate bilinear form on the orthogonal complement of
the span of a singleton is also non-degenerate. -/
theorem LinearMap.BilinForm.restrictOrthogonalSpanSingletonNondegenerate (B : BilinForm K V)
    (b₁ : B.Nondegenerate) (b₂ : B.IsRefl) {x : V} (hx : ¬B.IsOrtho x x) :
    LinearMap.BilinForm.Nondegenerate <| B.restrict <| B.orthogonal (K ∙ x) :=
  by
  refine' fun m hm => Submodule.coe_eq_zero.1 (b₁ m.1 fun n => _)
  have : n ∈ (K ∙ x) ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  rcases Submodule.mem_sup.1 this with ⟨y, hy, z, hz, rfl⟩
  specialize hm ⟨z, hz⟩
  rw [restrict] at hm
  erw [add_right, show B m.1 y = 0 by rw [b₂] <;> exact m.2 y hy, hm, add_zero]
#align bilin_form.restrict_orthogonal_span_singleton_nondegenerate LinearMap.BilinForm.restrictOrthogonalSpanSingletonNondegenerate
-/

section LinearAdjoints

#print LinearMap.BilinForm.compLeft_injective /-
theorem LinearMap.BilinForm.compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) :
    Function.Injective B.compLeft := fun φ ψ h =>
  by
  ext w
  refine' eq_of_sub_eq_zero (b _ _)
  intro v
  rw [sub_left, ← comp_left_apply, ← comp_left_apply, ← h, sub_self]
#align bilin_form.comp_left_injective LinearMap.BilinForm.compLeft_injective
-/

#print LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate /-
theorem LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁)
    (b : B.Nondegenerate) (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁)
    (hψ₁ : LinearMap.BilinForm.IsAdjointPair B B ψ₁ φ)
    (hψ₂ : LinearMap.BilinForm.IsAdjointPair B B ψ₂ φ) : ψ₁ = ψ₂ :=
  B.compLeft_injective b <|
    LinearMap.BilinForm.ext fun v w => by rw [comp_left_apply, comp_left_apply, hψ₁, hψ₂]
#align bilin_form.is_adjoint_pair_unique_of_nondegenerate LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate
-/

variable [FiniteDimensional K V]

#print LinearMap.BilinForm.symmCompOfNondegenerate /-
/-- Given bilinear forms `B₁, B₂` where `B₂` is nondegenerate, `symm_comp_of_nondegenerate`
is the linear map `B₂.to_lin⁻¹ ∘ B₁.to_lin`. -/
noncomputable def LinearMap.BilinForm.symmCompOfNondegenerate (B₁ B₂ : BilinForm K V)
    (b₂ : B₂.Nondegenerate) : V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp B₁.toLin
#align bilin_form.symm_comp_of_nondegenerate LinearMap.BilinForm.symmCompOfNondegenerate
-/

#print LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply /-
theorem LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V)
    {B₂ : BilinForm K V} (b₂ : B₂.Nondegenerate) (v : V) :
    LinearMap.BilinForm.toLin B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) =
      LinearMap.BilinForm.toLin B₁ v :=
  by erw [symm_comp_of_nondegenerate, LinearEquiv.apply_symm_apply (B₂.to_dual b₂) _]
#align bilin_form.comp_symm_comp_of_nondegenerate_apply LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply
-/

#print LinearMap.BilinForm.symmCompOfNondegenerate_left_apply /-
@[simp]
theorem LinearMap.BilinForm.symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V)
    {B₂ : BilinForm K V} (b₂ : B₂.Nondegenerate) (v w : V) :
    B₂ (LinearMap.BilinForm.symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v :=
  by
  conv_lhs => rw [← BilinForm.toLin_apply, comp_symm_comp_of_nondegenerate_apply]
  rfl
#align bilin_form.symm_comp_of_nondegenerate_left_apply LinearMap.BilinForm.symmCompOfNondegenerate_left_apply
-/

#print LinearMap.BilinForm.leftAdjointOfNondegenerate /-
/-- Given the nondegenerate bilinear form `B` and the linear map `φ`,
`left_adjoint_of_nondegenerate` provides the left adjoint of `φ` with respect to `B`.
The lemma proving this property is `bilin_form.is_adjoint_pair_left_adjoint_of_nondegenerate`. -/
noncomputable def LinearMap.BilinForm.leftAdjointOfNondegenerate (B : BilinForm K V)
    (b : B.Nondegenerate) (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  LinearMap.BilinForm.symmCompOfNondegenerate (B.compRight φ) B b
#align bilin_form.left_adjoint_of_nondegenerate LinearMap.BilinForm.leftAdjointOfNondegenerate
-/

#print LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate /-
theorem LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V)
    (b : B.Nondegenerate) (φ : V →ₗ[K] V) :
    LinearMap.BilinForm.IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x
#align bilin_form.is_adjoint_pair_left_adjoint_of_nondegenerate LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate
-/

#print LinearMap.BilinForm.isAdjointPair_iff_eq_of_nondegenerate /-
/-- Given the nondegenerate bilinear form `B`, the linear map `φ` has a unique left adjoint given by
`bilin_form.left_adjoint_of_nondegenerate`. -/
theorem LinearMap.BilinForm.isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V)
    (b : B.Nondegenerate) (ψ φ : V →ₗ[K] V) :
    LinearMap.BilinForm.IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩
#align bilin_form.is_adjoint_pair_iff_eq_of_nondegenerate LinearMap.BilinForm.isAdjointPair_iff_eq_of_nondegenerate
-/

end LinearAdjoints

end BilinForm

