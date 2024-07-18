/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Algebra.Group.Invertible.Defs
import LinearAlgebra.Matrix.Determinant.Basic
import LinearAlgebra.Matrix.BilinearForm
import LinearAlgebra.Matrix.Symmetric

#align_import linear_algebra.quadratic_form.basic from "leanprover-community/mathlib"@"d11f435d4e34a6cea0a1797d6b625b0c170be845"

/-!
# Quadratic forms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines quadratic forms over a `R`-module `M`.
A quadratic form on a ring `R` is a map `Q : M → R` such that:
* `quadratic_form.map_smul`: `Q (a • x) = a * a * Q x`
* `quadratic_form.polar_add_left`, `quadratic_form.polar_add_right`,
  `quadratic_form.polar_smul_left`, `quadratic_form.polar_smul_right`:
  the map `quadratic_form.polar Q := λ x y, Q (x + y) - Q x - Q y` is bilinear.

This notion generalizes to semirings using the approach in [izhakian2016][] which requires that
there be a (possibly non-unique) companion bilinear form `B` such that
`∀ x y, Q (x + y) = Q x + Q y + B x y`. Over a ring, this `B` is precisely `quadratic_form.polar Q`.

To build a `quadratic_form` from the `polar` axioms, use `quadratic_form.of_polar`.

Quadratic forms come with a scalar multiplication, `(a • Q) x = Q (a • x) = a * a * Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

 * `quadratic_form.of_polar`: a more familiar constructor that works on rings
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

variable {R R₁ : Type _} {M : Type _}

open scoped BigOperators

section Polar

variable [Ring R] [CommRing R₁] [AddCommGroup M]

namespace QuadraticMap

#print QuadraticMap.polar /-
/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar (f : M → R) (x y : M) :=
  f (x + y) - f x - f y
#align quadratic_form.polar QuadraticMap.polar
-/

#print QuadraticMap.polar_add /-
theorem polar_add (f g : M → R) (x y : M) : polar (f + g) x y = polar f x y + polar g x y := by
  simp only [polar, Pi.add_apply]; abel
#align quadratic_form.polar_add QuadraticMap.polar_add
-/

#print QuadraticMap.polar_neg /-
theorem polar_neg (f : M → R) (x y : M) : polar (-f) x y = -polar f x y := by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]
#align quadratic_form.polar_neg QuadraticMap.polar_neg
-/

#print QuadraticMap.polar_smul /-
theorem polar_smul [Monoid S] [DistribMulAction S R] (f : M → R) (s : S) (x y : M) :
    polar (s • f) x y = s • polar f x y := by simp only [polar, Pi.smul_apply, smul_sub]
#align quadratic_form.polar_smul QuadraticMap.polar_smul
-/

#print QuadraticMap.polar_comm /-
theorem polar_comm (f : M → R) (x y : M) : polar f x y = polar f y x := by
  rw [polar, polar, add_comm, sub_sub, sub_sub, add_comm (f x) (f y)]
#align quadratic_form.polar_comm QuadraticMap.polar_comm
-/

#print QuadraticMap.polar_add_left_iff /-
/-- Auxiliary lemma to express bilinearity of `quadratic_form.polar` without subtraction. -/
theorem polar_add_left_iff {f : M → R} {x x' y : M} :
    polar f (x + x') y = polar f x y + polar f x' y ↔
      f (x + x' + y) + (f x + f x' + f y) = f (x + x') + f (x' + y) + f (y + x) :=
  by
  simp only [← add_assoc]
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub]
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)]
  rw [add_comm y x, add_right_comm _ _ (f (x + y)), add_comm _ (f (x + y)),
    add_right_comm (f (x + y)), add_left_inj]
#align quadratic_form.polar_add_left_iff QuadraticMap.polar_add_left_iff
-/

#print QuadraticMap.polar_comp /-
theorem polar_comp {F : Type _} [Ring S] [AddMonoidHomClass F R S] (f : M → R) (g : F) (x y : M) :
    polar (g ∘ f) x y = g (polar f x y) := by
  simp only [polar, Pi.smul_apply, Function.comp_apply, map_sub]
#align quadratic_form.polar_comp QuadraticMap.polar_comp
-/

end QuadraticMap

end Polar

/-- A quadratic form over a module.

For a more familiar constructor when `R` is a ring, see `quadratic_form.of_polar`. -/
structure QuadraticMap (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] where
  toFun : M → R
  toFun_smul : ∀ (a : R) (x : M), to_fun (a • x) = a * a * to_fun x
  exists_companion' : ∃ B : BilinForm R M, ∀ x y, to_fun (x + y) = to_fun x + to_fun y + B x y
#align quadratic_form QuadraticMapₓ

namespace QuadraticMap

section DFunLike

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {Q Q' : QuadraticMap R M}

#print QuadraticMap.instFunLike /-
instance instFunLike : DFunLike (QuadraticMap R M) M fun _ => R
    where
  coe := toFun
  coe_injective' x y h := by cases x <;> cases y <;> congr
#align quadratic_form.fun_like QuadraticMap.instFunLike
-/

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : CoeFun (QuadraticMap R M) fun _ => M → R :=
  ⟨toFun⟩

variable (Q)

#print QuadraticMap.toFun_eq_coe /-
/-- The `simp` normal form for a quadratic form is `coe_fn`, not `to_fun`. -/
@[simp]
theorem toFun_eq_coe : Q.toFun = ⇑Q :=
  rfl
#align quadratic_form.to_fun_eq_coe QuadraticMap.toFun_eq_coe
-/

-- this must come after the coe_to_fun definition
initialize_simps_projections QuadraticMapₓ (toFun → apply)

variable {Q}

#print QuadraticMap.ext /-
@[ext]
theorem ext (H : ∀ x : M, Q x = Q' x) : Q = Q' :=
  DFunLike.ext _ _ H
#align quadratic_form.ext QuadraticMap.ext
-/

#print QuadraticMap.congr_fun /-
theorem congr_fun (h : Q = Q') (x : M) : Q x = Q' x :=
  DFunLike.congr_fun h _
#align quadratic_form.congr_fun QuadraticMap.congr_fun
-/

#print QuadraticMap.ext_iff /-
theorem ext_iff : Q = Q' ↔ ∀ x, Q x = Q' x :=
  DFunLike.ext_iff
#align quadratic_form.ext_iff QuadraticMap.ext_iff
-/

#print QuadraticMap.copy /-
/-- Copy of a `quadratic_form` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (Q : QuadraticMap R M) (Q' : M → R) (h : Q' = ⇑Q) : QuadraticMap R M
    where
  toFun := Q'
  toFun_smul := h.symm ▸ Q.toFun_smul
  exists_companion' := h.symm ▸ Q.exists_companion'
#align quadratic_form.copy QuadraticMap.copy
-/

#print QuadraticMap.coe_copy /-
@[simp]
theorem coe_copy (Q : QuadraticMap R M) (Q' : M → R) (h : Q' = ⇑Q) : ⇑(Q.copy Q' h) = Q' :=
  rfl
#align quadratic_form.coe_copy QuadraticMap.coe_copy
-/

#print QuadraticMap.copy_eq /-
theorem copy_eq (Q : QuadraticMap R M) (Q' : M → R) (h : Q' = ⇑Q) : Q.copy Q' h = Q :=
  DFunLike.ext' h
#align quadratic_form.copy_eq QuadraticMap.copy_eq
-/

end DFunLike

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (Q : QuadraticMap R M)

#print QuadraticMap.map_smul /-
theorem map_smul (a : R) (x : M) : Q (a • x) = a * a * Q x :=
  Q.toFun_smul a x
#align quadratic_form.map_smul QuadraticMap.map_smul
-/

#print QuadraticMap.exists_companion /-
theorem exists_companion : ∃ B : BilinForm R M, ∀ x y, Q (x + y) = Q x + Q y + B x y :=
  Q.exists_companion'
#align quadratic_form.exists_companion QuadraticMap.exists_companion
-/

#print QuadraticMap.map_add_add_add_map /-
theorem map_add_add_add_map (x y z : M) :
    Q (x + y + z) + (Q x + Q y + Q z) = Q (x + y) + Q (y + z) + Q (z + x) :=
  by
  obtain ⟨B, h⟩ := Q.exists_companion
  rw [add_comm z x]
  simp [h]
  abel
#align quadratic_form.map_add_add_add_map QuadraticMap.map_add_add_add_map
-/

#print QuadraticMap.map_add_self /-
theorem map_add_self (x : M) : Q (x + x) = 4 * Q x := by rw [← one_smul R x, ← add_smul, map_smul];
  norm_num
#align quadratic_form.map_add_self QuadraticMap.map_add_self
-/

#print QuadraticMap.map_zero /-
@[simp]
theorem map_zero : Q 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), map_smul, MulZeroClass.zero_mul, MulZeroClass.zero_mul]
#align quadratic_form.map_zero QuadraticMap.map_zero
-/

#print QuadraticMap.zeroHomClass /-
instance zeroHomClass : ZeroHomClass (QuadraticMap R M) M R :=
  { QuadraticMap.instFunLike with map_zero := map_zero }
#align quadratic_form.zero_hom_class QuadraticMap.zeroHomClass
-/

#print QuadraticMap.map_smul_of_tower /-
theorem map_smul_of_tower [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M] (a : S)
    (x : M) : Q (a • x) = (a * a) • Q x := by
  rw [← IsScalarTower.algebraMap_smul R a x, map_smul, ← RingHom.map_mul, Algebra.smul_def]
#align quadratic_form.map_smul_of_tower QuadraticMap.map_smul_of_tower
-/

end Semiring

section Ring

variable [Ring R] [CommRing R₁] [AddCommGroup M]

variable [Module R M] (Q : QuadraticMap R M)

#print QuadraticMap.map_neg /-
@[simp]
theorem map_neg (x : M) : Q (-x) = Q x := by
  rw [← @neg_one_smul R _ _ _ _ x, map_smul, neg_one_mul, neg_neg, one_mul]
#align quadratic_form.map_neg QuadraticMap.map_neg
-/

#print QuadraticMap.map_sub /-
theorem map_sub (x y : M) : Q (x - y) = Q (y - x) := by rw [← neg_sub, map_neg]
#align quadratic_form.map_sub QuadraticMap.map_sub
-/

#print QuadraticMap.polar_zero_left /-
@[simp]
theorem polar_zero_left (y : M) : polar Q 0 y = 0 := by
  simp only [polar, zero_add, QuadraticMap.map_zero, sub_zero, sub_self]
#align quadratic_form.polar_zero_left QuadraticMap.polar_zero_left
-/

#print QuadraticMap.polar_add_left /-
@[simp]
theorem polar_add_left (x x' y : M) : polar Q (x + x') y = polar Q x y + polar Q x' y :=
  polar_add_left_iff.mpr <| Q.map_add_add_add_map x x' y
#align quadratic_form.polar_add_left QuadraticMap.polar_add_left
-/

#print QuadraticMap.polar_smul_left /-
@[simp]
theorem polar_smul_left (a : R) (x y : M) : polar Q (a • x) y = a * polar Q x y :=
  by
  obtain ⟨B, h⟩ := Q.exists_companion
  simp_rw [polar, h, Q.map_smul, LinearMap.BilinForm.smul_left, sub_sub, add_sub_cancel_left]
#align quadratic_form.polar_smul_left QuadraticMap.polar_smul_left
-/

#print QuadraticMap.polar_neg_left /-
@[simp]
theorem polar_neg_left (x y : M) : polar Q (-x) y = -polar Q x y := by
  rw [← neg_one_smul R x, polar_smul_left, neg_one_mul]
#align quadratic_form.polar_neg_left QuadraticMap.polar_neg_left
-/

#print QuadraticMap.polar_sub_left /-
@[simp]
theorem polar_sub_left (x x' y : M) : polar Q (x - x') y = polar Q x y - polar Q x' y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_left, polar_neg_left]
#align quadratic_form.polar_sub_left QuadraticMap.polar_sub_left
-/

#print QuadraticMap.polar_zero_right /-
@[simp]
theorem polar_zero_right (y : M) : polar Q y 0 = 0 := by
  simp only [add_zero, polar, QuadraticMap.map_zero, sub_self]
#align quadratic_form.polar_zero_right QuadraticMap.polar_zero_right
-/

#print QuadraticMap.polar_add_right /-
@[simp]
theorem polar_add_right (x y y' : M) : polar Q x (y + y') = polar Q x y + polar Q x y' := by
  rw [polar_comm Q x, polar_comm Q x, polar_comm Q x, polar_add_left]
#align quadratic_form.polar_add_right QuadraticMap.polar_add_right
-/

#print QuadraticMap.polar_smul_right /-
@[simp]
theorem polar_smul_right (a : R) (x y : M) : polar Q x (a • y) = a * polar Q x y := by
  rw [polar_comm Q x, polar_comm Q x, polar_smul_left]
#align quadratic_form.polar_smul_right QuadraticMap.polar_smul_right
-/

#print QuadraticMap.polar_neg_right /-
@[simp]
theorem polar_neg_right (x y : M) : polar Q x (-y) = -polar Q x y := by
  rw [← neg_one_smul R y, polar_smul_right, neg_one_mul]
#align quadratic_form.polar_neg_right QuadraticMap.polar_neg_right
-/

#print QuadraticMap.polar_sub_right /-
@[simp]
theorem polar_sub_right (x y y' : M) : polar Q x (y - y') = polar Q x y - polar Q x y' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_right, polar_neg_right]
#align quadratic_form.polar_sub_right QuadraticMap.polar_sub_right
-/

#print QuadraticMap.polar_self /-
@[simp]
theorem polar_self (x : M) : polar Q x x = 2 * Q x :=
  by
  rw [polar, map_add_self, sub_sub, sub_eq_iff_eq_add, ← two_mul, ← two_mul, ← mul_assoc]
  norm_num
#align quadratic_form.polar_self QuadraticMap.polar_self
-/

#print QuadraticMap.polarBilin /-
/-- `quadratic_form.polar` as a bilinear form -/
@[simps]
def polarBilin : BilinForm R M where
  bilin := polar Q
  bilin_add_left := polar_add_left Q
  bilin_smul_left := polar_smul_left Q
  bilin_add_right x y z := by simp_rw [polar_comm _ x, polar_add_left Q]
  bilin_smul_right r x y := by simp_rw [polar_comm _ x, polar_smul_left Q]
#align quadratic_form.polar_bilin QuadraticMap.polarBilin
-/

variable [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

#print QuadraticMap.polar_smul_left_of_tower /-
@[simp]
theorem polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a x, polar_smul_left, Algebra.smul_def]
#align quadratic_form.polar_smul_left_of_tower QuadraticMap.polar_smul_left_of_tower
-/

#print QuadraticMap.polar_smul_right_of_tower /-
@[simp]
theorem polar_smul_right_of_tower (a : S) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a y, polar_smul_right, Algebra.smul_def]
#align quadratic_form.polar_smul_right_of_tower QuadraticMap.polar_smul_right_of_tower
-/

#print QuadraticMap.ofPolar /-
/-- An alternative constructor to `quadratic_form.mk`, for rings where `polar` can be used. -/
@[simps]
def ofPolar (to_fun : M → R) (to_fun_smul : ∀ (a : R) (x : M), to_fun (a • x) = a * a * to_fun x)
    (polar_add_left : ∀ x x' y : M, polar to_fun (x + x') y = polar to_fun x y + polar to_fun x' y)
    (polar_smul_left : ∀ (a : R) (x y : M), polar to_fun (a • x) y = a • polar to_fun x y) :
    QuadraticMap R M :=
  { toFun
    toFun_smul
    exists_companion' :=
      ⟨{  bilin := polar to_fun
          bilin_add_left := polar_add_left
          bilin_smul_left := polar_smul_left
          bilin_add_right := fun x y z => by simp_rw [polar_comm _ x, polar_add_left]
          bilin_smul_right := fun r x y => by
            simp_rw [polar_comm _ x, polar_smul_left, smul_eq_mul] },
        fun x y => by rw [BilinForm.coeFn_mk, polar, sub_sub, add_sub_cancel]⟩ }
#align quadratic_form.of_polar QuadraticMap.ofPolar
-/

#print QuadraticMap.choose_exists_companion /-
/-- In a ring the companion bilinear form is unique and equal to `quadratic_form.polar`. -/
theorem choose_exists_companion : Q.exists_companion.some = polarBilin Q :=
  LinearMap.BilinForm.ext fun x y => by
    rw [polar_bilin_apply, polar, Q.exists_companion.some_spec, sub_sub, add_sub_cancel_left]
#align quadratic_form.some_exists_companion QuadraticMap.choose_exists_companion
-/

end Ring

section SemiringOperators

variable [Semiring R] [AddCommMonoid M] [Module R M]

section SMul

variable [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]

/-- `quadratic_form R M` inherits the scalar action from any algebra over `R`.

When `R` is commutative, this provides an `R`-action via `algebra.id`. -/
instance : SMul S (QuadraticMap R M) :=
  ⟨fun a Q =>
    { toFun := a • Q
      toFun_smul := fun b x => by rw [Pi.smul_apply, map_smul, Pi.smul_apply, mul_smul_comm]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨a • B, by simp [h]⟩ }⟩

#print QuadraticMap.coeFn_smul /-
@[simp]
theorem coeFn_smul (a : S) (Q : QuadraticMap R M) : ⇑(a • Q) = a • Q :=
  rfl
#align quadratic_form.coe_fn_smul QuadraticMap.coeFn_smul
-/

#print QuadraticMap.smul_apply /-
@[simp]
theorem smul_apply (a : S) (Q : QuadraticMap R M) (x : M) : (a • Q) x = a • Q x :=
  rfl
#align quadratic_form.smul_apply QuadraticMap.smul_apply
-/

end SMul

instance : Zero (QuadraticMap R M) :=
  ⟨{  toFun := fun x => 0
      toFun_smul := fun a x => by simp only [MulZeroClass.mul_zero]
      exists_companion' :=
        ⟨0, fun x y => by simp only [add_zero, LinearMap.BilinForm.zero_apply]⟩ }⟩

#print QuadraticMap.coeFn_zero /-
@[simp]
theorem coeFn_zero : ⇑(0 : QuadraticMap R M) = 0 :=
  rfl
#align quadratic_form.coe_fn_zero QuadraticMap.coeFn_zero
-/

#print QuadraticMap.zero_apply /-
@[simp]
theorem zero_apply (x : M) : (0 : QuadraticMap R M) x = 0 :=
  rfl
#align quadratic_form.zero_apply QuadraticMap.zero_apply
-/

instance : Inhabited (QuadraticMap R M) :=
  ⟨0⟩

instance : Add (QuadraticMap R M) :=
  ⟨fun Q Q' =>
    { toFun := Q + Q'
      toFun_smul := fun a x => by simp only [Pi.add_apply, map_smul, mul_add]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        let ⟨B', h'⟩ := Q'.exists_companion
        ⟨B + B', fun x y => by
          simp_rw [Pi.add_apply, h, h', LinearMap.BilinForm.add_apply, add_add_add_comm]⟩ }⟩

#print QuadraticMap.coeFn_add /-
@[simp]
theorem coeFn_add (Q Q' : QuadraticMap R M) : ⇑(Q + Q') = Q + Q' :=
  rfl
#align quadratic_form.coe_fn_add QuadraticMap.coeFn_add
-/

#print QuadraticMap.add_apply /-
@[simp]
theorem add_apply (Q Q' : QuadraticMap R M) (x : M) : (Q + Q') x = Q x + Q' x :=
  rfl
#align quadratic_form.add_apply QuadraticMap.add_apply
-/

instance : AddCommMonoid (QuadraticMap R M) :=
  DFunLike.coe_injective.AddCommMonoid _ coeFn_zero coeFn_add fun _ _ => coeFn_smul _ _

#print QuadraticMap.coeFnAddMonoidHom /-
/-- `@coe_fn (quadratic_form R M)` as an `add_monoid_hom`.

This API mirrors `add_monoid_hom.coe_fn`. -/
@[simps apply]
def coeFnAddMonoidHom : QuadraticMap R M →+ M → R
    where
  toFun := coeFn
  map_zero' := coeFn_zero
  map_add' := coeFn_add
#align quadratic_form.coe_fn_add_monoid_hom QuadraticMap.coeFnAddMonoidHom
-/

#print QuadraticMap.evalAddMonoidHom /-
/-- Evaluation on a particular element of the module `M` is an additive map over quadratic forms. -/
@[simps apply]
def evalAddMonoidHom (m : M) : QuadraticMap R M →+ R :=
  (Pi.evalAddMonoidHom _ m).comp coeFnAddMonoidHom
#align quadratic_form.eval_add_monoid_hom QuadraticMap.evalAddMonoidHom
-/

section Sum

#print QuadraticMap.coeFn_sum /-
@[simp]
theorem coeFn_sum {ι : Type _} (Q : ι → QuadraticMap R M) (s : Finset ι) :
    ⇑(∑ i in s, Q i) = ∑ i in s, Q i :=
  (coeFnAddMonoidHom : _ →+ M → R).map_sum Q s
#align quadratic_form.coe_fn_sum QuadraticMap.coeFn_sum
-/

#print QuadraticMap.sum_apply /-
@[simp]
theorem sum_apply {ι : Type _} (Q : ι → QuadraticMap R M) (s : Finset ι) (x : M) :
    (∑ i in s, Q i) x = ∑ i in s, Q i x :=
  (evalAddMonoidHom x : _ →+ R).map_sum Q s
#align quadratic_form.sum_apply QuadraticMap.sum_apply
-/

end Sum

instance [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] :
    DistribMulAction S (QuadraticMap R M)
    where
  hMul_smul a b Q := ext fun x => by simp only [smul_apply, mul_smul]
  one_smul Q := ext fun x => by simp only [QuadraticMap.smul_apply, one_smul]
  smul_add a Q Q' := by ext; simp only [add_apply, smul_apply, smul_add]
  smul_zero a := by ext; simp only [zero_apply, smul_apply, smul_zero]

instance [Semiring S] [Module S R] [SMulCommClass S R R] : Module S (QuadraticMap R M)
    where
  zero_smul Q := by ext; simp only [zero_apply, smul_apply, zero_smul]
  add_smul a b Q := by ext; simp only [add_apply, smul_apply, add_smul]

end SemiringOperators

section RingOperators

variable [Ring R] [AddCommGroup M] [Module R M]

instance : Neg (QuadraticMap R M) :=
  ⟨fun Q =>
    { toFun := -Q
      toFun_smul := fun a x => by simp only [Pi.neg_apply, map_smul, mul_neg]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨-B, fun x y => by simp_rw [Pi.neg_apply, h, LinearMap.BilinForm.neg_apply, neg_add]⟩ }⟩

#print QuadraticMap.coeFn_neg /-
@[simp]
theorem coeFn_neg (Q : QuadraticMap R M) : ⇑(-Q) = -Q :=
  rfl
#align quadratic_form.coe_fn_neg QuadraticMap.coeFn_neg
-/

#print QuadraticMap.neg_apply /-
@[simp]
theorem neg_apply (Q : QuadraticMap R M) (x : M) : (-Q) x = -Q x :=
  rfl
#align quadratic_form.neg_apply QuadraticMap.neg_apply
-/

instance : Sub (QuadraticMap R M) :=
  ⟨fun Q Q' => (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _)⟩

#print QuadraticMap.coeFn_sub /-
@[simp]
theorem coeFn_sub (Q Q' : QuadraticMap R M) : ⇑(Q - Q') = Q - Q' :=
  rfl
#align quadratic_form.coe_fn_sub QuadraticMap.coeFn_sub
-/

#print QuadraticMap.sub_apply /-
@[simp]
theorem sub_apply (Q Q' : QuadraticMap R M) (x : M) : (Q - Q') x = Q x - Q' x :=
  rfl
#align quadratic_form.sub_apply QuadraticMap.sub_apply
-/

instance : AddCommGroup (QuadraticMap R M) :=
  DFunLike.coe_injective.AddCommGroup _ coeFn_zero coeFn_add coeFn_neg coeFn_sub
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

end RingOperators

section Comp

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {N : Type v} [AddCommMonoid N] [Module R N]

#print QuadraticMap.comp /-
/-- Compose the quadratic form with a linear function. -/
def comp (Q : QuadraticMap R N) (f : M →ₗ[R] N) : QuadraticMap R M
    where
  toFun x := Q (f x)
  toFun_smul a x := by simp only [map_smul, f.map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.comp f f, fun x y => by simp_rw [f.map_add, h, LinearMap.BilinForm.comp_apply]⟩
#align quadratic_form.comp QuadraticMap.comp
-/

#print QuadraticMap.comp_apply /-
@[simp]
theorem comp_apply (Q : QuadraticMap R N) (f : M →ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
  rfl
#align quadratic_form.comp_apply QuadraticMap.comp_apply
-/

#print LinearMap.compQuadraticMap' /-
/-- Compose a quadratic form with a linear function on the left. -/
@[simps (config := { simpRhs := true })]
def LinearMap.compQuadraticMap' {S : Type _} [CommSemiring S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (f : R →ₗ[S] S) (Q : QuadraticMap R M) : QuadraticMap S M
    where
  toFun x := f (Q x)
  toFun_smul b x := by rw [Q.map_smul_of_tower b x, f.map_smul, smul_eq_mul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨f.compBilinForm B, fun x y => by simp_rw [h, f.map_add, LinearMap.compBilinForm_apply]⟩
#align linear_map.comp_quadratic_form LinearMap.compQuadraticMap'
-/

end Comp

section CommRing

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

#print QuadraticMap.linMulLin /-
/-- The product of linear forms is a quadratic form. -/
def linMulLin (f g : M →ₗ[R] R) : QuadraticMap R M
    where
  toFun := f * g
  toFun_smul a x := by
    simp only [smul_eq_mul, RingHom.id_apply, Pi.mul_apply, LinearMap.map_smulₛₗ]; ring
  exists_companion' :=
    ⟨LinearMap.BilinForm.linMulLin f g + LinearMap.BilinForm.linMulLin g f, fun x y => by simp;
      ring⟩
#align quadratic_form.lin_mul_lin QuadraticMap.linMulLin
-/

#print QuadraticMap.linMulLin_apply /-
@[simp]
theorem linMulLin_apply (f g : M →ₗ[R] R) (x) : linMulLin f g x = f x * g x :=
  rfl
#align quadratic_form.lin_mul_lin_apply QuadraticMap.linMulLin_apply
-/

#print QuadraticMap.add_linMulLin /-
@[simp]
theorem add_linMulLin (f g h : M →ₗ[R] R) : linMulLin (f + g) h = linMulLin f h + linMulLin g h :=
  ext fun x => add_mul _ _ _
#align quadratic_form.add_lin_mul_lin QuadraticMap.add_linMulLin
-/

#print QuadraticMap.linMulLin_add /-
@[simp]
theorem linMulLin_add (f g h : M →ₗ[R] R) : linMulLin f (g + h) = linMulLin f g + linMulLin f h :=
  ext fun x => mul_add _ _ _
#align quadratic_form.lin_mul_lin_add QuadraticMap.linMulLin_add
-/

variable {N : Type v} [AddCommMonoid N] [Module R N]

#print QuadraticMap.linMulLin_comp /-
@[simp]
theorem linMulLin_comp (f g : M →ₗ[R] R) (h : N →ₗ[R] M) :
    (linMulLin f g).comp h = linMulLin (f.comp h) (g.comp h) :=
  rfl
#align quadratic_form.lin_mul_lin_comp QuadraticMap.linMulLin_comp
-/

variable {n : Type _}

#print QuadraticMap.sq /-
/-- `sq` is the quadratic form mapping the vector `x : R₁` to `x * x` -/
@[simps]
def sq : QuadraticMap R R :=
  linMulLin LinearMap.id LinearMap.id
#align quadratic_form.sq QuadraticMap.sq
-/

#print QuadraticMap.proj /-
/-- `proj i j` is the quadratic form mapping the vector `x : n → R₁` to `x i * x j` -/
def proj (i j : n) : QuadraticMap R (n → R) :=
  linMulLin (@LinearMap.proj _ _ _ (fun _ => R) _ _ i) (@LinearMap.proj _ _ _ (fun _ => R) _ _ j)
#align quadratic_form.proj QuadraticMap.proj
-/

#print QuadraticMap.proj_apply /-
@[simp]
theorem proj_apply (i j : n) (x : n → R) : proj i j x = x i * x j :=
  rfl
#align quadratic_form.proj_apply QuadraticMap.proj_apply
-/

end CommRing

end QuadraticMap

/-!
### Associated bilinear forms

Over a commutative ring with an inverse of 2, the theory of quadratic forms is
basically identical to that of symmetric bilinear forms. The map from quadratic
forms to bilinear forms giving this identification is called the `associated`
quadratic form.
-/


namespace BilinForm

open QuadraticMap

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {B : BilinForm R M}

#print LinearMap.BilinMap.toQuadraticMap /-
/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def LinearMap.BilinMap.toQuadraticMap (B : BilinForm R M) : QuadraticMap R M
    where
  toFun x := B x x
  toFun_smul a x := by simp only [mul_assoc, smul_right, smul_left]
  exists_companion' :=
    ⟨B + LinearMap.BilinForm.flipHom ℕ B, fun x y => by simp [add_add_add_comm, add_comm]⟩
#align bilin_form.to_quadratic_form LinearMap.BilinMap.toQuadraticMap
-/

#print LinearMap.BilinMap.toQuadraticMap_apply /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_apply (B : BilinForm R M) (x : M) :
    B.toQuadraticMap x = B x x :=
  rfl
#align bilin_form.to_quadratic_form_apply LinearMap.BilinMap.toQuadraticMap_apply
-/

section

variable (R M)

#print LinearMap.BilinMap.toQuadraticMap_zero /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_zero : (0 : BilinForm R M).toQuadraticMap = 0 :=
  rfl
#align bilin_form.to_quadratic_form_zero LinearMap.BilinMap.toQuadraticMap_zero
-/

end

#print LinearMap.BilinMap.toQuadraticMap_add /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_add (B₁ B₂ : BilinForm R M) :
    (B₁ + B₂).toQuadraticMap = B₁.toQuadraticMap + B₂.toQuadraticMap :=
  rfl
#align bilin_form.to_quadratic_form_add LinearMap.BilinMap.toQuadraticMap_add
-/

#print LinearMap.BilinMap.toQuadraticMap_smul /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_smul [Monoid S] [DistribMulAction S R]
    [SMulCommClass S R R] (a : S) (B : BilinForm R M) :
    (a • B).toQuadraticMap = a • B.toQuadraticMap :=
  rfl
#align bilin_form.to_quadratic_form_smul LinearMap.BilinMap.toQuadraticMap_smul
-/

section

variable (R M)

#print LinearMap.BilinMap.toQuadraticMapAddMonoidHom /-
/-- `bilin_form.to_quadratic_form` as an additive homomorphism -/
@[simps]
def LinearMap.BilinMap.toQuadraticMapAddMonoidHom : BilinForm R M →+ QuadraticMap R M
    where
  toFun := LinearMap.BilinMap.toQuadraticMap
  map_zero' := LinearMap.BilinMap.toQuadraticMap_zero _ _
  map_add' := LinearMap.BilinMap.toQuadraticMap_add
#align bilin_form.to_quadratic_form_add_monoid_hom LinearMap.BilinMap.toQuadraticMapAddMonoidHom
-/

end

#print LinearMap.BilinMap.toQuadraticMap_list_sum /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_list_sum (B : List (BilinForm R M)) :
    B.Sum.toQuadraticMap = (B.map LinearMap.BilinMap.toQuadraticMap).Sum :=
  map_list_sum (LinearMap.BilinMap.toQuadraticMapAddMonoidHom R M) B
#align bilin_form.to_quadratic_form_list_sum LinearMap.BilinMap.toQuadraticMap_list_sum
-/

#print LinearMap.BilinMap.toQuadraticMap_multiset_sum /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_multiset_sum (B : Multiset (BilinForm R M)) :
    B.Sum.toQuadraticMap = (B.map LinearMap.BilinMap.toQuadraticMap).Sum :=
  map_multiset_sum (LinearMap.BilinMap.toQuadraticMapAddMonoidHom R M) B
#align bilin_form.to_quadratic_form_multiset_sum LinearMap.BilinMap.toQuadraticMap_multiset_sum
-/

#print LinearMap.BilinMap.toQuadraticMap_sum /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_sum {ι : Type _} (s : Finset ι) (B : ι → BilinForm R M) :
    (∑ i in s, B i).toQuadraticMap = ∑ i in s, (B i).toQuadraticMap :=
  map_sum (LinearMap.BilinMap.toQuadraticMapAddMonoidHom R M) B s
#align bilin_form.to_quadratic_form_sum LinearMap.BilinMap.toQuadraticMap_sum
-/

#print LinearMap.BilinMap.toQuadraticMap_eq_zero /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_eq_zero {B : BilinForm R M} :
    B.toQuadraticMap = 0 ↔ B.IsAlt :=
  QuadraticMap.ext_iff
#align bilin_form.to_quadratic_form_eq_zero LinearMap.BilinMap.toQuadraticMap_eq_zero
-/

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]

variable {B : BilinForm R M}

#print LinearMap.BilinMap.polar_toQuadraticMap /-
theorem LinearMap.BilinMap.polar_toQuadraticMap (x y : M) :
    polar (fun x => B x x) x y = B x y + B y x := by
  simp only [add_assoc, add_sub_cancel_left, add_right, polar, add_left_inj, add_neg_cancel_left,
    add_left, sub_eq_add_neg _ (B y y), add_comm (B y x) _]
#align bilin_form.polar_to_quadratic_form LinearMap.BilinMap.polar_toQuadraticMap
-/

#print LinearMap.BilinMap.toQuadraticMap_neg /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_neg (B : BilinForm R M) :
    (-B).toQuadraticMap = -B.toQuadraticMap :=
  rfl
#align bilin_form.to_quadratic_form_neg LinearMap.BilinMap.toQuadraticMap_neg
-/

#print LinearMap.BilinMap.toQuadraticMap_sub /-
@[simp]
theorem LinearMap.BilinMap.toQuadraticMap_sub (B₁ B₂ : BilinForm R M) :
    (B₁ - B₂).toQuadraticMap = B₁.toQuadraticMap - B₂.toQuadraticMap :=
  rfl
#align bilin_form.to_quadratic_form_sub LinearMap.BilinMap.toQuadraticMap_sub
-/

end Ring

end BilinForm

namespace QuadraticMap

open BilinForm

section AssociatedHom

variable [Ring R] [CommRing R₁] [AddCommGroup M] [Module R M] [Module R₁ M]

variable (S) [CommSemiring S] [Algebra S R]

variable [Invertible (2 : R)] {B₁ : BilinForm R M}

#print QuadraticMap.associatedHom /-
/-- `associated_hom` is the map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative subring of `R`.

Over a commutative ring, use `associated`, which gives an `R`-linear map.  Over a general ring with
no nontrivial distinguished commutative subring, use `associated'`, which gives an additive
homomorphism (or more precisely a `ℤ`-linear map.) -/
def associatedHom : QuadraticMap R M →ₗ[S] BilinForm R M
    where
  toFun Q :=
    ((· • ·) : Submonoid.center R → BilinForm R M → BilinForm R M)
      ⟨⅟ 2, fun x => (Commute.one_right x).bit0_right.invOf_right⟩ Q.polarBilin
  map_add' Q Q' := by ext;
    simp only [LinearMap.BilinForm.add_apply, BilinForm.smul_apply, coe_fn_mk, polar_bilin_apply,
      polar_add, coe_fn_add, smul_add]
  map_smul' s Q := by ext;
    simp only [RingHom.id_apply, polar_smul, smul_comm s, polar_bilin_apply, coe_fn_mk, coe_fn_smul,
      BilinForm.smul_apply]
#align quadratic_form.associated_hom QuadraticMap.associatedHom
-/

variable (Q : QuadraticMap R M) (S)

#print QuadraticMap.associated_apply /-
@[simp]
theorem associated_apply (x y : M) : associatedHom S Q x y = ⅟ 2 * (Q (x + y) - Q x - Q y) :=
  rfl
#align quadratic_form.associated_apply QuadraticMap.associated_apply
-/

#print QuadraticMap.associated_isSymm /-
theorem associated_isSymm : (associatedHom S Q).IsSymm := fun x y => by
  simp only [associated_apply, add_comm, add_left_comm, sub_eq_add_neg]
#align quadratic_form.associated_is_symm QuadraticMap.associated_isSymm
-/

#print QuadraticMap.associated_comp /-
@[simp]
theorem associated_comp {N : Type v} [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) :
    associatedHom S (Q.comp f) = (associatedHom S Q).comp f f := by ext;
  simp only [QuadraticMap.comp_apply, LinearMap.BilinForm.comp_apply, associated_apply,
    LinearMap.map_add]
#align quadratic_form.associated_comp QuadraticMap.associated_comp
-/

#print QuadraticMap.associated_toQuadraticMap /-
theorem associated_toQuadraticMap (B : BilinForm R M) (x y : M) :
    associatedHom S B.toQuadraticMap x y = ⅟ 2 * (B x y + B y x) := by
  simp only [associated_apply, ← polar_to_quadratic_form, polar, to_quadratic_form_apply]
#align quadratic_form.associated_to_quadratic_form QuadraticMap.associated_toQuadraticMap
-/

#print QuadraticMap.associated_left_inverse /-
theorem associated_left_inverse (h : B₁.IsSymm) : associatedHom S B₁.toQuadraticMap = B₁ :=
  LinearMap.BilinForm.ext fun x y => by
    rw [associated_to_quadratic_form, is_symm.eq h x y, ← two_mul, ← mul_assoc, invOf_mul_self,
      one_mul]
#align quadratic_form.associated_left_inverse QuadraticMap.associated_left_inverse
-/

#print QuadraticMap.toQuadraticMap_associated /-
theorem toQuadraticMap_associated : (associatedHom S Q).toQuadraticMap = Q :=
  QuadraticMap.ext fun x =>
    calc
      (associatedHom S Q).toQuadraticMap x = ⅟ 2 * (Q x + Q x) := by
        simp only [add_assoc, add_sub_cancel_left, one_mul, to_quadratic_form_apply, add_mul,
          associated_apply, map_add_self, bit0]
      _ = Q x := by rw [← two_mul (Q x), ← mul_assoc, invOf_mul_self, one_mul]
#align quadratic_form.to_quadratic_form_associated QuadraticMap.toQuadraticMap_associated
-/

#print QuadraticMap.associated_rightInverse /-
-- note: usually `right_inverse` lemmas are named the other way around, but this is consistent
-- with historical naming in this file.
theorem associated_rightInverse :
    Function.RightInverse (associatedHom S)
      (LinearMap.BilinMap.toQuadraticMap : _ → QuadraticMap R M) :=
  fun Q => toQuadraticMap_associated S Q
#align quadratic_form.associated_right_inverse QuadraticMap.associated_rightInverse
-/

#print QuadraticMap.associated_eq_self_apply /-
theorem associated_eq_self_apply (x : M) : associatedHom S Q x x = Q x :=
  by
  rw [associated_apply, map_add_self]
  suffices ⅟ 2 * (2 * Q x) = Q x by
    convert this
    simp only [bit0, add_mul, one_mul]
    abel
  simp only [← mul_assoc, one_mul, invOf_mul_self]
#align quadratic_form.associated_eq_self_apply QuadraticMap.associated_eq_self_apply
-/

#print QuadraticMap.associated' /-
/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
abbrev associated' : QuadraticMap R M →ₗ[ℤ] BilinForm R M :=
  associatedHom ℤ
#align quadratic_form.associated' QuadraticMap.associated'
-/

#print QuadraticMap.canLift /-
/-- Symmetric bilinear forms can be lifted to quadratic forms -/
instance canLift :
    CanLift (BilinForm R M) (QuadraticMap R M) (associatedHom ℕ) LinearMap.BilinForm.IsSymm
    where prf B hB := ⟨B.toQuadraticMap, associated_left_inverse _ hB⟩
#align quadratic_form.can_lift QuadraticMap.canLift
-/

#print QuadraticMap.exists_quadraticForm_ne_zero /-
/-- There exists a non-null vector with respect to any quadratic form `Q` whose associated
bilinear form is non-zero, i.e. there exists `x` such that `Q x ≠ 0`. -/
theorem exists_quadraticForm_ne_zero {Q : QuadraticMap R M} (hB₁ : Q.associated' ≠ 0) :
    ∃ x, Q x ≠ 0 := by
  rw [← Classical.not_forall]
  intro h
  apply hB₁
  rw [(QuadraticMap.ext h : Q = 0), LinearMap.map_zero]
#align quadratic_form.exists_quadratic_form_ne_zero QuadraticMap.exists_quadraticForm_ne_zero
-/

end AssociatedHom

section Associated

variable [CommRing R₁] [AddCommGroup M] [Module R₁ M]

variable [Invertible (2 : R₁)]

#print QuadraticMap.associated /-
-- Note:  When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associated_hom` and place it in the previous section.
/-- `associated` is the linear map that sends a quadratic form over a commutative ring to its
associated symmetric bilinear form. -/
@[reducible]
def associated : QuadraticMap R₁ M →ₗ[R₁] BilinForm R₁ M :=
  associatedHom R₁
#align quadratic_form.associated QuadraticMap.associated
-/

#print QuadraticMap.associated_linMulLin /-
@[simp]
theorem associated_linMulLin (f g : M →ₗ[R₁] R₁) :
    (linMulLin f g).Associated =
      ⅟ (2 : R₁) • (LinearMap.BilinForm.linMulLin f g + LinearMap.BilinForm.linMulLin g f) :=
  by
  ext;
  simp only [smul_add, Algebra.id.smul_eq_mul, LinearMap.BilinForm.linMulLin_apply,
    QuadraticMap.linMulLin_apply, BilinForm.smul_apply, associated_apply,
    LinearMap.BilinForm.add_apply, LinearMap.map_add]
  ring
#align quadratic_form.associated_lin_mul_lin QuadraticMap.associated_linMulLin
-/

end Associated

section Anisotropic

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

#print QuadraticMap.Anisotropic /-
/-- An anisotropic quadratic form is zero only on zero vectors. -/
def Anisotropic (Q : QuadraticMap R M) : Prop :=
  ∀ x, Q x = 0 → x = 0
#align quadratic_form.anisotropic QuadraticMap.Anisotropic
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (x «expr ≠ » 0) -/
#print QuadraticMap.not_anisotropic_iff_exists /-
theorem not_anisotropic_iff_exists (Q : QuadraticMap R M) :
    ¬Anisotropic Q ↔ ∃ (x : _) (_ : x ≠ 0), Q x = 0 := by
  simp only [anisotropic, Classical.not_forall, exists_prop, and_comm]
#align quadratic_form.not_anisotropic_iff_exists QuadraticMap.not_anisotropic_iff_exists
-/

#print QuadraticMap.Anisotropic.eq_zero_iff /-
theorem Anisotropic.eq_zero_iff {Q : QuadraticMap R M} (h : Anisotropic Q) {x : M} :
    Q x = 0 ↔ x = 0 :=
  ⟨h x, fun h => h.symm ▸ map_zero Q⟩
#align quadratic_form.anisotropic.eq_zero_iff QuadraticMap.Anisotropic.eq_zero_iff
-/

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]

#print QuadraticMap.separatingLeft_of_anisotropic /-
/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
theorem separatingLeft_of_anisotropic [Invertible (2 : R)] (Q : QuadraticMap R M)
    (hB : Q.Anisotropic) : Q.associated'.Nondegenerate :=
  by
  intro x hx
  refine' hB _ _
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm
#align quadratic_form.nondegenerate_of_anisotropic QuadraticMap.separatingLeft_of_anisotropic
-/

end Ring

end Anisotropic

section PosDef

variable {R₂ : Type u} [OrderedRing R₂] [AddCommMonoid M] [Module R₂ M]

variable {Q₂ : QuadraticMap R₂ M}

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (x «expr ≠ » 0) -/
#print QuadraticMap.PosDef /-
/-- A positive definite quadratic form is positive on nonzero vectors. -/
def PosDef (Q₂ : QuadraticMap R₂ M) : Prop :=
  ∀ (x) (_ : x ≠ 0), 0 < Q₂ x
#align quadratic_form.pos_def QuadraticMap.PosDef
-/

#print QuadraticMap.PosDef.smul /-
theorem PosDef.smul {R} [LinearOrderedCommRing R] [Module R M] {Q : QuadraticMap R M} (h : PosDef Q)
    {a : R} (a_pos : 0 < a) : PosDef (a • Q) := fun x hx => mul_pos a_pos (h x hx)
#align quadratic_form.pos_def.smul QuadraticMap.PosDef.smul
-/

variable {n : Type _}

#print QuadraticMap.PosDef.nonneg /-
theorem PosDef.nonneg {Q : QuadraticMap R₂ M} (hQ : PosDef Q) (x : M) : 0 ≤ Q x :=
  (eq_or_ne x 0).elim (fun h => h.symm ▸ (map_zero Q).symm.le) fun h => (hQ _ h).le
#align quadratic_form.pos_def.nonneg QuadraticMap.PosDef.nonneg
-/

#print QuadraticMap.PosDef.anisotropic /-
theorem PosDef.anisotropic {Q : QuadraticMap R₂ M} (hQ : Q.PosDef) : Q.Anisotropic := fun x hQx =>
  by_contradiction fun hx =>
    lt_irrefl (0 : R₂) <| by
      have := hQ _ hx
      rw [hQx] at this
      exact this
#align quadratic_form.pos_def.anisotropic QuadraticMap.PosDef.anisotropic
-/

#print QuadraticMap.posDef_of_nonneg /-
theorem posDef_of_nonneg {Q : QuadraticMap R₂ M} (h : ∀ x, 0 ≤ Q x) (h0 : Q.Anisotropic) :
    PosDef Q := fun x hx => lt_of_le_of_ne (h x) (Ne.symm fun hQx => hx <| h0 _ hQx)
#align quadratic_form.pos_def_of_nonneg QuadraticMap.posDef_of_nonneg
-/

#print QuadraticMap.posDef_iff_nonneg /-
theorem posDef_iff_nonneg {Q : QuadraticMap R₂ M} : PosDef Q ↔ (∀ x, 0 ≤ Q x) ∧ Q.Anisotropic :=
  ⟨fun h => ⟨h.NonNeg, h.Anisotropic⟩, fun ⟨n, a⟩ => posDef_of_nonneg n a⟩
#align quadratic_form.pos_def_iff_nonneg QuadraticMap.posDef_iff_nonneg
-/

#print QuadraticMap.PosDef.add /-
theorem PosDef.add (Q Q' : QuadraticMap R₂ M) (hQ : PosDef Q) (hQ' : PosDef Q') : PosDef (Q + Q') :=
  fun x hx => add_pos (hQ x hx) (hQ' x hx)
#align quadratic_form.pos_def.add QuadraticMap.PosDef.add
-/

#print QuadraticMap.linMulLinSelfPosDef /-
theorem linMulLinSelfPosDef {R} [LinearOrderedCommRing R] [Module R M] (f : M →ₗ[R] R)
    (hf : LinearMap.ker f = ⊥) : PosDef (linMulLin f f) := fun x hx =>
  mul_self_pos.2 fun h => hx <| LinearMap.ker_eq_bot'.mp hf _ h
#align quadratic_form.lin_mul_lin_self_pos_def QuadraticMap.linMulLinSelfPosDef
-/

end PosDef

end QuadraticMap

section

/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/


variable {n : Type w} [Fintype n] [DecidableEq n]

variable [CommRing R₁] [AddCommMonoid M] [Module R₁ M]

#print Matrix.toQuadraticMap' /-
/-- `M.to_quadratic_form` is the map `λ x, col x ⬝ M ⬝ row x` as a quadratic form. -/
def Matrix.toQuadraticMap' (M : Matrix n n R₁) : QuadraticMap R₁ (n → R₁) :=
  M.toBilin'.toQuadraticMap
#align matrix.to_quadratic_form' Matrix.toQuadraticMap'
-/

variable [Invertible (2 : R₁)]

#print QuadraticMap.toMatrix' /-
/-- A matrix representation of the quadratic form. -/
def QuadraticMap.toMatrix' (Q : QuadraticMap R₁ (n → R₁)) : Matrix n n R₁ :=
  Q.Associated.toMatrix'
#align quadratic_form.to_matrix' QuadraticMap.toMatrix'
-/

open QuadraticMap

#print QuadraticMap.toMatrix'_smul /-
theorem QuadraticMap.toMatrix'_smul (a : R₁) (Q : QuadraticMap R₁ (n → R₁)) :
    (a • Q).toMatrix' = a • Q.toMatrix' := by
  simp only [to_matrix', LinearEquiv.map_smul, LinearMap.map_smul]
#align quadratic_form.to_matrix'_smul QuadraticMap.toMatrix'_smul
-/

#print QuadraticMap.isSymm_toMatrix' /-
theorem QuadraticMap.isSymm_toMatrix' (Q : QuadraticMap R₁ (n → R₁)) : Q.toMatrix'.IsSymm :=
  by
  ext i j
  rw [to_matrix', LinearMap.BilinForm.toMatrix'_apply, LinearMap.BilinForm.toMatrix'_apply,
    associated_is_symm]
#align quadratic_form.is_symm_to_matrix' QuadraticMap.isSymm_toMatrix'
-/

end

namespace QuadraticMap

variable {n : Type w} [Fintype n]

variable [CommRing R₁] [DecidableEq n] [Invertible (2 : R₁)]

variable {m : Type w} [DecidableEq m] [Fintype m]

open scoped Matrix

#print QuadraticMap.toMatrix'_comp /-
@[simp]
theorem toMatrix'_comp (Q : QuadraticMap R₁ (m → R₁)) (f : (n → R₁) →ₗ[R₁] m → R₁) :
    (Q.comp f).toMatrix' = f.toMatrix'ᵀ ⬝ Q.toMatrix' ⬝ f.toMatrix' := by ext;
  simp only [QuadraticMap.associated_comp, LinearMap.BilinForm.toMatrix'_comp, to_matrix']
#align quadratic_form.to_matrix'_comp QuadraticMap.toMatrix'_comp
-/

section Discriminant

variable {Q : QuadraticMap R₁ (n → R₁)}

#print QuadraticMap.discr /-
/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : QuadraticMap R₁ (n → R₁)) : R₁ :=
  Q.toMatrix'.det
#align quadratic_form.discr QuadraticMap.discr
-/

#print QuadraticMap.discr_smul /-
theorem discr_smul (a : R₁) : (a • Q).discr = a ^ Fintype.card n * Q.discr := by
  simp only [discr, to_matrix'_smul, Matrix.det_smul]
#align quadratic_form.discr_smul QuadraticMap.discr_smul
-/

#print QuadraticMap.discr_comp /-
theorem discr_comp (f : (n → R₁) →ₗ[R₁] n → R₁) :
    (Q.comp f).discr = f.toMatrix'.det * f.toMatrix'.det * Q.discr := by
  simp only [Matrix.det_transpose, mul_left_comm, QuadraticMap.toMatrix'_comp, mul_comm,
    Matrix.det_mul, discr]
#align quadratic_form.discr_comp QuadraticMap.discr_comp
-/

end Discriminant

end QuadraticMap

namespace QuadraticMap

end QuadraticMap

namespace BilinForm

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

#print LinearMap.BilinForm.separatingLeft_of_anisotropic /-
/-- A bilinear form is nondegenerate if the quadratic form it is associated with is anisotropic. -/
theorem LinearMap.BilinForm.separatingLeft_of_anisotropic {B : BilinForm R M}
    (hB : B.toQuadraticMap.Anisotropic) : B.Nondegenerate := fun x hx => hB _ (hx x)
#align bilin_form.nondegenerate_of_anisotropic LinearMap.BilinForm.separatingLeft_of_anisotropic
-/

end Semiring

variable [Ring R] [AddCommGroup M] [Module R M]

#print LinearMap.BilinForm.exists_bilinForm_self_ne_zero /-
/-- There exists a non-null vector with respect to any symmetric, nonzero bilinear form `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
theorem LinearMap.BilinForm.exists_bilinForm_self_ne_zero [htwo : Invertible (2 : R)]
    {B : BilinForm R M} (hB₁ : B ≠ 0) (hB₂ : B.IsSymm) : ∃ x, ¬B.IsOrtho x x :=
  by
  lift B to QuadraticMap R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticMap.exists_quadraticForm_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply ℕ x ▸ h)⟩
#align bilin_form.exists_bilin_form_self_ne_zero LinearMap.BilinForm.exists_bilinForm_self_ne_zero
-/

open FiniteDimensional

variable {V : Type u} {K : Type v} [Field K] [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

#print LinearMap.BilinForm.exists_orthogonal_basis /-
/-- Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`. -/
theorem LinearMap.BilinForm.exists_orthogonal_basis [hK : Invertible (2 : K)] {B : BilinForm K V}
    (hB₂ : B.IsSymm) : ∃ v : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ v :=
  by
  induction' hd : finrank K V with d ih generalizing V
  · exact ⟨basisOfFinrankZero hd, fun _ _ _ => zero_left _⟩
  haveI := finrank_pos_iff.1 (hd.symm ▸ Nat.succ_pos d : 0 < finrank K V)
  -- either the bilinear form is trivial or we can pick a non-null `x`
  obtain rfl | hB₁ := eq_or_ne B 0
  · let b := FiniteDimensional.finBasis K V
    rw [hd] at b
    refine' ⟨b, fun i j hij => rfl⟩
  obtain ⟨x, hx⟩ := exists_bilin_form_self_ne_zero hB₁ hB₂
  rw [← Submodule.finrank_add_eq_of_isCompl (is_compl_span_singleton_orthogonal hx).symm,
    finrank_span_singleton (ne_zero_of_not_is_ortho_self x hx)] at hd
  let B' := B.restrict (B.orthogonal <| K ∙ x)
  obtain ⟨v', hv₁⟩ := ih (B.restrict_symm hB₂ _ : B'.is_symm) (Nat.succ.inj hd)
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
        rw [is_ortho, smul_left, add_right, smul_right, div_mul_cancel₀ _ hx, add_neg_self,
          MulZeroClass.mul_zero])
  refine' ⟨b, _⟩
  · rw [Basis.coe_mkFinCons]
    intro j i
    refine' Fin.cases _ (fun i => _) i <;> refine' Fin.cases _ (fun j => _) j <;> intro hij <;>
      simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    · exact (hij rfl).elim
    · rw [is_ortho, hB₂]
      exact (v' j).IProp _ (Submodule.mem_span_singleton_self x)
    · exact (v' i).IProp _ (Submodule.mem_span_singleton_self x)
    · exact hv₁ (ne_of_apply_ne _ hij)
#align bilin_form.exists_orthogonal_basis LinearMap.BilinForm.exists_orthogonal_basis
-/

end BilinForm

namespace QuadraticMap

open Finset BilinForm

variable {M₁ : Type _} [Semiring R] [CommSemiring R₁] [AddCommMonoid M] [AddCommMonoid M₁]

variable [Module R M] [Module R M₁]

variable {ι : Type _} [Fintype ι] {v : Basis ι R M}

#print QuadraticMap.basisRepr /-
/-- Given a quadratic form `Q` and a basis, `basis_repr` is the basis representation of `Q`. -/
noncomputable def basisRepr (Q : QuadraticMap R M) (v : Basis ι R M) : QuadraticMap R (ι → R) :=
  Q.comp v.equivFun.symm
#align quadratic_form.basis_repr QuadraticMap.basisRepr
-/

#print QuadraticMap.basisRepr_apply /-
@[simp]
theorem basisRepr_apply (Q : QuadraticMap R M) (w : ι → R) :
    Q.basis_repr v w = Q (∑ i : ι, w i • v i) := by rw [← v.equiv_fun_symm_apply]; rfl
#align quadratic_form.basis_repr_apply QuadraticMap.basisRepr_apply
-/

section

variable (R₁)

#print QuadraticMap.weightedSumSquares /-
/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R₁` or
`[algebra S R₁]`, although this is stated more generally. -/
def weightedSumSquares [Monoid S] [DistribMulAction S R₁] [SMulCommClass S R₁ R₁] (w : ι → S) :
    QuadraticMap R₁ (ι → R₁) :=
  ∑ i : ι, w i • proj i i
#align quadratic_form.weighted_sum_squares QuadraticMap.weightedSumSquares
-/

end

#print QuadraticMap.weightedSumSquares_apply /-
@[simp]
theorem weightedSumSquares_apply [Monoid S] [DistribMulAction S R₁] [SMulCommClass S R₁ R₁]
    (w : ι → S) (v : ι → R₁) : weightedSumSquares R₁ w v = ∑ i : ι, w i • (v i * v i) :=
  QuadraticMap.sum_apply _ _ _
#align quadratic_form.weighted_sum_squares_apply QuadraticMap.weightedSumSquares_apply
-/

#print QuadraticMap.basisRepr_eq_of_iIsOrtho /-
/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
theorem basisRepr_eq_of_iIsOrtho {R₁ M} [CommRing R₁] [AddCommGroup M] [Module R₁ M]
    [Invertible (2 : R₁)] (Q : QuadraticMap R₁ M) (v : Basis ι R₁ M)
    (hv₂ : (associated Q).IsOrthoᵢ v) : Q.basis_repr v = weightedSumSquares _ fun i => Q (v i) :=
  by
  ext w
  rw [basis_repr_apply, ← @associated_eq_self_apply R₁, sum_left, weighted_sum_squares_apply]
  refine' sum_congr rfl fun j hj => _
  rw [← @associated_eq_self_apply R₁, sum_right, sum_eq_single_of_mem j hj]
  · rw [smul_left, smul_right, smul_eq_mul]; ring
  · intro i _ hij
    rw [smul_left, smul_right, show associated_hom R₁ Q (v j) (v i) = 0 from hv₂ hij.symm,
      MulZeroClass.mul_zero, MulZeroClass.mul_zero]
#align quadratic_form.basis_repr_eq_of_is_Ortho QuadraticMap.basisRepr_eq_of_iIsOrtho
-/

end QuadraticMap

