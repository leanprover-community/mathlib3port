/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser

! This file was ported from Lean 3 source module data.complex.module
! leanprover-community/mathlib commit b3f25363ae62cb169e72cd6b8b1ac97bacf21ca7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Orientation
import Mathbin.Algebra.Order.Smul
import Mathbin.Data.Complex.Basic
import Mathbin.Data.Fin.VecNotation
import Mathbin.FieldTheory.Tower
import Mathbin.Algebra.CharP.Invertible

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`has_smul`, `mul_action`, `distrib_mul_action`, `module`, `algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines bundled versions of four standard maps (respectively, the real part, the imaginary
part, the embedding of `ℝ` in `ℂ`, and the complex conjugate):

* `complex.re_lm` (`ℝ`-linear map);
* `complex.im_lm` (`ℝ`-linear map);
* `complex.of_real_am` (`ℝ`-algebra (homo)morphism);
* `complex.conj_ae` (`ℝ`-algebra equivalence).

It also provides a universal property of the complex numbers `complex.lift`, which constructs a
`ℂ →ₐ[ℝ] A` into any `ℝ`-algebra `A` given a square root of `-1`.

In addition, this file provides a decomposition into `real_part` and `imaginary_part` for any
element of a `star_module` over `ℂ`.

## Notation

* `ℜ` and `ℑ` for the `real_part` and `imaginary_part`, respectively, in the locale
  `complex_star_module`.
-/


namespace Complex

open ComplexConjugate

variable {R : Type _} {S : Type _}

section

variable [HasSmul R ℝ]

/- The useless `0` multiplication in `smul` is to make sure that
`restrict_scalars.module ℝ ℂ ℂ = complex.module` definitionally. -/
instance : HasSmul R ℂ where smul r x := ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩

theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(· • ·)]
#align complex.smul_re Complex.smul_re

theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(· • ·)]
#align complex.smul_im Complex.smul_im

@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl
#align complex.real_smul Complex.real_smul

end

instance [HasSmul R ℝ] [HasSmul S ℝ] [SMulCommClass R S ℝ] :
    SMulCommClass R S ℂ where smul_comm r s x := by ext <;> simp [smul_re, smul_im, smul_comm]

instance [HasSmul R S] [HasSmul R ℝ] [HasSmul S ℝ] [IsScalarTower R S ℝ] :
    IsScalarTower R S ℂ where smul_assoc r s x := by ext <;> simp [smul_re, smul_im, smul_assoc]

instance [HasSmul R ℝ] [HasSmul Rᵐᵒᵖ ℝ] [IsCentralScalar R ℝ] :
    IsCentralScalar R
      ℂ where op_smul_eq_smul r x := by ext <;> simp [smul_re, smul_im, op_smul_eq_smul]

instance [Monoid R] [MulAction R ℝ] :
    MulAction R
      ℂ where 
  one_smul x := by ext <;> simp [smul_re, smul_im, one_smul]
  mul_smul r s x := by ext <;> simp [smul_re, smul_im, mul_smul]

instance [DistribSMul R ℝ] :
    DistribSMul R
      ℂ where 
  smul_add r x y := by ext <;> simp [smul_re, smul_im, smul_add]
  smul_zero r := by ext <;> simp [smul_re, smul_im, smul_zero]

instance [Semiring R] [DistribMulAction R ℝ] : DistribMulAction R ℂ :=
  { Complex.distribSmul with }

instance [Semiring R] [Module R ℝ] :
    Module R ℂ where 
  add_smul r s x := by ext <;> simp [smul_re, smul_im, add_smul]
  zero_smul r := by ext <;> simp [smul_re, smul_im, zero_smul]

instance [CommSemiring R] [Algebra R ℝ] : Algebra R ℂ :=
  { Complex.ofReal.comp (algebraMap R ℝ) with
    smul := (· • ·)
    smul_def' := fun r x => by ext <;> simp [smul_re, smul_im, Algebra.smul_def]
    commutes' := fun r ⟨xr, xi⟩ => by ext <;> simp [smul_re, smul_im, Algebra.commutes] }

instance : StarModule ℝ ℂ :=
  ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_of_real]⟩

@[simp]
theorem coe_algebra_map : (algebraMap ℝ ℂ : ℝ → ℂ) = coe :=
  rfl
#align complex.coe_algebra_map Complex.coe_algebra_map

section

variable {A : Type _} [Semiring A] [Algebra ℝ A]

/-- We need this lemma since `complex.coe_algebra_map` diverts the simp-normal form away from
`alg_hom.commutes`. -/
@[simp]
theorem AlgHom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) : f x = algebraMap ℝ A x :=
  f.commutes x
#align alg_hom.map_coe_real_complex AlgHom.map_coe_real_complex

/-- Two `ℝ`-algebra homomorphisms from ℂ are equal if they agree on `complex.I`. -/
@[ext]
theorem alg_hom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f i = g i) : f = g := by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, AlgHom.map_add, AlgHom.map_coe_real_complex, AlgHom.map_mul, h]
#align complex.alg_hom_ext Complex.alg_hom_ext

end

section

open ComplexOrder

protected theorem ordered_smul : OrderedSmul ℝ ℂ :=
  OrderedSmul.mk' fun a b r hab hr => ⟨by simp [hr, hab.1.le], by simp [hab.2]⟩
#align complex.ordered_smul Complex.ordered_smul

scoped[ComplexOrder] attribute [instance] Complex.ordered_smul

end

open Submodule FiniteDimensional

/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basisOneI : Basis (Fin 2) ℝ ℂ :=
  Basis.ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by 
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      -- why does `simp` not know how to apply `smul_cons`, which is a `@[simp]` lemma, here?
      map_smul' := fun c z => by simp [Matrix.smul_cons c z.re, Matrix.smul_cons c z.im] }
#align complex.basis_one_I Complex.basisOneI

@[simp]
theorem coe_basis_one_I_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im] :=
  rfl
#align complex.coe_basis_one_I_repr Complex.coe_basis_one_I_repr

@[simp]
theorem coe_basis_one_I : ⇑basis_one_I = ![1, i] :=
  funext fun i =>
    Basis.apply_eq_iff.mpr <|
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;>
          simp only [coe_basis_one_I_repr, Finsupp.single_eq_same, Finsupp.single_eq_of_ne,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Nat.one_ne_zero,
            Fin.one_eq_zero_iff, Fin.zero_eq_one_iff, Ne.def, not_false_iff, one_re, one_im, I_re,
            I_im]
#align complex.coe_basis_one_I Complex.coe_basis_one_I

instance : FiniteDimensional ℝ ℂ :=
  of_fintype_basis basisOneI

@[simp]
theorem finrank_real_complex : FiniteDimensional.finrank ℝ ℂ = 2 := by
  rw [finrank_eq_card_basis basis_one_I, Fintype.card_fin]
#align complex.finrank_real_complex Complex.finrank_real_complex

@[simp]
theorem dim_real_complex : Module.rank ℝ ℂ = 2 := by simp [← finrank_eq_dim, finrank_real_complex]
#align complex.dim_real_complex Complex.dim_real_complex

theorem dim_real_complex'.{u} : Cardinal.lift.{u} (Module.rank ℝ ℂ) = 2 := by
  simp [← finrank_eq_dim, finrank_real_complex, bit0]
#align complex.dim_real_complex' Complex.dim_real_complex'

/-- `fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
theorem finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2) :=
  ⟨finrank_real_complex⟩
#align complex.finrank_real_complex_fact Complex.finrank_real_complex_fact

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.Orientation
#align complex.orientation Complex.orientation

end Complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance (priority := 900) Module.complexToReal (E : Type _) [AddCommGroup E] [Module ℂ E] :
    Module ℝ E :=
  RestrictScalars.module ℝ ℂ E
#align module.complex_to_real Module.complexToReal

instance Module.real_complex_tower (E : Type _) [AddCommGroup E] [Module ℂ E] :
    IsScalarTower ℝ ℂ E :=
  RestrictScalars.is_scalar_tower ℝ ℂ E
#align module.real_complex_tower Module.real_complex_tower

@[simp, norm_cast]
theorem Complex.coe_smul {E : Type _} [AddCommGroup E] [Module ℂ E] (x : ℝ) (y : E) :
    (x : ℂ) • y = x • y :=
  rfl
#align complex.coe_smul Complex.coe_smul

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `module.complex_to_real` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
instance (priority := 900) SMulCommClass.complex_to_real {M E : Type _} [AddCommGroup E]
    [Module ℂ E] [HasSmul M E] [SMulCommClass ℂ M E] :
    SMulCommClass ℝ M E where smul_comm r _ _ := (smul_comm (r : ℂ) _ _ : _)
#align smul_comm_class.complex_to_real SMulCommClass.complex_to_real

instance (priority := 100) FiniteDimensional.complex_to_real (E : Type _) [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E] : FiniteDimensional ℝ E :=
  FiniteDimensional.trans ℝ ℂ E
#align finite_dimensional.complex_to_real FiniteDimensional.complex_to_real

theorem dim_real_of_complex (E : Type _) [AddCommGroup E] [Module ℂ E] :
    Module.rank ℝ E = 2 * Module.rank ℂ E :=
  Cardinal.lift_inj.1 <| by
    rw [← dim_mul_dim' ℝ ℂ E, Complex.dim_real_complex]
    simp [bit0]
#align dim_real_of_complex dim_real_of_complex

theorem finrank_real_of_complex (E : Type _) [AddCommGroup E] [Module ℂ E] :
    FiniteDimensional.finrank ℝ E = 2 * FiniteDimensional.finrank ℂ E := by
  rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]
#align finrank_real_of_complex finrank_real_of_complex

instance (priority := 900) StarModule.complex_to_real {E : Type _} [AddCommGroup E] [HasStar E]
    [Module ℂ E] [StarModule ℂ E] : StarModule ℝ E :=
  ⟨fun r a => by
    rw [star_trivial r, restrict_scalars_smul_def, restrict_scalars_smul_def, star_smul,
      Complex.coe_algebra_map, Complex.star_def, Complex.conj_of_real]⟩
#align star_module.complex_to_real StarModule.complex_to_real

namespace Complex

open ComplexConjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reLm : ℂ →ₗ[ℝ] ℝ where 
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp
#align complex.re_lm Complex.reLm

@[simp]
theorem re_lm_coe : ⇑re_lm = re :=
  rfl
#align complex.re_lm_coe Complex.re_lm_coe

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def imLm : ℂ →ₗ[ℝ] ℝ where 
  toFun x := x.im
  map_add' := add_im
  map_smul' := by simp
#align complex.im_lm Complex.imLm

@[simp]
theorem im_lm_coe : ⇑im_lm = im :=
  rfl
#align complex.im_lm_coe Complex.im_lm_coe

/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealAm : ℝ →ₐ[ℝ] ℂ :=
  Algebra.ofId ℝ ℂ
#align complex.of_real_am Complex.ofRealAm

@[simp]
theorem of_real_am_coe : ⇑of_real_am = coe :=
  rfl
#align complex.of_real_am_coe Complex.of_real_am_coe

/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
def conjAe : ℂ ≃ₐ[ℝ] ℂ :=
  { conj with 
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_of_real }
#align complex.conj_ae Complex.conjAe

@[simp]
theorem conj_ae_coe : ⇑conj_ae = conj :=
  rfl
#align complex.conj_ae_coe Complex.conj_ae_coe

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
/-- The matrix representation of `conj_ae`. -/
@[simp]
theorem to_matrix_conj_ae :
    LinearMap.toMatrix basisOneI basisOneI conjAe.toLinearMap =
      «expr!![ »
        "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation" :=
  by 
  ext (i j)
  simp [LinearMap.to_matrix_apply]
  fin_cases i <;> fin_cases j <;> simp
#align complex.to_matrix_conj_ae Complex.to_matrix_conj_ae

/-- The identity and the complex conjugation are the only two `ℝ`-algebra homomorphisms of `ℂ`. -/
theorem real_alg_hom_eq_id_or_conj (f : ℂ →ₐ[ℝ] ℂ) : f = AlgHom.id ℝ ℂ ∨ f = conj_ae := by
  refine'
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp _ _ <;>
    refine' fun h => alg_hom_ext _
  exacts[h, conj_I.symm ▸ h]
#align complex.real_alg_hom_eq_id_or_conj Complex.real_alg_hom_eq_id_or_conj

section lift

variable {A : Type _} [Ring A] [Algebra ℝ A]

/-- There is an alg_hom from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `complex.lift` for this as an equiv. -/
def liftAux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
  AlgHom.ofLinearMap
    ((Algebra.ofId ℝ A).toLinearMap.comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap ℝ A 1 + (0 : ℝ) • I' = 1 by rw [RingHom.map_one, zero_smul, add_zero])
    fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ =>
    show
      algebraMap ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
        (algebraMap ℝ A x₁ + y₁ • I') * (algebraMap ℝ A x₂ + y₂ • I')
      by 
      rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm]
      congr 1
      -- equate "real" and "imaginary" parts
      ·
        rw [smul_mul_smul, hf, smul_neg, ← Algebra.algebra_map_eq_smul_one, ← sub_eq_add_neg, ←
          RingHom.map_mul, ← RingHom.map_sub]
      ·
        rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, ← Algebra.right_comm _ x₂, ←
          mul_assoc, ← add_mul, ← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add]
#align complex.lift_aux Complex.liftAux

@[simp]
theorem lift_aux_apply (I' : A) (hI') (z : ℂ) :
    liftAux I' hI' z = algebraMap ℝ A z.re + z.im • I' :=
  rfl
#align complex.lift_aux_apply Complex.lift_aux_apply

theorem lift_aux_apply_I (I' : A) (hI') : liftAux I' hI' i = I' := by simp
#align complex.lift_aux_apply_I Complex.lift_aux_apply_I

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `quaternion`s.

This isomorphism is named to match the very similar `zsqrtd.lift`. -/
@[simps (config := { simpRhs := true })]
def lift :
    { I' : A // I' * I' = -1 } ≃
      (ℂ →ₐ[ℝ] A) where 
  toFun I' := liftAux I' I'.Prop
  invFun F := ⟨F i, by rw [← F.map_mul, I_mul_I, AlgHom.map_neg, AlgHom.map_one]⟩
  left_inv I' := Subtype.ext <| lift_aux_apply_I I' I'.Prop
  right_inv F := alg_hom_ext <| lift_aux_apply_I _ _
#align complex.lift Complex.lift

-- When applied to `complex.I` itself, `lift` is the identity.
@[simp]
theorem lift_aux_I : liftAux i I_mul_I = AlgHom.id ℝ ℂ :=
  alg_hom_ext <| lift_aux_apply_I _ _
#align complex.lift_aux_I Complex.lift_aux_I

-- When applied to `-complex.I`, `lift` is conjugation, `conj`.
@[simp]
theorem lift_aux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conj_ae :=
  alg_hom_ext <| (lift_aux_apply_I _ _).trans conj_I.symm
#align complex.lift_aux_neg_I Complex.lift_aux_neg_I

end lift

end Complex

section RealImaginaryPart

open Complex

variable {A : Type _} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- Create a `self_adjoint` element from a `skew_adjoint` element by multiplying by the scalar
`-complex.I`. -/
@[simps]
def skewAdjoint.negISmul :
    skewAdjoint A →ₗ[ℝ]
      selfAdjoint
        A where 
  toFun a :=
    ⟨-I • a, by
      simp only [selfAdjoint.mem_iff, neg_smul, star_neg, star_smul, star_def, conj_I,
        skewAdjoint.star_coe_eq, neg_smul_neg]⟩
  map_add' a b := by 
    ext
    simp only [AddSubgroup.coe_add, smul_add, AddMemClass.mk_add_mk]
  map_smul' a b := by 
    ext
    simp only [neg_smul, skewAdjoint.coe_smul, AddSubgroup.coe_mk, RingHom.id_apply,
      selfAdjoint.coe_smul, smul_neg, neg_inj]
    rw [smul_comm]
#align skew_adjoint.neg_I_smul skewAdjoint.negISmul

theorem skewAdjoint.I_smul_neg_I (a : skewAdjoint A) : I • (skewAdjoint.negISmul a : A) = a := by
  simp only [smul_smul, skewAdjoint.neg_I_smul_apply_coe, neg_smul, smul_neg, I_mul_I, one_smul,
    neg_neg]
#align skew_adjoint.I_smul_neg_I skewAdjoint.I_smul_neg_I

/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`self_adjoint_part ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginary_part`, which doesn't exist in star modules over other rings. -/
noncomputable def realPart : A →ₗ[ℝ] selfAdjoint A :=
  selfAdjointPart ℝ
#align real_part realPart

/-- The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linear map into the
self adjoint elements. In a general star module, we have a decomposition into the `self_adjoint`
and `skew_adjoint` parts, but in a star module over `ℂ` we have
`real_part_add_I_smul_imaginary_part`, which allows us to decompose into a linear combination of
`self_adjoint`s. -/
noncomputable def imaginaryPart : A →ₗ[ℝ] selfAdjoint A :=
  skewAdjoint.negISmul.comp (skewAdjointPart ℝ)
#align imaginary_part imaginaryPart

-- mathport name: exprℜ
scoped[ComplexStarModule] notation "ℜ" => realPart

-- mathport name: exprℑ
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

@[simp]
theorem real_part_apply_coe (a : A) : (ℜ a : A) = (2 : ℝ)⁻¹ • (a + star a) := by
  unfold realPart
  simp only [self_adjoint_part_apply_coe, invOf_eq_inv]
#align real_part_apply_coe real_part_apply_coe

@[simp]
theorem imaginary_part_apply_coe (a : A) : (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) := by
  unfold imaginaryPart
  simp only [LinearMap.coe_comp, skewAdjoint.neg_I_smul_apply_coe, skew_adjoint_part_apply_coe,
    invOf_eq_inv]
#align imaginary_part_apply_coe imaginary_part_apply_coe

/-- The standard decomposition of `ℜ a + complex.I • ℑ a = a` of an element of a star module over
`ℂ` into a linear combination of self adjoint elements. -/
theorem real_part_add_I_smul_imaginary_part (a : A) : (ℜ a + I • ℑ a : A) = a := by
  simpa only [smul_smul, real_part_apply_coe, imaginary_part_apply_coe, neg_smul, I_mul_I, one_smul,
    neg_sub, add_add_sub_cancel, smul_sub, smul_add, neg_sub_neg, invOf_eq_inv] using
    inv_of_two_smul_add_inv_of_two_smul ℝ a
#align real_part_add_I_smul_imaginary_part real_part_add_I_smul_imaginary_part

@[simp]
theorem real_part_I_smul (a : A) : ℜ (I • a) = -ℑ a := by
  ext
  simp [smul_comm I, smul_sub, sub_eq_add_neg, add_comm]
#align real_part_I_smul real_part_I_smul

@[simp]
theorem imaginary_part_I_smul (a : A) : ℑ (I • a) = ℜ a := by
  ext
  simp [smul_comm I, smul_smul I]
#align imaginary_part_I_smul imaginary_part_I_smul

theorem real_part_smul (z : ℂ) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a := by
  nth_rw 1 [← re_add_im z]
  simp [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]
#align real_part_smul real_part_smul

theorem imaginary_part_smul (z : ℂ) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a := by
  nth_rw 1 [← re_add_im z]
  simp [-re_add_im, add_smul, ← smul_smul]
#align imaginary_part_smul imaginary_part_smul

end RealImaginaryPart

