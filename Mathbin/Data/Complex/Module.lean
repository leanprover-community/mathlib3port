/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser

! This file was ported from Lean 3 source module data.complex.module
! leanprover-community/mathlib commit fe8d0ff42c3c24d789f491dc2622b6cac3d61564
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Smul
import Mathbin.Data.Complex.Basic
import Mathbin.Data.Fin.VecNotation
import Mathbin.FieldTheory.Tower
import Mathbin.Algebra.CharP.Invertible

/-!
# Complex number as a vector space over `ℝ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

variable [SMul R ℝ]

/- The useless `0` multiplication in `smul` is to make sure that
`restrict_scalars.module ℝ ℂ ℂ = complex.module` definitionally. -/
instance : SMul R ℂ where smul r x := ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩

/- warning: complex.smul_re -> Complex.smul_re is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : SMul.{u1, 0} R Real] (r : R) (z : Complex), Eq.{1} Real (Complex.re (SMul.smul.{u1, 0} R Complex (Complex.hasSmul.{u1} R _inst_1) r z)) (SMul.smul.{u1, 0} R Real _inst_1 r (Complex.re z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : SMul.{u1, 0} R Real] (r : R) (z : Complex), Eq.{1} Real (Complex.re (HSMul.hSMul.{u1, 0, 0} R Complex Complex (instHSMul.{u1, 0} R Complex (Complex.instSMulComplex.{u1} R _inst_1)) r z)) (HSMul.hSMul.{u1, 0, 0} R Real Real (instHSMul.{u1, 0} R Real _inst_1) r (Complex.re z))
Case conversion may be inaccurate. Consider using '#align complex.smul_re Complex.smul_reₓ'. -/
theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(· • ·)]
#align complex.smul_re Complex.smul_re

/- warning: complex.smul_im -> Complex.smul_im is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : SMul.{u1, 0} R Real] (r : R) (z : Complex), Eq.{1} Real (Complex.im (SMul.smul.{u1, 0} R Complex (Complex.hasSmul.{u1} R _inst_1) r z)) (SMul.smul.{u1, 0} R Real _inst_1 r (Complex.im z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : SMul.{u1, 0} R Real] (r : R) (z : Complex), Eq.{1} Real (Complex.im (HSMul.hSMul.{u1, 0, 0} R Complex Complex (instHSMul.{u1, 0} R Complex (Complex.instSMulComplex.{u1} R _inst_1)) r z)) (HSMul.hSMul.{u1, 0, 0} R Real Real (instHSMul.{u1, 0} R Real _inst_1) r (Complex.im z))
Case conversion may be inaccurate. Consider using '#align complex.smul_im Complex.smul_imₓ'. -/
theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(· • ·)]
#align complex.smul_im Complex.smul_im

/- warning: complex.real_smul -> Complex.real_smul is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Complex}, Eq.{1} Complex (SMul.smul.{0, 0} Real Complex (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) x z) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) z)
but is expected to have type
  forall {x : Real} {z : Complex}, Eq.{1} Complex (HSMul.hSMul.{0, 0, 0} Real Complex Complex (instHSMul.{0, 0} Real Complex (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal)))) x z) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' x) z)
Case conversion may be inaccurate. Consider using '#align complex.real_smul Complex.real_smulₓ'. -/
@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl
#align complex.real_smul Complex.real_smul

end

instance [SMul R ℝ] [SMul S ℝ] [SMulCommClass R S ℝ] : SMulCommClass R S ℂ
    where smul_comm r s x := by ext <;> simp [smul_re, smul_im, smul_comm]

instance [SMul R S] [SMul R ℝ] [SMul S ℝ] [IsScalarTower R S ℝ] : IsScalarTower R S ℂ
    where smul_assoc r s x := by ext <;> simp [smul_re, smul_im, smul_assoc]

instance [SMul R ℝ] [SMul Rᵐᵒᵖ ℝ] [IsCentralScalar R ℝ] : IsCentralScalar R ℂ
    where op_smul_eq_smul r x := by ext <;> simp [smul_re, smul_im, op_smul_eq_smul]

instance [Monoid R] [MulAction R ℝ] : MulAction R ℂ
    where
  one_smul x := by ext <;> simp [smul_re, smul_im, one_smul]
  mul_smul r s x := by ext <;> simp [smul_re, smul_im, mul_smul]

instance [DistribSMul R ℝ] : DistribSMul R ℂ
    where
  smul_add r x y := by ext <;> simp [smul_re, smul_im, smul_add]
  smul_zero r := by ext <;> simp [smul_re, smul_im, smul_zero]

instance [Semiring R] [DistribMulAction R ℝ] : DistribMulAction R ℂ :=
  { Complex.distribSmul with }

instance [Semiring R] [Module R ℝ] : Module R ℂ
    where
  add_smul r s x := by ext <;> simp [smul_re, smul_im, add_smul]
  zero_smul r := by ext <;> simp [smul_re, smul_im, zero_smul]

instance [CommSemiring R] [Algebra R ℝ] : Algebra R ℂ :=
  { Complex.ofReal.comp (algebraMap R ℝ) with
    smul := (· • ·)
    smul_def' := fun r x => by ext <;> simp [smul_re, smul_im, Algebra.smul_def]
    commutes' := fun r ⟨xr, xi⟩ => by ext <;> simp [smul_re, smul_im, Algebra.commutes] }

instance : StarModule ℝ ℂ :=
  ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_of_real]⟩

/- warning: complex.coe_algebra_map -> Complex.coe_algebraMap is a dubious translation:
lean 3 declaration is
  Eq.{1} ((fun (_x : RingHom.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))) => Real -> Complex) (algebraMap.{0, 0} Real Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)))) (coeFn.{1, 1} (RingHom.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))) (fun (_x : RingHom.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))) => Real -> Complex) (RingHom.hasCoeToFun.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))) (algebraMap.{0, 0} Real Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))))
but is expected to have type
  Eq.{1} (forall (a : Real), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Real) => Complex) a) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.instCommSemiringReal)) (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Real) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.instCommSemiringReal)) (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) Real Complex (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.instCommSemiringReal)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.instCommSemiringReal)) (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) Real Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.instCommSemiringReal))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.instCommSemiringReal)) (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.instCommSemiringReal)) (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex) (RingHom.instRingHomClassRingHom.{0, 0} Real Complex (Semiring.toNonAssocSemiring.{0} Real (CommSemiring.toSemiring.{0} Real Real.instCommSemiringReal)) (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) (algebraMap.{0, 0} Real Complex Real.instCommSemiringReal Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)))) Complex.ofReal'
Case conversion may be inaccurate. Consider using '#align complex.coe_algebra_map Complex.coe_algebraMapₓ'. -/
@[simp]
theorem coe_algebraMap : (algebraMap ℝ ℂ : ℝ → ℂ) = coe :=
  rfl
#align complex.coe_algebra_map Complex.coe_algebraMap

section

variable {A : Type _} [Semiring A] [Algebra ℝ A]

/- warning: alg_hom.map_coe_real_complex -> AlgHom.map_coe_real_complex is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.map_coe_real_complex AlgHom.map_coe_real_complexₓ'. -/
/-- We need this lemma since `complex.coe_algebra_map` diverts the simp-normal form away from
`alg_hom.commutes`. -/
@[simp]
theorem AlgHom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) : f x = algebraMap ℝ A x :=
  f.commutes x
#align alg_hom.map_coe_real_complex AlgHom.map_coe_real_complex

/- warning: complex.alg_hom_ext -> Complex.algHom_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.alg_hom_ext Complex.algHom_extₓ'. -/
/-- Two `ℝ`-algebra homomorphisms from ℂ are equal if they agree on `complex.I`. -/
@[ext]
theorem algHom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f I = g I) : f = g :=
  by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, AlgHom.map_add, AlgHom.map_coe_real_complex, AlgHom.map_mul, h]
#align complex.alg_hom_ext Complex.algHom_ext

end

section

open ComplexOrder

/- warning: complex.ordered_smul -> Complex.orderedSMul is a dubious translation:
lean 3 declaration is
  OrderedSMul.{0, 0} Real Complex Real.orderedSemiring (OrderedSemiring.toOrderedAddCommMonoid.{0} Complex (StrictOrderedSemiring.toOrderedSemiring.{0} Complex (StrictOrderedRing.toStrictOrderedSemiring.{0} Complex (StrictOrderedCommRing.toStrictOrderedRing.{0} Complex Complex.strictOrderedCommRing)))) (MulActionWithZero.toSMulWithZero.{0, 0} Real Complex Real.monoidWithZero (AddZeroClass.toHasZero.{0} Complex (AddMonoid.toAddZeroClass.{0} Complex (AddCommMonoid.toAddMonoid.{0} Complex (OrderedAddCommMonoid.toAddCommMonoid.{0} Complex (OrderedSemiring.toOrderedAddCommMonoid.{0} Complex (StrictOrderedSemiring.toOrderedSemiring.{0} Complex (StrictOrderedRing.toStrictOrderedSemiring.{0} Complex (StrictOrderedCommRing.toStrictOrderedRing.{0} Complex Complex.strictOrderedCommRing)))))))) (Module.toMulActionWithZero.{0, 0} Real Complex Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))))
but is expected to have type
  OrderedSMul.{0, 0} Real Complex Real.orderedSemiring (OrderedSemiring.toOrderedAddCommMonoid.{0} Complex (OrderedCommSemiring.toOrderedSemiring.{0} Complex (StrictOrderedCommSemiring.toOrderedCommSemiring.{0} Complex (StrictOrderedCommRing.toStrictOrderedCommSemiring.{0} Complex Complex.strictOrderedCommRing)))) (MulActionWithZero.toSMulWithZero.{0, 0} Real Complex Real.instMonoidWithZeroReal (AddMonoid.toZero.{0} Complex (AddCommMonoid.toAddMonoid.{0} Complex (OrderedAddCommMonoid.toAddCommMonoid.{0} Complex (OrderedSemiring.toOrderedAddCommMonoid.{0} Complex (OrderedCommSemiring.toOrderedSemiring.{0} Complex (StrictOrderedCommSemiring.toOrderedCommSemiring.{0} Complex (StrictOrderedCommRing.toStrictOrderedCommSemiring.{0} Complex Complex.strictOrderedCommRing))))))) (Module.toMulActionWithZero.{0, 0} Real Complex Real.semiring (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} Complex (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Complex (StrictOrderedCommSemiring.toStrictOrderedSemiring.{0} Complex (StrictOrderedCommRing.toStrictOrderedCommSemiring.{0} Complex Complex.strictOrderedCommRing)))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))))
Case conversion may be inaccurate. Consider using '#align complex.ordered_smul Complex.orderedSMulₓ'. -/
protected theorem orderedSMul : OrderedSMul ℝ ℂ :=
  OrderedSMul.mk' fun a b r hab hr => ⟨by simp [hr, hab.1.le], by simp [hab.2]⟩
#align complex.ordered_smul Complex.orderedSMul

scoped[ComplexOrder] attribute [instance] Complex.orderedSMul

end

open Submodule FiniteDimensional

/- warning: complex.basis_one_I -> Complex.basisOneI is a dubious translation:
lean 3 declaration is
  Basis.{0, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Real Complex Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))
but is expected to have type
  Basis.{0, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Complex Real.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))
Case conversion may be inaccurate. Consider using '#align complex.basis_one_I Complex.basisOneIₓ'. -/
/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basisOneI : Basis (Fin 2) ℝ ℂ :=
  Basis.ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by ext i; fin_cases i <;> simp
      map_add' := fun z z' => by simp
      -- why does `simp` not know how to apply `smul_cons`, which is a `@[simp]` lemma, here?
      map_smul' := fun c z => by simp [Matrix.smul_cons c z.re, Matrix.smul_cons c z.im] }
#align complex.basis_one_I Complex.basisOneI

/- warning: complex.coe_basis_one_I_repr -> Complex.coe_basisOneI_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.coe_basis_one_I_repr Complex.coe_basisOneI_reprₓ'. -/
@[simp]
theorem coe_basisOneI_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im] :=
  rfl
#align complex.coe_basis_one_I_repr Complex.coe_basisOneI_repr

/- warning: complex.coe_basis_one_I -> Complex.coe_basisOneI is a dubious translation:
lean 3 declaration is
  Eq.{1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> Complex) (coeFn.{1, 1} (Basis.{0, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Real Complex Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (fun (_x : Basis.{0, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Real Complex Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) => (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> Complex) (FunLike.hasCoeToFun.{1, 1, 1} (Basis.{0, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Real Complex Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (_x : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Complex) (Basis.funLike.{0, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Real Complex Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)))) Complex.basisOneI) (Matrix.vecCons.{0} Complex (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))) (Matrix.vecCons.{0} Complex (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) Complex.I (Matrix.vecEmpty.{0} Complex)))
but is expected to have type
  Eq.{1} (forall (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Complex) a) (FunLike.coe.{1, 1, 1} (Basis.{0, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Complex Real.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (_x : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Complex) _x) (Basis.funLike.{0, 0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Real Complex Real.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) Complex.basisOneI) (Matrix.vecCons.{0} Complex (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)) (Matrix.vecCons.{0} Complex (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) Complex.I (Matrix.vecEmpty.{0} Complex)))
Case conversion may be inaccurate. Consider using '#align complex.coe_basis_one_I Complex.coe_basisOneIₓ'. -/
@[simp]
theorem coe_basisOneI : ⇑basisOneI = ![1, I] :=
  funext fun i =>
    Basis.apply_eq_iff.mpr <|
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;>
          simp only [coe_basis_one_I_repr, Finsupp.single_eq_of_ne, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Fin.one_eq_zero_iff, Ne.def, not_false_iff, I_re,
            Nat.succ_succ_ne_one, one_im, I_im, one_re, Finsupp.single_eq_same, Fin.zero_eq_one_iff]
#align complex.coe_basis_one_I Complex.coe_basisOneI

instance : FiniteDimensional ℝ ℂ :=
  of_fintype_basis basisOneI

/- warning: complex.finrank_real_complex -> Complex.finrank_real_complex is a dubious translation:
lean 3 declaration is
  Eq.{1} Nat (FiniteDimensional.finrank.{0, 0} Real Complex Real.semiring Complex.addCommGroup (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  Eq.{1} Nat (FiniteDimensional.finrank.{0, 0} Real Complex Real.semiring Complex.addCommGroup (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
Case conversion may be inaccurate. Consider using '#align complex.finrank_real_complex Complex.finrank_real_complexₓ'. -/
@[simp]
theorem finrank_real_complex : FiniteDimensional.finrank ℝ ℂ = 2 := by
  rw [finrank_eq_card_basis basis_one_I, Fintype.card_fin]
#align complex.finrank_real_complex Complex.finrank_real_complex

/- warning: complex.rank_real_complex -> Complex.rank_real_complex is a dubious translation:
lean 3 declaration is
  Eq.{2} Cardinal.{0} (Module.rank.{0, 0} Real Complex Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (OfNat.ofNat.{1} Cardinal.{0} 2 (OfNat.mk.{1} Cardinal.{0} 2 (bit0.{1} Cardinal.{0} Cardinal.hasAdd.{0} (One.one.{1} Cardinal.{0} Cardinal.hasOne.{0}))))
but is expected to have type
  Eq.{2} Cardinal.{0} (Module.rank.{0, 0} Real Complex Real.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (OfNat.ofNat.{1} Cardinal.{0} 2 (instOfNat.{1} Cardinal.{0} 2 Cardinal.instNatCastCardinal.{0} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align complex.rank_real_complex Complex.rank_real_complexₓ'. -/
@[simp]
theorem rank_real_complex : Module.rank ℝ ℂ = 2 := by simp [← finrank_eq_rank, finrank_real_complex]
#align complex.rank_real_complex Complex.rank_real_complex

/- warning: complex.rank_real_complex' -> Complex.rank_real_complex' is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.lift.{u1, 0} (Module.rank.{0, 0} Real Complex Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))))
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.lift.{u1, 0} (Module.rank.{0, 0} Real Complex Real.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align complex.rank_real_complex' Complex.rank_real_complex'ₓ'. -/
theorem rank_real_complex'.{u} : Cardinal.lift.{u} (Module.rank ℝ ℂ) = 2 := by
  simp [← finrank_eq_rank, finrank_real_complex, bit0]
#align complex.rank_real_complex' Complex.rank_real_complex'

/- warning: complex.finrank_real_complex_fact -> Complex.finrank_real_complex_fact is a dubious translation:
lean 3 declaration is
  Fact (Eq.{1} Nat (FiniteDimensional.finrank.{0, 0} Real Complex Real.semiring Complex.addCommGroup (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  Fact (Eq.{1} Nat (FiniteDimensional.finrank.{0, 0} Real Complex Real.semiring Complex.addCommGroup (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align complex.finrank_real_complex_fact Complex.finrank_real_complex_factₓ'. -/
/-- `fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
theorem finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2) :=
  ⟨finrank_real_complex⟩
#align complex.finrank_real_complex_fact Complex.finrank_real_complex_fact

end Complex

#print Module.complexToReal /-
/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance (priority := 900) Module.complexToReal (E : Type _) [AddCommGroup E] [Module ℂ E] :
    Module ℝ E :=
  RestrictScalars.module ℝ ℂ E
#align module.complex_to_real Module.complexToReal
-/

/- warning: module.real_complex_tower -> Module.real_complex_tower is a dubious translation:
lean 3 declaration is
  forall (E : Type.{u1}) [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)], IsScalarTower.{0, 0, u1} Real Complex E (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (SMulZeroClass.toHasSmul.{0, u1} Complex E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Complex E (MulZeroClass.toHasZero.{0} Complex (MulZeroOneClass.toMulZeroClass.{0} Complex (MonoidWithZero.toMulZeroOneClass.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex E (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring)) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (Module.toMulActionWithZero.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_2)))) (SMulZeroClass.toHasSmul.{0, u1} Real E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real Real.semiring)))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E (Semiring.toMonoidWithZero.{0} Real Real.semiring) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) (Module.complexToReal.{u1} E _inst_1 _inst_2)))))
but is expected to have type
  forall (E : Type.{u1}) [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)], IsScalarTower.{0, 0, u1} Real Complex E (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (SMulZeroClass.toSMul.{0, u1} Complex E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Complex E Complex.instZeroComplex (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex E (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (Module.toMulActionWithZero.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_2)))) (SMulZeroClass.toSMul.{0, u1} Real E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real E Real.instZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) (Module.complexToReal.{u1} E _inst_1 _inst_2)))))
Case conversion may be inaccurate. Consider using '#align module.real_complex_tower Module.real_complex_towerₓ'. -/
instance Module.real_complex_tower (E : Type _) [AddCommGroup E] [Module ℂ E] :
    IsScalarTower ℝ ℂ E :=
  RestrictScalars.isScalarTower ℝ ℂ E
#align module.real_complex_tower Module.real_complex_tower

/- warning: complex.coe_smul -> Complex.coe_smul is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)] (x : Real) (y : E), Eq.{succ u1} E (SMul.smul.{0, u1} Complex E (SMulZeroClass.toHasSmul.{0, u1} Complex E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Complex E (MulZeroClass.toHasZero.{0} Complex (MulZeroOneClass.toMulZeroClass.{0} Complex (MonoidWithZero.toMulZeroOneClass.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex E (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring)) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (Module.toMulActionWithZero.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_2)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) y) (SMul.smul.{0, u1} Real E (SMulZeroClass.toHasSmul.{0, u1} Real E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real Real.semiring)))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E (Semiring.toMonoidWithZero.{0} Real Real.semiring) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) (Module.complexToReal.{u1} E _inst_1 _inst_2))))) x y)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)] (x : Real) (y : E), Eq.{succ u1} E (HSMul.hSMul.{0, u1, u1} Complex E E (instHSMul.{0, u1} Complex E (SMulZeroClass.toSMul.{0, u1} Complex E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Complex E Complex.instZeroComplex (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex E (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (Module.toMulActionWithZero.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_2))))) (Complex.ofReal' x) y) (HSMul.hSMul.{0, u1, u1} Real E E (instHSMul.{0, u1} Real E (SMulZeroClass.toSMul.{0, u1} Real E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real E Real.instZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) (Module.complexToReal.{u1} E _inst_1 _inst_2)))))) x y)
Case conversion may be inaccurate. Consider using '#align complex.coe_smul Complex.coe_smulₓ'. -/
@[simp, norm_cast]
theorem Complex.coe_smul {E : Type _} [AddCommGroup E] [Module ℂ E] (x : ℝ) (y : E) :
    (x : ℂ) • y = x • y :=
  rfl
#align complex.coe_smul Complex.coe_smul

#print SMulCommClass.complexToReal /-
/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `module.complex_to_real` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
instance (priority := 900) SMulCommClass.complexToReal {M E : Type _} [AddCommGroup E] [Module ℂ E]
    [SMul M E] [SMulCommClass ℂ M E] : SMulCommClass ℝ M E
    where smul_comm r _ _ := (smul_comm (r : ℂ) _ _ : _)
#align smul_comm_class.complex_to_real SMulCommClass.complexToReal
-/

/- warning: finite_dimensional.complex_to_real -> FiniteDimensional.complexToReal is a dubious translation:
lean 3 declaration is
  forall (E : Type.{u1}) [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u1} Complex E (Field.toDivisionRing.{0} Complex Complex.field) _inst_1 _inst_2], FiniteDimensional.{0, u1} Real E Real.divisionRing _inst_1 (Module.complexToReal.{u1} E _inst_1 _inst_2)
but is expected to have type
  forall (E : Type.{u1}) [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u1} Complex E (Field.toDivisionRing.{0} Complex Complex.instFieldComplex) _inst_1 _inst_2], FiniteDimensional.{0, u1} Real E Real.instDivisionRingReal _inst_1 (Module.complexToReal.{u1} E _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align finite_dimensional.complex_to_real FiniteDimensional.complexToRealₓ'. -/
instance (priority := 100) FiniteDimensional.complexToReal (E : Type _) [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E] : FiniteDimensional ℝ E :=
  FiniteDimensional.trans ℝ ℂ E
#align finite_dimensional.complex_to_real FiniteDimensional.complexToReal

/- warning: rank_real_of_complex -> rank_real_of_complex is a dubious translation:
lean 3 declaration is
  forall (E : Type.{u1}) [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)], Eq.{succ (succ u1)} Cardinal.{u1} (Module.rank.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) (Module.complexToReal.{u1} E _inst_1 _inst_2)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Module.rank.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_2))
but is expected to have type
  forall (E : Type.{u1}) [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)], Eq.{succ (succ u1)} Cardinal.{u1} (Module.rank.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) (Module.complexToReal.{u1} E _inst_1 _inst_2)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Module.rank.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_2))
Case conversion may be inaccurate. Consider using '#align rank_real_of_complex rank_real_of_complexₓ'. -/
theorem rank_real_of_complex (E : Type _) [AddCommGroup E] [Module ℂ E] :
    Module.rank ℝ E = 2 * Module.rank ℂ E :=
  Cardinal.lift_inj.1 <| by rw [← lift_rank_mul_lift_rank ℝ ℂ E, Complex.rank_real_complex];
    simp [bit0]
#align rank_real_of_complex rank_real_of_complex

#print finrank_real_of_complex /-
theorem finrank_real_of_complex (E : Type _) [AddCommGroup E] [Module ℂ E] :
    FiniteDimensional.finrank ℝ E = 2 * FiniteDimensional.finrank ℂ E := by
  rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]
#align finrank_real_of_complex finrank_real_of_complex
-/

/- warning: star_module.complex_to_real -> StarModule.complexToReal is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Star.{u1} E] [_inst_3 : Module.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)] [_inst_4 : StarModule.{0, u1} Complex E (InvolutiveStar.toHasStar.{0} Complex (StarAddMonoid.toHasInvolutiveStar.{0} Complex (AddCommMonoid.toAddMonoid.{0} Complex (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Complex (NonUnitalRing.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalRing.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing)))))) (StarRing.toStarAddMonoid.{0} Complex (NonUnitalRing.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalRing.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing))) Complex.starRing))) _inst_2 (SMulZeroClass.toHasSmul.{0, u1} Complex E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Complex E (MulZeroClass.toHasZero.{0} Complex (MulZeroOneClass.toMulZeroClass.{0} Complex (MonoidWithZero.toMulZeroOneClass.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex E (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring)) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (Module.toMulActionWithZero.{0, u1} Complex E (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_3))))], StarModule.{0, u1} Real E (InvolutiveStar.toHasStar.{0} Real (StarAddMonoid.toHasInvolutiveStar.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real (NonUnitalRing.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalRing.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))))) (StarRing.toStarAddMonoid.{0} Real (NonUnitalRing.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalRing.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing))) Real.starRing))) _inst_2 (SMulZeroClass.toHasSmul.{0, u1} Real E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real Real.semiring)))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E (Semiring.toMonoidWithZero.{0} Real Real.semiring) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) (Module.complexToReal.{u1} E _inst_1 _inst_3)))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Star.{u1} E] [_inst_3 : Module.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)] [_inst_4 : StarModule.{0, u1} Complex E (InvolutiveStar.toStar.{0} Complex (StarAddMonoid.toInvolutiveStar.{0} Complex (AddMonoidWithOne.toAddMonoid.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.Complex.addGroupWithOne)) (StarRing.toStarAddMonoid.{0} Complex (NonUnitalCommSemiring.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalCommSemiring.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing))) Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing))) _inst_2 (SMulZeroClass.toSMul.{0, u1} Complex E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Complex E Complex.instZeroComplex (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex E (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (Module.toMulActionWithZero.{0, u1} Complex E Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_3))))], StarModule.{0, u1} Real E (InvolutiveStar.toStar.{0} Real (StarAddMonoid.toInvolutiveStar.{0} Real Real.instAddMonoidReal (StarRing.toStarAddMonoid.{0} Real (NonUnitalCommSemiring.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalCommSemiring.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing))) Real.instStarRingRealToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing))) _inst_2 (SMulZeroClass.toSMul.{0, u1} Real E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real E Real.instZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) (Module.complexToReal.{u1} E _inst_1 _inst_3)))))
Case conversion may be inaccurate. Consider using '#align star_module.complex_to_real StarModule.complexToRealₓ'. -/
instance (priority := 900) StarModule.complexToReal {E : Type _} [AddCommGroup E] [Star E]
    [Module ℂ E] [StarModule ℂ E] : StarModule ℝ E :=
  ⟨fun r a => by rw [← smul_one_smul ℂ r a, star_smul, star_smul, star_one, smul_one_smul]⟩
#align star_module.complex_to_real StarModule.complexToReal

namespace Complex

open ComplexConjugate

/- warning: complex.re_lm -> Complex.reLm is a dubious translation:
lean 3 declaration is
  LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.addCommMonoid (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)
but is expected to have type
  LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) Real.instAddCommMonoidReal (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)
Case conversion may be inaccurate. Consider using '#align complex.re_lm Complex.reLmₓ'. -/
/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp
#align complex.re_lm Complex.reLm

/- warning: complex.re_lm_coe -> Complex.reLm_coe is a dubious translation:
lean 3 declaration is
  Eq.{1} (Complex -> Real) (coeFn.{1, 1} (LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.addCommMonoid (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)) (fun (_x : LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.addCommMonoid (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)) => Complex -> Real) (LinearMap.hasCoeToFun.{0, 0, 0, 0} Real Real Complex Real Real.semiring Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.addCommMonoid (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.reLm) Complex.re
but is expected to have type
  Eq.{1} (forall (ᾰ : Complex), (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : Complex) => Real) ᾰ) (FunLike.coe.{1, 1, 1} (LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) Real.instAddCommMonoidReal (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : Complex) => Real) _x) (LinearMap.instFunLikeLinearMap.{0, 0, 0, 0} Real Real Complex Real Real.semiring Real.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) Real.instAddCommMonoidReal (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.reLm) Complex.re
Case conversion may be inaccurate. Consider using '#align complex.re_lm_coe Complex.reLm_coeₓ'. -/
@[simp]
theorem reLm_coe : ⇑reLm = re :=
  rfl
#align complex.re_lm_coe Complex.reLm_coe

/- warning: complex.im_lm -> Complex.imLm is a dubious translation:
lean 3 declaration is
  LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.addCommMonoid (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)
but is expected to have type
  LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) Real.instAddCommMonoidReal (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)
Case conversion may be inaccurate. Consider using '#align complex.im_lm Complex.imLmₓ'. -/
/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def imLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.im
  map_add' := add_im
  map_smul' := by simp
#align complex.im_lm Complex.imLm

/- warning: complex.im_lm_coe -> Complex.imLm_coe is a dubious translation:
lean 3 declaration is
  Eq.{1} (Complex -> Real) (coeFn.{1, 1} (LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.addCommMonoid (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)) (fun (_x : LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.addCommMonoid (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)) => Complex -> Real) (LinearMap.hasCoeToFun.{0, 0, 0, 0} Real Real Complex Real Real.semiring Real.semiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) Real.addCommMonoid (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.imLm) Complex.im
but is expected to have type
  Eq.{1} (forall (ᾰ : Complex), (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : Complex) => Real) ᾰ) (FunLike.coe.{1, 1, 1} (LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Complex Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) Real.instAddCommMonoidReal (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring)) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : Complex) => Real) _x) (LinearMap.instFunLikeLinearMap.{0, 0, 0, 0} Real Real Complex Real Real.semiring Real.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) Real.instAddCommMonoidReal (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Semiring.toModule.{0} Real Real.semiring) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex.imLm) Complex.im
Case conversion may be inaccurate. Consider using '#align complex.im_lm_coe Complex.imLm_coeₓ'. -/
@[simp]
theorem imLm_coe : ⇑imLm = im :=
  rfl
#align complex.im_lm_coe Complex.imLm_coe

/- warning: complex.of_real_am -> Complex.ofRealAm is a dubious translation:
lean 3 declaration is
  AlgHom.{0, 0, 0} Real Real Complex Real.commSemiring Real.semiring (Ring.toSemiring.{0} Complex Complex.ring) (Algebra.id.{0} Real Real.commSemiring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))
but is expected to have type
  AlgHom.{0, 0, 0} Real Real Complex Real.instCommSemiringReal Real.semiring Complex.instSemiringComplex (Algebra.id.{0} Real Real.instCommSemiringReal) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal))
Case conversion may be inaccurate. Consider using '#align complex.of_real_am Complex.ofRealAmₓ'. -/
/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealAm : ℝ →ₐ[ℝ] ℂ :=
  Algebra.ofId ℝ ℂ
#align complex.of_real_am Complex.ofRealAm

#print Complex.ofRealAm_coe /-
@[simp]
theorem ofRealAm_coe : ⇑ofRealAm = coe :=
  rfl
#align complex.of_real_am_coe Complex.ofRealAm_coe
-/

/- warning: complex.conj_ae -> Complex.conjAe is a dubious translation:
lean 3 declaration is
  AlgEquiv.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))
but is expected to have type
  AlgEquiv.{0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal))
Case conversion may be inaccurate. Consider using '#align complex.conj_ae Complex.conjAeₓ'. -/
/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
def conjAe : ℂ ≃ₐ[ℝ] ℂ :=
  { conj with
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_ofReal }
#align complex.conj_ae Complex.conjAe

/- warning: complex.conj_ae_coe -> Complex.conjAe_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.conj_ae_coe Complex.conjAe_coeₓ'. -/
@[simp]
theorem conjAe_coe : ⇑conjAe = conj :=
  rfl
#align complex.conj_ae_coe Complex.conjAe_coe

/- warning: complex.to_matrix_conj_ae -> Complex.toMatrix_conjAe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.to_matrix_conj_ae Complex.toMatrix_conjAeₓ'. -/
/-- The matrix representation of `conj_ae`. -/
@[simp]
theorem toMatrix_conjAe :
    LinearMap.toMatrix basisOneI basisOneI conjAe.toLinearMap = !![1, 0; 0, -1] :=
  by
  ext (i j)
  simp [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp
#align complex.to_matrix_conj_ae Complex.toMatrix_conjAe

/- warning: complex.real_alg_hom_eq_id_or_conj -> Complex.real_algHom_eq_id_or_conj is a dubious translation:
lean 3 declaration is
  forall (f : AlgHom.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))), Or (Eq.{1} (AlgHom.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) f (AlgHom.id.{0, 0} Real Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)))) (Eq.{1} (AlgHom.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (AlgEquiv.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) (AlgHom.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) (HasLiftT.mk.{1, 1} (AlgEquiv.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) (AlgHom.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) (CoeTCₓ.coe.{1, 1} (AlgEquiv.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) (AlgHom.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) (AlgHomClass.coeTC.{0, 0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (AlgEquiv.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) (AlgEquivClass.toAlgHomClass.{0, 0, 0, 0} (AlgEquiv.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (AlgEquiv.algEquivClass.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))))))) Complex.conjAe))
but is expected to have type
  forall (f : AlgHom.{0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal))), Or (Eq.{1} (AlgHom.{0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal))) f (AlgHom.id.{0, 0} Real Complex Real.instCommSemiringReal Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)))) (Eq.{1} (AlgHom.{0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal))) f (AlgHomClass.toAlgHom.{0, 0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (AlgEquiv.{0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal))) (AlgEquivClass.toAlgHomClass.{0, 0, 0, 0} (AlgEquiv.{0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal))) Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (AlgEquiv.instAlgEquivClassAlgEquiv.{0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)))) Complex.conjAe))
Case conversion may be inaccurate. Consider using '#align complex.real_alg_hom_eq_id_or_conj Complex.real_algHom_eq_id_or_conjₓ'. -/
/-- The identity and the complex conjugation are the only two `ℝ`-algebra homomorphisms of `ℂ`. -/
theorem real_algHom_eq_id_or_conj (f : ℂ →ₐ[ℝ] ℂ) : f = AlgHom.id ℝ ℂ ∨ f = conjAe :=
  by
  refine'
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp _ _ <;>
    refine' fun h => alg_hom_ext _
  exacts[h, conj_I.symm ▸ h]
#align complex.real_alg_hom_eq_id_or_conj Complex.real_algHom_eq_id_or_conj

/- warning: complex.equiv_real_prod_add_hom -> Complex.equivRealProdAddHom is a dubious translation:
lean 3 declaration is
  AddEquiv.{0, 0} Complex (Prod.{0, 0} Real Real) Complex.hasAdd (Prod.hasAdd.{0, 0} Real Real Real.hasAdd Real.hasAdd)
but is expected to have type
  AddEquiv.{0, 0} Complex (Prod.{0, 0} Real Real) Complex.instAddComplex (Prod.instAddSum.{0, 0} Real Real Real.instAddReal Real.instAddReal)
Case conversion may be inaccurate. Consider using '#align complex.equiv_real_prod_add_hom Complex.equivRealProdAddHomₓ'. -/
/-- The natural `add_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with map_add' := by simp }
#align complex.equiv_real_prod_add_hom Complex.equivRealProdAddHom

/- warning: complex.equiv_real_prod_lm -> Complex.equivRealProdLm is a dubious translation:
lean 3 declaration is
  LinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHomInvPair.ids.{0} Real Real.semiring) (RingHomInvPair.ids.{0} Real Real.semiring) Complex (Prod.{0, 0} Real Real) (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Prod.addCommMonoid.{0, 0} Real Real Real.addCommMonoid Real.addCommMonoid) (Complex.module.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Prod.module.{0, 0, 0} Real Real Real Real.semiring Real.addCommMonoid Real.addCommMonoid (Semiring.toModule.{0} Real Real.semiring) (Semiring.toModule.{0} Real Real.semiring))
but is expected to have type
  LinearEquiv.{0, 0, 0, 0} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHomInvPair.ids.{0} Real Real.semiring) (RingHomInvPair.ids.{0} Real Real.semiring) Complex (Prod.{0, 0} Real Real) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Prod.instAddCommMonoidSum.{0, 0} Real Real Real.instAddCommMonoidReal Real.instAddCommMonoidReal) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real Real.semiring (Semiring.toModule.{0} Real Real.semiring)) (Prod.module.{0, 0, 0} Real Real Real Real.semiring Real.instAddCommMonoidReal Real.instAddCommMonoidReal (Semiring.toModule.{0} Real Real.semiring) (Semiring.toModule.{0} Real Real.semiring))
Case conversion may be inaccurate. Consider using '#align complex.equiv_real_prod_lm Complex.equivRealProdLmₓ'. -/
/-- The natural `linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdLm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  { equivRealProdAddHom with map_smul' := by simp [equiv_real_prod_add_hom] }
#align complex.equiv_real_prod_lm Complex.equivRealProdLm

section lift

variable {A : Type _} [Ring A] [Algebra ℝ A]

/- warning: complex.lift_aux -> Complex.liftAux is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : Ring.{u1} A] [_inst_2 : Algebra.{0, u1} Real A Real.commSemiring (Ring.toSemiring.{u1} A _inst_1)] (I' : A), (Eq.{succ u1} A (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A (Distrib.toHasMul.{u1} A (Ring.toDistrib.{u1} A _inst_1))) I' I') (Neg.neg.{u1} A (SubNegMonoid.toHasNeg.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))) (OfNat.ofNat.{u1} A 1 (OfNat.mk.{u1} A 1 (One.one.{u1} A (AddMonoidWithOne.toOne.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))))))) -> (AlgHom.{0, 0, u1} Real Complex A Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{u1} A _inst_1) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) _inst_2)
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : Ring.{u1} A] [_inst_2 : Algebra.{0, u1} Real A Real.instCommSemiringReal (Ring.toSemiring.{u1} A _inst_1)] (I' : A), (Eq.{succ u1} A (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A (NonUnitalNonAssocRing.toMul.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A _inst_1)))) I' I') (Neg.neg.{u1} A (Ring.toNeg.{u1} A _inst_1) (OfNat.ofNat.{u1} A 1 (One.toOfNat1.{u1} A (Semiring.toOne.{u1} A (Ring.toSemiring.{u1} A _inst_1)))))) -> (AlgHom.{0, 0, u1} Real Complex A Real.instCommSemiringReal Complex.instSemiringComplex (Ring.toSemiring.{u1} A _inst_1) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) _inst_2)
Case conversion may be inaccurate. Consider using '#align complex.lift_aux Complex.liftAuxₓ'. -/
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
        rw [smul_mul_smul, hf, smul_neg, ← Algebra.algebraMap_eq_smul_one, ← sub_eq_add_neg, ←
          RingHom.map_mul, ← RingHom.map_sub]
      ·
        rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, ← Algebra.right_comm _ x₂, ←
          mul_assoc, ← add_mul, ← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add]
#align complex.lift_aux Complex.liftAux

/- warning: complex.lift_aux_apply -> Complex.liftAux_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.lift_aux_apply Complex.liftAux_applyₓ'. -/
@[simp]
theorem liftAux_apply (I' : A) (hI') (z : ℂ) : liftAux I' hI' z = algebraMap ℝ A z.re + z.im • I' :=
  rfl
#align complex.lift_aux_apply Complex.liftAux_apply

/- warning: complex.lift_aux_apply_I -> Complex.liftAux_apply_I is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.lift_aux_apply_I Complex.liftAux_apply_Iₓ'. -/
theorem liftAux_apply_I (I' : A) (hI') : liftAux I' hI' I = I' := by simp
#align complex.lift_aux_apply_I Complex.liftAux_apply_I

/- warning: complex.lift -> Complex.lift is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : Ring.{u1} A] [_inst_2 : Algebra.{0, u1} Real A Real.commSemiring (Ring.toSemiring.{u1} A _inst_1)], Equiv.{succ u1, succ u1} (Subtype.{succ u1} A (fun (I' : A) => Eq.{succ u1} A (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A (Distrib.toHasMul.{u1} A (Ring.toDistrib.{u1} A _inst_1))) I' I') (Neg.neg.{u1} A (SubNegMonoid.toHasNeg.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))) (OfNat.ofNat.{u1} A 1 (OfNat.mk.{u1} A 1 (One.one.{u1} A (AddMonoidWithOne.toOne.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))))))))) (AlgHom.{0, 0, u1} Real Complex A Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{u1} A _inst_1) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) _inst_2)
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : Ring.{u1} A] [_inst_2 : Algebra.{0, u1} Real A Real.instCommSemiringReal (Ring.toSemiring.{u1} A _inst_1)], Equiv.{succ u1, succ u1} (Subtype.{succ u1} A (fun (I' : A) => Eq.{succ u1} A (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A (NonUnitalNonAssocRing.toMul.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A _inst_1)))) I' I') (Neg.neg.{u1} A (Ring.toNeg.{u1} A _inst_1) (OfNat.ofNat.{u1} A 1 (One.toOfNat1.{u1} A (Semiring.toOne.{u1} A (Ring.toSemiring.{u1} A _inst_1))))))) (AlgHom.{0, 0, u1} Real Complex A Real.instCommSemiringReal Complex.instSemiringComplex (Ring.toSemiring.{u1} A _inst_1) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) _inst_2)
Case conversion may be inaccurate. Consider using '#align complex.lift Complex.liftₓ'. -/
/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `quaternion`s.

This isomorphism is named to match the very similar `zsqrtd.lift`. -/
@[simps (config := { simpRhs := true })]
def lift : { I' : A // I' * I' = -1 } ≃ (ℂ →ₐ[ℝ] A)
    where
  toFun I' := liftAux I' I'.Prop
  invFun F := ⟨F I, by rw [← F.map_mul, I_mul_I, AlgHom.map_neg, AlgHom.map_one]⟩
  left_inv I' := Subtype.ext <| liftAux_apply_I I' I'.Prop
  right_inv F := algHom_ext <| liftAux_apply_I _ _
#align complex.lift Complex.lift

/- warning: complex.lift_aux_I -> Complex.liftAux_I is a dubious translation:
lean 3 declaration is
  Eq.{1} (AlgHom.{0, 0, 0} Real Complex Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring))) (Complex.liftAux.{0} Complex Complex.ring (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)) Complex.I Complex.I_mul_I) (AlgHom.id.{0, 0} Real Complex Real.commSemiring (Ring.toSemiring.{0} Complex Complex.ring) (Complex.algebra.{0} Real Real.commSemiring (Algebra.id.{0} Real Real.commSemiring)))
but is expected to have type
  Eq.{1} (AlgHom.{0, 0, 0} Real Complex Complex Real.instCommSemiringReal Complex.instSemiringComplex (Ring.toSemiring.{0} Complex Complex.instRingComplex) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal))) (Complex.liftAux.{0} Complex Complex.instRingComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)) Complex.I Complex.I_mul_I) (AlgHom.id.{0, 0} Real Complex Real.instCommSemiringReal Complex.instSemiringComplex (Complex.instAlgebraComplexInstSemiringComplex.{0} Real Real.instCommSemiringReal (Algebra.id.{0} Real Real.instCommSemiringReal)))
Case conversion may be inaccurate. Consider using '#align complex.lift_aux_I Complex.liftAux_Iₓ'. -/
-- When applied to `complex.I` itself, `lift` is the identity.
@[simp]
theorem liftAux_I : liftAux I I_mul_I = AlgHom.id ℝ ℂ :=
  algHom_ext <| liftAux_apply_I _ _
#align complex.lift_aux_I Complex.liftAux_I

/- warning: complex.lift_aux_neg_I -> Complex.liftAux_neg_I is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align complex.lift_aux_neg_I Complex.liftAux_neg_Iₓ'. -/
-- When applied to `-complex.I`, `lift` is conjugation, `conj`.
@[simp]
theorem liftAux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe :=
  algHom_ext <| (liftAux_apply_I _ _).trans conj_I.symm
#align complex.lift_aux_neg_I Complex.liftAux_neg_I

end lift

end Complex

section RealImaginaryPart

open Complex

variable {A : Type _} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/- warning: skew_adjoint.neg_I_smul -> skewAdjoint.negISMul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align skew_adjoint.neg_I_smul skewAdjoint.negISMulₓ'. -/
/-- Create a `self_adjoint` element from a `skew_adjoint` element by multiplying by the scalar
`-complex.I`. -/
@[simps]
def skewAdjoint.negISMul : skewAdjoint A →ₗ[ℝ] selfAdjoint A
    where
  toFun a :=
    ⟨-I • a, by
      simp only [selfAdjoint.mem_iff, neg_smul, star_neg, star_smul, star_def, conj_I,
        skewAdjoint.star_val_eq, neg_smul_neg]⟩
  map_add' a b := by ext; simp only [AddSubgroup.coe_add, smul_add, AddMemClass.mk_add_mk]
  map_smul' a b := by
    ext;
    simp only [neg_smul, skewAdjoint.val_smul, AddSubgroup.coe_mk, RingHom.id_apply,
      selfAdjoint.val_smul, smul_neg, neg_inj]
    rw [smul_comm]
#align skew_adjoint.neg_I_smul skewAdjoint.negISMul

/- warning: skew_adjoint.I_smul_neg_I -> skewAdjoint.I_smul_neg_I is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align skew_adjoint.I_smul_neg_I skewAdjoint.I_smul_neg_Iₓ'. -/
theorem skewAdjoint.I_smul_neg_I (a : skewAdjoint A) : I • (skewAdjoint.negISMul a : A) = a := by
  simp only [smul_smul, skewAdjoint.negISMul_apply_coe, neg_smul, smul_neg, I_mul_I, one_smul,
    neg_neg]
#align skew_adjoint.I_smul_neg_I skewAdjoint.I_smul_neg_I

/- warning: real_part -> realPart is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : AddCommGroup.{u1} A] [_inst_2 : Module.{0, u1} Complex A (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)] [_inst_3 : StarAddMonoid.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)))] [_inst_4 : StarModule.{0, u1} Complex A (InvolutiveStar.toHasStar.{0} Complex (StarAddMonoid.toHasInvolutiveStar.{0} Complex (AddCommMonoid.toAddMonoid.{0} Complex (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Complex (NonUnitalRing.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalRing.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing)))))) (StarRing.toStarAddMonoid.{0} Complex (NonUnitalRing.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalRing.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing))) Complex.starRing))) (InvolutiveStar.toHasStar.{u1} A (StarAddMonoid.toHasInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) _inst_3)) (SMulZeroClass.toHasSmul.{0, u1} Complex A (AddZeroClass.toHasZero.{u1} A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Complex A (MulZeroClass.toHasZero.{0} Complex (MulZeroOneClass.toMulZeroClass.{0} Complex (MonoidWithZero.toMulZeroOneClass.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))))) (AddZeroClass.toHasZero.{u1} A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex A (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring)) (AddZeroClass.toHasZero.{u1} A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)))) (Module.toMulActionWithZero.{0, u1} Complex A (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) _inst_2))))], LinearMap.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) A (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) A (AddSubgroup.setLike.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3)) (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) A (AddSubgroup.setLike.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3)) (AddSubgroup.toAddCommGroup.{u1} A _inst_1 (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3))) (Module.complexToReal.{u1} A _inst_1 _inst_2) (selfAdjoint.module.{0, u1} Real A (InvolutiveStar.toHasStar.{0} Real (StarAddMonoid.toHasInvolutiveStar.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real (NonUnitalRing.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalRing.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))))) (StarRing.toStarAddMonoid.{0} Real (NonUnitalRing.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalRing.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing))) Real.starRing))) Real.trivialStar _inst_1 _inst_3 Real.semiring (Module.complexToReal.{u1} A _inst_1 _inst_2) (realPart._proof_1.{u1} A _inst_1 _inst_2 _inst_3 _inst_4))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : AddCommGroup.{u1} A] [_inst_2 : Module.{0, u1} Complex A Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)] [_inst_3 : StarAddMonoid.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)))] [_inst_4 : StarModule.{0, u1} Complex A (InvolutiveStar.toStar.{0} Complex (StarAddMonoid.toInvolutiveStar.{0} Complex (AddMonoidWithOne.toAddMonoid.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.Complex.addGroupWithOne)) (StarRing.toStarAddMonoid.{0} Complex (NonUnitalCommSemiring.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalCommSemiring.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing))) Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing))) (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) _inst_3)) (SMulZeroClass.toSMul.{0, u1} Complex A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Complex A Complex.instZeroComplex (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex A (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_1))))) (Module.toMulActionWithZero.{0, u1} Complex A Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) _inst_2))))], LinearMap.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) A (Subtype.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) x (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) (AddSubmonoid.toAddCommMonoid.{u1} A (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) (AddSubgroup.toAddSubmonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3))) (Module.complexToReal.{u1} A _inst_1 _inst_2) (selfAdjoint.instModuleSubtypeMemAddSubgroupToAddGroupInstMembershipInstSetLikeAddSubgroupSelfAdjointToAddCommMonoidToAddCommMonoidToAddSubmonoid.{0, u1} Real A (InvolutiveStar.toStar.{0} Real (StarAddMonoid.toInvolutiveStar.{0} Real Real.instAddMonoidReal (StarRing.toStarAddMonoid.{0} Real (NonUnitalCommSemiring.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalCommSemiring.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing))) Real.instStarRingRealToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing))) Real.instTrivialStarRealToStarToInvolutiveStarInstAddMonoidRealToStarAddMonoidToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRingInstStarRingRealToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing _inst_1 _inst_3 Real.semiring (Module.complexToReal.{u1} A _inst_1 _inst_2) (StarModule.complexToReal.{u1} A _inst_1 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) _inst_3)) _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align real_part realPartₓ'. -/
/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`self_adjoint_part ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginary_part`, which doesn't exist in star modules over other rings. -/
noncomputable def realPart : A →ₗ[ℝ] selfAdjoint A :=
  selfAdjointPart ℝ
#align real_part realPart

/- warning: imaginary_part -> imaginaryPart is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : AddCommGroup.{u1} A] [_inst_2 : Module.{0, u1} Complex A (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)] [_inst_3 : StarAddMonoid.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)))] [_inst_4 : StarModule.{0, u1} Complex A (InvolutiveStar.toHasStar.{0} Complex (StarAddMonoid.toHasInvolutiveStar.{0} Complex (AddCommMonoid.toAddMonoid.{0} Complex (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Complex (NonUnitalRing.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalRing.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing)))))) (StarRing.toStarAddMonoid.{0} Complex (NonUnitalRing.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalRing.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing))) Complex.starRing))) (InvolutiveStar.toHasStar.{u1} A (StarAddMonoid.toHasInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) _inst_3)) (SMulZeroClass.toHasSmul.{0, u1} Complex A (AddZeroClass.toHasZero.{u1} A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Complex A (MulZeroClass.toHasZero.{0} Complex (MulZeroOneClass.toMulZeroClass.{0} Complex (MonoidWithZero.toMulZeroOneClass.{0} Complex (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring))))) (AddZeroClass.toHasZero.{u1} A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex A (Semiring.toMonoidWithZero.{0} Complex (Ring.toSemiring.{0} Complex Complex.ring)) (AddZeroClass.toHasZero.{u1} A (AddMonoid.toAddZeroClass.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)))) (Module.toMulActionWithZero.{0, u1} Complex A (Ring.toSemiring.{0} Complex Complex.ring) (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) _inst_2))))], LinearMap.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) A (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) A (AddSubgroup.setLike.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3)) (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) A (AddSubgroup.setLike.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3)) (AddSubgroup.toAddCommGroup.{u1} A _inst_1 (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3))) (Module.complexToReal.{u1} A _inst_1 _inst_2) (selfAdjoint.module.{0, u1} Real A (InvolutiveStar.toHasStar.{0} Real (StarAddMonoid.toHasInvolutiveStar.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{0} Real (NonUnitalRing.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalRing.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))))) (StarRing.toStarAddMonoid.{0} Real (NonUnitalRing.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalRing.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing))) Real.starRing))) Real.trivialStar _inst_1 _inst_3 Real.semiring (Module.complexToReal.{u1} A _inst_1 _inst_2) (imaginaryPart._proof_1.{u1} A _inst_1 _inst_2 _inst_3 _inst_4))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : AddCommGroup.{u1} A] [_inst_2 : Module.{0, u1} Complex A Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} A _inst_1)] [_inst_3 : StarAddMonoid.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)))] [_inst_4 : StarModule.{0, u1} Complex A (InvolutiveStar.toStar.{0} Complex (StarAddMonoid.toInvolutiveStar.{0} Complex (AddMonoidWithOne.toAddMonoid.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.Complex.addGroupWithOne)) (StarRing.toStarAddMonoid.{0} Complex (NonUnitalCommSemiring.toNonUnitalSemiring.{0} Complex (NonUnitalCommRing.toNonUnitalCommSemiring.{0} Complex (CommRing.toNonUnitalCommRing.{0} Complex Complex.commRing))) Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing))) (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) _inst_3)) (SMulZeroClass.toSMul.{0, u1} Complex A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Complex A Complex.instZeroComplex (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Complex A (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_1))))) (Module.toMulActionWithZero.{0, u1} Complex A Complex.instSemiringComplex (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) _inst_2))))], LinearMap.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) A (Subtype.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1)) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) x (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) (AddSubmonoid.toAddCommMonoid.{u1} A (AddCommGroup.toAddCommMonoid.{u1} A _inst_1) (AddSubgroup.toAddSubmonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) (selfAdjoint.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1) _inst_3))) (Module.complexToReal.{u1} A _inst_1 _inst_2) (selfAdjoint.instModuleSubtypeMemAddSubgroupToAddGroupInstMembershipInstSetLikeAddSubgroupSelfAdjointToAddCommMonoidToAddCommMonoidToAddSubmonoid.{0, u1} Real A (InvolutiveStar.toStar.{0} Real (StarAddMonoid.toInvolutiveStar.{0} Real Real.instAddMonoidReal (StarRing.toStarAddMonoid.{0} Real (NonUnitalCommSemiring.toNonUnitalSemiring.{0} Real (NonUnitalCommRing.toNonUnitalCommSemiring.{0} Real (CommRing.toNonUnitalCommRing.{0} Real Real.commRing))) Real.instStarRingRealToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing))) Real.instTrivialStarRealToStarToInvolutiveStarInstAddMonoidRealToStarAddMonoidToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRingInstStarRingRealToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing _inst_1 _inst_3 Real.semiring (Module.complexToReal.{u1} A _inst_1 _inst_2) (StarModule.complexToReal.{u1} A _inst_1 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_1))) _inst_3)) _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align imaginary_part imaginaryPartₓ'. -/
/-- The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linear map into the
self adjoint elements. In a general star module, we have a decomposition into the `self_adjoint`
and `skew_adjoint` parts, but in a star module over `ℂ` we have
`real_part_add_I_smul_imaginary_part`, which allows us to decompose into a linear combination of
`self_adjoint`s. -/
noncomputable def imaginaryPart : A →ₗ[ℝ] selfAdjoint A :=
  skewAdjoint.negISMul.comp (skewAdjointPart ℝ)
#align imaginary_part imaginaryPart

-- mathport name: exprℜ
scoped[ComplexStarModule] notation "ℜ" => realPart

-- mathport name: exprℑ
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

/- warning: real_part_apply_coe -> realPart_apply_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align real_part_apply_coe realPart_apply_coeₓ'. -/
@[simp]
theorem realPart_apply_coe (a : A) : (ℜ a : A) = (2 : ℝ)⁻¹ • (a + star a) := by unfold realPart;
  simp only [selfAdjointPart_apply_coe, invOf_eq_inv]
#align real_part_apply_coe realPart_apply_coe

/- warning: imaginary_part_apply_coe -> imaginaryPart_apply_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align imaginary_part_apply_coe imaginaryPart_apply_coeₓ'. -/
@[simp]
theorem imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) :=
  by
  unfold imaginaryPart
  simp only [LinearMap.coe_comp, skewAdjoint.negISMul_apply_coe, skewAdjointPart_apply_coe,
    invOf_eq_inv]
#align imaginary_part_apply_coe imaginaryPart_apply_coe

/- warning: real_part_add_I_smul_imaginary_part -> realPart_add_I_smul_imaginaryPart is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align real_part_add_I_smul_imaginary_part realPart_add_I_smul_imaginaryPartₓ'. -/
/-- The standard decomposition of `ℜ a + complex.I • ℑ a = a` of an element of a star module over
`ℂ` into a linear combination of self adjoint elements. -/
theorem realPart_add_I_smul_imaginaryPart (a : A) : (ℜ a + I • ℑ a : A) = a := by
  simpa only [smul_smul, realPart_apply_coe, imaginaryPart_apply_coe, neg_smul, I_mul_I, one_smul,
    neg_sub, add_add_sub_cancel, smul_sub, smul_add, neg_sub_neg, invOf_eq_inv] using
    invOf_two_smul_add_invOf_two_smul ℝ a
#align real_part_add_I_smul_imaginary_part realPart_add_I_smul_imaginaryPart

/- warning: real_part_I_smul -> realPart_I_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align real_part_I_smul realPart_I_smulₓ'. -/
@[simp]
theorem realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a := by ext;
  simp [smul_comm I, smul_sub, sub_eq_add_neg, add_comm]
#align real_part_I_smul realPart_I_smul

/- warning: imaginary_part_I_smul -> imaginaryPart_I_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align imaginary_part_I_smul imaginaryPart_I_smulₓ'. -/
@[simp]
theorem imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a := by ext; simp [smul_comm I, smul_smul I]
#align imaginary_part_I_smul imaginaryPart_I_smul

/- warning: real_part_smul -> realPart_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align real_part_smul realPart_smulₓ'. -/
theorem realPart_smul (z : ℂ) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a := by
  nth_rw 1 [← re_add_im z]; simp [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]
#align real_part_smul realPart_smul

/- warning: imaginary_part_smul -> imaginaryPart_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align imaginary_part_smul imaginaryPart_smulₓ'. -/
theorem imaginaryPart_smul (z : ℂ) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a := by
  nth_rw 1 [← re_add_im z]; simp [-re_add_im, add_smul, ← smul_smul]
#align imaginary_part_smul imaginaryPart_smul

end RealImaginaryPart

