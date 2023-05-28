/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang

! This file was ported from Lean 3 source module ring_theory.derivation
! leanprover-community/mathlib commit 26ae6f6771ba2d8c76ac47efb84ef2908f178630
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Lie.OfAssociative
import Mathbin.RingTheory.Adjoin.Basic
import Mathbin.RingTheory.Ideal.QuotientOperations

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Main results

- `derivation`: The type of `R`-derivations from `A` to `M`. This has an `A`-module structure.
- `derivation.llcomp`: We may compose linear maps and derivations to obtain a derivation,
  and the composition is bilinear.
- `derivation.lie_algebra`: The `R`-derivations from `A` to `A` form an lie algebra over `R`.
- `derivation_to_square_zero_equiv_lift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

## Future project

- Generalize derivations into bimodules.

-/


open Algebra

open BigOperators

/-- `D : derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality. We also require that `D 1 = 0`. See `derivation.mk'` for a constructor that deduces this
assumption from the Leibniz rule when `M` is cancellative.

TODO: update this when bimodules are defined. -/
@[protect_proj]
structure Derivation (R : Type _) (A : Type _) [CommSemiring R] [CommSemiring A] [Algebra R A]
  (M : Type _) [AddCommMonoid M] [Module A M] [Module R M] extends A →ₗ[R] M where
  map_one_eq_zero' : to_linear_map 1 = 0
  leibniz' (a b : A) : to_linear_map (a * b) = a • to_linear_map b + b • to_linear_map a
#align derivation Derivation

/-- The `linear_map` underlying a `derivation`. -/
add_decl_doc Derivation.toLinearMap

namespace Derivation

section

variable {R : Type _} [CommSemiring R]

variable {A : Type _} [CommSemiring A] [Algebra R A]

variable {M : Type _} [AddCommMonoid M] [Module A M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

instance : AddMonoidHomClass (Derivation R A M) A M
    where
  coe D := D.toFun
  coe_injective' D1 D2 h := by cases D1; cases D2; congr ; exact FunLike.coe_injective h
  map_add D := D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (Derivation R A M) fun _ => A → M :=
  ⟨fun D => D.toLinearMap.toFun⟩

-- Not a simp lemma because it can be proved via `coe_fn_coe` + `to_linear_map_eq_coe`
theorem toFun_eq_coe : D.toFun = ⇑D :=
  rfl
#align derivation.to_fun_eq_coe Derivation.toFun_eq_coe

instance hasCoeToLinearMap : Coe (Derivation R A M) (A →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩
#align derivation.has_coe_to_linear_map Derivation.hasCoeToLinearMap

@[simp]
theorem toLinearMap_eq_coe : D.toLinearMap = D :=
  rfl
#align derivation.to_linear_map_eq_coe Derivation.toLinearMap_eq_coe

@[simp]
theorem mk_coe (f : A →ₗ[R] M) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : Derivation R A M) : A → M) = f :=
  rfl
#align derivation.mk_coe Derivation.mk_coe

@[simp, norm_cast]
theorem coeFn_coe (f : Derivation R A M) : ⇑(f : A →ₗ[R] M) = f :=
  rfl
#align derivation.coe_fn_coe Derivation.coeFn_coe

theorem coe_injective : @Function.Injective (Derivation R A M) (A → M) coeFn :=
  FunLike.coe_injective
#align derivation.coe_injective Derivation.coe_injective

@[ext]
theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
  FunLike.ext _ _ H
#align derivation.ext Derivation.ext

theorem congr_fun (h : D1 = D2) (a : A) : D1 a = D2 a :=
  FunLike.congr_fun h a
#align derivation.congr_fun Derivation.congr_fun

protected theorem map_add : D (a + b) = D a + D b :=
  map_add D a b
#align derivation.map_add Derivation.map_add

protected theorem map_zero : D 0 = 0 :=
  map_zero D
#align derivation.map_zero Derivation.map_zero

@[simp]
theorem map_smul : D (r • a) = r • D a :=
  D.toLinearMap.map_smul r a
#align derivation.map_smul Derivation.map_smul

@[simp]
theorem leibniz : D (a * b) = a • D b + b • D a :=
  D.leibniz' _ _
#align derivation.leibniz Derivation.leibniz

theorem map_sum {ι : Type _} (s : Finset ι) (f : ι → A) : D (∑ i in s, f i) = ∑ i in s, D (f i) :=
  D.toLinearMap.map_sum
#align derivation.map_sum Derivation.map_sum

@[simp]
theorem map_smul_of_tower {S : Type _} [SMul S A] [SMul S M] [LinearMap.CompatibleSMul A M S R]
    (D : Derivation R A M) (r : S) (a : A) : D (r • a) = r • D a :=
  D.toLinearMap.map_smul_of_tower r a
#align derivation.map_smul_of_tower Derivation.map_smul_of_tower

@[simp]
theorem map_one_eq_zero : D 1 = 0 :=
  D.map_one_eq_zero'
#align derivation.map_one_eq_zero Derivation.map_one_eq_zero

@[simp]
theorem map_algebraMap : D (algebraMap R A r) = 0 := by
  rw [← mul_one r, RingHom.map_mul, RingHom.map_one, ← smul_def, map_smul, map_one_eq_zero,
    smul_zero]
#align derivation.map_algebra_map Derivation.map_algebraMap

@[simp]
theorem map_coe_nat (n : ℕ) : D (n : A) = 0 := by
  rw [← nsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]
#align derivation.map_coe_nat Derivation.map_coe_nat

@[simp]
theorem leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a :=
  by
  induction' n with n ihn
  · rw [pow_zero, map_one_eq_zero, zero_smul]
  · rcases(zero_le n).eq_or_lt with (rfl | hpos)
    · rw [pow_one, one_smul, pow_zero, one_smul]
    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ, Nat.sub_add_cancel hpos]
      simp only [pow_succ, leibniz, ihn, smul_comm a n, smul_smul a, add_smul, this,
        Nat.succ_eq_add_one, Nat.add_succ_sub_one, add_zero, one_nsmul]
#align derivation.leibniz_pow Derivation.leibniz_pow

theorem eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (adjoin R s) := fun x hx =>
  Algebra.adjoin_induction hx h (fun r => (D1.map_algebraMap r).trans (D2.map_algebraMap r).symm)
    (fun x y hx hy => by simp only [map_add, *]) fun x y hx hy => by simp only [leibniz, *]
#align derivation.eq_on_adjoin Derivation.eqOn_adjoin

/-- If adjoin of a set is the whole algebra, then any two derivations equal on this set are equal
on the whole algebra. -/
theorem ext_of_adjoin_eq_top (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2 s) : D1 = D2 :=
  ext fun a => eqOn_adjoin h <| hs.symm ▸ trivial
#align derivation.ext_of_adjoin_eq_top Derivation.ext_of_adjoin_eq_top

-- Data typeclasses
instance : Zero (Derivation R A M) :=
  ⟨{  toLinearMap := 0
      map_one_eq_zero' := rfl
      leibniz' := fun a b => by simp only [add_zero, LinearMap.zero_apply, smul_zero] }⟩

@[simp]
theorem coe_zero : ⇑(0 : Derivation R A M) = 0 :=
  rfl
#align derivation.coe_zero Derivation.coe_zero

@[simp]
theorem coe_zero_linearMap : ↑(0 : Derivation R A M) = (0 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_zero_linear_map Derivation.coe_zero_linearMap

theorem zero_apply (a : A) : (0 : Derivation R A M) a = 0 :=
  rfl
#align derivation.zero_apply Derivation.zero_apply

instance : Add (Derivation R A M) :=
  ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        simp only [leibniz, LinearMap.add_apply, coe_fn_coe, smul_add, add_add_add_comm] }⟩

@[simp]
theorem coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl
#align derivation.coe_add Derivation.coe_add

@[simp]
theorem coe_add_linearMap (D1 D2 : Derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_add_linear_map Derivation.coe_add_linearMap

theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl
#align derivation.add_apply Derivation.add_apply

instance : Inhabited (Derivation R A M) :=
  ⟨0⟩

section Scalar

variable {S T : Type _}

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulCommClass S A M]

variable [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulCommClass T A M]

instance (priority := 100) : SMul S (Derivation R A M) :=
  ⟨fun r D =>
    { toLinearMap := r • D
      map_one_eq_zero' := by rw [LinearMap.smul_apply, coe_fn_coe, D.map_one_eq_zero, smul_zero]
      leibniz' := fun a b => by
        simp only [LinearMap.smul_apply, coe_fn_coe, leibniz, smul_add, smul_comm r] }⟩

@[simp]
theorem coe_smul (r : S) (D : Derivation R A M) : ⇑(r • D) = r • D :=
  rfl
#align derivation.coe_smul Derivation.coe_smul

@[simp]
theorem coe_smul_linearMap (r : S) (D : Derivation R A M) : ↑(r • D) = (r • D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_smul_linear_map Derivation.coe_smul_linearMap

theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
  rfl
#align derivation.smul_apply Derivation.smul_apply

instance : AddCommMonoid (Derivation R A M) :=
  coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => rfl

/-- `coe_fn` as an `add_monoid_hom`. -/
def coeFnAddMonoidHom : Derivation R A M →+ A → M
    where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add
#align derivation.coe_fn_add_monoid_hom Derivation.coeFnAddMonoidHom

instance (priority := 100) : DistribMulAction S (Derivation R A M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance [DistribMulAction Sᵐᵒᵖ M] [IsCentralScalar S M] : IsCentralScalar S (Derivation R A M)
    where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

instance [SMul S T] [IsScalarTower S T M] : IsScalarTower S T (Derivation R A M) :=
  ⟨fun x y z => ext fun a => smul_assoc _ _ _⟩

instance [SMulCommClass S T M] : SMulCommClass S T (Derivation R A M) :=
  ⟨fun x y z => ext fun a => smul_comm _ _ _⟩

end Scalar

instance (priority := 100) {S : Type _} [Semiring S] [Module S M] [SMulCommClass R S M]
    [SMulCommClass S A M] : Module S (Derivation R A M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

section PushForward

variable {N : Type _} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A M]
  [IsScalarTower R A N]

variable (f : M →ₗ[A] N) (e : M ≃ₗ[A] N)

/-- We can push forward derivations using linear maps, i.e., the composition of a derivation with a
linear map is a derivation. Furthermore, this operation is linear on the spaces of derivations. -/
def LinearMap.compDer : Derivation R A M →ₗ[R] Derivation R A N
    where
  toFun D :=
    { toLinearMap := (f : M →ₗ[R] N).comp (D : A →ₗ[R] M)
      map_one_eq_zero' := by simp only [LinearMap.comp_apply, coe_fn_coe, map_one_eq_zero, map_zero]
      leibniz' := fun a b => by
        simp only [coe_fn_coe, LinearMap.comp_apply, LinearMap.map_add, leibniz,
          LinearMap.coe_restrictScalars, LinearMap.map_smul] }
  map_add' D₁ D₂ := by ext; exact LinearMap.map_add _ _ _
  map_smul' r D := by ext; exact LinearMap.map_smul _ _ _
#align linear_map.comp_der LinearMap.compDer

@[simp]
theorem coe_to_linearMap_comp : (f.compDer D : A →ₗ[R] N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_to_linear_map_comp Derivation.coe_to_linearMap_comp

@[simp]
theorem coe_comp : (f.compDer D : A → N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_comp Derivation.coe_comp

/-- The composition of a derivation with a linear map as a bilinear map -/
@[simps]
def llcomp : (M →ₗ[A] N) →ₗ[A] Derivation R A M →ₗ[R] Derivation R A N
    where
  toFun f := f.compDer
  map_add' f₁ f₂ := by ext; rfl
  map_smul' r D := by ext; rfl
#align derivation.llcomp Derivation.llcomp

/-- Pushing a derivation foward through a linear equivalence is an equivalence. -/
def LinearEquiv.compDer : Derivation R A M ≃ₗ[R] Derivation R A N :=
  { e.toLinearMap.compDer with
    invFun := e.symm.toLinearMap.compDer
    left_inv := fun D => by ext a; exact e.symm_apply_apply (D a)
    right_inv := fun D => by ext a; exact e.apply_symm_apply (D a) }
#align linear_equiv.comp_der LinearEquiv.compDer

end PushForward

section RestrictScalars

variable {S : Type _} [CommSemiring S]

variable [Algebra S A] [Module S M] [LinearMap.CompatibleSMul A M R S]

variable (R)

/-- If `A` is both an `R`-algebra and an `S`-algebra; `M` is both an `R`-module and an `S`-module,
then an `S`-derivation `A → M` is also an `R`-derivation if it is also `R`-linear. -/
protected def restrictScalars (d : Derivation S A M) : Derivation R A M
    where
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' := d.leibniz
  toLinearMap := d.toLinearMap.restrictScalars R
#align derivation.restrict_scalars Derivation.restrictScalars

end RestrictScalars

end

section Cancel

variable {R : Type _} [CommSemiring R] {A : Type _} [CommSemiring A] [Algebra R A] {M : Type _}
  [AddCancelCommMonoid M] [Module R M] [Module A M]

/-- Define `derivation R A M` from a linear map when `M` is cancellative by verifying the Leibniz
rule. -/
def mk' (D : A →ₗ[R] M) (h : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation R A M
    where
  toLinearMap := D
  map_one_eq_zero' := add_right_eq_self.1 <| by simpa only [one_smul, one_mul] using (h 1 1).symm
  leibniz' := h
#align derivation.mk' Derivation.mk'

@[simp]
theorem coe_mk' (D : A →ₗ[R] M) (h) : ⇑(mk' D h) = D :=
  rfl
#align derivation.coe_mk' Derivation.coe_mk'

@[simp]
theorem coe_mk'_linearMap (D : A →ₗ[R] M) (h) : (mk' D h : A →ₗ[R] M) = D :=
  rfl
#align derivation.coe_mk'_linear_map Derivation.coe_mk'_linearMap

end Cancel

section

variable {R : Type _} [CommRing R]

variable {A : Type _} [CommRing A] [Algebra R A]

section

variable {M : Type _} [AddCommGroup M] [Module A M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

protected theorem map_neg : D (-a) = -D a :=
  map_neg D a
#align derivation.map_neg Derivation.map_neg

protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b
#align derivation.map_sub Derivation.map_sub

@[simp]
theorem map_coe_int (n : ℤ) : D (n : A) = 0 := by
  rw [← zsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]
#align derivation.map_coe_int Derivation.map_coe_int

theorem leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -a ^ 2 • D b :=
  by
  rw [neg_smul]
  refine' eq_neg_of_add_eq_zero_left _
  calc
    D a + a ^ 2 • D b = a • b • D a + a • a • D b := by simp only [smul_smul, h, one_smul, sq]
    _ = a • D (a * b) := by rw [leibniz, smul_add, add_comm]
    _ = 0 := by rw [h, map_one_eq_zero, smul_zero]
    
#align derivation.leibniz_of_mul_eq_one Derivation.leibniz_of_mul_eq_one

theorem leibniz_invOf [Invertible a] : D (⅟ a) = -⅟ a ^ 2 • D a :=
  D.leibniz_of_mul_eq_one <| invOf_mul_self a
#align derivation.leibniz_inv_of Derivation.leibniz_invOf

theorem leibniz_inv {K : Type _} [Field K] [Module K M] [Algebra R K] (D : Derivation R K M)
    (a : K) : D a⁻¹ = -a⁻¹ ^ 2 • D a :=
  by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel ha)
#align derivation.leibniz_inv Derivation.leibniz_inv

instance : Neg (Derivation R A M) :=
  ⟨fun D =>
    mk' (-D) fun a b => by
      simp only [LinearMap.neg_apply, smul_neg, neg_add_rev, leibniz, coe_fn_coe, add_comm]⟩

@[simp]
theorem coe_neg (D : Derivation R A M) : ⇑(-D) = -D :=
  rfl
#align derivation.coe_neg Derivation.coe_neg

@[simp]
theorem coe_neg_linearMap (D : Derivation R A M) : ↑(-D) = (-D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_neg_linear_map Derivation.coe_neg_linearMap

theorem neg_apply : (-D) a = -D a :=
  rfl
#align derivation.neg_apply Derivation.neg_apply

instance : Sub (Derivation R A M) :=
  ⟨fun D1 D2 =>
    mk' (D1 - D2 : A →ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, leibniz, coe_fn_coe, smul_sub, add_sub_add_comm]⟩

@[simp]
theorem coe_sub (D1 D2 : Derivation R A M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl
#align derivation.coe_sub Derivation.coe_sub

@[simp]
theorem coe_sub_linearMap (D1 D2 : Derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_sub_linear_map Derivation.coe_sub_linearMap

theorem sub_apply : (D1 - D2) a = D1 a - D2 a :=
  rfl
#align derivation.sub_apply Derivation.sub_apply

instance : AddCommGroup (Derivation R A M) :=
  coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end

section LieStructures

/-! # Lie structures -/


variable (D : Derivation R A A) {D1 D2 : Derivation R A A} (r : R) (a b : A)

/-- The commutator of derivations is again a derivation. -/
instance : Bracket (Derivation R A A) (Derivation R A A) :=
  ⟨fun D1 D2 =>
    mk' ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ fun a b =>
      by
      simp only [Ring.lie_def, map_add, id.smul_eq_mul, LinearMap.mul_apply, leibniz, coe_fn_coe,
        LinearMap.sub_apply]
      ring⟩

@[simp]
theorem commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ :=
  rfl
#align derivation.commutator_coe_linear_map Derivation.commutator_coe_linear_map

theorem commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl
#align derivation.commutator_apply Derivation.commutator_apply

instance : LieRing (Derivation R A A)
    where
  add_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_add d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_self d := by ext a; simp only [commutator_apply, add_apply, map_add]; ring_nf
  leibniz_lie d e f := by ext a; simp only [commutator_apply, add_apply, sub_apply, map_sub]; ring

instance : LieAlgebra R (Derivation R A A) :=
  { Derivation.module with
    lie_smul := fun r d e => by ext a;
      simp only [commutator_apply, map_smul, smul_sub, smul_apply] }

end LieStructures

end

end Derivation

section ToSquareZero

universe u v w

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [CommRing B]

variable [Algebra R A] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥)

/-- If `f₁ f₂ : A →ₐ[R] B` are two lifts of the same `A →ₐ[R] B ⧸ I`,
  we may define a map `f₁ - f₂ : A →ₗ[R] I`. -/
def diffToIdealOfQuotientCompEq (f₁ f₂ : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) : A →ₗ[R] I :=
  LinearMap.codRestrict (I.restrictScalars _) (f₁.toLinearMap - f₂.toLinearMap)
    (by
      intro x
      change f₁ x - f₂ x ∈ I
      rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply, e]
      rfl)
#align diff_to_ideal_of_quotient_comp_eq diffToIdealOfQuotientCompEq

@[simp]
theorem diffToIdealOfQuotientCompEq_apply (f₁ f₂ : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) (x : A) :
    ((diffToIdealOfQuotientCompEq I f₁ f₂ e) x : B) = f₁ x - f₂ x :=
  rfl
#align diff_to_ideal_of_quotient_comp_eq_apply diffToIdealOfQuotientCompEq_apply

variable [Algebra A B] [IsScalarTower R A B]

include hI

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`, each lift `A →ₐ[R] B`
of the canonical map `A →ₐ[R] B ⧸ I` corresponds to a `R`-derivation from `A` to `I`. -/
def derivationToSquareZeroOfLift (f : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) : Derivation R A I :=
  by
  refine'
    {
      diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B)
        _ with
      map_one_eq_zero' := _
      leibniz' := _ }
  · rw [e]; ext; rfl
  · ext; change f 1 - algebraMap A B 1 = 0; rw [map_one, map_one, sub_self]
  · intro x y
    let F := diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) (by rw [e]; ext; rfl)
    have : (f x - algebraMap A B x) * (f y - algebraMap A B y) = 0 :=
      by
      rw [← Ideal.mem_bot, ← hI, pow_two]
      convert Ideal.mul_mem_mul (F x).2 (F y).2 using 1
    ext
    dsimp only [Submodule.coe_add, Submodule.coe_mk, LinearMap.coe_mk,
      diffToIdealOfQuotientCompEq_apply, Submodule.coe_smul_of_tower, IsScalarTower.coe_toAlgHom',
      LinearMap.toFun_eq_coe]
    simp only [map_mul, sub_mul, mul_sub, Algebra.smul_def] at this⊢
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at this
    rw [this]
    ring
#align derivation_to_square_zero_of_lift derivationToSquareZeroOfLift

theorem derivationToSquareZeroOfLift_apply (f : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) (x : A) :
    (derivationToSquareZeroOfLift I hI f e x : B) = f x - algebraMap A B x :=
  rfl
#align derivation_to_square_zero_of_lift_apply derivationToSquareZeroOfLift_apply

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`, each `R`-derivation
from `A` to `I` corresponds to a lift `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps (config := { attrs := [] })]
def liftOfDerivationToSquareZero (f : Derivation R A I) : A →ₐ[R] B :=
  {
    ((I.restrictScalars R).Subtype.comp f.toLinearMap + (IsScalarTower.toAlgHom R A B).toLinearMap :
      A →ₗ[R] B) with
    toFun := fun x => f x + algebraMap A B x
    map_one' := by rw [map_one, f.map_one_eq_zero, Submodule.coe_zero, zero_add]
    map_mul' := fun x y =>
      by
      have : (f x : B) * f y = 0 := by rw [← Ideal.mem_bot, ← hI, pow_two];
        convert Ideal.mul_mem_mul (f x).2 (f y).2 using 1
      simp only [map_mul, f.leibniz, add_mul, mul_add, Submodule.coe_add,
        Submodule.coe_smul_of_tower, Algebra.smul_def, this]
      ring
    commutes' := fun r => by
      simp only [Derivation.map_algebraMap, eq_self_iff_true, zero_add, Submodule.coe_zero, ←
        IsScalarTower.algebraMap_apply R A B r]
    map_zero' :=
      ((I.restrictScalars R).Subtype.comp f.toLinearMap +
          (IsScalarTower.toAlgHom R A B).toLinearMap).map_zero }
#align lift_of_derivation_to_square_zero liftOfDerivationToSquareZero

@[simp]
theorem liftOfDerivationToSquareZero_mk_apply (d : Derivation R A I) (x : A) :
    Ideal.Quotient.mk I (liftOfDerivationToSquareZero I hI d x) = algebraMap A (B ⧸ I) x :=
  by
  rw [liftOfDerivationToSquareZero_apply, map_add, ideal.quotient.eq_zero_iff_mem.mpr (d x).Prop,
    zero_add]
  rfl
#align lift_of_derivation_to_square_zero_mk_apply liftOfDerivationToSquareZero_mk_apply

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`,
there is a 1-1 correspondance between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps]
def derivationToSquareZeroEquivLift :
    Derivation R A I ≃
      { f : A →ₐ[R] B // (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I) } :=
  by
  refine'
    ⟨fun d => ⟨liftOfDerivationToSquareZero I hI d, _⟩, fun f =>
      (derivationToSquareZeroOfLift I hI f.1 f.2 : _), _, _⟩
  · ext x; exact liftOfDerivationToSquareZero_mk_apply I hI d x
  · intro d; ext x; exact add_sub_cancel (d x : B) (algebraMap A B x)
  · rintro ⟨f, hf⟩; ext x; exact sub_add_cancel (f x) (algebraMap A B x)
#align derivation_to_square_zero_equiv_lift derivationToSquareZeroEquivLift

end ToSquareZero

