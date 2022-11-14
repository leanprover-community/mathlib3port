/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import Mathbin.RingTheory.Adjoin.Basic
import Mathbin.Algebra.Lie.OfAssociative
import Mathbin.RingTheory.Ideal.Cotangent
import Mathbin.RingTheory.IsTensorProduct
import Mathbin.RingTheory.Ideal.Cotangent

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
- `kaehler_differential`: The module of kaehler differentials. For an `R`-algebra `S`, we provide
  the notation `Ω[S⁄R]` for `kaehler_differential R S`.
  Note that the slash is `\textfractionsolidus`.
- `kaehler_differential.D`: The derivation into the module of kaehler differentials.
- `kaehler_differential.span_range_derivation`: The image of `D` spans `Ω[S⁄R]` as an `S`-module.
- `kaehler_differential.linear_map_equiv_derivation`:
  The isomorphism `Hom_R(Ω[S⁄R], M) ≃ₗ[S] Der_R(S, M)`.
- `kaehler_differential.map`: Given a map between the arrows `R → A` and `S → B`, we have an
  `A`-linear map `Ω[A⁄R] → Ω[B⁄S]`.

## Future project

Generalize this into bimodules.
-/


open Algebra

open BigOperators

/-- `D : derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality. We also require that `D 1 = 0`. See `derivation.mk'` for a constructor that deduces this
assumption from the Leibniz rule when `M` is cancellative.

TODO: update this when bimodules are defined. -/
@[protect_proj]
structure Derivation (R : Type _) (A : Type _) [CommSemiring R] [CommSemiring A] [Algebra R A] (M : Type _)
  [AddCommMonoid M] [Module A M] [Module R M] extends A →ₗ[R] M where
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

instance : AddMonoidHomClass (Derivation R A M) A M where
  coe D := D.toFun
  coe_injective' D1 D2 h := by
    cases D1
    cases D2
    congr
    exact FunLike.coe_injective h
  map_add D := D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (Derivation R A M) fun _ => A → M :=
  ⟨fun D => D.toLinearMap.toFun⟩

-- Not a simp lemma because it can be proved via `coe_fn_coe` + `to_linear_map_eq_coe`
theorem to_fun_eq_coe : D.toFun = ⇑D :=
  rfl
#align derivation.to_fun_eq_coe Derivation.to_fun_eq_coe

instance hasCoeToLinearMap : Coe (Derivation R A M) (A →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩
#align derivation.has_coe_to_linear_map Derivation.hasCoeToLinearMap

@[simp]
theorem to_linear_map_eq_coe : D.toLinearMap = D :=
  rfl
#align derivation.to_linear_map_eq_coe Derivation.to_linear_map_eq_coe

@[simp]
theorem mk_coe (f : A →ₗ[R] M) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : Derivation R A M) : A → M) = f :=
  rfl
#align derivation.mk_coe Derivation.mk_coe

@[simp, norm_cast]
theorem coe_fn_coe (f : Derivation R A M) : ⇑(f : A →ₗ[R] M) = f :=
  rfl
#align derivation.coe_fn_coe Derivation.coe_fn_coe

theorem coe_injective : @Function.Injective (Derivation R A M) (A → M) coeFn :=
  FunLike.coe_injective
#align derivation.coe_injective Derivation.coe_injective

@[ext.1]
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
theorem map_smul_of_tower {S : Type _} [HasSmul S A] [HasSmul S M] [LinearMap.CompatibleSmul A M S R]
    (D : Derivation R A M) (r : S) (a : A) : D (r • a) = r • D a :=
  D.toLinearMap.map_smul_of_tower r a
#align derivation.map_smul_of_tower Derivation.map_smul_of_tower

@[simp]
theorem map_one_eq_zero : D 1 = 0 :=
  D.map_one_eq_zero'
#align derivation.map_one_eq_zero Derivation.map_one_eq_zero

@[simp]
theorem map_algebra_map : D (algebraMap R A r) = 0 := by
  rw [← mul_one r, RingHom.map_mul, RingHom.map_one, ← smul_def, map_smul, map_one_eq_zero, smul_zero]
#align derivation.map_algebra_map Derivation.map_algebra_map

@[simp]
theorem map_coe_nat (n : ℕ) : D (n : A) = 0 := by rw [← nsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]
#align derivation.map_coe_nat Derivation.map_coe_nat

@[simp]
theorem leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  induction' n with n ihn
  · rw [pow_zero, map_one_eq_zero, zero_smul]
    
  · rcases(zero_le n).eq_or_lt with (rfl | hpos)
    · rw [pow_one, one_smul, pow_zero, one_smul]
      
    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ, Nat.sub_add_cancel hpos]
      simp only [pow_succ, leibniz, ihn, smul_comm a n, smul_smul a, add_smul, this, Nat.succ_eq_add_one,
        Nat.add_succ_sub_one, add_zero, one_nsmul]
      
    
#align derivation.leibniz_pow Derivation.leibniz_pow

theorem eq_on_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (adjoin R s) := fun x hx =>
  Algebra.adjoinInduction hx h (fun r => (D1.map_algebra_map r).trans (D2.map_algebra_map r).symm)
    (fun x y hx hy => by simp only [map_add, *]) fun x y hx hy => by simp only [leibniz, *]
#align derivation.eq_on_adjoin Derivation.eq_on_adjoin

/-- If adjoin of a set is the whole algebra, then any two derivations equal on this set are equal
on the whole algebra. -/
theorem ext_of_adjoin_eq_top (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2 s) : D1 = D2 :=
  ext fun a => eq_on_adjoin h <| hs.symm ▸ trivial
#align derivation.ext_of_adjoin_eq_top Derivation.ext_of_adjoin_eq_top

-- Data typeclasses
instance : Zero (Derivation R A M) :=
  ⟨{ toLinearMap := 0, map_one_eq_zero' := rfl,
      leibniz' := fun a b => by simp only [add_zero, LinearMap.zero_apply, smul_zero] }⟩

@[simp]
theorem coe_zero : ⇑(0 : Derivation R A M) = 0 :=
  rfl
#align derivation.coe_zero Derivation.coe_zero

@[simp]
theorem coe_zero_linear_map : ↑(0 : Derivation R A M) = (0 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_zero_linear_map Derivation.coe_zero_linear_map

theorem zero_apply (a : A) : (0 : Derivation R A M) a = 0 :=
  rfl
#align derivation.zero_apply Derivation.zero_apply

instance : Add (Derivation R A M) :=
  ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2, map_one_eq_zero' := by simp,
      leibniz' := fun a b => by simp only [leibniz, LinearMap.add_apply, coe_fn_coe, smul_add, add_add_add_comm] }⟩

@[simp]
theorem coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl
#align derivation.coe_add Derivation.coe_add

@[simp]
theorem coe_add_linear_map (D1 D2 : Derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_add_linear_map Derivation.coe_add_linear_map

theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl
#align derivation.add_apply Derivation.add_apply

instance : Inhabited (Derivation R A M) :=
  ⟨0⟩

section Scalar

variable {S : Type _} [Monoid S] [DistribMulAction S M] [SmulCommClass R S M] [SmulCommClass S A M]

instance (priority := 100) : HasSmul S (Derivation R A M) :=
  ⟨fun r D =>
    { toLinearMap := r • D, map_one_eq_zero' := by rw [LinearMap.smul_apply, coe_fn_coe, D.map_one_eq_zero, smul_zero],
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coe_fn_coe, leibniz, smul_add, smul_comm r] }⟩

@[simp]
theorem coe_smul (r : S) (D : Derivation R A M) : ⇑(r • D) = r • D :=
  rfl
#align derivation.coe_smul Derivation.coe_smul

@[simp]
theorem coe_smul_linear_map (r : S) (D : Derivation R A M) : ↑(r • D) = (r • D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_smul_linear_map Derivation.coe_smul_linear_map

theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
  rfl
#align derivation.smul_apply Derivation.smul_apply

instance : AddCommMonoid (Derivation R A M) :=
  coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => rfl

/-- `coe_fn` as an `add_monoid_hom`. -/
def coeFnAddMonoidHom : Derivation R A M →+ A → M where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add
#align derivation.coe_fn_add_monoid_hom Derivation.coeFnAddMonoidHom

instance (priority := 100) : DistribMulAction S (Derivation R A M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance [DistribMulAction Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar S (Derivation R A M) where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

end Scalar

instance (priority := 100) {S : Type _} [Semiring S] [Module S M] [SmulCommClass R S M] [SmulCommClass S A M] :
    Module S (Derivation R A M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

instance [IsScalarTower R A M] : IsScalarTower R A (Derivation R A M) :=
  ⟨fun x y z => ext fun a => smul_assoc _ _ _⟩

section PushForward

variable {N : Type _} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A M] [IsScalarTower R A N]

variable (f : M →ₗ[A] N) (e : M ≃ₗ[A] N)

/-- We can push forward derivations using linear maps, i.e., the composition of a derivation with a
linear map is a derivation. Furthermore, this operation is linear on the spaces of derivations. -/
def _root_.linear_map.comp_der : Derivation R A M →ₗ[R] Derivation R A N where
  toFun D :=
    { toLinearMap := (f : M →ₗ[R] N).comp (D : A →ₗ[R] M),
      map_one_eq_zero' := by simp only [LinearMap.comp_apply, coe_fn_coe, map_one_eq_zero, map_zero],
      leibniz' := fun a b => by
        simp only [coe_fn_coe, LinearMap.comp_apply, LinearMap.map_add, leibniz, LinearMap.coe_coe_is_scalar_tower,
          LinearMap.map_smul] }
  map_add' D₁ D₂ := by
    ext
    exact LinearMap.map_add _ _ _
  map_smul' r D := by
    ext
    exact LinearMap.map_smul _ _ _
#align derivation._root_.linear_map.comp_der derivation._root_.linear_map.comp_der

@[simp]
theorem coe_to_linear_map_comp : (f.compDer D : A →ₗ[R] N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_to_linear_map_comp Derivation.coe_to_linear_map_comp

@[simp]
theorem coe_comp : (f.compDer D : A → N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_comp Derivation.coe_comp

/-- The composition of a derivation with a linear map as a bilinear map -/
@[simps]
def llcomp : (M →ₗ[A] N) →ₗ[A] Derivation R A M →ₗ[R] Derivation R A N where
  toFun f := f.compDer
  map_add' f₁ f₂ := by
    ext
    rfl
  map_smul' r D := by
    ext
    rfl
#align derivation.llcomp Derivation.llcomp

/-- Pushing a derivation foward through a linear equivalence is an equivalence. -/
def _root_.linear_equiv.comp_der : Derivation R A M ≃ₗ[R] Derivation R A N :=
  { e.toLinearMap.compDer with invFun := e.symm.toLinearMap.compDer,
    left_inv := fun D => by
      ext a
      exact e.symm_apply_apply (D a),
    right_inv := fun D => by
      ext a
      exact e.apply_symm_apply (D a) }
#align derivation._root_.linear_equiv.comp_der derivation._root_.linear_equiv.comp_der

end PushForward

section RestrictScalars

variable {S : Type _} [CommSemiring S]

variable [Algebra S A] [Module S M] [LinearMap.CompatibleSmul A M R S]

variable (R)

/-- If `A` is both an `R`-algebra and an `S`-algebra; `M` is both an `R`-module and an `S`-module,
then an `S`-derivation `A → M` is also an `R`-derivation if it is also `R`-linear. -/
protected def restrictScalars (d : Derivation S A M) : Derivation R A M where
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' := d.leibniz
  toLinearMap := d.toLinearMap.restrictScalars R
#align derivation.restrict_scalars Derivation.restrictScalars

end RestrictScalars

end

section Cancel

variable {R : Type _} [CommSemiring R] {A : Type _} [CommSemiring A] [Algebra R A] {M : Type _} [AddCancelCommMonoid M]
  [Module R M] [Module A M]

/-- Define `derivation R A M` from a linear map when `M` is cancellative by verifying the Leibniz
rule. -/
def mk' (D : A →ₗ[R] M) (h : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation R A M where
  toLinearMap := D
  map_one_eq_zero' := add_right_eq_self.1 <| by simpa only [one_smul, one_mul] using (h 1 1).symm
  leibniz' := h
#align derivation.mk' Derivation.mk'

@[simp]
theorem coe_mk' (D : A →ₗ[R] M) (h) : ⇑(mk' D h) = D :=
  rfl
#align derivation.coe_mk' Derivation.coe_mk'

@[simp]
theorem coe_mk'_linear_map (D : A →ₗ[R] M) (h) : (mk' D h : A →ₗ[R] M) = D :=
  rfl
#align derivation.coe_mk'_linear_map Derivation.coe_mk'_linear_map

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
theorem map_coe_int (n : ℤ) : D (n : A) = 0 := by rw [← zsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]
#align derivation.map_coe_int Derivation.map_coe_int

theorem leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -a ^ 2 • D b := by
  rw [neg_smul]
  refine' eq_neg_of_add_eq_zero_left _
  calc
    D a + a ^ 2 • D b = a • b • D a + a • a • D b := by simp only [smul_smul, h, one_smul, sq]
    _ = a • D (a * b) := by rw [leibniz, smul_add, add_comm]
    _ = 0 := by rw [h, map_one_eq_zero, smul_zero]
    
#align derivation.leibniz_of_mul_eq_one Derivation.leibniz_of_mul_eq_one

theorem leibniz_inv_of [Invertible a] : D (⅟ a) = -⅟ a ^ 2 • D a :=
  D.leibniz_of_mul_eq_one <| inv_of_mul_self a
#align derivation.leibniz_inv_of Derivation.leibniz_inv_of

theorem leibniz_inv {K : Type _} [Field K] [Module K M] [Algebra R K] (D : Derivation R K M) (a : K) :
    D a⁻¹ = -a⁻¹ ^ 2 • D a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
    
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel ha)
    
#align derivation.leibniz_inv Derivation.leibniz_inv

instance : Neg (Derivation R A M) :=
  ⟨fun D =>
    (mk' (-D)) fun a b => by simp only [LinearMap.neg_apply, smul_neg, neg_add_rev, leibniz, coe_fn_coe, add_comm]⟩

@[simp]
theorem coe_neg (D : Derivation R A M) : ⇑(-D) = -D :=
  rfl
#align derivation.coe_neg Derivation.coe_neg

@[simp]
theorem coe_neg_linear_map (D : Derivation R A M) : ↑(-D) = (-D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_neg_linear_map Derivation.coe_neg_linear_map

theorem neg_apply : (-D) a = -D a :=
  rfl
#align derivation.neg_apply Derivation.neg_apply

instance : Sub (Derivation R A M) :=
  ⟨fun D1 D2 =>
    (mk' (D1 - D2 : A →ₗ[R] M)) fun a b => by
      simp only [LinearMap.sub_apply, leibniz, coe_fn_coe, smul_sub, add_sub_add_comm]⟩

@[simp]
theorem coe_sub (D1 D2 : Derivation R A M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl
#align derivation.coe_sub Derivation.coe_sub

@[simp]
theorem coe_sub_linear_map (D1 D2 : Derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_sub_linear_map Derivation.coe_sub_linear_map

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
    (mk' ⁅(D1 : Module.EndCat R A), (D2 : Module.EndCat R A)⁆) fun a b => by
      simp only [Ring.lie_def, map_add, id.smul_eq_mul, LinearMap.mul_apply, leibniz, coe_fn_coe, LinearMap.sub_apply]
      ring⟩

@[simp]
theorem commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.EndCat R A), (D2 : Module.EndCat R A)⁆ :=
  rfl
#align derivation.commutator_coe_linear_map Derivation.commutator_coe_linear_map

theorem commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl
#align derivation.commutator_apply Derivation.commutator_apply

instance : LieRing (Derivation R A A) where
  add_lie d e f := by
    ext a
    simp only [commutator_apply, add_apply, map_add]
    ring
  lie_add d e f := by
    ext a
    simp only [commutator_apply, add_apply, map_add]
    ring
  lie_self d := by
    ext a
    simp only [commutator_apply, add_apply, map_add]
    ring_nf
  leibniz_lie d e f := by
    ext a
    simp only [commutator_apply, add_apply, sub_apply, map_sub]
    ring

instance : LieAlgebra R (Derivation R A A) :=
  { Derivation.module with
    lie_smul := fun r d e => by
      ext a
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
theorem diff_to_ideal_of_quotient_comp_eq_apply (f₁ f₂ : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) (x : A) :
    ((diffToIdealOfQuotientCompEq I f₁ f₂ e) x : B) = f₁ x - f₂ x :=
  rfl
#align diff_to_ideal_of_quotient_comp_eq_apply diff_to_ideal_of_quotient_comp_eq_apply

variable [Algebra A B] [IsScalarTower R A B]

include hI

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`, each lift `A →ₐ[R] B`
of the canonical map `A →ₐ[R] B ⧸ I` corresponds to a `R`-derivation from `A` to `I`. -/
def derivationToSquareZeroOfLift (f : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) : Derivation R A I := by
  refine' { diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) _ with map_one_eq_zero' := _, leibniz' := _ }
  · rw [e]
    ext
    rfl
    
  · ext
    change f 1 - algebraMap A B 1 = 0
    rw [map_one, map_one, sub_self]
    
  · intro x y
    let F :=
      diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B)
        (by
          rw [e]
          ext
          rfl)
    have : (f x - algebraMap A B x) * (f y - algebraMap A B y) = 0 := by
      rw [← Ideal.mem_bot, ← hI, pow_two]
      convert Ideal.mul_mem_mul (F x).2 (F y).2 using 1
    ext
    dsimp only [Submodule.coe_add, Submodule.coe_mk, LinearMap.coe_mk, diff_to_ideal_of_quotient_comp_eq_apply,
      Submodule.coe_smul_of_tower, IsScalarTower.coe_to_alg_hom', LinearMap.to_fun_eq_coe]
    simp only [map_mul, sub_mul, mul_sub, Algebra.smul_def] at this⊢
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at this
    rw [this]
    ring
    
#align derivation_to_square_zero_of_lift derivationToSquareZeroOfLift

theorem derivation_to_square_zero_of_lift_apply (f : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) (x : A) :
    (derivationToSquareZeroOfLift I hI f e x : B) = f x - algebraMap A B x :=
  rfl
#align derivation_to_square_zero_of_lift_apply derivation_to_square_zero_of_lift_apply

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`, each `R`-derivation
from `A` to `I` corresponds to a lift `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
def liftOfDerivationToSquareZero (f : Derivation R A I) : A →ₐ[R] B :=
  { (I.restrictScalars R).Subtype.comp f.toLinearMap + (IsScalarTower.toAlgHom R A B).toLinearMap with
    map_one' := show (f 1 : B) + algebraMap A B 1 = 1 by rw [map_one, f.map_one_eq_zero, Submodule.coe_zero, zero_add],
    map_mul' := fun x y => by
      have : (f x : B) * f y = 0 := by
        rw [← Ideal.mem_bot, ← hI, pow_two]
        convert Ideal.mul_mem_mul (f x).2 (f y).2 using 1
      dsimp
      simp only [map_mul, f.leibniz, add_mul, mul_add, Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def,
        this]
      ring,
    commutes' := fun r => by
      dsimp
      simp [← IsScalarTower.algebra_map_apply R A B r],
    map_zero' :=
      ((I.restrictScalars R).Subtype.comp f.toLinearMap + (IsScalarTower.toAlgHom R A B).toLinearMap).map_zero }
#align lift_of_derivation_to_square_zero liftOfDerivationToSquareZero

theorem lift_of_derivation_to_square_zero_apply (f : Derivation R A I) (x : A) :
    liftOfDerivationToSquareZero I hI f x = f x + algebraMap A B x :=
  rfl
#align lift_of_derivation_to_square_zero_apply lift_of_derivation_to_square_zero_apply

@[simp]
theorem lift_of_derivation_to_square_zero_mk_apply (d : Derivation R A I) (x : A) :
    Ideal.Quotient.mk I (liftOfDerivationToSquareZero I hI d x) = algebraMap A (B ⧸ I) x := by
  rw [lift_of_derivation_to_square_zero_apply, map_add, ideal.quotient.eq_zero_iff_mem.mpr (d x).Prop, zero_add]
  rfl
#align lift_of_derivation_to_square_zero_mk_apply lift_of_derivation_to_square_zero_mk_apply

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`,
there is a 1-1 correspondance between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps]
def derivationToSquareZeroEquivLift :
    Derivation R A I ≃ { f : A →ₐ[R] B // (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I) } := by
  refine'
    ⟨fun d => ⟨liftOfDerivationToSquareZero I hI d, _⟩, fun f => (derivationToSquareZeroOfLift I hI f.1 f.2 : _), _, _⟩
  · ext x
    exact lift_of_derivation_to_square_zero_mk_apply I hI d x
    
  · intro d
    ext x
    exact add_sub_cancel (d x : B) (algebraMap A B x)
    
  · rintro ⟨f, hf⟩
    ext x
    exact sub_add_cancel (f x) (algebraMap A B x)
    
#align derivation_to_square_zero_equiv_lift derivationToSquareZeroEquivLift

end ToSquareZero

section KaehlerDifferential

open TensorProduct

variable (R S : Type _) [CommRing R] [CommRing S] [Algebra R S]

/-- The kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`. -/
abbrev KaehlerDifferential.ideal : Ideal (S ⊗[R] S) :=
  RingHom.ker (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S)
#align kaehler_differential.ideal KaehlerDifferential.ideal

variable {S}

theorem KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (a : S) :
    (1 : S) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : S) ∈ KaehlerDifferential.ideal R S := by simp [RingHom.mem_ker]
#align kaehler_differential.one_smul_sub_smul_one_mem_ideal KaehlerDifferential.one_smul_sub_smul_one_mem_ideal

variable {R}

variable {M : Type _} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- For a `R`-derivation `S → M`, this is the map `S ⊗[R] S →ₗ[S] M` sending `s ⊗ₜ t ↦ s • D t`. -/
def Derivation.tensorProductTo (D : Derivation R S M) : S ⊗[R] S →ₗ[S] M :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.lsmul S (S →ₗ[R] M)).flip D.toLinearMap)
#align derivation.tensor_product_to Derivation.tensorProductTo

theorem Derivation.tensor_product_to_tmul (D : Derivation R S M) (s t : S) : D.tensorProductTo (s ⊗ₜ t) = s • D t :=
  TensorProduct.lift.tmul s t
#align derivation.tensor_product_to_tmul Derivation.tensor_product_to_tmul

theorem Derivation.tensor_product_to_mul (D : Derivation R S M) (x y : S ⊗[R] S) :
    D.tensorProductTo (x * y) =
      TensorProduct.lmul' R x • D.tensorProductTo y + TensorProduct.lmul' R y • D.tensorProductTo x :=
  by
  apply TensorProduct.induction_on x
  · rw [zero_mul, map_zero, map_zero, zero_smul, smul_zero, add_zero]
    
  swap
  · rintro
    simp only [add_mul, map_add, add_smul, *, smul_add]
    rw [add_add_add_comm]
    
  intro x₁ x₂
  apply TensorProduct.induction_on y
  · rw [mul_zero, map_zero, map_zero, zero_smul, smul_zero, add_zero]
    
  swap
  · rintro
    simp only [mul_add, map_add, add_smul, *, smul_add]
    rw [add_add_add_comm]
    
  intro x y
  simp only [tensor_product.tmul_mul_tmul, Derivation.tensorProductTo, TensorProduct.AlgebraTensorModule.lift_apply,
    TensorProduct.lift.tmul', tensor_product.lmul'_apply_tmul]
  dsimp
  rw [D.leibniz]
  simp only [smul_smul, smul_add, mul_comm (x * y) x₁, mul_right_comm x₁ x₂, ← mul_assoc]
#align derivation.tensor_product_to_mul Derivation.tensor_product_to_mul

variable (R S)

/-- The kernel of `S ⊗[R] S →ₐ[R] S` is generated by `1 ⊗ s - s ⊗ 1` as a `S`-module. -/
theorem KaehlerDifferential.submodule_span_range_eq_ideal :
    Submodule.span S (Set.range fun s : S => (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
      (KaehlerDifferential.ideal R S).restrictScalars S :=
  by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal _ _
    
  · rintro x (hx : _ = _)
    have : x - tensor_product.lmul' R x ⊗ₜ[R] (1 : S) = x := by rw [hx, TensorProduct.zero_tmul, sub_zero]
    rw [← this]
    clear this hx
    apply TensorProduct.induction_on x <;> clear x
    · rw [map_zero, TensorProduct.zero_tmul, sub_zero]
      exact zero_mem _
      
    · intro x y
      convert_to x • (1 ⊗ₜ y - y ⊗ₜ 1) ∈ _
      · rw [tensor_product.lmul'_apply_tmul, smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
          smul_eq_mul, mul_one]
        
      · refine' Submodule.smul_mem _ x _
        apply Submodule.subset_span
        exact Set.mem_range_self y
        
      
    · intro x y hx hy
      rw [map_add, TensorProduct.add_tmul, ← sub_add_sub_comm]
      exact add_mem hx hy
      
    
#align kaehler_differential.submodule_span_range_eq_ideal KaehlerDifferential.submodule_span_range_eq_ideal

theorem KaehlerDifferential.span_range_eq_ideal :
    Ideal.span (Set.range fun s : S => (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) = KaehlerDifferential.ideal R S := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal _ _
    
  · change (KaehlerDifferential.ideal R S).restrictScalars S ≤ (Ideal.span _).restrictScalars S
    rw [← KaehlerDifferential.submodule_span_range_eq_ideal, Ideal.span]
    conv_rhs => rw [← Submodule.span_span_of_tower S]
    exact Submodule.subset_span
    
#align kaehler_differential.span_range_eq_ideal KaehlerDifferential.span_range_eq_ideal

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] tensor_product(S, R, S) -/
/-- The module of Kähler differentials (Kahler differentials, Kaehler differentials).
This is implemented as `I / I ^ 2` with `I` the kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.
To view elements as a linear combination of the form `s • D s'`, use
`kaehler_differential.tensor_product_to_surjective` and `derivation.tensor_product_to_tmul`.

We also provide the notation `Ω[S⁄R]` for `kaehler_differential R S`.
Note that the slash is `\textfractionsolidus`.
-/
def KaehlerDifferential : Type _ :=
  (KaehlerDifferential.ideal R S).Cotangent deriving AddCommGroup,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] tensor_product(S, R, S)»
#align kaehler_differential KaehlerDifferential

-- mathport name: «exprΩ[ ⁄ ]»
notation:100 "Ω[" S "⁄" R "]" => KaehlerDifferential R S

instance : Nonempty (Ω[S⁄R]) :=
  ⟨0⟩

instance KaehlerDifferential.module' {R' : Type _} [CommRing R'] [Algebra R' S] : Module R' (Ω[S⁄R]) :=
  (Module.compHom (KaehlerDifferential.ideal R S).Cotangent (algebraMap R' S) : _)
#align kaehler_differential.module' KaehlerDifferential.module'

instance : IsScalarTower S (S ⊗[R] S) (Ω[S⁄R]) :=
  Ideal.Cotangent.is_scalar_tower _

instance KaehlerDifferential.is_scalar_tower_of_tower {R₁ R₂ : Type _} [CommRing R₁] [CommRing R₂] [Algebra R₁ S]
    [Algebra R₂ S] [Algebra R₁ R₂] [IsScalarTower R₁ R₂ S] : IsScalarTower R₁ R₂ (Ω[S⁄R]) := by
  convert RestrictScalars.is_scalar_tower R₁ R₂ (Ω[S⁄R]) using 1
  ext (x m)
  show algebraMap R₁ S x • m = algebraMap R₂ S (algebraMap R₁ R₂ x) • m
  rw [← IsScalarTower.algebra_map_apply]
#align kaehler_differential.is_scalar_tower_of_tower KaehlerDifferential.is_scalar_tower_of_tower

instance KaehlerDifferential.is_scalar_tower' : IsScalarTower R (S ⊗[R] S) (Ω[S⁄R]) := by
  convert RestrictScalars.is_scalar_tower R (S ⊗[R] S) (Ω[S⁄R]) using 1
  ext (x m)
  show algebraMap R S x • m = algebraMap R (S ⊗[R] S) x • m
  simp_rw [IsScalarTower.algebra_map_apply R S (S ⊗[R] S), IsScalarTower.algebra_map_smul]
#align kaehler_differential.is_scalar_tower' KaehlerDifferential.is_scalar_tower'

/-- The quotient map `I → Ω[S⁄R]` with `I` being the kernel of `S ⊗[R] S → S`. -/
def KaehlerDifferential.fromIdeal : KaehlerDifferential.ideal R S →ₗ[S ⊗[R] S] Ω[S⁄R] :=
  (KaehlerDifferential.ideal R S).toCotangent
#align kaehler_differential.from_ideal KaehlerDifferential.fromIdeal

/-- (Implementation) The underlying linear map of the derivation into `Ω[S⁄R]`. -/
def KaehlerDifferential.dLinearMap : S →ₗ[R] Ω[S⁄R] :=
  ((KaehlerDifferential.fromIdeal R S).restrictScalars R).comp
    ((TensorProduct.includeRight.toLinearMap - TensorProduct.includeLeft.toLinearMap : S →ₗ[R] S ⊗[R] S).codRestrict
      ((KaehlerDifferential.ideal R S).restrictScalars R) (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R) :
      _ →ₗ[R] _)
#align kaehler_differential.D_linear_map KaehlerDifferential.dLinearMap

theorem KaehlerDifferential.D_linear_map_apply (s : S) :
    KaehlerDifferential.dLinearMap R S s =
      (KaehlerDifferential.ideal R S).toCotangent
        ⟨1 ⊗ₜ s - s ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s⟩ :=
  rfl
#align kaehler_differential.D_linear_map_apply KaehlerDifferential.D_linear_map_apply

/-- The universal derivation into `Ω[S⁄R]`. -/
def KaehlerDifferential.d : Derivation R S (Ω[S⁄R]) :=
  { KaehlerDifferential.dLinearMap R S with
    map_one_eq_zero' := by
      dsimp [KaehlerDifferential.D_linear_map_apply]
      rw [Ideal.to_cotangent_eq_zero, Subtype.coe_mk, sub_self]
      exact zero_mem _,
    leibniz' := fun a b => by
      dsimp [KaehlerDifferential.D_linear_map_apply]
      rw [← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower, ← map_add, Ideal.to_cotangent_eq, pow_two]
      convert
        Submodule.mul_mem_mul (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R a : _)
          (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b : _) using
        1
      simp only [AddSubgroupClass.coe_sub, Submodule.coe_add, Submodule.coe_mk, tensor_product.tmul_mul_tmul, mul_sub,
        sub_mul, mul_comm b, Submodule.coe_smul_of_tower, smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      ring_nf }
#align kaehler_differential.D KaehlerDifferential.d

theorem KaehlerDifferential.D_apply (s : S) :
    KaehlerDifferential.d R S s =
      (KaehlerDifferential.ideal R S).toCotangent
        ⟨1 ⊗ₜ s - s ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s⟩ :=
  rfl
#align kaehler_differential.D_apply KaehlerDifferential.D_apply

theorem KaehlerDifferential.span_range_derivation : Submodule.span S (Set.range <| KaehlerDifferential.d R S) = ⊤ := by
  rw [_root_.eq_top_iff]
  rintro x -
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.to_cotangent_surjective _ x
  have : x ∈ (KaehlerDifferential.ideal R S).restrictScalars S := hx
  rw [← KaehlerDifferential.submodule_span_range_eq_ideal] at this
  suffices
    ∃ hx,
      (KaehlerDifferential.ideal R S).toCotangent ⟨x, hx⟩ ∈ Submodule.span S (Set.range <| KaehlerDifferential.d R S)
    by exact this.some_spec
  apply Submodule.span_induction this
  · rintro _ ⟨x, rfl⟩
    refine' ⟨KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R x, _⟩
    apply Submodule.subset_span
    exact ⟨x, KaehlerDifferential.D_linear_map_apply R S x⟩
    
  · exact ⟨zero_mem _, zero_mem _⟩
    
  · rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨add_mem hx₁ hy₁, add_mem hx₂ hy₂⟩
    
  · rintro r x ⟨hx₁, hx₂⟩
    exact ⟨((KaehlerDifferential.ideal R S).restrictScalars S).smul_mem r hx₁, Submodule.smul_mem _ r hx₂⟩
    
#align kaehler_differential.span_range_derivation KaehlerDifferential.span_range_derivation

variable {R S}

/-- The linear map from `Ω[S⁄R]`, associated with a derivation. -/
def Derivation.liftKaehlerDifferential (D : Derivation R S M) : Ω[S⁄R] →ₗ[S] M := by
  refine'
    ((KaehlerDifferential.ideal R S • ⊤ : Submodule (S ⊗[R] S) (KaehlerDifferential.ideal R S)).restrictScalars S).liftq
      _ _
  · exact D.tensor_product_to.comp ((KaehlerDifferential.ideal R S).Subtype.restrictScalars S)
    
  · intro x hx
    change _ = _
    apply Submodule.smul_induction_on hx <;> clear hx x
    · rintro x (hx : _ = _) ⟨y, hy : _ = _⟩ -
      dsimp
      rw [Derivation.tensor_product_to_mul, hx, hy, zero_smul, zero_smul, zero_add]
      
    · intro x y ex ey
      rw [map_add, ex, ey, zero_add]
      
    
#align derivation.lift_kaehler_differential Derivation.liftKaehlerDifferential

theorem Derivation.lift_kaehler_differential_apply (D : Derivation R S M) (x) :
    D.liftKaehlerDifferential ((KaehlerDifferential.ideal R S).toCotangent x) = D.tensorProductTo x :=
  rfl
#align derivation.lift_kaehler_differential_apply Derivation.lift_kaehler_differential_apply

theorem Derivation.lift_kaehler_differential_comp (D : Derivation R S M) :
    D.liftKaehlerDifferential.compDer (KaehlerDifferential.d R S) = D := by
  ext a
  dsimp [KaehlerDifferential.D_apply]
  refine' (D.lift_kaehler_differential_apply _).trans _
  rw [Subtype.coe_mk, map_sub, Derivation.tensor_product_to_tmul, Derivation.tensor_product_to_tmul, one_smul,
    D.map_one_eq_zero, smul_zero, sub_zero]
#align derivation.lift_kaehler_differential_comp Derivation.lift_kaehler_differential_comp

@[ext.1]
theorem Derivation.lift_kaehler_differential_unique (f f' : Ω[S⁄R] →ₗ[S] M)
    (hf : f.compDer (KaehlerDifferential.d R S) = f'.compDer (KaehlerDifferential.d R S)) : f = f' := by
  apply LinearMap.ext
  intro x
  have : x ∈ Submodule.span S (Set.range <| KaehlerDifferential.d R S) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  apply Submodule.span_induction this
  · rintro _ ⟨x, rfl⟩
    exact congr_arg (fun D : Derivation R S M => D x) hf
    
  · rw [map_zero, map_zero]
    
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
    
  · intro a x e
    rw [map_smul, map_smul, e]
    
#align derivation.lift_kaehler_differential_unique Derivation.lift_kaehler_differential_unique

variable (R S)

theorem Derivation.lift_kaehler_differential_D : (KaehlerDifferential.d R S).liftKaehlerDifferential = LinearMap.id :=
  Derivation.lift_kaehler_differential_unique _ _ (KaehlerDifferential.d R S).lift_kaehler_differential_comp
#align derivation.lift_kaehler_differential_D Derivation.lift_kaehler_differential_D

variable {R S}

theorem KaehlerDifferential.D_tensor_product_to (x : KaehlerDifferential.ideal R S) :
    (KaehlerDifferential.d R S).tensorProductTo x = (KaehlerDifferential.ideal R S).toCotangent x := by
  rw [← Derivation.lift_kaehler_differential_apply, Derivation.lift_kaehler_differential_D]
  rfl
#align kaehler_differential.D_tensor_product_to KaehlerDifferential.D_tensor_product_to

variable (R S)

theorem KaehlerDifferential.tensor_product_to_surjective :
    Function.Surjective (KaehlerDifferential.d R S).tensorProductTo := by
  intro x
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.ideal R S).to_cotangent_surjective x
  exact ⟨x, KaehlerDifferential.D_tensor_product_to x⟩
#align kaehler_differential.tensor_product_to_surjective KaehlerDifferential.tensor_product_to_surjective

/-- The `S`-linear maps from `Ω[S⁄R]` to `M` are (`S`-linearly) equivalent to `R`-derivations
from `S` to `M`.  -/
def KaehlerDifferential.linearMapEquivDerivation : (Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M :=
  { Derivation.llcomp.flip <| KaehlerDifferential.d R S with invFun := Derivation.liftKaehlerDifferential,
    left_inv := fun f => Derivation.lift_kaehler_differential_unique _ _ (Derivation.lift_kaehler_differential_comp _),
    right_inv := Derivation.lift_kaehler_differential_comp }
#align kaehler_differential.linear_map_equiv_derivation KaehlerDifferential.linearMapEquivDerivation

/-- The quotient ring of `S ⊗ S ⧸ J ^ 2` by `Ω[S⁄R]` is isomorphic to `S`. -/
def KaehlerDifferential.quotientCotangentIdealRingEquiv :
    (S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) ⧸ (KaehlerDifferential.ideal R S).cotangentIdeal ≃+* S := by
  have :
    Function.RightInverse tensor_product.include_left (↑(tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S) : S ⊗[R] S →+* S) :=
    by
    intro x
    rw [AlgHom.coe_to_ring_hom, ← AlgHom.comp_apply, tensor_product.lmul'_comp_include_left]
    rfl
  refine' (Ideal.quotCotangent _).trans _
  refine' (Ideal.quotEquivOfEq _).trans (RingHom.quotientKerEquivOfRightInverse this)
  ext
  rfl
#align kaehler_differential.quotient_cotangent_ideal_ring_equiv KaehlerDifferential.quotientCotangentIdealRingEquiv

/-- The quotient ring of `S ⊗ S ⧸ J ^ 2` by `Ω[S⁄R]` is isomorphic to `S` as an `S`-algebra. -/
def KaehlerDifferential.quotientCotangentIdeal :
    ((S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) ⧸ (KaehlerDifferential.ideal R S).cotangentIdeal) ≃ₐ[S] S :=
  { KaehlerDifferential.quotientCotangentIdealRingEquiv R S with
    commutes' := (KaehlerDifferential.quotientCotangentIdealRingEquiv R S).apply_symm_apply }
#align kaehler_differential.quotient_cotangent_ideal KaehlerDifferential.quotientCotangentIdeal

theorem KaehlerDifferential.End_equiv_aux (f : S →ₐ[R] S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) :
    (Ideal.Quotient.mkₐ R (KaehlerDifferential.ideal R S).cotangentIdeal).comp f = IsScalarTower.toAlgHom R S _ ↔
      (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S :=
  by
  rw [AlgHom.ext_iff, AlgHom.ext_iff]
  apply forall_congr'
  intro x
  have e₁ :
    (tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift (f x) =
      KaehlerDifferential.quotientCotangentIdealRingEquiv R S
        (Ideal.Quotient.mk (KaehlerDifferential.ideal R S).cotangentIdeal <| f x) :=
    by
    generalize f x = y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rfl
  have e₂ : x = KaehlerDifferential.quotientCotangentIdealRingEquiv R S (IsScalarTower.toAlgHom R S _ x) :=
    ((tensor_product.lmul'_apply_tmul x 1).trans (mul_one x)).symm
  constructor
  · intro e
    exact
      (e₁.trans
            (@RingEquiv.congr_arg _ _ _ _ _ _ (KaehlerDifferential.quotientCotangentIdealRingEquiv R S) _ _ e)).trans
        e₂.symm
    
  · intro e
    apply (KaehlerDifferential.quotientCotangentIdealRingEquiv R S).Injective
    exact e₁.symm.trans (e.trans e₂)
    
#align kaehler_differential.End_equiv_aux KaehlerDifferential.End_equiv_aux

-- This has type
-- `derivation R S Ω[ S / R ] ≃ₗ[R] derivation R S (kaehler_differential.ideal R S).cotangent_ideal`
-- But lean times-out if this is given explicitly.
/-- Derivations into `Ω[S⁄R]` is equivalent to derivations
into `(kaehler_differential.ideal R S).cotangent_ideal` -/
noncomputable def KaehlerDifferential.endEquivDerivation' :=
  @LinearEquiv.compDer R _ _ _ _ (Ω[S⁄R]) _ _ _ _ _ _ _ _ _
    ((KaehlerDifferential.ideal R S).cotangentEquivIdeal.restrictScalars S)
#align kaehler_differential.End_equiv_derivation' KaehlerDifferential.endEquivDerivation'

/-- (Implementation) An `equiv` version of `kaehler_differential.End_equiv_aux`.
Used in `kaehler_differential.End_equiv`. -/
def KaehlerDifferential.endEquivAuxEquiv :
    { f //
        (Ideal.Quotient.mkₐ R (KaehlerDifferential.ideal R S).cotangentIdeal).comp f = IsScalarTower.toAlgHom R S _ } ≃
      { f // (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S } :=
  (Equiv.refl _).subtypeEquiv (KaehlerDifferential.End_equiv_aux R S)
#align kaehler_differential.End_equiv_aux_equiv KaehlerDifferential.endEquivAuxEquiv

/-- The endomorphisms of `Ω[S⁄R]` corresponds to sections of the surjection `S ⊗[R] S ⧸ J ^ 2 →ₐ[R] S`,
with `J` being the kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.
-/
noncomputable def KaehlerDifferential.endEquiv :
    Module.EndCat S (Ω[S⁄R]) ≃
      { f // (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S } :=
  (KaehlerDifferential.linearMapEquivDerivation R S).toEquiv.trans <|
    (KaehlerDifferential.endEquivDerivation' R S).toEquiv.trans <|
      (derivationToSquareZeroEquivLift (KaehlerDifferential.ideal R S).cotangentIdeal
            (KaehlerDifferential.ideal R S).cotangent_ideal_square).trans <|
        KaehlerDifferential.endEquivAuxEquiv R S
#align kaehler_differential.End_equiv KaehlerDifferential.endEquiv

section ExactSequence

/- We have the commutative diagram
A --→ B
↑     ↑
|     |
R --→ S -/
variable (A B : Type _) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

variable {R B}

/-- For a tower `R → A → B` and an `R`-derivation `B → M`, we may compose with `A → B` to obtain an
`R`-derivation `A → M`. -/
def Derivation.compAlgebraMap [Module A M] [Module B M] [IsScalarTower A B M] (d : Derivation R B M) :
    Derivation R A M where
  map_one_eq_zero' := by simp
  leibniz' a b := by simp
  toLinearMap := d.toLinearMap.comp (IsScalarTower.toAlgHom R A B).toLinearMap
#align derivation.comp_algebra_map Derivation.compAlgebraMap

variable (R B)

/-- The map `Ω[A⁄R] →ₗ[A] Ω[B⁄R]` given a square
A --→ B
↑     ↑
|     |
R --→ S -/
def KaehlerDifferential.map : Ω[A⁄R] →ₗ[A] Ω[B⁄S] :=
  Derivation.liftKaehlerDifferential (((KaehlerDifferential.d S B).restrictScalars R).comp_algebra_map A)
#align kaehler_differential.map KaehlerDifferential.map

theorem KaehlerDifferential.map_comp_der :
    (KaehlerDifferential.map R S A B).compDer (KaehlerDifferential.d R A) =
      ((KaehlerDifferential.d S B).restrictScalars R).comp_algebra_map A :=
  Derivation.lift_kaehler_differential_comp _
#align kaehler_differential.map_comp_der KaehlerDifferential.map_comp_der

theorem KaehlerDifferential.map_D (x : A) :
    KaehlerDifferential.map R S A B (KaehlerDifferential.d R A x) = KaehlerDifferential.d S B (algebraMap A B x) :=
  Derivation.congr_fun (KaehlerDifferential.map_comp_der R S A B) x
#align kaehler_differential.map_D KaehlerDifferential.map_D

open IsScalarTower (toAlgHom)

theorem KaehlerDifferential.map_surjective_of_surjective (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.map R S A B) := by
  rw [← LinearMap.range_eq_top, _root_.eq_top_iff, ← @Submodule.restrict_scalars_top B A, ←
    KaehlerDifferential.span_range_derivation, ← Submodule.span_eq_restrict_scalars _ _ _ _ h, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := h x
  rw [← KaehlerDifferential.map_D R S A B]
  exact ⟨_, rfl⟩
#align kaehler_differential.map_surjective_of_surjective KaehlerDifferential.map_surjective_of_surjective

/-- The lift of the map `Ω[A⁄R] →ₗ[A] Ω[B⁄R]` to the base change along `A → B`.
This is the first map in the exact sequence `B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0`. -/
noncomputable def KaehlerDifferential.mapBaseChange : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R] :=
  (TensorProduct.isBaseChange A (Ω[A⁄R]) B).lift (KaehlerDifferential.map R R A B)
#align kaehler_differential.map_base_change KaehlerDifferential.mapBaseChange

@[simp]
theorem KaehlerDifferential.map_base_change_tmul (x : B) (y : Ω[A⁄R]) :
    KaehlerDifferential.mapBaseChange R A B (x ⊗ₜ y) = x • KaehlerDifferential.map R R A B y := by
  conv_lhs => rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul', LinearMap.map_smul]
  congr 1
  exact IsBaseChange.lift_eq _ _ _
#align kaehler_differential.map_base_change_tmul KaehlerDifferential.map_base_change_tmul

end ExactSequence

end KaehlerDifferential

