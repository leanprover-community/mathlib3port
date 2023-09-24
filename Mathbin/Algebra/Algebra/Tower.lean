/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/
import Algebra.Algebra.Equiv
import LinearAlgebra.Span

#align_import algebra.algebra.tower from "leanprover-community/mathlib"@"832f7b9162039c28b9361289c8681f155cae758f"

/-!
# Towers of algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove basic facts about towers of algebra.

An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `to_alg_hom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/


open scoped Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {A}

/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `R`-module `M`.

This is a stronger version of `distrib_mul_action.to_linear_map`, and could also have been
called `algebra.to_module_End`. -/
def lsmul : A →ₐ[R] Module.End R M
    where
  toFun := DistribMulAction.toLinearMap R M
  map_one' := LinearMap.ext fun _ => one_smul A _
  map_mul' a b := LinearMap.ext <| smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' a b := LinearMap.ext fun _ => add_smul _ _ _
  commutes' r := LinearMap.ext <| algebraMap_smul A r
#align algebra.lsmul Algebra.lsmulₓ

#print Algebra.lsmul_coe /-
@[simp]
theorem lsmul_coe (a : A) : (lsmul R M a : M → M) = (· • ·) a :=
  rfl
#align algebra.lsmul_coe Algebra.lsmul_coe
-/

end Algebra

namespace IsScalarTower

section Module

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [SMul R M] [MulAction A M] [IsScalarTower R A M]

variable {R} (A) {M}

#print IsScalarTower.algebraMap_smul /-
theorem algebraMap_smul (r : R) (x : M) : algebraMap R A r • x = r • x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
#align is_scalar_tower.algebra_map_smul IsScalarTower.algebraMap_smul
-/

end Module

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable {R S A}

#print IsScalarTower.of_algebraMap_eq /-
theorem of_algebraMap_eq [Algebra R A]
    (h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S A :=
  ⟨fun x y z => by simp_rw [Algebra.smul_def, RingHom.map_mul, mul_assoc, h]⟩
#align is_scalar_tower.of_algebra_map_eq IsScalarTower.of_algebraMap_eq
-/

#print IsScalarTower.of_algebraMap_eq' /-
/-- See note [partially-applied ext lemmas]. -/
theorem of_algebraMap_eq' [Algebra R A]
    (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A :=
  of_algebraMap_eq <| RingHom.ext_iff.1 h
#align is_scalar_tower.of_algebra_map_eq' IsScalarTower.of_algebraMap_eq'
-/

variable (R S A)

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

#print IsScalarTower.algebraMap_eq /-
theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) :=
  RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
#align is_scalar_tower.algebra_map_eq IsScalarTower.algebraMap_eq
-/

#print IsScalarTower.algebraMap_apply /-
theorem algebraMap_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R S x) := by
  rw [algebra_map_eq R S A, RingHom.comp_apply]
#align is_scalar_tower.algebra_map_apply IsScalarTower.algebraMap_apply
-/

#print IsScalarTower.Algebra.ext /-
@[ext]
theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h :
      ∀ (r : S) (x : A),
        (haveI := h1
          r • x) =
          r • x) :
    h1 = h2 :=
  Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1
#align is_scalar_tower.algebra.ext IsScalarTower.Algebra.ext
-/

#print IsScalarTower.toAlgHom /-
/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def toAlgHom : S →ₐ[R] A :=
  { algebraMap S A with commutes' := fun _ => (algebraMap_apply _ _ _ _).symm }
#align is_scalar_tower.to_alg_hom IsScalarTower.toAlgHom
-/

#print IsScalarTower.toAlgHom_apply /-
theorem toAlgHom_apply (y : S) : toAlgHom R S A y = algebraMap S A y :=
  rfl
#align is_scalar_tower.to_alg_hom_apply IsScalarTower.toAlgHom_apply
-/

#print IsScalarTower.coe_toAlgHom /-
@[simp]
theorem coe_toAlgHom : ↑(toAlgHom R S A) = algebraMap S A :=
  RingHom.ext fun _ => rfl
#align is_scalar_tower.coe_to_alg_hom IsScalarTower.coe_toAlgHom
-/

#print IsScalarTower.coe_toAlgHom' /-
@[simp]
theorem coe_toAlgHom' : (toAlgHom R S A : S → A) = algebraMap S A :=
  rfl
#align is_scalar_tower.coe_to_alg_hom' IsScalarTower.coe_toAlgHom'
-/

variable {R S A B}

#print AlgHom.map_algebraMap /-
@[simp]
theorem AlgHom.map_algebraMap (f : A →ₐ[S] B) (r : R) : f (algebraMap R A r) = algebraMap R B r :=
  by rw [algebraMap_apply R S A r, f.commutes, ← algebraMap_apply R S B]
#align alg_hom.map_algebra_map AlgHom.map_algebraMap
-/

variable (R)

#print AlgHom.comp_algebraMap_of_tower /-
@[simp]
theorem AlgHom.comp_algebraMap_of_tower (f : A →ₐ[S] B) :
    (f : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext f.map_algebraMap
#align alg_hom.comp_algebra_map_of_tower AlgHom.comp_algebraMap_of_tower
-/

variable (R) {S A B}

#print IsScalarTower.subsemiring /-
-- conflicts with is_scalar_tower.subalgebra
instance (priority := 999) subsemiring (U : Subsemiring S) : IsScalarTower U S A :=
  of_algebraMap_eq fun x => rfl
#align is_scalar_tower.subsemiring IsScalarTower.subsemiring
-/

#print IsScalarTower.of_ring_hom /-
@[nolint instance_priority]
instance of_ring_hom {R A B : Type _} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    @IsScalarTower R A B _ f.toRingHom.toAlgebra.toSMul _ :=
  letI := (f : A →+* B).toAlgebra
  of_algebra_map_eq fun x => (f.commutes x).symm
#align is_scalar_tower.of_ring_hom IsScalarTower.of_ring_hom
-/

end Semiring

end IsScalarTower

section Homs

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

variable (R) {A S B}

open IsScalarTower

namespace AlgHom

#print AlgHom.restrictScalars /-
/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
  { (f : A →+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
#align alg_hom.restrict_scalars AlgHom.restrictScalars
-/

#print AlgHom.restrictScalars_apply /-
theorem restrictScalars_apply (f : A →ₐ[S] B) (x : A) : f.restrictScalars R x = f x :=
  rfl
#align alg_hom.restrict_scalars_apply AlgHom.restrictScalars_apply
-/

#print AlgHom.coe_restrictScalars /-
@[simp]
theorem coe_restrictScalars (f : A →ₐ[S] B) : (f.restrictScalars R : A →+* B) = f :=
  rfl
#align alg_hom.coe_restrict_scalars AlgHom.coe_restrictScalars
-/

#print AlgHom.coe_restrictScalars' /-
@[simp]
theorem coe_restrictScalars' (f : A →ₐ[S] B) : (restrictScalars R f : A → B) = f :=
  rfl
#align alg_hom.coe_restrict_scalars' AlgHom.coe_restrictScalars'
-/

#print AlgHom.restrictScalars_injective /-
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₐ[S] B) → A →ₐ[R] B) := fun f g h =>
  AlgHom.ext (AlgHom.congr_fun h : _)
#align alg_hom.restrict_scalars_injective AlgHom.restrictScalars_injective
-/

end AlgHom

namespace AlgEquiv

#print AlgEquiv.restrictScalars /-
/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
  { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
#align alg_equiv.restrict_scalars AlgEquiv.restrictScalars
-/

#print AlgEquiv.restrictScalars_apply /-
theorem restrictScalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrictScalars R x = f x :=
  rfl
#align alg_equiv.restrict_scalars_apply AlgEquiv.restrictScalars_apply
-/

#print AlgEquiv.coe_restrictScalars /-
@[simp]
theorem coe_restrictScalars (f : A ≃ₐ[S] B) : (f.restrictScalars R : A ≃+* B) = f :=
  rfl
#align alg_equiv.coe_restrict_scalars AlgEquiv.coe_restrictScalars
-/

#print AlgEquiv.coe_restrictScalars' /-
@[simp]
theorem coe_restrictScalars' (f : A ≃ₐ[S] B) : (restrictScalars R f : A → B) = f :=
  rfl
#align alg_equiv.coe_restrict_scalars' AlgEquiv.coe_restrictScalars'
-/

#print AlgEquiv.restrictScalars_injective /-
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ≃ₐ[S] B) → A ≃ₐ[R] B) := fun f g h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h : _)
#align alg_equiv.restrict_scalars_injective AlgEquiv.restrictScalars_injective
-/

end AlgEquiv

end Homs

namespace Submodule

variable (R A) {M}

variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]

variable [Module R M] [Module A M] [IsScalarTower R A M]

#print Submodule.restrictScalars_span /-
/-- If `A` is an `R`-algebra such that the induced morphism `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
theorem restrictScalars_span (hsur : Function.Surjective (algebraMap R A)) (X : Set M) :
    restrictScalars R (span A X) = span R X :=
  by
  refine' ((span_le_restrict_scalars R A X).antisymm fun m hm => _).symm
  refine' span_induction hm subset_span (zero_mem _) (fun _ _ => add_mem) fun a m hm => _
  obtain ⟨r, rfl⟩ := hsur a
  simpa [algebraMap_smul] using smul_mem _ r hm
#align submodule.restrict_scalars_span Submodule.restrictScalars_span
-/

#print Submodule.coe_span_eq_span_of_surjective /-
theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s :=
  congr_arg coe (Submodule.restrictScalars_span R A h s)
#align submodule.coe_span_eq_span_of_surjective Submodule.coe_span_eq_span_of_surjective
-/

end Submodule

section Semiring

variable {R S A}

namespace Submodule

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid A]

variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

open IsScalarTower

#print Submodule.smul_mem_span_smul_of_mem /-
theorem smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k ∈ span R s) {x : A}
    (hx : x ∈ t) : k • x ∈ span R (s • t) :=
  span_induction hks (fun c hc => subset_span <| Set.mem_smul.2 ⟨c, x, hc, hx, rfl⟩)
    (by rw [zero_smul]; exact zero_mem _)
    (fun c₁ c₂ ih₁ ih₂ => by rw [add_smul]; exact add_mem ih₁ ih₂) fun b c hc => by
    rw [IsScalarTower.smul_assoc]; exact smul_mem _ _ hc
#align submodule.smul_mem_span_smul_of_mem Submodule.smul_mem_span_smul_of_mem
-/

variable [SMulCommClass R S A]

#print Submodule.smul_mem_span_smul /-
theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R t) : k • x ∈ span R (s • t) :=
  span_induction hx (fun x hx => smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hx)
    (by rw [smul_zero]; exact zero_mem _)
    (fun x y ihx ihy => by rw [smul_add]; exact add_mem ihx ihy) fun c x hx =>
    smul_comm c k x ▸ smul_mem _ _ hx
#align submodule.smul_mem_span_smul Submodule.smul_mem_span_smul
-/

#print Submodule.smul_mem_span_smul' /-
theorem smul_mem_span_smul' {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R (s • t)) : k • x ∈ span R (s • t) :=
  span_induction hx
    (fun x hx => by
      let ⟨p, q, hp, hq, hpq⟩ := Set.mem_smul.1 hx
      rw [← hpq, smul_smul]; exact smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hq)
    (by rw [smul_zero]; exact zero_mem _)
    (fun x y ihx ihy => by rw [smul_add]; exact add_mem ihx ihy) fun c x hx =>
    smul_comm c k x ▸ smul_mem _ _ hx
#align submodule.smul_mem_span_smul' Submodule.smul_mem_span_smul'
-/

#print Submodule.span_smul_of_span_eq_top /-
theorem span_smul_of_span_eq_top {s : Set S} (hs : span R s = ⊤) (t : Set A) :
    span R (s • t) = (span S t).restrictScalars R :=
  le_antisymm
    (span_le.2 fun x hx =>
      let ⟨p, q, hps, hqt, hpqx⟩ := Set.mem_smul.1 hx
      hpqx ▸ (span S t).smul_mem p (subset_span hqt))
    fun p hp =>
    span_induction hp (fun x hx => one_smul S x ▸ smul_mem_span_smul hs (subset_span hx))
      (zero_mem _) (fun _ _ => add_mem) fun k x hx => smul_mem_span_smul' hs hx
#align submodule.span_smul_of_span_eq_top Submodule.span_smul_of_span_eq_top
-/

end Module

section Algebra

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]

variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

#print Submodule.span_algebraMap_image /-
/-- A variant of `submodule.span_image` for `algebra_map`. -/
theorem span_algebraMap_image (a : Set R) :
    Submodule.span R (algebraMap R S '' a) = (Submodule.span R a).map (Algebra.linearMap R S) :=
  (Submodule.span_image <| Algebra.linearMap R S).trans rfl
#align submodule.span_algebra_map_image Submodule.span_algebraMap_image
-/

#print Submodule.span_algebraMap_image_of_tower /-
theorem span_algebraMap_image_of_tower {S T : Type _} [CommSemiring S] [Semiring T] [Module R S]
    [IsScalarTower R S S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) =
      (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) :=
  (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl
#align submodule.span_algebra_map_image_of_tower Submodule.span_algebraMap_image_of_tower
-/

#print Submodule.map_mem_span_algebraMap_image /-
theorem map_mem_span_algebraMap_image {S T : Type _} [CommSemiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x : S) (a : Set S)
    (hx : x ∈ Submodule.span R a) : algebraMap S T x ∈ Submodule.span R (algebraMap S T '' a) := by
  rw [span_algebra_map_image_of_tower, mem_map]; exact ⟨x, hx, rfl⟩
#align submodule.map_mem_span_algebra_map_image Submodule.map_mem_span_algebraMap_image
-/

end Algebra

end Submodule

end Semiring

section Ring

namespace Algebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

#print Algebra.lsmul_injective /-
theorem lsmul_injective [NoZeroSMulDivisors A M] {x : A} (hx : x ≠ 0) :
    Function.Injective (lsmul R M x) :=
  smul_right_injective _ hx
#align algebra.lsmul_injective Algebra.lsmul_injective
-/

end Algebra

end Ring

