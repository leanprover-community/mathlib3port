/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.RingTheory.Nilpotent
import Mathbin.RingTheory.TensorProduct
import Mathbin.LinearAlgebra.Isomorphisms
import Mathbin.RingTheory.Ideal.Cotangent

/-!

# Formally étale morphisms

An `R`-algebra `A` is formally étale (resp. unramified, smooth) if for every `R`-algebra,
every square-zero ideal `I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
exactly (resp. at most, at least) one lift `A →ₐ[R] B`.

We show that the property extends onto nilpotent ideals, and that these properties are stable
under `R`-algebra homomorphisms and compositions.

-/


universe u

namespace Algebra

section

variable (R : Type u) [CommSemiringₓ R]

variable (A : Type u) [Semiringₓ A] [Algebra R A]

variable {B : Type u} [CommRingₓ B] [Algebra R B] (I : Ideal B)

include R A

/-- An `R`-algebra `A` is formally unramified if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallyUnramified : Prop where
  comp_injective :
    ∀ ⦃B : Type u⦄ [CommRingₓ B],
      ∀ [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥),
        Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)

/-- An `R` algebra `A` is formally smooth if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at least one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallySmooth : Prop where
  comp_surjective :
    ∀ ⦃B : Type u⦄ [CommRingₓ B],
      ∀ [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)

/-- An `R` algebra `A` is formally étale if for every `R`-algebra, every square-zero ideal
`I : ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists exactly one lift `A →ₐ[R] B`. -/
@[mk_iff]
class FormallyEtale : Prop where
  comp_bijective :
    ∀ ⦃B : Type u⦄ [CommRingₓ B],
      ∀ [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥),
        Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)

variable {R A}

theorem FormallyEtale.iff_unramified_and_smooth : FormallyEtale R A ↔ FormallyUnramified R A ∧ FormallySmooth R A := by
  rw [formally_unramified_iff, formally_smooth_iff, formally_etale_iff]
  simp_rw [← forall_and_distrib]
  rfl

instance (priority := 100) FormallyEtale.to_unramified [h : FormallyEtale R A] : FormallyUnramified R A :=
  (FormallyEtale.iff_unramified_and_smooth.mp h).1

instance (priority := 100) FormallyEtale.to_smooth [h : FormallyEtale R A] : FormallySmooth R A :=
  (FormallyEtale.iff_unramified_and_smooth.mp h).2

theorem FormallyEtale.of_unramified_and_smooth [h₁ : FormallyUnramified R A] [h₂ : FormallySmooth R A] :
    FormallyEtale R A :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨h₁, h₂⟩

omit R A

theorem FormallyUnramified.lift_unique {B : Type u} [CommRingₓ B] [_RB : Algebra R B] [FormallyUnramified R A]
    (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp g₁ = (Ideal.Quotient.mkₐ R I).comp g₂) : g₁ = g₂ := by
  revert g₁ g₂
  change Function.Injective (Ideal.Quotient.mkₐ R I).comp
  revert _RB
  apply Ideal.IsNilpotent.induction_on I hI
  · intro B _ I hI _
    exact formally_unramified.comp_injective I hI
    
  · intro B _ I J hIJ h₁ h₂ _ g₁ g₂ e
    apply h₁
    apply h₂
    ext x
    replace e := AlgHom.congr_fun e x
    dsimp' only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]  at e⊢
    rwa [Ideal.Quotient.eq, ← map_sub, Ideal.mem_quotient_iff_mem hIJ, ← Ideal.Quotient.eq]
    

theorem FormallyUnramified.ext [FormallyUnramified R A] (hI : IsNilpotent I) {g₁ g₂ : A →ₐ[R] B}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique I hI g₁ g₂ (AlgHom.ext H)

theorem FormallySmooth.exists_lift {B : Type u} [CommRingₓ B] [_RB : Algebra R B] [FormallySmooth R A] (I : Ideal B)
    (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) : ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert _RB
  apply Ideal.IsNilpotent.induction_on I hI
  · intro B _ I hI _
    exact formally_smooth.comp_surjective I hI
    
  · intro B _ I J hIJ h₁ h₂ _ g
    let this : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      { (DoubleQuot.quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq (sup_eq_right.mpr hIJ)) with
        commutes' := fun x => rfl }
    obtain ⟨g', e⟩ := h₂ (this.symm.to_alg_hom.comp g)
    obtain ⟨g', rfl⟩ := h₁ g'
    replace e := congr_arg this.to_alg_hom.comp e
    conv_rhs at e =>
      rw [← AlgHom.comp_assoc, AlgEquiv.to_alg_hom_eq_coe, AlgEquiv.to_alg_hom_eq_coe, AlgEquiv.comp_symm,
        AlgHom.id_comp]
    exact ⟨g', e⟩
    

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` square-zero,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable def FormallySmooth.lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    A →ₐ[R] B :=
  (FormallySmooth.exists_lift I hI g).some

@[simp]
theorem FormallySmooth.comp_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    (Ideal.Quotient.mkₐ R I).comp (FormallySmooth.lift I hI g) = g :=
  (FormallySmooth.exists_lift I hI g).some_spec

@[simp]
theorem FormallySmooth.mk_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) (x : A) :
    Ideal.Quotient.mk I (FormallySmooth.lift I hI g x) = g x :=
  AlgHom.congr_fun (FormallySmooth.comp_lift I hI g : _) x

variable {C : Type u} [CommRingₓ C] [Algebra R C]

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` nilpotent,
this is an arbitrary lift `A →ₐ[R] B`. -/
noncomputable def FormallySmooth.liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent (g : B →+* C).ker) : A →ₐ[R] B :=
  FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)

@[simp]
theorem FormallySmooth.lift_of_surjective_apply [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent (g : B →+* C).ker) (x : A) :
    g (FormallySmooth.liftOfSurjective f g hg hg' x) = f x := by
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).symm.Injective
  change _ = ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f) x
  rw [← formally_smooth.mk_lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)]
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).Injective
  rw [AlgEquiv.apply_symm_apply, Ideal.quotientKerAlgEquivOfSurjective, Ideal.quotientKerAlgEquivOfRightInverse.apply]
  exact (Ideal.ker_lift_alg_mk _ _).symm

@[simp]
theorem FormallySmooth.comp_lift_of_surjective [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent (g : B →+* C).ker) :
    g.comp (FormallySmooth.liftOfSurjective f g hg hg') = f :=
  AlgHom.ext (FormallySmooth.lift_of_surjective_apply f g hg hg')

end

section OfEquiv

variable {R : Type u} [CommSemiringₓ R]

variable {A B : Type u} [Semiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B]

theorem FormallySmooth.of_equiv [FormallySmooth R A] (e : A ≃ₐ[R] B) : FormallySmooth R B := by
  constructor
  intro C _ _ I hI f
  use (formally_smooth.lift I ⟨2, hI⟩ (f.comp e : A →ₐ[R] C ⧸ I)).comp e.symm
  rw [← AlgHom.comp_assoc, formally_smooth.comp_lift, AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.comp_id]

theorem FormallyUnramified.of_equiv [FormallyUnramified R A] (e : A ≃ₐ[R] B) : FormallyUnramified R B := by
  constructor
  intro C _ _ I hI f₁ f₂ e'
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  refine' formally_unramified.comp_injective I hI _
  rw [← AlgHom.comp_assoc, e', AlgHom.comp_assoc]

theorem FormallyEtale.of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩

end OfEquiv

section Polynomial

variable (R : Type u) [CommSemiringₓ R]

instance FormallySmooth.mv_polynomial (σ : Type u) : FormallySmooth R (MvPolynomial σ R) := by
  constructor
  intro C _ _ I hI f
  have : ∀ s : σ, ∃ c : C, Ideal.Quotient.mk I c = f (MvPolynomial.x s) := fun s => Ideal.Quotient.mk_surjective _
  choose g hg
  refine' ⟨MvPolynomial.aeval g, _⟩
  ext s
  rw [← hg, AlgHom.comp_apply, MvPolynomial.aeval_X]
  rfl

instance FormallySmooth.polynomial : FormallySmooth R (Polynomial R) :=
  @FormallySmooth.of_equiv _ _ _ _ _ (FormallySmooth.mv_polynomial R PUnit) (MvPolynomial.punitAlgEquiv R)

end Polynomial

section Comp

variable (R : Type u) [CommSemiringₓ R]

variable (A : Type u) [CommSemiringₓ A] [Algebra R A]

variable (B : Type u) [Semiringₓ B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem FormallySmooth.comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
  constructor
  intro C _ _ I hI f
  obtain ⟨f', e⟩ := formally_smooth.comp_surjective I hI (f.comp (IsScalarTower.toAlgHom R A B))
  letI := f'.to_ring_hom.to_algebra
  obtain ⟨f'', e'⟩ := formally_smooth.comp_surjective I hI { f.to_ring_hom with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R  at e'
  exact ⟨f''.restrict_scalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩

theorem FormallyUnramified.comp [FormallyUnramified R A] [FormallyUnramified A B] : FormallyUnramified R B := by
  constructor
  intro C _ _ I hI f₁ f₂ e
  have e' :=
    formally_unramified.lift_unique I ⟨2, hI⟩ (f₁.comp <| IsScalarTower.toAlgHom R A B)
      (f₂.comp <| IsScalarTower.toAlgHom R A B)
      (by
        rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc])
  letI := (f₁.comp (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  let F₁ : B →ₐ[A] C := { f₁ with commutes' := fun r => rfl }
  let F₂ : B →ₐ[A] C := { f₂ with commutes' := AlgHom.congr_fun e'.symm }
  ext1
  change F₁ x = F₂ x
  congr
  exact formally_unramified.ext I ⟨2, hI⟩ (AlgHom.congr_fun e)

theorem FormallyUnramified.of_comp [FormallyUnramified R B] : FormallyUnramified A B := by
  constructor
  intro Q _ _ I e f₁ f₂ e'
  letI := ((algebraMap A Q).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A Q := IsScalarTower.of_algebra_map_eq' rfl
  refine' AlgHom.restrict_scalars_injective R _
  refine' formally_unramified.ext I ⟨2, e⟩ _
  intro x
  exact AlgHom.congr_fun e' x

theorem FormallyEtale.comp [FormallyEtale R A] [FormallyEtale A B] : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩

end Comp

section OfSurjective

variable {R S : Type u} [CommRingₓ R] [CommSemiringₓ S]

variable {P A : Type u} [CommRingₓ A] [Algebra R A] [CommRingₓ P] [Algebra R P]

variable (I : Ideal P) (f : P →ₐ[R] A) (hf : Function.Surjective f)

theorem FormallySmooth.of_split [FormallySmooth R P] (g : A →ₐ[R] P ⧸ f.toRingHom.ker ^ 2)
    (hg : f.kerSquareLift.comp g = AlgHom.id R A) : FormallySmooth R A := by
  constructor
  intro C _ _ I hI i
  let l : P ⧸ f.to_ring_hom.ker ^ 2 →ₐ[R] C := by
    refine' Ideal.Quotient.liftₐ _ (formally_smooth.lift I ⟨2, hI⟩ (i.comp f)) _
    have : RingHom.ker f ≤ I.comap (formally_smooth.lift I ⟨2, hI⟩ (i.comp f)) := by
      rintro x (hx : f x = 0)
      have : _ = i (f x) := (formally_smooth.mk_lift I ⟨2, hI⟩ (i.comp f) x : _)
      rwa [hx, map_zero, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_eq_zero] at this
    intro x hx
    have := (Ideal.pow_mono this 2).trans (Ideal.le_comap_pow _ 2) hx
    rwa [hI] at this
  have : i.comp f.ker_square_lift = (Ideal.Quotient.mkₐ R _).comp l := by
    apply AlgHom.coe_ring_hom_injective
    apply Ideal.Quotient.ring_hom_ext
    ext x
    exact (formally_smooth.mk_lift I ⟨2, hI⟩ (i.comp f) x).symm
  exact
    ⟨l.comp g, by
      rw [← AlgHom.comp_assoc, ← this, AlgHom.comp_assoc, hg, AlgHom.comp_id]⟩

include hf

/-- Let `P →ₐ[R] A` be a surjection with kernel `J`, and `P` a formally smooth `R`-algebra,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has a section.

Geometric intuition: we require that a first-order thickening of `Spec A` inside `Spec P` admits
a retraction. -/
theorem FormallySmooth.iff_split_surjection [FormallySmooth R P] :
    FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgHom.id R A := by
  constructor
  · intro
    have surj : Function.Surjective f.ker_square_lift := fun x => ⟨Submodule.Quotient.mk (hf x).some, (hf x).some_spec⟩
    have sqz : RingHom.ker f.ker_square_lift.to_ring_hom ^ 2 = 0 := by
      rw [AlgHom.ker_ker_sqare_lift, Ideal.cotangent_ideal_square, Ideal.zero_eq_bot]
    refine' ⟨formally_smooth.lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom, _⟩
    ext x
    have :=
      (Ideal.quotientKerAlgEquivOfSurjective surj).toAlgHom.congr_arg
        (formally_smooth.mk_lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom x)
    dsimp'  at this
    rw [AlgEquiv.apply_symm_apply] at this
    conv_rhs => rw [← this, AlgHom.id_apply]
    obtain ⟨y, e⟩ :=
      Ideal.Quotient.mk_surjective
        (formally_smooth.lift _ ⟨2, sqz⟩ (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom x)
    dsimp'  at e⊢
    rw [← e]
    rfl
    
  · rintro ⟨g, hg⟩
    exact formally_smooth.of_split f g hg
    

end OfSurjective

section BaseChange

open TensorProduct

variable {R : Type u} [CommSemiringₓ R]

variable {A : Type u} [Semiringₓ A] [Algebra R A]

variable (B : Type u) [CommSemiringₓ B] [Algebra R B]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
instance FormallyUnramified.base_change [FormallyUnramified R A] : FormallyUnramified B (B ⊗[R] A) := by
  constructor
  intro C _ _ I hI f₁ f₂ e
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebra_map_eq' rfl
  apply AlgHom.restrict_scalars_injective R
  apply TensorProduct.ext
  any_goals {
  }
  intro b a
  have : b ⊗ₜ[R] a = b • 1 ⊗ₜ a := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_oneₓ]
  rw [this, AlgHom.restrict_scalars_apply, AlgHom.restrict_scalars_apply, map_smul, map_smul]
  congr 1
  change
    ((f₁.restrict_scalars R).comp tensor_product.include_right) a =
      ((f₂.restrict_scalars R).comp tensor_product.include_right) a
  congr 1
  refine' formally_unramified.ext I ⟨2, hI⟩ _
  intro x
  exact AlgHom.congr_fun e (1 ⊗ₜ x)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
instance FormallySmooth.base_change [FormallySmooth R A] : FormallySmooth B (B ⊗[R] A) := by
  constructor
  intro C _ _ I hI f
  letI := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebra_map_eq' rfl
  refine' ⟨tensor_product.product_left_alg_hom (Algebra.ofId B C) _, _⟩
  · exact formally_smooth.lift I ⟨2, hI⟩ ((f.restrict_scalars R).comp tensor_product.include_right)
    
  · apply AlgHom.restrict_scalars_injective R
    apply TensorProduct.ext
    any_goals {
    }
    intro b a
    suffices algebraMap B _ b * f (1 ⊗ₜ[R] a) = f (b ⊗ₜ[R] a) by
      simpa [Algebra.of_id_apply]
    rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_oneₓ]
    

instance FormallyEtale.base_change [FormallyEtale R A] : FormallyEtale B (B ⊗[R] A) :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩

end BaseChange

section Localization

variable {R S Rₘ Sₘ : Type u} [CommRingₓ R] [CommRingₓ S] [CommRingₓ Rₘ] [CommRingₓ Sₘ]

variable (M : Submonoid R)

variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]

variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]

variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]

attribute [local elabAsElim] Ideal.IsNilpotent.induction_on

include M

theorem FormallySmooth.of_is_localization : FormallySmooth R Rₘ := by
  constructor
  intro Q _ _ I e f
  have : ∀ x : M, IsUnit (algebraMap R Q x) := by
    intro x
    apply (IsNilpotent.is_unit_quotient_mk_iff ⟨2, e⟩).mp
    convert (IsLocalization.map_units Rₘ x).map f
    simp only [Ideal.Quotient.mk_algebra_map, AlgHom.commutes]
  let this : Rₘ →ₐ[R] Q := { IsLocalization.lift this with commutes' := IsLocalization.lift_eq this }
  use this
  apply AlgHom.coe_ring_hom_injective
  refine' IsLocalization.ring_hom_ext M _
  ext
  simp

/-- This holds in general for epimorphisms. -/
theorem FormallyUnramified.of_is_localization : FormallyUnramified R Rₘ := by
  constructor
  intro Q _ _ I e f₁ f₂ e
  apply AlgHom.coe_ring_hom_injective
  refine' IsLocalization.ring_hom_ext M _
  ext
  simp

theorem FormallyEtale.of_is_localization : FormallyEtale R Rₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.of_is_localization M, FormallySmooth.of_is_localization M⟩

theorem FormallySmooth.localization_base [FormallySmooth R Sₘ] : FormallySmooth Rₘ Sₘ := by
  constructor
  intro Q _ _ I e f
  letI := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  letI : IsScalarTower R Rₘ Q := IsScalarTower.of_algebra_map_eq' rfl
  let f : Sₘ →ₐ[Rₘ] Q := by
    refine' { formally_smooth.lift I ⟨2, e⟩ (f.restrict_scalars R) with commutes' := _ }
    intro r
    change
      (RingHom.comp (formally_smooth.lift I ⟨2, e⟩ (f.restrict_scalars R) : Sₘ →+* Q) (algebraMap _ _)) r =
        algebraMap _ _ r
    congr 1
    refine' IsLocalization.ring_hom_ext M _
    rw [RingHom.comp_assoc, ← IsScalarTower.algebra_map_eq, ← IsScalarTower.algebra_map_eq, AlgHom.comp_algebra_map]
  use f
  ext
  simp

/-- This actually does not need the localization instance, and is stated here again for
consistency. See `algebra.formally_unramified.of_comp` instead.

 The intended use is for copying proofs between `formally_{unramified, smooth, etale}`
 without the need to change anything (including removing redundant arguments). -/
@[nolint unused_arguments]
theorem FormallyUnramified.localization_base [FormallyUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ :=
  FormallyUnramified.of_comp R Rₘ Sₘ

theorem FormallyEtale.localization_base [FormallyEtale R Sₘ] : FormallyEtale Rₘ Sₘ :=
  FormallyEtale.iff_unramified_and_smooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩

theorem FormallySmooth.localization_map [FormallySmooth R S] : FormallySmooth Rₘ Sₘ := by
  haveI : formally_smooth S Sₘ := formally_smooth.of_is_localization (M.map (algebraMap R S))
  haveI : formally_smooth R Sₘ := formally_smooth.comp R S Sₘ
  exact formally_smooth.localization_base M

theorem FormallyUnramified.localization_map [FormallyUnramified R S] : FormallyUnramified Rₘ Sₘ := by
  haveI : formally_unramified S Sₘ := formally_unramified.of_is_localization (M.map (algebraMap R S))
  haveI : formally_unramified R Sₘ := formally_unramified.comp R S Sₘ
  exact formally_unramified.localization_base M

theorem FormallyEtale.localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ := by
  haveI : formally_etale S Sₘ := formally_etale.of_is_localization (M.map (algebraMap R S))
  haveI : formally_etale R Sₘ := formally_etale.comp R S Sₘ
  exact formally_etale.localization_base M

end Localization

end Algebra

