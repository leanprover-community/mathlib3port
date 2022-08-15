/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.RingTheory.Nilpotent
import Mathbin.RingTheory.TensorProduct
import Mathbin.LinearAlgebra.Isomorphisms

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

theorem FormallyUnramified.lift_unique [FormallyUnramified R A] (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp g₁ = (Ideal.Quotient.mkₐ R I).comp g₂) : g₁ = g₂ := by
  revert g₁ g₂
  change Function.Injective (Ideal.Quotient.mkₐ R I).comp
  revert _inst_5
  apply Ideal.IsNilpotent.induction_on I hI
  · intro B _ I hI _
    exact formally_unramified.comp_injective I hI
    
  · intro B _ I J hIJ h₁ h₂ _ g₁ g₂ e
    apply h₁
    apply h₂
    ext x
    replace e := AlgHom.congr_fun e x
    dsimp' only [← AlgHom.comp_apply, ← Ideal.Quotient.mkₐ_eq_mk]  at e⊢
    rwa [Ideal.Quotient.eq, ← map_sub, Ideal.mem_quotient_iff_mem hIJ, ← Ideal.Quotient.eq]
    

theorem FormallyUnramified.ext [FormallyUnramified R A] (hI : IsNilpotent I) {g₁ g₂ : A →ₐ[R] B}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique I hI g₁ g₂ (AlgHom.ext H)

theorem FormallySmooth.exists_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert _inst_5
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

theorem FormallyEtale.comp [FormallyEtale R A] [FormallyEtale A B] : FormallyEtale R B :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩

end Comp

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
      simpa [← Algebra.of_id_apply]
    rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_oneₓ]
    

instance FormallyEtale.base_change [FormallyEtale R A] : FormallyEtale B (B ⊗[R] A) :=
  FormallyEtale.iff_unramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩

end BaseChange

end Algebra

