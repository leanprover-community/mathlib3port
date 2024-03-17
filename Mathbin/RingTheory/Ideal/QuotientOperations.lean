/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import RingTheory.Ideal.Operations
import RingTheory.Ideal.Quotient

#align_import ring_theory.ideal.quotient_operations from "leanprover-community/mathlib"@"b88d81c84530450a8989e918608e5960f015e6c8"

/-!
# More operations on modules and ideals related to quotients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

#print RingHom.kerLift /-
/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_equiv_of_right_inverse`) /
is surjective (`quotient_ker_equiv_of_surjective`).
-/
def kerLift (f : R →+* S) : R ⧸ f.ker →+* S :=
  Ideal.Quotient.lift _ f fun r => f.mem_ker.mp
#align ring_hom.ker_lift RingHom.kerLift
-/

#print RingHom.kerLift_mk /-
@[simp]
theorem kerLift_mk (f : R →+* S) (r : R) : kerLift f (Ideal.Quotient.mk f.ker r) = f r :=
  Ideal.Quotient.lift_mk _ _ _
#align ring_hom.ker_lift_mk RingHom.kerLift_mk
-/

#print RingHom.kerLift_injective /-
/-- The induced map from the quotient by the kernel is injective. -/
theorem kerLift_injective (f : R →+* S) : Function.Injective (kerLift f) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : f a = f b) =>
    Ideal.Quotient.eq.2 <| show a - b ∈ ker f by rw [mem_ker, map_sub, h, sub_self]
#align ring_hom.ker_lift_injective RingHom.kerLift_injective
-/

#print RingHom.lift_injective_of_ker_le_ideal /-
theorem lift_injective_of_ker_le_ideal (I : Ideal R) {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hI : f.ker ≤ I) : Function.Injective (Ideal.Quotient.lift I f H) :=
  by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [Ideal.Quotient.lift_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI ((RingHom.mem_ker f).mpr hu)
#align ring_hom.lift_injective_of_ker_le_ideal RingHom.lift_injective_of_ker_le_ideal
-/

variable {f}

#print RingHom.quotientKerEquivOfRightInverse /-
/-- The **first isomorphism theorem** for commutative rings, computable version. -/
def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) : R ⧸ f.ker ≃+* S :=
  { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk f.ker ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply ker_lift_injective
      simp [hf (f x)]
    right_inv := hf }
#align ring_hom.quotient_ker_equiv_of_right_inverse RingHom.quotientKerEquivOfRightInverse
-/

#print RingHom.quotientKerEquivOfRightInverse.apply /-
@[simp]
theorem quotientKerEquivOfRightInverse.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : R ⧸ f.ker) : quotientKerEquivOfRightInverse hf x = kerLift f x :=
  rfl
#align ring_hom.quotient_ker_equiv_of_right_inverse.apply RingHom.quotientKerEquivOfRightInverse.apply
-/

#print RingHom.quotientKerEquivOfRightInverse.Symm.apply /-
@[simp]
theorem quotientKerEquivOfRightInverse.Symm.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : S) : (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk f.ker (g x) :=
  rfl
#align ring_hom.quotient_ker_equiv_of_right_inverse.symm.apply RingHom.quotientKerEquivOfRightInverse.Symm.apply
-/

#print RingHom.quotientKerEquivOfSurjective /-
/-- The **first isomorphism theorem** for commutative rings. -/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ f.ker ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.choose_spec hf.HasRightInverse)
#align ring_hom.quotient_ker_equiv_of_surjective RingHom.quotientKerEquivOfSurjective
-/

end RingHom

namespace Ideal

variable {R : Type u} {S : Type v} {F : Type w} [CommRing R] [CommRing S]

#print Ideal.map_quotient_self /-
@[simp]
theorem map_quotient_self (I : Ideal R) : map (Quotient.mk I) I = ⊥ :=
  eq_bot_iff.2 <|
    Ideal.map_le_iff_le_comap.2 fun x hx =>
      (Submodule.mem_bot (R ⧸ I)).2 <| Ideal.Quotient.eq_zero_iff_mem.2 hx
#align ideal.map_quotient_self Ideal.map_quotient_self
-/

#print Ideal.mk_ker /-
@[simp]
theorem mk_ker {I : Ideal R} : (Quotient.mk I).ker = I := by
  ext <;> rw [RingHom.ker, mem_comap, Submodule.mem_bot, quotient.eq_zero_iff_mem]
#align ideal.mk_ker Ideal.mk_ker
-/

#print Ideal.map_mk_eq_bot_of_le /-
theorem map_mk_eq_bot_of_le {I J : Ideal R} (h : I ≤ J) : I.map J.Quotient.mk = ⊥ := by
  rw [map_eq_bot_iff_le_ker, mk_ker]; exact h
#align ideal.map_mk_eq_bot_of_le Ideal.map_mk_eq_bot_of_le
-/

#print Ideal.ker_quotient_lift /-
theorem ker_quotient_lift {S : Type v} [CommRing S] {I : Ideal R} (f : R →+* S) (H : I ≤ f.ker) :
    (Ideal.Quotient.lift I f H).ker = f.ker.map I.Quotient.mk :=
  by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := quotient.mk_surjective x
    rw [RingHom.mem_ker, ← hy, Ideal.Quotient.lift_mk, ← RingHom.mem_ker] at hx
    rw [← hy, mem_map_iff_of_surjective I.Quotient.mk quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
  · intro hx
    rw [mem_map_iff_of_surjective I.Quotient.mk quotient.mk_surjective] at hx
    obtain ⟨y, hy⟩ := hx
    rw [RingHom.mem_ker, ← hy.right, Ideal.Quotient.lift_mk, ← RingHom.mem_ker f]
    exact hy.left
#align ideal.ker_quotient_lift Ideal.ker_quotient_lift
-/

#print Ideal.bot_quotient_isMaximal_iff /-
@[simp]
theorem bot_quotient_isMaximal_iff (I : Ideal R) : (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal :=
  ⟨fun hI =>
    @mk_ker _ _ I ▸
      @comap_isMaximal_of_surjective _ _ _ _ _ _ (Quotient.mk I) Quotient.mk_surjective ⊥ hI,
    fun hI => by skip; letI := quotient.field I; exact bot_is_maximal⟩
#align ideal.bot_quotient_is_maximal_iff Ideal.bot_quotient_isMaximal_iff
-/

#print Ideal.mem_quotient_iff_mem_sup /-
/-- See also `ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
theorem mem_quotient_iff_mem_sup {I J : Ideal R} {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J ⊔ I := by
  rw [← mem_comap, comap_map_of_surjective (Quotient.mk' I) quotient.mk_surjective, ←
    RingHom.ker_eq_comap_bot, mk_ker]
#align ideal.mem_quotient_iff_mem_sup Ideal.mem_quotient_iff_mem_sup
-/

#print Ideal.mem_quotient_iff_mem /-
/-- See also `ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
theorem mem_quotient_iff_mem {I J : Ideal R} (hIJ : I ≤ J) {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J := by
  rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]
#align ideal.mem_quotient_iff_mem Ideal.mem_quotient_iff_mem
-/

#print Ideal.comap_map_mk /-
theorem comap_map_mk {I J : Ideal R} (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J := by ext;
  rw [← Ideal.mem_quotient_iff_mem h, Ideal.mem_comap]
#align ideal.comap_map_mk Ideal.comap_map_mk
-/

section QuotientAlgebra

variable (R₁ R₂ : Type _) {A B : Type _}

variable [CommSemiring R₁] [CommSemiring R₂] [CommRing A] [CommRing B]

variable [Algebra R₁ A] [Algebra R₂ A] [Algebra R₁ B]

#print Ideal.Quotient.algebra /-
/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
instance Quotient.algebra {I : Ideal A} : Algebra R₁ (A ⧸ I) :=
  {
    RingHom.comp (Ideal.Quotient.mk I)
      (algebraMap R₁
        A) with
    toFun := fun x => Ideal.Quotient.mk I (algebraMap R₁ A x)
    smul := (· • ·)
    smul_def' := fun r x =>
      Quotient.inductionOn' x fun x =>
        ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (RingHom.map_mul _ _ _)
    commutes' := fun _ _ => mul_comm _ _ }
#align ideal.quotient.algebra Ideal.Quotient.algebra
-/

#print Ideal.Quotient.isScalarTower /-
-- Lean can struggle to find this instance later if we don't provide this shortcut
instance Quotient.isScalarTower [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A) :
    IsScalarTower R₁ R₂ (A ⧸ I) := by infer_instance
#align ideal.quotient.is_scalar_tower Ideal.Quotient.isScalarTower
-/

#print Ideal.Quotient.mkₐ /-
/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
def Quotient.mkₐ (I : Ideal A) : A →ₐ[R₁] A ⧸ I :=
  ⟨fun a => Submodule.Quotient.mk a, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
#align ideal.quotient.mkₐ Ideal.Quotient.mkₐ
-/

#print Ideal.Quotient.algHom_ext /-
theorem Quotient.algHom_ext {I : Ideal A} {S} [Semiring S] [Algebra R₁ S] ⦃f g : A ⧸ I →ₐ[R₁] S⦄
    (h : f.comp (Quotient.mkₐ R₁ I) = g.comp (Quotient.mkₐ R₁ I)) : f = g :=
  AlgHom.ext fun x => Quotient.inductionOn' x <| AlgHom.congr_fun h
#align ideal.quotient.alg_hom_ext Ideal.Quotient.algHom_ext
-/

#print Ideal.Quotient.alg_map_eq /-
theorem Quotient.alg_map_eq (I : Ideal A) :
    algebraMap R₁ (A ⧸ I) = (algebraMap A (A ⧸ I)).comp (algebraMap R₁ A) :=
  rfl
#align ideal.quotient.alg_map_eq Ideal.Quotient.alg_map_eq
-/

#print Ideal.Quotient.mkₐ_toRingHom /-
theorem Quotient.mkₐ_toRingHom (I : Ideal A) :
    (Quotient.mkₐ R₁ I).toRingHom = Ideal.Quotient.mk I :=
  rfl
#align ideal.quotient.mkₐ_to_ring_hom Ideal.Quotient.mkₐ_toRingHom
-/

#print Ideal.Quotient.mkₐ_eq_mk /-
@[simp]
theorem Quotient.mkₐ_eq_mk (I : Ideal A) : ⇑(Quotient.mkₐ R₁ I) = Ideal.Quotient.mk I :=
  rfl
#align ideal.quotient.mkₐ_eq_mk Ideal.Quotient.mkₐ_eq_mk
-/

#print Ideal.Quotient.algebraMap_eq /-
@[simp]
theorem Quotient.algebraMap_eq (I : Ideal R) : algebraMap R (R ⧸ I) = I.Quotient.mk :=
  rfl
#align ideal.quotient.algebra_map_eq Ideal.Quotient.algebraMap_eq
-/

#print Ideal.Quotient.mk_comp_algebraMap /-
@[simp]
theorem Quotient.mk_comp_algebraMap (I : Ideal A) :
    (Quotient.mk I).comp (algebraMap R₁ A) = algebraMap R₁ (A ⧸ I) :=
  rfl
#align ideal.quotient.mk_comp_algebra_map Ideal.Quotient.mk_comp_algebraMap
-/

#print Ideal.Quotient.mk_algebraMap /-
@[simp]
theorem Quotient.mk_algebraMap (I : Ideal A) (x : R₁) :
    Quotient.mk I (algebraMap R₁ A x) = algebraMap R₁ (A ⧸ I) x :=
  rfl
#align ideal.quotient.mk_algebra_map Ideal.Quotient.mk_algebraMap
-/

#print Ideal.Quotient.mkₐ_surjective /-
/-- The canonical morphism `A →ₐ[R₁] I.quotient` is surjective. -/
theorem Quotient.mkₐ_surjective (I : Ideal A) : Function.Surjective (Quotient.mkₐ R₁ I) :=
  surjective_quot_mk _
#align ideal.quotient.mkₐ_surjective Ideal.Quotient.mkₐ_surjective
-/

#print Ideal.Quotient.mkₐ_ker /-
/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
theorem Quotient.mkₐ_ker (I : Ideal A) : (Quotient.mkₐ R₁ I : A →+* A ⧸ I).ker = I :=
  Ideal.mk_ker
#align ideal.quotient.mkₐ_ker Ideal.Quotient.mkₐ_ker
-/

variable {R₁}

#print Ideal.Quotient.liftₐ /-
/-- `ideal.quotient.lift` as an `alg_hom`. -/
def Quotient.liftₐ (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    A ⧸ I →ₐ[R₁] B :=
  {-- this is is_scalar_tower.algebra_map_apply R₁ A (A ⧸ I) but the file `algebra.algebra.tower`
      -- imports this file.
      Ideal.Quotient.lift
      I (f : A →+* B) hI with
    commutes' := fun r =>
      by
      have : algebraMap R₁ (A ⧸ I) r = algebraMap A (A ⧸ I) (algebraMap R₁ A r) := by
        simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
      rw [this, Ideal.Quotient.algebraMap_eq, RingHom.toFun_eq_coe, Ideal.Quotient.lift_mk,
        AlgHom.coe_toRingHom, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        map_smul, map_one] }
#align ideal.quotient.liftₐ Ideal.Quotient.liftₐ
-/

#print Ideal.Quotient.liftₐ_apply /-
@[simp]
theorem Quotient.liftₐ_apply (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) (x) :
    Ideal.Quotient.liftₐ I f hI x = Ideal.Quotient.lift I (f : A →+* B) hI x :=
  rfl
#align ideal.quotient.liftₐ_apply Ideal.Quotient.liftₐ_apply
-/

#print Ideal.Quotient.liftₐ_comp /-
theorem Quotient.liftₐ_comp (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    (Ideal.Quotient.liftₐ I f hI).comp (Ideal.Quotient.mkₐ R₁ I) = f :=
  AlgHom.ext fun x => (Ideal.Quotient.lift_mk I (f : A →+* B) hI : _)
#align ideal.quotient.liftₐ_comp Ideal.Quotient.liftₐ_comp
-/

#print Ideal.KerLift.map_smul /-
theorem KerLift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ f.toRingHom.ker) :
    f.toRingHom.kerLift (r • x) = r • f.toRingHom.kerLift x :=
  by
  obtain ⟨a, rfl⟩ := quotient.mkₐ_surjective R₁ _ x
  rw [← AlgHom.map_smul, quotient.mkₐ_eq_mk, RingHom.kerLift_mk]
  exact f.map_smul _ _
#align ideal.ker_lift.map_smul Ideal.KerLift.map_smul
-/

#print Ideal.kerLiftAlg /-
/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_alg_equiv_of_right_inverse`) /
is surjective (`quotient_ker_alg_equiv_of_surjective`).
-/
def kerLiftAlg (f : A →ₐ[R₁] B) : A ⧸ f.toRingHom.ker →ₐ[R₁] B :=
  AlgHom.mk' f.toRingHom.kerLift fun _ _ => KerLift.map_smul f _ _
#align ideal.ker_lift_alg Ideal.kerLiftAlg
-/

#print Ideal.kerLiftAlg_mk /-
@[simp]
theorem kerLiftAlg_mk (f : A →ₐ[R₁] B) (a : A) :
    kerLiftAlg f (Quotient.mk f.toRingHom.ker a) = f a :=
  rfl
#align ideal.ker_lift_alg_mk Ideal.kerLiftAlg_mk
-/

#print Ideal.kerLiftAlg_toRingHom /-
@[simp]
theorem kerLiftAlg_toRingHom (f : A →ₐ[R₁] B) : (kerLiftAlg f).toRingHom = RingHom.kerLift f :=
  rfl
#align ideal.ker_lift_alg_to_ring_hom Ideal.kerLiftAlg_toRingHom
-/

#print Ideal.kerLiftAlg_injective /-
/-- The induced algebra morphism from the quotient by the kernel is injective. -/
theorem kerLiftAlg_injective (f : A →ₐ[R₁] B) : Function.Injective (kerLiftAlg f) :=
  RingHom.kerLift_injective f
#align ideal.ker_lift_alg_injective Ideal.kerLiftAlg_injective
-/

#print Ideal.quotientKerAlgEquivOfRightInverse /-
/-- The **first isomorphism** theorem for algebras, computable version. -/
def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) : (A ⧸ f.toRingHom.ker) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse fun x => show f.toRingHom (g x) = x from hf x,
    kerLiftAlg f with }
#align ideal.quotient_ker_alg_equiv_of_right_inverse Ideal.quotientKerAlgEquivOfRightInverse
-/

#print Ideal.quotientKerAlgEquivOfRightInverse_apply /-
@[simp]
theorem Ideal.quotientKerAlgEquivOfRightInverse_apply {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) (x : A ⧸ f.toRingHom.ker) :
    quotientKerAlgEquivOfRightInverse hf x = kerLiftAlg f x :=
  rfl
#align ideal.quotient_ker_alg_equiv_of_right_inverse.apply Ideal.quotientKerAlgEquivOfRightInverse_apply
-/

#print Ideal.quotientKerAlgEquivOfRightInverse_symm_apply /-
@[simp]
theorem Ideal.quotientKerAlgEquivOfRightInverse_symm_apply {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) (x : B) :
    (quotientKerAlgEquivOfRightInverse hf).symm x = Quotient.mkₐ R₁ f.toRingHom.ker (g x) :=
  rfl
#align ideal.quotient_ker_alg_equiv_of_right_inverse_symm.apply Ideal.quotientKerAlgEquivOfRightInverse_symm_apply
-/

#print Ideal.quotientKerAlgEquivOfSurjective /-
/-- The **first isomorphism theorem** for algebras. -/
noncomputable def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ f.toRingHom.ker) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.HasRightInverse)
#align ideal.quotient_ker_alg_equiv_of_surjective Ideal.quotientKerAlgEquivOfSurjective
-/

#print Ideal.quotientMap /-
/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotientMap {I : Ideal R} (J : Ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) : R ⧸ I →+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, quotient.eq_zero_iff_mem] using hIJ ha
#align ideal.quotient_map Ideal.quotientMap
-/

#print Ideal.quotientMap_mk /-
@[simp]
theorem quotientMap_mk {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f} {x : R} :
    quotientMap I f H (Quotient.mk J x) = Quotient.mk I (f x) :=
  Quotient.lift_mk J _ _
#align ideal.quotient_map_mk Ideal.quotientMap_mk
-/

#print Ideal.quotientMap_algebraMap /-
@[simp]
theorem quotientMap_algebraMap {J : Ideal A} {I : Ideal S} {f : A →+* S} {H : J ≤ I.comap f}
    {x : R₁} : quotientMap I f H (algebraMap R₁ (A ⧸ J) x) = Quotient.mk I (f (algebraMap _ _ x)) :=
  Quotient.lift_mk J _ _
#align ideal.quotient_map_algebra_map Ideal.quotientMap_algebraMap
-/

#print Ideal.quotientMap_comp_mk /-
theorem quotientMap_comp_mk {J : Ideal R} {I : Ideal S} {f : R →+* S} (H : J ≤ I.comap f) :
    (quotientMap I f H).comp (Quotient.mk J) = (Quotient.mk I).comp f :=
  RingHom.ext fun x => by simp only [Function.comp_apply, RingHom.coe_comp, Ideal.quotientMap_mk]
#align ideal.quotient_map_comp_mk Ideal.quotientMap_comp_mk
-/

#print Ideal.quotientEquiv /-
/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+** S`,  where `J = f(I)`. -/
@[simps]
def quotientEquiv (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) :
    R ⧸ I ≃+* S ⧸ J :=
  {
    quotientMap J (↑f)
      (by rw [hIJ];
        exact
          @le_comap_map _ S _ _ _ _ _
            _) with
    invFun := quotientMap I (↑f.symm) (by rw [hIJ]; exact le_of_eq (map_comap_of_equiv I f))
    left_inv := by rintro ⟨r⟩; simp
    right_inv := by rintro ⟨s⟩; simp }
#align ideal.quotient_equiv Ideal.quotientEquiv
-/

#print Ideal.quotientEquiv_mk /-
@[simp]
theorem quotientEquiv_mk (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S))
    (x : R) : quotientEquiv I J f hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x) :=
  rfl
#align ideal.quotient_equiv_mk Ideal.quotientEquiv_mk
-/

#print Ideal.quotientEquiv_symm_mk /-
@[simp]
theorem quotientEquiv_symm_mk (I : Ideal R) (J : Ideal S) (f : R ≃+* S)
    (hIJ : J = I.map (f : R →+* S)) (x : S) :
    (quotientEquiv I J f hIJ).symm (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I (f.symm x) :=
  rfl
#align ideal.quotient_equiv_symm_mk Ideal.quotientEquiv_symm_mk
-/

#print Ideal.quotientMap_injective' /-
/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
theorem quotientMap_injective' {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f}
    (h : I.comap f ≤ J) : Function.Injective (quotientMap I f H) :=
  by
  refine' (injective_iff_map_eq_zero (QuotientMap I f H)).2 fun a ha => _
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a
  rw [quotient_map_mk, quotient.eq_zero_iff_mem] at ha
  exact quotient.eq_zero_iff_mem.mpr (h ha)
#align ideal.quotient_map_injective' Ideal.quotientMap_injective'
-/

#print Ideal.quotientMap_injective /-
/-- If we take `J = I.comap f` then `quotient_map` is injective automatically. -/
theorem quotientMap_injective {I : Ideal S} {f : R →+* S} :
    Function.Injective (quotientMap I f le_rfl) :=
  quotientMap_injective' le_rfl
#align ideal.quotient_map_injective Ideal.quotientMap_injective
-/

#print Ideal.quotientMap_surjective /-
theorem quotientMap_surjective {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f}
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I f H) := fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩
#align ideal.quotient_map_surjective Ideal.quotientMap_surjective
-/

#print Ideal.comp_quotientMap_eq_of_comp_eq /-
/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
theorem comp_quotientMap_eq_of_comp_eq {R' S' : Type _} [CommRing R'] [CommRing S'] {f : R →+* S}
    {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f) (I : Ideal S') :
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
      (quotientMap I f' le_rfl).comp
        (quotientMap (I.comap f') g
          (le_of_eq (trans (comap_comap f g') (hfg ▸ comap_comap g f')))) :=
  by
  refine' RingHom.ext fun a => _
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a
  simp only [RingHom.comp_apply, quotient_map_mk]
  exact congr_arg (Quotient.mk' I) (trans (g'.comp_apply f r).symm (hfg ▸ f'.comp_apply g r))
#align ideal.comp_quotient_map_eq_of_comp_eq Ideal.comp_quotientMap_eq_of_comp_eq
-/

#print Ideal.quotientMapₐ /-
/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
def quotientMapₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
    A ⧸ I →ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A →+* B) hIJ with commutes' := fun r => by simp }
#align ideal.quotient_mapₐ Ideal.quotientMapₐ
-/

#print Ideal.quotient_map_mkₐ /-
@[simp]
theorem quotient_map_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) {x : A} :
    quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x) :=
  rfl
#align ideal.quotient_map_mkₐ Ideal.quotient_map_mkₐ
-/

#print Ideal.quotient_map_comp_mkₐ /-
theorem quotient_map_comp_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
    (quotientMapₐ J f H).comp (Quotient.mkₐ R₁ I) = (Quotient.mkₐ R₁ J).comp f :=
  AlgHom.ext fun x => by simp only [quotient_map_mkₐ, quotient.mkₐ_eq_mk, AlgHom.comp_apply]
#align ideal.quotient_map_comp_mkₐ Ideal.quotient_map_comp_mkₐ
-/

#print Ideal.quotientEquivAlg /-
/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where`J = f(I)`. -/
def quotientEquivAlg (I : Ideal A) (J : Ideal B) (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with commutes' := fun r => by simp }
#align ideal.quotient_equiv_alg Ideal.quotientEquivAlg
-/

#print Ideal.quotientAlgebra /-
instance (priority := 100) quotientAlgebra {I : Ideal A} [Algebra R A] :
    Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  (quotientMap I (algebraMap R A) (le_of_eq rfl)).toAlgebra
#align ideal.quotient_algebra Ideal.quotientAlgebra
-/

#print Ideal.algebraMap_quotient_injective /-
theorem algebraMap_quotient_injective {I : Ideal A} [Algebra R A] :
    Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)) :=
  by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := quotient.eq.mp hab
  rw [← RingHom.map_sub] at hab
  exact quotient.eq.mpr hab
#align ideal.algebra_map_quotient_injective Ideal.algebraMap_quotient_injective
-/

variable (R₁)

#print Ideal.quotientEquivAlgOfEq /-
/-- Quotienting by equal ideals gives equivalent algebras. -/
def quotientEquivAlgOfEq {I J : Ideal A} (h : I = J) : (A ⧸ I) ≃ₐ[R₁] A ⧸ J :=
  quotientEquivAlg I J AlgEquiv.refl <| h ▸ (map_id I).symm
#align ideal.quotient_equiv_alg_of_eq Ideal.quotientEquivAlgOfEq
-/

#print Ideal.quotientEquivAlgOfEq_mk /-
@[simp]
theorem quotientEquivAlgOfEq_mk {I J : Ideal A} (h : I = J) (x : A) :
    quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl
#align ideal.quotient_equiv_alg_of_eq_mk Ideal.quotientEquivAlgOfEq_mk
-/

#print Ideal.quotientEquivAlgOfEq_symm /-
@[simp]
theorem quotientEquivAlgOfEq_symm {I J : Ideal A} (h : I = J) :
    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by ext <;> rfl
#align ideal.quotient_equiv_alg_of_eq_symm Ideal.quotientEquivAlgOfEq_symm
-/

end QuotientAlgebra

end Ideal

namespace DoubleQuot

open Ideal

variable {R : Type u}

section

variable [CommRing R] (I J : Ideal R)

#print DoubleQuot.quotLeftToQuotSup /-
/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
def quotLeftToQuotSup : R ⧸ I →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.factor I (I ⊔ J) le_sup_left
#align double_quot.quot_left_to_quot_sup DoubleQuot.quotLeftToQuotSup
-/

#print DoubleQuot.ker_quotLeftToQuotSup /-
/-- The kernel of `quot_left_to_quot_sup` -/
theorem ker_quotLeftToQuotSup : (quotLeftToQuotSup I J).ker = J.map (Ideal.Quotient.mk I) := by
  simp only [mk_ker, sup_idem, sup_comm, quot_left_to_quot_sup, quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective I.Quotient.mk quotient.mk_surjective, ← sup_assoc]
#align double_quot.ker_quot_left_to_quot_sup DoubleQuot.ker_quotLeftToQuotSup
-/

#print DoubleQuot.quotQuotToQuotSup /-
/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quot_left_to_quot_sup` where `J'`
  is the image of `J` in `R/I`-/
def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quot_left_to_quot_sup I J)
    (ker_quot_left_to_quot_sup I J).symm.le
#align double_quot.quot_quot_to_quot_sup DoubleQuot.quotQuotToQuotSup
-/

#print DoubleQuot.quotQuotMk /-
/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
def quotQuotMk : R →+* (R ⧸ I) ⧸ J.map I.Quotient.mk :=
  (J.map I.Quotient.mk).Quotient.mk.comp I.Quotient.mk
#align double_quot.quot_quot_mk DoubleQuot.quotQuotMk
-/

#print DoubleQuot.ker_quotQuotMk /-
/-- The kernel of `quot_quot_mk` -/
theorem ker_quotQuotMk : (quotQuotMk I J).ker = I ⊔ J := by
  rw [RingHom.ker_eq_comap_bot, quot_quot_mk, ← comap_comap, ← RingHom.ker, mk_ker,
    comap_map_of_surjective (Ideal.Quotient.mk I) quotient.mk_surjective, ← RingHom.ker, mk_ker,
    sup_comm]
#align double_quot.ker_quot_quot_mk DoubleQuot.ker_quotQuotMk
-/

#print DoubleQuot.liftSupQuotQuotMk /-
/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J' `induced by `quot_quot_mk` -/
def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le
#align double_quot.lift_sup_quot_quot_mk DoubleQuot.liftSupQuotQuotMk
-/

#print DoubleQuot.quotQuotEquivQuotSup /-
/-- `quot_quot_to_quot_add` and `lift_sup_double_qot_mk` are inverse isomorphisms. In the case where
    `I ≤ J`, this is the Third Isomorphism Theorem (see `quot_quot_equiv_quot_of_le`)-/
def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J :=
  RingEquiv.ofHomInv (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J) (by ext z; rfl) (by ext z; rfl)
#align double_quot.quot_quot_equiv_quot_sup DoubleQuot.quotQuotEquivQuotSup
-/

#print DoubleQuot.quotQuotEquivQuotSup_quotQuotMk /-
@[simp]
theorem quotQuotEquivQuotSup_quotQuotMk (x : R) :
    quotQuotEquivQuotSup I J (quotQuotMk I J x) = Ideal.Quotient.mk (I ⊔ J) x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_quot_quot_mk DoubleQuot.quotQuotEquivQuotSup_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk /-
@[simp]
theorem quotQuotEquivQuotSup_symm_quotQuotMk (x : R) :
    (quotQuotEquivQuotSup I J).symm (Ideal.Quotient.mk (I ⊔ J) x) = quotQuotMk I J x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_symm_quot_quot_mk DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivComm /-
/-- The obvious isomorphism `(R/I)/J' → (R/J)/I' `   -/
def quotQuotEquivComm : (R ⧸ I) ⧸ J.map I.Quotient.mk ≃+* (R ⧸ J) ⧸ I.map J.Quotient.mk :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq sup_comm)).trans (quotQuotEquivQuotSup J I).symm
#align double_quot.quot_quot_equiv_comm DoubleQuot.quotQuotEquivComm
-/

#print DoubleQuot.quotQuotEquivComm_quotQuotMk /-
@[simp]
theorem quotQuotEquivComm_quotQuotMk (x : R) :
    quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x :=
  rfl
#align double_quot.quot_quot_equiv_comm_quot_quot_mk DoubleQuot.quotQuotEquivComm_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivComm_comp_quotQuotMk /-
@[simp]
theorem quotQuotEquivComm_comp_quotQuotMk :
    RingHom.comp (↑(quotQuotEquivComm I J)) (quotQuotMk I J) = quotQuotMk J I :=
  RingHom.ext <| quotQuotEquivComm_quotQuotMk I J
#align double_quot.quot_quot_equiv_comm_comp_quot_quot_mk DoubleQuot.quotQuotEquivComm_comp_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivComm_symm /-
@[simp]
theorem quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm J I :=
  rfl
#align double_quot.quot_quot_equiv_comm_symm DoubleQuot.quotQuotEquivComm_symm
-/

variable {I J}

#print DoubleQuot.quotQuotEquivQuotOfLE /-
/-- **The Third Isomorphism theorem** for rings. See `quot_quot_equiv_quot_sup` for a version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLE (h : I ≤ J) : (R ⧸ I) ⧸ J.map I.Quotient.mk ≃+* R ⧸ J :=
  (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)
#align double_quot.quot_quot_equiv_quot_of_le DoubleQuot.quotQuotEquivQuotOfLE
-/

#print DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk /-
@[simp]
theorem quotQuotEquivQuotOfLE_quotQuotMk (x : R) (h : I ≤ J) :
    quotQuotEquivQuotOfLE h (quotQuotMk I J x) = J.Quotient.mk x :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivQuotOfLE_symm_mk /-
@[simp]
theorem quotQuotEquivQuotOfLE_symm_mk (x : R) (h : I ≤ J) :
    (quotQuotEquivQuotOfLE h).symm (J.Quotient.mk x) = quotQuotMk I J x :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_mk DoubleQuot.quotQuotEquivQuotOfLE_symm_mk
-/

#print DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk /-
theorem quotQuotEquivQuotOfLE_comp_quotQuotMk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h)) (quotQuotMk I J) = J.Quotient.mk := by ext <;> rfl
#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk /-
theorem quotQuotEquivQuotOfLE_symm_comp_mk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h).symm) J.Quotient.mk = quotQuotMk I J := by ext <;> rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mk DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk
-/

end

section Algebra

#print DoubleQuot.quotQuotEquivComm_mk_mk /-
@[simp]
theorem quotQuotEquivComm_mk_mk [CommRing R] (I J : Ideal R) (x : R) :
    quotQuotEquivComm I J (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = algebraMap R _ x :=
  rfl
#align double_quot.quot_quot_equiv_comm_mk_mk DoubleQuot.quotQuotEquivComm_mk_mk
-/

variable [CommSemiring R] {A : Type v} [CommRing A] [Algebra R A] (I J : Ideal A)

#print DoubleQuot.quotQuotEquivQuotSup_quot_quot_algebraMap /-
@[simp]
theorem quotQuotEquivQuotSup_quot_quot_algebraMap (x : R) :
    DoubleQuot.quotQuotEquivQuotSup I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_quot_quot_algebra_map DoubleQuot.quotQuotEquivQuotSup_quot_quot_algebraMap
-/

#print DoubleQuot.quotQuotEquivComm_algebraMap /-
@[simp]
theorem quotQuotEquivComm_algebraMap (x : R) :
    quotQuotEquivComm I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl
#align double_quot.quot_quot_equiv_comm_algebra_map DoubleQuot.quotQuotEquivComm_algebraMap
-/

end Algebra

section AlgebraQuotient

variable (R) {A : Type _} [CommSemiring R] [CommRing A] [Algebra R A]

variable (I J : Ideal A)

#print DoubleQuot.quotLeftToQuotSupₐ /-
/-- The natural algebra homomorphism `A / I → A / (I ⊔ J)`. -/
def quotLeftToQuotSupₐ : A ⧸ I →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotLeftToQuotSup I J) rfl (map_mul _) rfl (map_add _) fun _ => rfl
#align double_quot.quot_left_to_quot_supₐ DoubleQuot.quotLeftToQuotSupₐ
-/

#print DoubleQuot.quotLeftToQuotSupₐ_toRingHom /-
@[simp]
theorem quotLeftToQuotSupₐ_toRingHom :
    (quotLeftToQuotSupₐ R I J).toRingHom = quotLeftToQuotSup I J :=
  rfl
#align double_quot.quot_left_to_quot_supₐ_to_ring_hom DoubleQuot.quotLeftToQuotSupₐ_toRingHom
-/

#print DoubleQuot.coe_quotLeftToQuotSupₐ /-
@[simp]
theorem coe_quotLeftToQuotSupₐ : ⇑(quotLeftToQuotSupₐ R I J) = quotLeftToQuotSup I J :=
  rfl
#align double_quot.coe_quot_left_to_quot_supₐ DoubleQuot.coe_quotLeftToQuotSupₐ
-/

#print DoubleQuot.quotQuotToQuotSupₐ /-
/-- The algebra homomorphism `(A / I) / J' -> A / (I ⊔ J) induced by `quot_left_to_quot_sup`,
  where `J'` is the projection of `J` in `A / I`. -/
def quotQuotToQuotSupₐ : (A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R) →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotQuotToQuotSup I J) rfl (map_mul _) rfl (map_add _) fun _ => rfl
#align double_quot.quot_quot_to_quot_supₐ DoubleQuot.quotQuotToQuotSupₐ
-/

#print DoubleQuot.quotQuotToQuotSupₐ_toRingHom /-
@[simp]
theorem quotQuotToQuotSupₐ_toRingHom :
    (quotQuotToQuotSupₐ R I J).toRingHom = quotQuotToQuotSup I J :=
  rfl
#align double_quot.quot_quot_to_quot_supₐ_to_ring_hom DoubleQuot.quotQuotToQuotSupₐ_toRingHom
-/

#print DoubleQuot.coe_quotQuotToQuotSupₐ /-
@[simp]
theorem coe_quotQuotToQuotSupₐ : ⇑(quotQuotToQuotSupₐ R I J) = quotQuotToQuotSup I J :=
  rfl
#align double_quot.coe_quot_quot_to_quot_supₐ DoubleQuot.coe_quotQuotToQuotSupₐ
-/

#print DoubleQuot.quotQuotMkₐ /-
/-- The composition of the algebra homomorphisms `A → (A / I)` and `(A / I) → (A / I) / J'`,
  where `J'` is the projection `J` in `A / I`. -/
def quotQuotMkₐ : A →ₐ[R] (A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R) :=
  AlgHom.mk (quotQuotMk I J) rfl (map_mul _) rfl (map_add _) fun _ => rfl
#align double_quot.quot_quot_mkₐ DoubleQuot.quotQuotMkₐ
-/

#print DoubleQuot.quotQuotMkₐ_toRingHom /-
@[simp]
theorem quotQuotMkₐ_toRingHom : (quotQuotMkₐ R I J).toRingHom = quotQuotMk I J :=
  rfl
#align double_quot.quot_quot_mkₐ_to_ring_hom DoubleQuot.quotQuotMkₐ_toRingHom
-/

#print DoubleQuot.coe_quotQuotMkₐ /-
@[simp]
theorem coe_quotQuotMkₐ : ⇑(quotQuotMkₐ R I J) = quotQuotMk I J :=
  rfl
#align double_quot.coe_quot_quot_mkₐ DoubleQuot.coe_quotQuotMkₐ
-/

#print DoubleQuot.liftSupQuotQuotMkₐ /-
/-- The injective algebra homomorphism `A / (I ⊔ J) → (A / I) / J'`induced by `quot_quot_mk`,
  where `J'` is the projection `J` in `A / I`. -/
def liftSupQuotQuotMkₐ (I J : Ideal A) : A ⧸ I ⊔ J →ₐ[R] (A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R) :=
  AlgHom.mk (liftSupQuotQuotMk I J) rfl (map_mul _) rfl (map_add _) fun _ => rfl
#align double_quot.lift_sup_quot_quot_mkₐ DoubleQuot.liftSupQuotQuotMkₐ
-/

#print DoubleQuot.liftSupQuotQuotMkₐ_toRingHom /-
@[simp]
theorem liftSupQuotQuotMkₐ_toRingHom :
    (liftSupQuotQuotMkₐ R I J).toRingHom = liftSupQuotQuotMk I J :=
  rfl
#align double_quot.lift_sup_quot_quot_mkₐ_to_ring_hom DoubleQuot.liftSupQuotQuotMkₐ_toRingHom
-/

#print DoubleQuot.coe_liftSupQuotQuotMkₐ /-
@[simp]
theorem coe_liftSupQuotQuotMkₐ : ⇑(liftSupQuotQuotMkₐ R I J) = liftSupQuotQuotMk I J :=
  rfl
#align double_quot.coe_lift_sup_quot_quot_mkₐ DoubleQuot.coe_liftSupQuotQuotMkₐ
-/

#print DoubleQuot.quotQuotEquivQuotSupₐ /-
/-- `quot_quot_to_quot_add` and `lift_sup_quot_quot_mk` are inverse isomorphisms. In the case where
    `I ≤ J`, this is the Third Isomorphism Theorem (see `quot_quot_equiv_quot_of_le`). -/
def quotQuotEquivQuotSupₐ : ((A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R)) ≃ₐ[R] A ⧸ I ⊔ J :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivQuotSup I J) fun _ => rfl
#align double_quot.quot_quot_equiv_quot_supₐ DoubleQuot.quotQuotEquivQuotSupₐ
-/

#print DoubleQuot.quotQuotEquivQuotSupₐ_toRingEquiv /-
@[simp]
theorem quotQuotEquivQuotSupₐ_toRingEquiv :
    (quotQuotEquivQuotSupₐ R I J).toRingEquiv = quotQuotEquivQuotSup I J :=
  rfl
#align double_quot.quot_quot_equiv_quot_supₐ_to_ring_equiv DoubleQuot.quotQuotEquivQuotSupₐ_toRingEquiv
-/

#print DoubleQuot.coe_quotQuotEquivQuotSupₐ /-
@[simp]
theorem coe_quotQuotEquivQuotSupₐ : ⇑(quotQuotEquivQuotSupₐ R I J) = quotQuotEquivQuotSup I J :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_supₐ DoubleQuot.coe_quotQuotEquivQuotSupₐ
-/

#print DoubleQuot.quotQuotEquivQuotSupₐ_symm_toRingEquiv /-
@[simp]
theorem quotQuotEquivQuotSupₐ_symm_toRingEquiv :
    (quotQuotEquivQuotSupₐ R I J).symm.toRingEquiv = (quotQuotEquivQuotSup I J).symm :=
  rfl
#align double_quot.quot_quot_equiv_quot_supₐ_symm_to_ring_equiv DoubleQuot.quotQuotEquivQuotSupₐ_symm_toRingEquiv
-/

#print DoubleQuot.coe_quotQuotEquivQuotSupₐ_symm /-
@[simp]
theorem coe_quotQuotEquivQuotSupₐ_symm :
    ⇑(quotQuotEquivQuotSupₐ R I J).symm = (quotQuotEquivQuotSup I J).symm :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_supₐ_symm DoubleQuot.coe_quotQuotEquivQuotSupₐ_symm
-/

#print DoubleQuot.quotQuotEquivCommₐ /-
/-- The natural algebra isomorphism `(A / I) / J' → (A / J) / I'`,
  where `J'` (resp. `I'`) is the projection of `J` in `A / I` (resp. `I` in `A / J`). -/
def quotQuotEquivCommₐ :
    ((A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R)) ≃ₐ[R] (A ⧸ J) ⧸ I.map (J.Quotient.mkₐ R) :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivComm I J) fun _ => rfl
#align double_quot.quot_quot_equiv_commₐ DoubleQuot.quotQuotEquivCommₐ
-/

#print DoubleQuot.quotQuotEquivCommₐ_toRingEquiv /-
@[simp]
theorem quotQuotEquivCommₐ_toRingEquiv :
    (quotQuotEquivCommₐ R I J).toRingEquiv = quotQuotEquivComm I J :=
  rfl
#align double_quot.quot_quot_equiv_commₐ_to_ring_equiv DoubleQuot.quotQuotEquivCommₐ_toRingEquiv
-/

#print DoubleQuot.coe_quotQuotEquivCommₐ /-
@[simp]
theorem coe_quotQuotEquivCommₐ : ⇑(quotQuotEquivCommₐ R I J) = quotQuotEquivComm I J :=
  rfl
#align double_quot.coe_quot_quot_equiv_commₐ DoubleQuot.coe_quotQuotEquivCommₐ
-/

#print DoubleQuot.quotQuotEquivComm_symmₐ /-
@[simp]
theorem quotQuotEquivComm_symmₐ : (quotQuotEquivCommₐ R I J).symm = quotQuotEquivCommₐ R J I :=
  -- TODO: should be `rfl` but times out
    AlgEquiv.ext
    fun x => (DFunLike.congr_fun (quotQuotEquivComm_symm I J) x : _)
#align double_quot.quot_quot_equiv_comm_symmₐ DoubleQuot.quotQuotEquivComm_symmₐ
-/

#print DoubleQuot.quotQuotEquivComm_comp_quotQuotMkₐ /-
@[simp]
theorem quotQuotEquivComm_comp_quotQuotMkₐ :
    AlgHom.comp (↑(quotQuotEquivCommₐ R I J)) (quotQuotMkₐ R I J) = quotQuotMkₐ R J I :=
  AlgHom.ext <| quotQuotEquivComm_quotQuotMk I J
#align double_quot.quot_quot_equiv_comm_comp_quot_quot_mkₐ DoubleQuot.quotQuotEquivComm_comp_quotQuotMkₐ
-/

variable {I J}

#print DoubleQuot.quotQuotEquivQuotOfLEₐ /-
/-- The **third isomoprhism theorem** for rings. See `quot_quot_equiv_quot_sup` for version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLEₐ (h : I ≤ J) : ((A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R)) ≃ₐ[R] A ⧸ J :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivQuotOfLE h) fun _ => rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ DoubleQuot.quotQuotEquivQuotOfLEₐ
-/

#print DoubleQuot.quotQuotEquivQuotOfLEₐ_toRingEquiv /-
@[simp]
theorem quotQuotEquivQuotOfLEₐ_toRingEquiv (h : I ≤ J) :
    (quotQuotEquivQuotOfLEₐ R h).toRingEquiv = quotQuotEquivQuotOfLE h :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ_to_ring_equiv DoubleQuot.quotQuotEquivQuotOfLEₐ_toRingEquiv
-/

#print DoubleQuot.coe_quotQuotEquivQuotOfLEₐ /-
@[simp]
theorem coe_quotQuotEquivQuotOfLEₐ (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h) = quotQuotEquivQuotOfLE h :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_of_leₐ DoubleQuot.coe_quotQuotEquivQuotOfLEₐ
-/

#print DoubleQuot.quotQuotEquivQuotOfLEₐ_symm_toRingEquiv /-
@[simp]
theorem quotQuotEquivQuotOfLEₐ_symm_toRingEquiv (h : I ≤ J) :
    (quotQuotEquivQuotOfLEₐ R h).symm.toRingEquiv = (quotQuotEquivQuotOfLE h).symm :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ_symm_to_ring_equiv DoubleQuot.quotQuotEquivQuotOfLEₐ_symm_toRingEquiv
-/

#print DoubleQuot.coe_quotQuotEquivQuotOfLEₐ_symm /-
@[simp]
theorem coe_quotQuotEquivQuotOfLEₐ_symm (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h).symm = (quotQuotEquivQuotOfLE h).symm :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_of_leₐ_symm DoubleQuot.coe_quotQuotEquivQuotOfLEₐ_symm
-/

#print DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMkₐ /-
@[simp]
theorem quotQuotEquivQuotOfLE_comp_quotQuotMkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h)) (quotQuotMkₐ R I J) = J.Quotient.mkₐ R :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mkₐ DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMkₐ
-/

#print DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mkₐ /-
@[simp]
theorem quotQuotEquivQuotOfLE_symm_comp_mkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h).symm) (J.Quotient.mkₐ R) = quotQuotMkₐ R I J :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mkₐ DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mkₐ
-/

end AlgebraQuotient

end DoubleQuot

