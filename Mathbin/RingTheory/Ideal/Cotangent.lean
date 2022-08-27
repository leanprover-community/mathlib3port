/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.Algebra.Module.Torsion
import Mathbin.Algebra.Ring.Idempotents
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.RingTheory.Nakayama

/-!
# The module `I ⧸ I ^ 2`

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `ideal.cotangent_equiv_ideal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/


namespace Ideal

variable {R S S' : Type _} [CommRingₓ R] [CommSemiringₓ S] [Algebra S R]

variable [CommSemiringₓ S'] [Algebra S' R] [Algebra S S'] [IsScalarTower S S' R] (I : Ideal R)

-- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] «expr ⧸ »(R, I)
/-- `I ⧸ I ^ 2` as a quotient of `I`. -/
def Cotangent : Type _ :=
  I ⧸ (I • ⊤ : Submodule R I)deriving AddCommGroupₓ,
  ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] «expr ⧸ »(R, I)

instance : Inhabited I.Cotangent :=
  ⟨0⟩

instance Cotangent.moduleOfTower : Module S I.Cotangent :=
  Submodule.Quotient.module' _

instance : IsScalarTower S S' I.Cotangent := by
  delta' cotangent
  constructor
  intro s s' x
  rw [← @IsScalarTower.algebra_map_smul S' R, ← @IsScalarTower.algebra_map_smul S' R, ← smul_assoc, ←
    IsScalarTower.to_alg_hom_apply S S' R, map_smul]
  rfl

instance [IsNoetherian R I] : IsNoetherian R I.Cotangent := by
  delta' cotangent
  infer_instance

/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps (config := lemmasOnly) apply]
def toCotangent : I →ₗ[R] I.Cotangent :=
  Submodule.mkq _

theorem map_to_cotangent_ker : I.toCotangent.ker.map I.Subtype = I ^ 2 := by
  simp [Ideal.toCotangent, Submodule.map_smul'', pow_two]

theorem mem_to_cotangent_ker {x : I} : x ∈ I.toCotangent.ker ↔ (x : R) ∈ I ^ 2 := by
  rw [← I.map_to_cotangent_ker]
  simp

theorem to_cotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) ∈ I ^ 2 := by
  rw [← sub_eq_zero, ← map_sub]
  exact I.mem_to_cotangent_ker

theorem to_cotangent_eq_zero (x : I) : I.toCotangent x = 0 ↔ (x : R) ∈ I ^ 2 :=
  I.mem_to_cotangent_ker

theorem to_cotangent_surjective : Function.Surjective I.toCotangent :=
  Submodule.mkq_surjective _

theorem to_cotangent_range : I.toCotangent.range = ⊤ :=
  Submodule.range_mkq _

theorem cotangent_subsingleton_iff : Subsingleton I.Cotangent ↔ IsIdempotentElem I := by
  constructor
  · intro H
    refine' (pow_two I).symm.trans (le_antisymmₓ (Ideal.pow_le_self two_ne_zero) _)
    exact fun x hx => (I.to_cotangent_eq_zero ⟨x, hx⟩).mp (Subsingleton.elimₓ _ _)
    
  · exact fun e =>
      ⟨fun x y =>
        (Quotientₓ.induction_on₂' x y) fun x y =>
          I.to_cotangent_eq.mpr <| ((pow_two I).trans e).symm ▸ I.sub_mem x.Prop y.Prop⟩
    

/-- The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`. -/
def cotangentToQuotientSquare : I.Cotangent →ₗ[R] R ⧸ I ^ 2 :=
  Submodule.mapq (I • ⊤) (I ^ 2) I.Subtype
    (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
        smul_eq_mul, pow_two]
      exact rfl.le)

theorem to_quotient_square_comp_to_cotangent :
    I.cotangentToQuotientSquare.comp I.toCotangent = (I ^ 2).mkq.comp (Submodule.subtype I) :=
  LinearMap.ext fun _ => rfl

@[simp]
theorem to_cotangent_to_quotient_square (x : I) : I.cotangentToQuotientSquare (I.toCotangent x) = (I ^ 2).mkq x :=
  rfl

/-- `I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`. -/
def cotangentIdeal (I : Ideal R) : Ideal (R ⧸ I ^ 2) := by
  haveI : @RingHomSurjective R (R ⧸ I ^ 2) _ _ _ := ⟨Ideal.Quotient.mk_surjective⟩
  let rq := I ^ 2
  exact Submodule.map rq.to_semilinear_map I

theorem cotangent_ideal_square (I : Ideal R) : I.cotangentIdeal ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two I.cotangent_ideal, ← smul_eq_mul]
  intro x hx
  apply Submodule.smul_induction_on hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    apply (Submodule.Quotient.eq _).mpr _
    rw [sub_zero, pow_two]
    exact Ideal.mul_mem_mul hx hy
    
  · intro x y hx hy
    exact add_mem hx hy
    

theorem to_quotient_square_range : I.cotangentToQuotientSquare.range = I.cotangentIdeal.restrictScalars R := by
  trans (I.cotangent_to_quotient_square.comp I.to_cotangent).range
  · rw [LinearMap.range_comp, I.to_cotangent_range, Submodule.map_top]
    
  · rw [to_quotient_square_comp_to_cotangent, LinearMap.range_comp, I.range_subtype]
    ext
    rfl
    

/-- The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of `I` or the
ideal of `R / I ^ 2`. -/
noncomputable def cotangentEquivIdeal : I.Cotangent ≃ₗ[R] I.cotangentIdeal := by
  refine'
    { I.cotangent_to_quotient_square.cod_restrict (I.cotangent_ideal.restrict_scalars R) fun x => by
        rw [← to_quotient_square_range]
        exact LinearMap.mem_range_self _ _,
      Equivₓ.ofBijective _ ⟨_, _⟩ with }
  · rintro x y e
    replace e := congr_arg Subtype.val e
    obtain ⟨x, rfl⟩ := I.to_cotangent_surjective x
    obtain ⟨y, rfl⟩ := I.to_cotangent_surjective y
    rw [I.to_cotangent_eq]
    dsimp' only [to_cotangent_to_quotient_square, Submodule.mkq_apply]  at e
    rwa [Submodule.Quotient.eq] at e
    
  · rintro ⟨_, x, hx, rfl⟩
    refine' ⟨I.to_cotangent ⟨x, hx⟩, Subtype.ext rfl⟩
    

@[simp, nolint simp_nf]
theorem cotangent_equiv_ideal_apply (x : I.Cotangent) : ↑(I.cotangentEquivIdeal x) = I.cotangentToQuotientSquare x :=
  rfl

theorem cotangent_equiv_ideal_symm_apply (x : R) (hx : x ∈ I) :
    I.cotangentEquivIdeal.symm ⟨(I ^ 2).mkq x, Submodule.mem_map_of_mem hx⟩ = I.toCotangent ⟨x, hx⟩ := by
  apply I.cotangent_equiv_ideal.injective
  rw [I.cotangent_equiv_ideal.apply_symm_apply]
  ext
  rfl

variable {A B : Type _} [CommRingₓ A] [CommRingₓ B] [Algebra R A] [Algebra R B]

/-- The lift of `f : A →ₐ[R] B` to `A ⧸ J ^ 2 →ₐ[R] B` with `J` being the kernel of `f`. -/
def _root_.alg_hom.ker_square_lift (f : A →ₐ[R] B) : A ⧸ f.toRingHom.ker ^ 2 →ₐ[R] B := by
  refine' { Ideal.Quotient.lift (f.to_ring_hom.ker ^ 2) f.to_ring_hom _ with commutes' := _ }
  · intro a ha
    exact Ideal.pow_le_self two_ne_zero ha
    
  · intro r
    rw [IsScalarTower.algebra_map_apply R A, RingHom.to_fun_eq_coe, Ideal.Quotient.algebra_map_eq,
      Ideal.Quotient.lift_mk]
    exact f.map_algebra_map r
    

theorem _root_.alg_hom.ker_ker_sqare_lift (f : A →ₐ[R] B) :
    f.kerSquareLift.toRingHom.ker = f.toRingHom.ker.cotangentIdeal := by
  apply le_antisymmₓ
  · intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, hx, rfl⟩
    
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
    

end Ideal

namespace LocalRing

variable (R : Type _) [CommRingₓ R] [LocalRing R]

/-- The `A ⧸ I`-vector space `I ⧸ I ^ 2`. -/
@[reducible]
def CotangentSpace : Type _ :=
  (maximalIdeal R).Cotangent

instance : Module (ResidueField R) (CotangentSpace R) :=
  Ideal.Cotangent.module _

instance : IsScalarTower R (ResidueField R) (CotangentSpace R) :=
  Module.IsTorsionBySet.is_scalar_tower _

instance [IsNoetherianRing R] : FiniteDimensional (ResidueField R) (CotangentSpace R) :=
  Module.Finite.of_restrict_scalars_finite R _ _

end LocalRing

