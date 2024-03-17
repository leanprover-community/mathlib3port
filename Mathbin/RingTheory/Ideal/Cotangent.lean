/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import RingTheory.Ideal.Operations
import Algebra.Module.Torsion
import Algebra.Ring.Idempotents
import LinearAlgebra.FiniteDimensional
import RingTheory.Ideal.LocalRing

#align_import ring_theory.ideal.cotangent from "leanprover-community/mathlib"@"4b92a463033b5587bb011657e25e4710bfca7364"

/-!
# The module `I ⧸ I ^ 2`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `ideal.cotangent_equiv_ideal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/


namespace Ideal

variable {R S S' : Type _} [CommRing R] [CommSemiring S] [Algebra S R]

variable [CommSemiring S'] [Algebra S' R] [Algebra S S'] [IsScalarTower S S' R] (I : Ideal R)

/- ./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler module[module] «expr ⧸ »(R, I) -/
#print Ideal.Cotangent /-
/-- `I ⧸ I ^ 2` as a quotient of `I`. -/
def Cotangent : Type _ :=
  I ⧸ (I • ⊤ : Submodule R I)
deriving AddCommGroup,
  ./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler module[module] «expr ⧸ »(R, I)
#align ideal.cotangent Ideal.Cotangent
-/

instance : Inhabited I.Cotangent :=
  ⟨0⟩

#print Ideal.Cotangent.moduleOfTower /-
instance Cotangent.moduleOfTower : Module S I.Cotangent :=
  Submodule.Quotient.module' _
#align ideal.cotangent.module_of_tower Ideal.Cotangent.moduleOfTower
-/

instance : IsScalarTower S S' I.Cotangent :=
  Submodule.Quotient.isScalarTower _ _

instance [IsNoetherian R I] : IsNoetherian R I.Cotangent :=
  Submodule.Quotient.isNoetherian _

#print Ideal.toCotangent /-
/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps (config := lemmasOnly) apply]
def toCotangent : I →ₗ[R] I.Cotangent :=
  Submodule.mkQ _
#align ideal.to_cotangent Ideal.toCotangent
-/

#print Ideal.map_toCotangent_ker /-
theorem map_toCotangent_ker : I.toCotangent.ker.map I.Subtype = I ^ 2 := by
  simp [Ideal.toCotangent, Submodule.map_smul'', pow_two]
#align ideal.map_to_cotangent_ker Ideal.map_toCotangent_ker
-/

#print Ideal.mem_toCotangent_ker /-
theorem mem_toCotangent_ker {x : I} : x ∈ I.toCotangent.ker ↔ (x : R) ∈ I ^ 2 :=
  by
  rw [← I.map_to_cotangent_ker]
  simp
#align ideal.mem_to_cotangent_ker Ideal.mem_toCotangent_ker
-/

#print Ideal.toCotangent_eq /-
theorem toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) ∈ I ^ 2 :=
  by
  rw [← sub_eq_zero, ← map_sub]
  exact I.mem_to_cotangent_ker
#align ideal.to_cotangent_eq Ideal.toCotangent_eq
-/

#print Ideal.toCotangent_eq_zero /-
theorem toCotangent_eq_zero (x : I) : I.toCotangent x = 0 ↔ (x : R) ∈ I ^ 2 :=
  I.mem_toCotangent_ker
#align ideal.to_cotangent_eq_zero Ideal.toCotangent_eq_zero
-/

#print Ideal.toCotangent_surjective /-
theorem toCotangent_surjective : Function.Surjective I.toCotangent :=
  Submodule.mkQ_surjective _
#align ideal.to_cotangent_surjective Ideal.toCotangent_surjective
-/

#print Ideal.toCotangent_range /-
theorem toCotangent_range : I.toCotangent.range = ⊤ :=
  Submodule.range_mkQ _
#align ideal.to_cotangent_range Ideal.toCotangent_range
-/

#print Ideal.cotangent_subsingleton_iff /-
theorem cotangent_subsingleton_iff : Subsingleton I.Cotangent ↔ IsIdempotentElem I :=
  by
  constructor
  · intro H
    refine' (pow_two I).symm.trans (le_antisymm (Ideal.pow_le_self two_ne_zero) _)
    exact fun x hx => (I.to_cotangent_eq_zero ⟨x, hx⟩).mp (Subsingleton.elim _ _)
  ·
    exact fun e =>
      ⟨fun x y =>
        Quotient.inductionOn₂' x y fun x y =>
          I.to_cotangent_eq.mpr <| ((pow_two I).trans e).symm ▸ I.sub_mem x.Prop y.Prop⟩
#align ideal.cotangent_subsingleton_iff Ideal.cotangent_subsingleton_iff
-/

#print Ideal.cotangentToQuotientSquare /-
/-- The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`. -/
def cotangentToQuotientSquare : I.Cotangent →ₗ[R] R ⧸ I ^ 2 :=
  Submodule.mapQ (I • ⊤) (I ^ 2) I.Subtype
    (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top,
        Submodule.range_subtype, smul_eq_mul, pow_two]
      exact rfl.le)
#align ideal.cotangent_to_quotient_square Ideal.cotangentToQuotientSquare
-/

#print Ideal.to_quotient_square_comp_toCotangent /-
theorem to_quotient_square_comp_toCotangent :
    I.cotangentToQuotientSquare.comp I.toCotangent = (I ^ 2).mkQ.comp (Submodule.subtype I) :=
  LinearMap.ext fun _ => rfl
#align ideal.to_quotient_square_comp_to_cotangent Ideal.to_quotient_square_comp_toCotangent
-/

#print Ideal.toCotangent_to_quotient_square /-
@[simp]
theorem toCotangent_to_quotient_square (x : I) :
    I.cotangentToQuotientSquare (I.toCotangent x) = (I ^ 2).mkQ x :=
  rfl
#align ideal.to_cotangent_to_quotient_square Ideal.toCotangent_to_quotient_square
-/

#print Ideal.cotangentIdeal /-
/-- `I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`. -/
def cotangentIdeal (I : Ideal R) : Ideal (R ⧸ I ^ 2) :=
  by
  haveI : @RingHomSurjective R (R ⧸ I ^ 2) _ _ _ := ⟨Ideal.Quotient.mk_surjective⟩
  let rq := (I ^ 2).Quotient.mk
  exact Submodule.map rq.to_semilinear_map I
#align ideal.cotangent_ideal Ideal.cotangentIdeal
-/

#print Ideal.cotangentIdeal_square /-
theorem cotangentIdeal_square (I : Ideal R) : I.cotangentIdeal ^ 2 = ⊥ :=
  by
  rw [eq_bot_iff, pow_two I.cotangent_ideal, ← smul_eq_mul]
  intro x hx
  apply Submodule.smul_induction_on hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; apply (Submodule.Quotient.eq _).mpr _
    rw [sub_zero, pow_two]; exact Ideal.mul_mem_mul hx hy
  · intro x y hx hy; exact add_mem hx hy
#align ideal.cotangent_ideal_square Ideal.cotangentIdeal_square
-/

#print Ideal.to_quotient_square_range /-
theorem to_quotient_square_range :
    I.cotangentToQuotientSquare.range = I.cotangentIdeal.restrictScalars R :=
  by
  trans (I.cotangent_to_quotient_square.comp I.to_cotangent).range
  · rw [LinearMap.range_comp, I.to_cotangent_range, Submodule.map_top]
  · rw [to_quotient_square_comp_to_cotangent, LinearMap.range_comp, I.range_subtype]; ext; rfl
#align ideal.to_quotient_square_range Ideal.to_quotient_square_range
-/

#print Ideal.cotangentEquivIdeal /-
/-- The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of `I` or the
ideal of `R / I ^ 2`. -/
noncomputable def cotangentEquivIdeal : I.Cotangent ≃ₗ[R] I.cotangentIdeal :=
  by
  refine'
    {
      I.cotangent_to_quotient_square.cod_restrict (I.cotangent_ideal.restrict_scalars R) fun x => by
        rw [← to_quotient_square_range]; exact LinearMap.mem_range_self _ _,
      Equiv.ofBijective _ ⟨_, _⟩ with }
  · rintro x y e
    replace e := congr_arg Subtype.val e
    obtain ⟨x, rfl⟩ := I.to_cotangent_surjective x
    obtain ⟨y, rfl⟩ := I.to_cotangent_surjective y
    rw [I.to_cotangent_eq]
    dsimp only [to_cotangent_to_quotient_square, Submodule.mkQ_apply] at e
    rwa [Submodule.Quotient.eq] at e
  · rintro ⟨_, x, hx, rfl⟩
    refine' ⟨I.to_cotangent ⟨x, hx⟩, Subtype.ext rfl⟩
#align ideal.cotangent_equiv_ideal Ideal.cotangentEquivIdeal
-/

#print Ideal.cotangentEquivIdeal_apply /-
@[simp, nolint simp_nf]
theorem cotangentEquivIdeal_apply (x : I.Cotangent) :
    ↑(I.cotangentEquivIdeal x) = I.cotangentToQuotientSquare x :=
  rfl
#align ideal.cotangent_equiv_ideal_apply Ideal.cotangentEquivIdeal_apply
-/

#print Ideal.cotangentEquivIdeal_symm_apply /-
theorem cotangentEquivIdeal_symm_apply (x : R) (hx : x ∈ I) :
    I.cotangentEquivIdeal.symm ⟨(I ^ 2).mkQ x, Submodule.mem_map_of_mem hx⟩ =
      I.toCotangent ⟨x, hx⟩ :=
  by
  apply I.cotangent_equiv_ideal.injective
  rw [I.cotangent_equiv_ideal.apply_symm_apply]
  ext
  rfl
#align ideal.cotangent_equiv_ideal_symm_apply Ideal.cotangentEquivIdeal_symm_apply
-/

variable {A B : Type _} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

#print AlgHom.kerSquareLift /-
/-- The lift of `f : A →ₐ[R] B` to `A ⧸ J ^ 2 →ₐ[R] B` with `J` being the kernel of `f`. -/
def AlgHom.kerSquareLift (f : A →ₐ[R] B) : A ⧸ f.toRingHom.ker ^ 2 →ₐ[R] B :=
  by
  refine' { Ideal.Quotient.lift (f.to_ring_hom.ker ^ 2) f.to_ring_hom _ with commutes' := _ }
  · intro a ha; exact Ideal.pow_le_self two_ne_zero ha
  · intro r;
    rw [IsScalarTower.algebraMap_apply R A, RingHom.toFun_eq_coe, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.lift_mk]
    exact f.map_algebra_map r
#align alg_hom.ker_square_lift AlgHom.kerSquareLift
-/

#print AlgHom.ker_kerSquareLift /-
theorem AlgHom.ker_kerSquareLift (f : A →ₐ[R] B) :
    f.kerSquareLift.toRingHom.ker = f.toRingHom.ker.cotangentIdeal :=
  by
  apply le_antisymm
  · intro x hx; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hx
#align alg_hom.ker_ker_sqare_lift AlgHom.ker_kerSquareLift
-/

#print Ideal.quotCotangent /-
/-- The quotient ring of `I ⧸ I ^ 2` is `R ⧸ I`. -/
def quotCotangent : (R ⧸ I ^ 2) ⧸ I.cotangentIdeal ≃+* R ⧸ I :=
  by
  refine' (Ideal.quotEquivOfEq (Ideal.map_eq_submodule_map _ _).symm).trans _
  refine' (DoubleQuot.quotQuotEquivQuotSup _ _).trans _
  exact Ideal.quotEquivOfEq (sup_eq_right.mpr <| Ideal.pow_le_self two_ne_zero)
#align ideal.quot_cotangent Ideal.quotCotangent
-/

end Ideal

namespace LocalRing

variable (R : Type _) [CommRing R] [LocalRing R]

#print LocalRing.CotangentSpace /-
/-- The `A ⧸ I`-vector space `I ⧸ I ^ 2`. -/
@[reducible]
def CotangentSpace : Type _ :=
  (maximalIdeal R).Cotangent
#align local_ring.cotangent_space LocalRing.CotangentSpace
-/

instance : Module (ResidueField R) (CotangentSpace R) :=
  Ideal.Cotangent.module _

instance : IsScalarTower R (ResidueField R) (CotangentSpace R) :=
  Module.IsTorsionBySet.isScalarTower _

instance [IsNoetherianRing R] : FiniteDimensional (ResidueField R) (CotangentSpace R) :=
  Module.Finite.of_restrictScalars_finite R _ _

end LocalRing

