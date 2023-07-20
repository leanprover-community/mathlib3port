/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Algebra.Basic
import Mathbin.Algebra.Category.Module.Limits
import Mathbin.Algebra.Category.Ring.Limits

#align_import algebra.category.Algebra.limits from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# The category of R-algebras has all limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v w u

-- `u` is determined by the ring, so can come last
noncomputable section

namespace AlgebraCat

variable {R : Type u} [CommRing R]

variable {J : Type v} [SmallCategory J]

#print AlgebraCat.semiringObj /-
instance semiringObj (F : J ⥤ AlgebraCat.{max v w} R) (j) :
    Semiring ((F ⋙ forget (AlgebraCat R)).obj j) := by change Semiring (F.obj j); infer_instance
#align Algebra.semiring_obj AlgebraCat.semiringObj
-/

#print AlgebraCat.algebraObj /-
instance algebraObj (F : J ⥤ AlgebraCat.{max v w} R) (j) :
    Algebra R ((F ⋙ forget (AlgebraCat R)).obj j) := by change Algebra R (F.obj j); infer_instance
#align Algebra.algebra_obj AlgebraCat.algebraObj
-/

#print AlgebraCat.sectionsSubalgebra /-
/-- The flat sections of a functor into `Algebra R` form a submodule of all sections.
-/
def sectionsSubalgebra (F : J ⥤ AlgebraCat.{max v w} R) : Subalgebra R (∀ j, F.obj j) :=
  {
    SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgebraCat R) RingCat.{max v w} ⋙ forget₂ RingCat SemiRingCat.{max v w}) with
    algebraMap_mem' := fun r j j' f => (F.map f).commutes r }
#align Algebra.sections_subalgebra AlgebraCat.sectionsSubalgebra
-/

#print AlgebraCat.limitSemiring /-
instance limitSemiring (F : J ⥤ AlgebraCat.{max v w} R) :
    Ring (Types.limitCone (F ⋙ forget (AlgebraCat.{max v w} R))).pt :=
  by
  change Ring (sections_subalgebra F)
  infer_instance
#align Algebra.limit_semiring AlgebraCat.limitSemiring
-/

#print AlgebraCat.limitAlgebra /-
instance limitAlgebra (F : J ⥤ AlgebraCat.{max v w} R) :
    Algebra R (Types.limitCone (F ⋙ forget (AlgebraCat.{max v w} R))).pt :=
  by
  have :
    Algebra R (types.limit_cone (F ⋙ forget (AlgebraCat.{max v w} R))).pt =
      Algebra R (sections_subalgebra F) :=
    by rfl
  rw [this]
  infer_instance
#align Algebra.limit_algebra AlgebraCat.limitAlgebra
-/

#print AlgebraCat.limitπAlgHom /-
/-- `limit.π (F ⋙ forget (Algebra R)) j` as a `alg_hom`. -/
def limitπAlgHom (F : J ⥤ AlgebraCat.{max v w} R) (j) :
    (Types.limitCone (F ⋙ forget (AlgebraCat R))).pt →ₐ[R]
      (F ⋙ forget (AlgebraCat.{max v w} R)).obj j :=
  {
    SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgebraCat R) RingCat.{max v w} ⋙ forget₂ RingCat SemiRingCat.{max v w}) j with
    commutes' := fun r => rfl }
#align Algebra.limit_π_alg_hom AlgebraCat.limitπAlgHom
-/

namespace HasLimits

#print AlgebraCat.HasLimits.limitCone /-
-- The next two definitions are used in the construction of `has_limits (Algebra R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
/-- Construction of a limit cone in `Algebra R`.
(Internal use only; use the limits API.)
-/
def limitCone (F : J ⥤ AlgebraCat.{max v w} R) : Cone F
    where
  pt := AlgebraCat.of R (Types.limitCone (F ⋙ forget _)).pt
  π :=
    { app := limitπAlgHom F
      naturality' := fun j j' f =>
        AlgHom.coe_fn_injective ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
#align Algebra.has_limits.limit_cone AlgebraCat.HasLimits.limitCone
-/

#print AlgebraCat.HasLimits.limitConeIsLimit /-
/-- Witness that the limit cone in `Algebra R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ AlgebraCat.{max v w} R) : IsLimit (limitCone F) :=
  by
  refine'
    is_limit.of_faithful (forget (AlgebraCat R)) (types.limit_cone_is_limit _) (fun s => { .. })
      fun s => rfl
  · simp only [forget_map_eq_coe, AlgHom.map_one, functor.map_cone_π_app]; rfl
  · intro x y; simp only [forget_map_eq_coe, AlgHom.map_mul, functor.map_cone_π_app]; rfl
  · simp only [forget_map_eq_coe, AlgHom.map_zero, functor.map_cone_π_app]; rfl
  · intro x y; simp only [forget_map_eq_coe, AlgHom.map_add, functor.map_cone_π_app]; rfl
  · intro r; ext j; exact (s.π.app j).commutes r
#align Algebra.has_limits.limit_cone_is_limit AlgebraCat.HasLimits.limitConeIsLimit
-/

end HasLimits

open HasLimits

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
#print AlgebraCat.hasLimitsOfSize /-
/-- The category of R-algebras has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v, v} (AlgebraCat.{max v w} R) :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      {
        HasLimit := fun F =>
          has_limit.mk
            { Cone := limit_cone F
              IsLimit := limit_cone_is_limit F } } }
#align Algebra.has_limits_of_size AlgebraCat.hasLimitsOfSize
-/

#print AlgebraCat.hasLimits /-
instance hasLimits : HasLimits (AlgebraCat.{w} R) :=
  AlgebraCat.hasLimitsOfSize.{w, w, u}
#align Algebra.has_limits AlgebraCat.hasLimits
-/

#print AlgebraCat.forget₂RingPreservesLimitsOfSize /-
/-- The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂RingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ (AlgebraCat R) RingCat.{max v w})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (by apply RingCat.limitConeIsLimit (F ⋙ forget₂ (AlgebraCat R) RingCat.{max v w})) }
#align Algebra.forget₂_Ring_preserves_limits_of_size AlgebraCat.forget₂RingPreservesLimitsOfSize
-/

#print AlgebraCat.forget₂RingPreservesLimits /-
instance forget₂RingPreservesLimits : PreservesLimits (forget₂ (AlgebraCat R) RingCat.{w}) :=
  AlgebraCat.forget₂RingPreservesLimitsOfSize.{w, w}
#align Algebra.forget₂_Ring_preserves_limits AlgebraCat.forget₂RingPreservesLimits
-/

#print AlgebraCat.forget₂ModulePreservesLimitsOfSize /-
/-- The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂ModulePreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ (AlgebraCat R) (ModuleCat.{max v w} R))
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (by
            apply
              ModuleCat.HasLimits.limitConeIsLimit
                (F ⋙ forget₂ (AlgebraCat R) (ModuleCat.{max v w} R))) }
#align Algebra.forget₂_Module_preserves_limits_of_size AlgebraCat.forget₂ModulePreservesLimitsOfSize
-/

#print AlgebraCat.forget₂ModulePreservesLimits /-
instance forget₂ModulePreservesLimits :
    PreservesLimits (forget₂ (AlgebraCat R) (ModuleCat.{w} R)) :=
  AlgebraCat.forget₂ModulePreservesLimitsOfSize.{w, w}
#align Algebra.forget₂_Module_preserves_limits AlgebraCat.forget₂ModulePreservesLimits
-/

#print AlgebraCat.forgetPreservesLimitsOfSize /-
/-- The forgetful functor from R-algebras to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget (AlgebraCat.{max v w} R))
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (types.limit_cone_is_limit (F ⋙ forget _)) }
#align Algebra.forget_preserves_limits_of_size AlgebraCat.forgetPreservesLimitsOfSize
-/

#print AlgebraCat.forgetPreservesLimits /-
instance forgetPreservesLimits : PreservesLimits (forget (AlgebraCat.{w} R)) :=
  AlgebraCat.forgetPreservesLimitsOfSize.{w, w}
#align Algebra.forget_preserves_limits AlgebraCat.forgetPreservesLimits
-/

end AlgebraCat

