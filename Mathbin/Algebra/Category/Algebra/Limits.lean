import Mathbin.Algebra.Category.Algebra.Basic 
import Mathbin.Algebra.Category.Module.Limits 
import Mathbin.Algebra.Category.CommRing.Limits

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

noncomputable theory

namespace AlgebraCat

variable {R : Type u} [CommRingₓ R]

variable {J : Type v} [small_category J]

instance semiring_obj (F : J ⥤ AlgebraCat R) j : Semiringₓ ((F ⋙ forget (AlgebraCat R)).obj j) :=
  by 
    change Semiringₓ (F.obj j)
    infer_instance

instance algebra_obj (F : J ⥤ AlgebraCat R) j : Algebra R ((F ⋙ forget (AlgebraCat R)).obj j) :=
  by 
    change Algebra R (F.obj j)
    infer_instance

/--
The flat sections of a functor into `Algebra R` form a submodule of all sections.
-/
def sections_subalgebra (F : J ⥤ AlgebraCat R) : Subalgebra R (∀ j, F.obj j) :=
  { SemiRing.sectionsSubsemiring (F ⋙ forget₂ (AlgebraCat R) Ringₓₓ ⋙ forget₂ Ringₓₓ SemiRing) with
    algebra_map_mem' := fun r j j' f => (F.map f).commutes r }

instance limit_semiring (F : J ⥤ AlgebraCat R) : Ringₓ (types.limit_cone (F ⋙ forget (AlgebraCat.{v} R))).x :=
  by 
    change Ringₓ (sections_subalgebra F)
    infer_instance

-- error in Algebra.Category.Algebra.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance limit_algebra
(F : «expr ⥤ »(J, Algebra R)) : algebra R (types.limit_cone «expr ⋙ »(F, forget (Algebra.{v} R))).X :=
begin
  have [] [":", expr «expr = »(algebra R (types.limit_cone «expr ⋙ »(F, forget (Algebra.{v} R))).X, algebra R (sections_subalgebra F))] [],
  by refl,
  rw [expr this] [],
  apply_instance
end

/-- `limit.π (F ⋙ forget (Algebra R)) j` as a `alg_hom`. -/
def limit_π_alg_hom (F : J ⥤ AlgebraCat.{v} R) j :
  (types.limit_cone (F ⋙ forget (AlgebraCat R))).x →ₐ[R] (F ⋙ forget (AlgebraCat.{v} R)).obj j :=
  { SemiRing.limitπRingHom (F ⋙ forget₂ (AlgebraCat R) Ringₓₓ.{v} ⋙ forget₂ Ringₓₓ SemiRing.{v}) j with
    commutes' := fun r => rfl }

namespace HasLimits

/--
Construction of a limit cone in `Algebra R`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ AlgebraCat.{v} R) : cone F :=
  { x := AlgebraCat.of R (types.limit_cone (F ⋙ forget _)).x,
    π :=
      { app := limit_π_alg_hom F,
        naturality' := fun j j' f => AlgHom.coe_fn_injective ((types.limit_cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `Algebra R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ AlgebraCat R) : is_limit (limit_cone F) :=
  by 
    refine' is_limit.of_faithful (forget (AlgebraCat R)) (types.limit_cone_is_limit _) (fun s => { .. }) fun s => rfl
    ·
      simp only [forget_map_eq_coe, AlgHom.map_one, functor.map_cone_π_app]
      rfl
    ·
      intro x y 
      simp only [forget_map_eq_coe, AlgHom.map_mul, functor.map_cone_π_app]
      rfl
    ·
      simp only [forget_map_eq_coe, AlgHom.map_zero, functor.map_cone_π_app]
      rfl
    ·
      intro x y 
      simp only [forget_map_eq_coe, AlgHom.map_add, functor.map_cone_π_app]
      rfl
    ·
      intro r 
      ext j 
      exact (s.π.app j).commutes r

end HasLimits

open HasLimits

-- error in Algebra.Category.Algebra.Limits: ././Mathport/Syntax/Translate/Basic.lean:927:38: unsupported irreducible non-definition
/-- The category of R-algebras has all limits. -/ @[irreducible] instance has_limits : has_limits (Algebra R) :=
{ has_limits_of_shape := λ
  J 𝒥, by exactI [expr { has_limit := λ F, has_limit.mk { cone := limit_cone F, is_limit := limit_cone_is_limit F } }] }

/--
The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂_Ring_preserves_limits : preserves_limits (forget₂ (AlgebraCat R) Ringₓₓ.{v}) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (by 
                      apply Ringₓₓ.limitConeIsLimit (F ⋙ forget₂ (AlgebraCat R) Ringₓₓ)) } }

/--
The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂_Module_preserves_limits : preserves_limits (forget₂ (AlgebraCat R) (ModuleCat.{v} R)) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (by 
                      apply ModuleCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ (AlgebraCat R) (ModuleCat R))) } }

/--
The forgetful functor from R-algebras to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget (AlgebraCat R)) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (types.limit_cone_is_limit (F ⋙ forget _)) } }

end AlgebraCat

