import Mathbin.Algebra.Category.Module.Basic 
import Mathbin.Algebra.Category.Group.Limits 
import Mathbin.Algebra.DirectLimit

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u v

noncomputable theory

namespace ModuleCat

variable{R : Type u}[Ringₓ R]

variable{J : Type v}[small_category J]

instance add_comm_group_obj (F : J ⥤ ModuleCat.{v} R) j : AddCommGroupₓ ((F ⋙ forget (ModuleCat R)).obj j) :=
  by 
    change AddCommGroupₓ (F.obj j)
    infer_instance

instance module_obj (F : J ⥤ ModuleCat.{v} R) j : Module R ((F ⋙ forget (ModuleCat R)).obj j) :=
  by 
    change Module R (F.obj j)
    infer_instance

/--
The flat sections of a functor into `Module R` form a submodule of all sections.
-/
def sections_submodule (F : J ⥤ ModuleCat R) : Submodule R (∀ j, F.obj j) :=
  { AddGroupₓₓ.sectionsAddSubgroup
      (F ⋙ forget₂ (ModuleCat R) AddCommGroupₓₓ.{v} ⋙ forget₂ AddCommGroupₓₓ AddGroupₓₓ.{v}) with
    Carrier := (F ⋙ forget (ModuleCat R)).sections,
    smul_mem' :=
      fun r s sh j j' f =>
        by 
          simp only [forget_map_eq_coe, functor.comp_map, Pi.smul_apply, LinearMap.map_smul]
          dsimp [functor.sections]  at sh 
          rw [sh f] }

instance limit_add_comm_monoid (F : J ⥤ ModuleCat R) :
  AddCommMonoidₓ (types.limit_cone (F ⋙ forget (ModuleCat.{v} R))).x :=
  show AddCommMonoidₓ (sections_submodule F)by 
    infer_instance

instance limit_add_comm_group (F : J ⥤ ModuleCat R) :
  AddCommGroupₓ (types.limit_cone (F ⋙ forget (ModuleCat.{v} R))).x :=
  show AddCommGroupₓ (sections_submodule F)by 
    infer_instance

instance limit_module (F : J ⥤ ModuleCat R) : Module R (types.limit_cone (F ⋙ forget (ModuleCat.{v} R))).x :=
  show Module R (sections_submodule F)by 
    infer_instance

/-- `limit.π (F ⋙ forget Ring) j` as a `ring_hom`. -/
def limit_π_linear_map (F : J ⥤ ModuleCat R) j :
  (types.limit_cone (F ⋙ forget (ModuleCat.{v} R))).x →ₗ[R] (F ⋙ forget (ModuleCat R)).obj j :=
  { toFun := (types.limit_cone (F ⋙ forget (ModuleCat R))).π.app j, map_smul' := fun x y => rfl,
    map_add' := fun x y => rfl }

namespace HasLimits

/--
Construction of a limit cone in `Module R`.
(Internal use only; use the limits API.)
-/
def limit_cone (F : J ⥤ ModuleCat R) : cone F :=
  { x := ModuleCat.of R (types.limit_cone (F ⋙ forget _)).x,
    π :=
      { app := limit_π_linear_map F,
        naturality' := fun j j' f => LinearMap.coe_injective ((types.limit_cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `Module R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit (F : J ⥤ ModuleCat R) : is_limit (limit_cone F) :=
  by 
    refine'
        is_limit.of_faithful (forget (ModuleCat R)) (types.limit_cone_is_limit _) (fun s => ⟨_, _, _⟩) fun s => rfl <;>
      tidy

end HasLimits

open HasLimits

/-- The category of R-modules has all limits. -/
@[irreducible]
instance has_limits : has_limits (ModuleCat.{v} R) :=
  { HasLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exactI { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } } }

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_AddCommGroup_preserves_limits_aux (F : J ⥤ ModuleCat R) :
  is_limit ((forget₂ (ModuleCat R) AddCommGroupₓₓ).mapCone (limit_cone F)) :=
  AddCommGroupₓₓ.limitConeIsLimit (F ⋙ forget₂ (ModuleCat R) AddCommGroupₓₓ)

/--
The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂_AddCommGroup_preserves_limits : preserves_limits (forget₂ (ModuleCat R) AddCommGroupₓₓ.{v}) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exactI
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (forget₂_AddCommGroup_preserves_limits_aux F) } }

/--
The forgetful functor from R-modules to types preserves all limits.
-/
instance forget_preserves_limits : preserves_limits (forget (ModuleCat R)) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exactI
            { PreservesLimit :=
                fun F =>
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (types.limit_cone_is_limit (F ⋙ forget _)) } }

section DirectLimit

open Module

variable{ι : Type v}

variable[dec_ι : DecidableEq ι][DirectedOrder ι]

variable(G : ι → Type v)

variable[∀ i, AddCommGroupₓ (G i)][∀ i, Module R (G i)]

variable(f : ∀ i j, i ≤ j → G i →ₗ[R] G j)[Module.DirectedSystem G f]

/-- The diagram (in the sense of `category_theory`)
 of an unbundled `direct_limit` of modules. -/
@[simps]
def direct_limit_diagram : ι ⥤ ModuleCat R :=
  { obj := fun i => ModuleCat.of R (G i), map := fun i j hij => f i j hij.le,
    map_id' :=
      fun i =>
        by 
          apply LinearMap.ext 
          intro x 
          apply Module.DirectedSystem.map_self,
    map_comp' :=
      fun i j k hij hjk =>
        by 
          apply LinearMap.ext 
          intro x 
          symm 
          apply Module.DirectedSystem.map_map }

variable[DecidableEq ι]

/-- The `cocone` on `direct_limit_diagram` corresponding to
the unbundled `direct_limit` of modules.

In `direct_limit_is_colimit` we show that it is a colimit cocone. -/
@[simps]
def direct_limit_cocone : cocone (direct_limit_diagram G f) :=
  { x := ModuleCat.of R$ direct_limit G f,
    ι :=
      { app := Module.DirectLimit.of R ι G f,
        naturality' :=
          fun i j hij =>
            by 
              apply LinearMap.ext 
              intro x 
              exact direct_limit.of_f } }

/-- The unbundled `direct_limit` of modules is a colimit
in the sense of `category_theory`. -/
@[simps]
def direct_limit_is_colimit [Nonempty ι] : is_colimit (direct_limit_cocone G f) :=
  { desc :=
      fun s =>
        direct_limit.lift R ι G f s.ι.app$
          fun i j h x =>
            by 
              rw [←s.w (hom_of_le h)]
              rfl,
    fac' :=
      fun s i =>
        by 
          apply LinearMap.ext 
          intro x 
          dsimp 
          exact direct_limit.lift_of s.ι.app _ x,
    uniq' :=
      fun s m h =>
        by 
          have  : s.ι.app = fun i => LinearMap.comp m (direct_limit.of R ι (fun i => G i) (fun i j H => f i j H) i)
          ·
            funext i 
            rw [←h]
            rfl 
          apply LinearMap.ext 
          intro x 
          simp only [this]
          apply Module.DirectLimit.lift_unique }

end DirectLimit

end ModuleCat

