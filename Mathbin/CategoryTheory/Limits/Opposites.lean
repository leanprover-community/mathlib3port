import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts 
import Mathbin.CategoryTheory.Limits.Shapes.Kernels 
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We also give special cases for (co)products,
but not yet for pullbacks / pushouts or for (co)equalizers.

-/


universe v u

noncomputable theory

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable{C : Type u}[category.{v} C]

variable{J : Type v}[small_category J]

variable(F : J ⥤ «expr ᵒᵖ» C)

/--
If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_limit_of_has_colimit_left_op [has_colimit F.left_op] : has_limit F :=
  has_limit.mk
    { Cone := cone_of_cocone_left_op (colimit.cocone F.left_op),
      IsLimit :=
        { lift := fun s => (colimit.desc F.left_op (cocone_left_op_of_cone s)).op,
          fac' :=
            fun s j =>
              by 
                rw [cone_of_cocone_left_op_π_app, colimit.cocone_ι, ←op_comp, colimit.ι_desc,
                  cocone_left_op_of_cone_ι_app, Quiver.Hom.op_unop]
                rfl,
          uniq' :=
            fun s m w =>
              by 
                have u := (colimit.is_colimit F.left_op).uniq (cocone_left_op_of_cone s) m.unop 
                convert congr_argₓ (fun f : _ ⟶ _ => f.op) (u _)
                clear u 
                intro j 
                rw [cocone_left_op_of_cone_ι_app, colimit.cocone_ι]
                convert congr_argₓ (fun f : _ ⟶ _ => f.unop) (w (unop j))
                clear w 
                rw [cone_of_cocone_left_op_π_app, colimit.cocone_ι, Quiver.Hom.unop_op]
                rfl } }

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_limits_of_shape_op_of_has_colimits_of_shape [has_colimits_of_shape («expr ᵒᵖ» J) C] :
  has_limits_of_shape J («expr ᵒᵖ» C) :=
  { HasLimit := fun F => has_limit_of_has_colimit_left_op F }

attribute [local instance] has_limits_of_shape_op_of_has_colimits_of_shape

/--
If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
theorem has_limits_op_of_has_colimits [has_colimits C] : has_limits («expr ᵒᵖ» C) :=
  {  }

/--
If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_colimit_of_has_limit_left_op [has_limit F.left_op] : has_colimit F :=
  has_colimit.mk
    { Cocone := cocone_of_cone_left_op (limit.cone F.left_op),
      IsColimit :=
        { desc := fun s => (limit.lift F.left_op (cone_left_op_of_cocone s)).op,
          fac' :=
            fun s j =>
              by 
                rw [cocone_of_cone_left_op_ι_app, limit.cone_π, ←op_comp, limit.lift_π, cone_left_op_of_cocone_π_app,
                  Quiver.Hom.op_unop]
                rfl,
          uniq' :=
            fun s m w =>
              by 
                have u := (limit.is_limit F.left_op).uniq (cone_left_op_of_cocone s) m.unop 
                convert congr_argₓ (fun f : _ ⟶ _ => f.op) (u _)
                clear u 
                intro j 
                rw [cone_left_op_of_cocone_π_app, limit.cone_π]
                convert congr_argₓ (fun f : _ ⟶ _ => f.unop) (w (unop j))
                clear w 
                rw [cocone_of_cone_left_op_ι_app, limit.cone_π, Quiver.Hom.unop_op]
                rfl } }

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_colimits_of_shape_op_of_has_limits_of_shape [has_limits_of_shape («expr ᵒᵖ» J) C] :
  has_colimits_of_shape J («expr ᵒᵖ» C) :=
  { HasColimit := fun F => has_colimit_of_has_limit_left_op F }

attribute [local instance] has_colimits_of_shape_op_of_has_limits_of_shape

/--
If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
theorem has_colimits_op_of_has_limits [has_limits C] : has_colimits («expr ᵒᵖ» C) :=
  {  }

variable(X : Type v)

/--
If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
theorem has_coproducts_opposite [has_products_of_shape X C] : has_coproducts_of_shape X («expr ᵒᵖ» C) :=
  by 
    haveI  : has_limits_of_shape («expr ᵒᵖ» (discrete X)) C :=
      has_limits_of_shape_of_equivalence (discrete.opposite X).symm 
    infer_instance

/--
If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
theorem has_products_opposite [has_coproducts_of_shape X C] : has_products_of_shape X («expr ᵒᵖ» C) :=
  by 
    haveI  : has_colimits_of_shape («expr ᵒᵖ» (discrete X)) C :=
      has_colimits_of_shape_of_equivalence (discrete.opposite X).symm 
    infer_instance

theorem has_finite_coproducts_opposite [has_finite_products C] : has_finite_coproducts («expr ᵒᵖ» C) :=
  { out :=
      fun J 𝒟 𝒥 =>
        by 
          resetI 
          haveI  : has_limits_of_shape («expr ᵒᵖ» (discrete J)) C :=
            has_limits_of_shape_of_equivalence (discrete.opposite J).symm 
          infer_instance }

theorem has_finite_products_opposite [has_finite_coproducts C] : has_finite_products («expr ᵒᵖ» C) :=
  { out :=
      fun J 𝒟 𝒥 =>
        by 
          resetI 
          haveI  : has_colimits_of_shape («expr ᵒᵖ» (discrete J)) C :=
            has_colimits_of_shape_of_equivalence (discrete.opposite J).symm 
          infer_instance }

attribute [local instance] fin_category_opposite

theorem has_finite_colimits_opposite [has_finite_limits C] : has_finite_colimits («expr ᵒᵖ» C) :=
  { out :=
      fun J 𝒟 𝒥 =>
        by 
          resetI 
          infer_instance }

theorem has_finite_limits_opposite [has_finite_colimits C] : has_finite_limits («expr ᵒᵖ» C) :=
  { out :=
      fun J 𝒟 𝒥 =>
        by 
          resetI 
          infer_instance }

end CategoryTheory.Limits

