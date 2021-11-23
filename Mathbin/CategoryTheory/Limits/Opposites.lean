import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts 
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

-- error in CategoryTheory.Limits.Opposites: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/ theorem has_limit_of_has_colimit_left_op [has_colimit F.left_op] : has_limit F :=
has_limit.mk { cone := cone_of_cocone_left_op (colimit.cocone F.left_op),
  is_limit := { lift := λ s, (colimit.desc F.left_op (cocone_left_op_of_cone s)).op,
    fac' := λ s j, begin
      rw ["[", expr cone_of_cocone_left_op_π_app, ",", expr colimit.cocone_ι, ",", "<-", expr op_comp, ",", expr colimit.ι_desc, ",", expr cocone_left_op_of_cone_ι_app, ",", expr quiver.hom.op_unop, "]"] [],
      refl
    end,
    uniq' := λ s m w, begin
      have [ident u] [] [":=", expr (colimit.is_colimit F.left_op).uniq (cocone_left_op_of_cone s) m.unop],
      convert [] [expr congr_arg (λ f : «expr ⟶ »(_, _), f.op) (u _)] [],
      clear [ident u],
      intro [ident j],
      rw ["[", expr cocone_left_op_of_cone_ι_app, ",", expr colimit.cocone_ι, "]"] [],
      convert [] [expr congr_arg (λ f : «expr ⟶ »(_, _), f.unop) (w (unop j))] [],
      clear [ident w],
      rw ["[", expr cone_of_cocone_left_op_π_app, ",", expr colimit.cocone_ι, ",", expr quiver.hom.unop_op, "]"] [],
      refl
    end } }

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

-- error in CategoryTheory.Limits.Opposites: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/ theorem has_colimit_of_has_limit_left_op [has_limit F.left_op] : has_colimit F :=
has_colimit.mk { cocone := cocone_of_cone_left_op (limit.cone F.left_op),
  is_colimit := { desc := λ s, (limit.lift F.left_op (cone_left_op_of_cocone s)).op,
    fac' := λ s j, begin
      rw ["[", expr cocone_of_cone_left_op_ι_app, ",", expr limit.cone_π, ",", "<-", expr op_comp, ",", expr limit.lift_π, ",", expr cone_left_op_of_cocone_π_app, ",", expr quiver.hom.op_unop, "]"] [],
      refl
    end,
    uniq' := λ s m w, begin
      have [ident u] [] [":=", expr (limit.is_limit F.left_op).uniq (cone_left_op_of_cocone s) m.unop],
      convert [] [expr congr_arg (λ f : «expr ⟶ »(_, _), f.op) (u _)] [],
      clear [ident u],
      intro [ident j],
      rw ["[", expr cone_left_op_of_cocone_π_app, ",", expr limit.cone_π, "]"] [],
      convert [] [expr congr_arg (λ f : «expr ⟶ »(_, _), f.unop) (w (unop j))] [],
      clear [ident w],
      rw ["[", expr cocone_of_cone_left_op_ι_app, ",", expr limit.cone_π, ",", expr quiver.hom.unop_op, "]"] [],
      refl
    end } }

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

-- error in CategoryTheory.Limits.Opposites: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/ theorem has_coproducts_opposite [has_products_of_shape X C] : has_coproducts_of_shape X «expr ᵒᵖ»(C) :=
begin
  haveI [] [":", expr has_limits_of_shape «expr ᵒᵖ»(discrete X) C] [":=", expr has_limits_of_shape_of_equivalence (discrete.opposite X).symm],
  apply_instance
end

-- error in CategoryTheory.Limits.Opposites: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/ theorem has_products_opposite [has_coproducts_of_shape X C] : has_products_of_shape X «expr ᵒᵖ»(C) :=
begin
  haveI [] [":", expr has_colimits_of_shape «expr ᵒᵖ»(discrete X) C] [":=", expr has_colimits_of_shape_of_equivalence (discrete.opposite X).symm],
  apply_instance
end

-- error in CategoryTheory.Limits.Opposites: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_finite_coproducts_opposite [has_finite_products C] : has_finite_coproducts «expr ᵒᵖ»(C) :=
{ out := λ J 𝒟 𝒥, begin
    resetI,
    haveI [] [":", expr has_limits_of_shape «expr ᵒᵖ»(discrete J) C] [":=", expr has_limits_of_shape_of_equivalence (discrete.opposite J).symm],
    apply_instance
  end }

-- error in CategoryTheory.Limits.Opposites: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_finite_products_opposite [has_finite_coproducts C] : has_finite_products «expr ᵒᵖ»(C) :=
{ out := λ J 𝒟 𝒥, begin
    resetI,
    haveI [] [":", expr has_colimits_of_shape «expr ᵒᵖ»(discrete J) C] [":=", expr has_colimits_of_shape_of_equivalence (discrete.opposite J).symm],
    apply_instance
  end }

attribute [local instance] fin_category_opposite

theorem has_finite_colimits_opposite [has_finite_limits C] : has_finite_colimits («expr ᵒᵖ» C) :=
  { out :=
      fun J 𝒟 𝒥 =>
        by 
          skip 
          infer_instance }

theorem has_finite_limits_opposite [has_finite_colimits C] : has_finite_limits («expr ᵒᵖ» C) :=
  { out :=
      fun J 𝒟 𝒥 =>
        by 
          skip 
          infer_instance }

end CategoryTheory.Limits

