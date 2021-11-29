import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks 
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts 
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

## TODO

Dualise and apply to functor categories.

-/


universe v u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [category.{v} C] [category.{v} D]

variable (F : C ⥤ D)

-- error in CategoryTheory.Limits.Constructions.EpiMono: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
instance preserves_mono {X Y : C} (f : «expr ⟶ »(X, Y)) [preserves_limit (cospan f f) F] [mono f] : mono (F.map f) :=
begin
  have [] [] [":=", expr is_limit_pullback_cone_map_of_is_limit F _ (pullback_cone.is_limit_mk_id_id f)],
  simp_rw ["[", expr F.map_id, "]"] ["at", ident this],
  apply [expr pullback_cone.mono_of_is_limit_mk_id_id _ this]
end

-- error in CategoryTheory.Limits.Constructions.EpiMono: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
theorem reflects_mono {X Y : C} (f : «expr ⟶ »(X, Y)) [reflects_limit (cospan f f) F] [mono (F.map f)] : mono f :=
begin
  have [] [] [":=", expr pullback_cone.is_limit_mk_id_id (F.map f)],
  simp_rw ["[", "<-", expr F.map_id, "]"] ["at", ident this],
  apply [expr pullback_cone.mono_of_is_limit_mk_id_id _ (is_limit_of_is_limit_pullback_cone_map F _ this)]
end

end CategoryTheory

