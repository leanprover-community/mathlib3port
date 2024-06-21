/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Algebra.Category.Grp.Basic
import Algebra.Category.MonCat.FilteredColimits

#align_import algebra.category.Group.filtered_colimits from "leanprover-community/mathlib"@"a87d22575d946e1e156fc1edd1e1269600a8a282"

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Group`.
We show that the colimit of `F ⋙ forget₂ Group Mon` (in `Mon`) carries the structure of a group,
thereby showing that the forgetful functor `forget₂ Group Mon` preserves filtered colimits. In
particular, this implies that `forget Group` preserves filtered colimits. Similarly for `AddGroup`,
`CommGroup` and `AddCommGroup`.

-/


universe v u

noncomputable section

open scoped Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max'

-- avoid name collision with `_root_.max`.
namespace Grp.FilteredColimits

section

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

-- We use parameters here, mainly so we can have the abbreviations `G` and `G.mk` below, without
-- passing around `F` all the time.
parameter {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ Grp.{max v u})

#print Grp.FilteredColimits.G /-
/-- The colimit of `F ⋙ forget₂ Group Mon` in the category `Mon`.
In the following, we will show that this has the structure of a group.
-/
@[to_additive
      "The colimit of `F ⋙ forget₂ AddGroup AddMon` in the category `AddMon`.\nIn the following, we will show that this has the structure of an additive group."]
abbrev G : MonCat :=
  MonCat.FilteredColimits.colimit (F ⋙ forget₂ Grp MonCat.{max v u})
#align Group.filtered_colimits.G Grp.FilteredColimits.G
#align AddGroup.filtered_colimits.G AddGrp.FilteredColimits.G
-/

#print Grp.FilteredColimits.G.mk /-
/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
abbrev G.mk : (Σ j, F.obj j) → G :=
  Quot.mk (Types.Quot.Rel (F ⋙ forget Grp))
#align Group.filtered_colimits.G.mk Grp.FilteredColimits.G.mk
#align AddGroup.filtered_colimits.G.mk AddGrp.FilteredColimits.G.mk
-/

#print Grp.FilteredColimits.G.mk_eq /-
@[to_additive]
theorem G.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : G.mk x = G.mk y :=
  Quot.EqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget Grp) x y h)
#align Group.filtered_colimits.G.mk_eq Grp.FilteredColimits.G.mk_eq
#align AddGroup.filtered_colimits.G.mk_eq AddGrp.FilteredColimits.G.mk_eq
-/

#print Grp.FilteredColimits.colimitInvAux /-
/-- The "unlifted" version of taking inverses in the colimit. -/
@[to_additive "The \"unlifted\" version of negation in the colimit."]
def colimitInvAux (x : Σ j, F.obj j) : G :=
  G.mk ⟨x.1, x.2⁻¹⟩
#align Group.filtered_colimits.colimit_inv_aux Grp.FilteredColimits.colimitInvAux
#align AddGroup.filtered_colimits.colimit_neg_aux AddGrp.FilteredColimits.colimitNegAux
-/

#print Grp.FilteredColimits.colimitInvAux_eq_of_rel /-
@[to_additive]
theorem colimitInvAux_eq_of_rel (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget Grp) x y) : colimit_inv_aux x = colimit_inv_aux y :=
  by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [MonoidHom.map_inv, MonoidHom.map_inv, inv_inj]
  exact hfg
#align Group.filtered_colimits.colimit_inv_aux_eq_of_rel Grp.FilteredColimits.colimitInvAux_eq_of_rel
#align AddGroup.filtered_colimits.colimit_neg_aux_eq_of_rel AddGrp.FilteredColimits.colimitNegAux_eq_of_rel
-/

#print Grp.FilteredColimits.colimitInv /-
/-- Taking inverses in the colimit. See also `colimit_inv_aux`. -/
@[to_additive "Negation in the colimit. See also `colimit_neg_aux`."]
instance colimitInv : Inv G
    where inv x := by
    refine' Quot.lift (colimit_inv_aux F) _ x
    intro x y h
    apply colimit_inv_aux_eq_of_rel
    apply types.filtered_colimit.rel_of_quot_rel
    exact h
#align Group.filtered_colimits.colimit_has_inv Grp.FilteredColimits.colimitInv
#align AddGroup.filtered_colimits.colimit_has_neg AddGrp.FilteredColimits.colimitNeg
-/

#print Grp.FilteredColimits.colimit_inv_mk_eq /-
@[simp, to_additive]
theorem colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk x)⁻¹ = G.mk ⟨x.1, x.2⁻¹⟩ :=
  rfl
#align Group.filtered_colimits.colimit_inv_mk_eq Grp.FilteredColimits.colimit_inv_mk_eq
#align AddGroup.filtered_colimits.colimit_neg_mk_eq AddGrp.FilteredColimits.colimit_neg_mk_eq
-/

#print Grp.FilteredColimits.colimitGroup /-
@[to_additive]
instance colimitGroup : Group G :=
  { G.Monoid, colimit_has_inv with
    hMul_left_inv := fun x => by
      apply Quot.inductionOn x; clear x; intro x
      cases' x with j x
      erw [colimit_inv_mk_eq,
        colimit_mul_mk_eq (F ⋙ forget₂ Grp MonCat.{max v u}) ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq (F ⋙ forget₂ Grp MonCat.{max v u}) j]
      dsimp
      simp only [CategoryTheory.Functor.map_id, id_apply, mul_left_inv] }
#align Group.filtered_colimits.colimit_group Grp.FilteredColimits.colimitGroup
#align AddGroup.filtered_colimits.colimit_add_group AddGrp.FilteredColimits.colimitAddGroup
-/

#print Grp.FilteredColimits.colimit /-
/-- The bundled group giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive group giving the filtered colimit of a diagram."]
def colimit : Grp :=
  Grp.of G
#align Group.filtered_colimits.colimit Grp.FilteredColimits.colimit
#align AddGroup.filtered_colimits.colimit AddGrp.FilteredColimits.colimit
-/

#print Grp.FilteredColimits.colimitCocone /-
/-- The cocone over the proposed colimit group. -/
@[to_additive "The cocone over the proposed colimit additive group."]
def colimitCocone : cocone F where
  pt := colimit
  ι := { (MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ Grp MonCat.{max v u})).ι with }
#align Group.filtered_colimits.colimit_cocone Grp.FilteredColimits.colimitCocone
#align AddGroup.filtered_colimits.colimit_cocone AddGrp.FilteredColimits.colimitCocone
-/

#print Grp.FilteredColimits.colimitCoconeIsColimit /-
/-- The proposed colimit cocone is a colimit in `Group`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddGroup`."]
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc t :=
    MonCat.FilteredColimits.colimitDesc (F ⋙ forget₂ Grp MonCat.{max v u})
      ((forget₂ Grp MonCat).mapCocone t)
  fac t j :=
    DFunLike.coe_injective <|
      (Types.colimitCoconeIsColimit (F ⋙ forget Grp)).fac ((forget Grp).mapCocone t) j
  uniq t m h :=
    DFunLike.coe_injective <|
      (Types.colimitCoconeIsColimit (F ⋙ forget Grp)).uniq ((forget Grp).mapCocone t) m fun j =>
        funext fun x => DFunLike.congr_fun (h j) x
#align Group.filtered_colimits.colimit_cocone_is_colimit Grp.FilteredColimits.colimitCoconeIsColimit
#align AddGroup.filtered_colimits.colimit_cocone_is_colimit AddGrp.FilteredColimits.colimitCoconeIsColimit
-/

#print Grp.FilteredColimits.forget₂MonPreservesFilteredColimits /-
@[to_additive forget₂_AddMon_preserves_filtered_colimits]
instance forget₂MonPreservesFilteredColimits : PreservesFilteredColimits (forget₂ Grp MonCat.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ Grp MonCat.{u})) }
#align Group.filtered_colimits.forget₂_Mon_preserves_filtered_colimits Grp.FilteredColimits.forget₂MonPreservesFilteredColimits
#align AddGroup.filtered_colimits.forget₂_AddMon_preserves_filtered_colimits AddGrp.FilteredColimits.forget₂AddMonPreservesFilteredColimits
-/

#print Grp.FilteredColimits.forgetPreservesFilteredColimits /-
@[to_additive]
instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget Grp.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ Grp MonCat) (forget MonCat.{u})
#align Group.filtered_colimits.forget_preserves_filtered_colimits Grp.FilteredColimits.forgetPreservesFilteredColimits
#align AddGroup.filtered_colimits.forget_preserves_filtered_colimits AddGrp.FilteredColimits.forgetPreservesFilteredColimits
-/

end

end Grp.FilteredColimits

namespace CommGrp.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `G` below, without
-- passing around `F` all the time.
parameter {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommGrp.{max v u})

#print CommGrp.FilteredColimits.G /-
/-- The colimit of `F ⋙ forget₂ CommGroup Group` in the category `Group`.
In the following, we will show that this has the structure of a _commutative_ group.
-/
@[to_additive
      "The colimit of `F ⋙ forget₂ AddCommGroup AddGroup` in the category `AddGroup`.\nIn the following, we will show that this has the structure of a _commutative_ additive group."]
abbrev G : Grp :=
  Grp.FilteredColimits.colimit (F ⋙ forget₂ CommGrp Grp.{max v u})
#align CommGroup.filtered_colimits.G CommGrp.FilteredColimits.G
#align AddCommGroup.filtered_colimits.G AddCommGrp.FilteredColimits.G
-/

#print CommGrp.FilteredColimits.colimitCommGroup /-
@[to_additive]
instance colimitCommGroup : CommGroup G :=
  { G.Group,
    CommMonCat.FilteredColimits.colimitCommMonoid (F ⋙ forget₂ CommGrp CommMonCat.{max v u}) with }
#align CommGroup.filtered_colimits.colimit_comm_group CommGrp.FilteredColimits.colimitCommGroup
#align AddCommGroup.filtered_colimits.colimit_add_comm_group AddCommGrp.FilteredColimits.colimitAddCommGroup
-/

#print CommGrp.FilteredColimits.colimit /-
/-- The bundled commutative group giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative group giving the filtered colimit of a diagram."]
def colimit : CommGrp :=
  CommGrp.of G
#align CommGroup.filtered_colimits.colimit CommGrp.FilteredColimits.colimit
#align AddCommGroup.filtered_colimits.colimit AddCommGrp.FilteredColimits.colimit
-/

#print CommGrp.FilteredColimits.colimitCocone /-
/-- The cocone over the proposed colimit commutative group. -/
@[to_additive "The cocone over the proposed colimit additive commutative group."]
def colimitCocone : cocone F where
  pt := colimit
  ι := { (Grp.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrp Grp.{max v u})).ι with }
#align CommGroup.filtered_colimits.colimit_cocone CommGrp.FilteredColimits.colimitCocone
#align AddCommGroup.filtered_colimits.colimit_cocone AddCommGrp.FilteredColimits.colimitCocone
-/

#print CommGrp.FilteredColimits.colimitCoconeIsColimit /-
/-- The proposed colimit cocone is a colimit in `CommGroup`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommGroup`."]
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc t :=
    (Grp.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGrp Grp.{max v u})).desc
      ((forget₂ CommGrp Grp.{max v u}).mapCocone t)
  fac t j :=
    DFunLike.coe_injective <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommGrp)).fac ((forget CommGrp).mapCocone t) j
  uniq t m h :=
    DFunLike.coe_injective <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommGrp)).uniq ((forget CommGrp).mapCocone t) m
        fun j => funext fun x => DFunLike.congr_fun (h j) x
#align CommGroup.filtered_colimits.colimit_cocone_is_colimit CommGrp.FilteredColimits.colimitCoconeIsColimit
#align AddCommGroup.filtered_colimits.colimit_cocone_is_colimit AddCommGrp.FilteredColimits.colimitCoconeIsColimit
-/

#print CommGrp.FilteredColimits.forget₂GroupPreservesFilteredColimits /-
@[to_additive forget₂_AddGroup_preserves_filtered_colimits]
instance forget₂GroupPreservesFilteredColimits : PreservesFilteredColimits (forget₂ CommGrp Grp.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (Grp.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGrp Grp.{u})) }
#align CommGroup.filtered_colimits.forget₂_Group_preserves_filtered_colimits CommGrp.FilteredColimits.forget₂GroupPreservesFilteredColimits
#align AddCommGroup.filtered_colimits.forget₂_AddGroup_preserves_filtered_colimits AddCommGrp.FilteredColimits.forget₂AddGroupPreservesFilteredColimits
-/

#print CommGrp.FilteredColimits.forgetPreservesFilteredColimits /-
@[to_additive]
instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommGrp.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommGrp Grp) (forget Grp.{u})
#align CommGroup.filtered_colimits.forget_preserves_filtered_colimits CommGrp.FilteredColimits.forgetPreservesFilteredColimits
#align AddCommGroup.filtered_colimits.forget_preserves_filtered_colimits AddCommGrp.FilteredColimits.forgetPreservesFilteredColimits
-/

end

end CommGrp.FilteredColimits

