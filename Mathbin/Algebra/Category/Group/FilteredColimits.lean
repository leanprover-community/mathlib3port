import Mathbin.Algebra.Category.Group.Basic 
import Mathbin.Algebra.Category.Mon.FilteredColimits

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Group`.
We show that the colimit of `F ⋙ forget₂ Group Mon` (in `Mon`) carries the structure of a group,
thereby showing that the forgetful functor `forget₂ Group Mon` preserves filtered colimits. In
particular, this implies that `forget Group` preserves filtered colimits. Similarly for `AddGroup`,
`CommGroup` and `AddCommGroup`.

-/


universe v

noncomputable theory

open_locale Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max→max'

namespace Groupₓₓ.FilteredColimits

section 

open Mon.filtered_colimits(colimit_one_eq colimit_mul_mk_eq)

parameter {J : Type v}[small_category J][is_filtered J](F : J ⥤ Groupₓₓ.{v})

/--
The colimit of `F ⋙ forget₂ Group Mon` in the category `Mon`.
In the following, we will show that this has the structure of a group.
-/
@[toAdditive
      "The colimit of `F ⋙ forget₂ AddGroup AddMon` in the category `AddMon`.\nIn the following, we will show that this has the structure of an additive group."]
abbrev G : Mon :=
  Mon.FilteredColimits.colimit (F ⋙ forget₂ Groupₓₓ Mon)

/-- The canonical projection into the colimit, as a quotient type. -/
@[toAdditive "The canonical projection into the colimit, as a quotient type."]
abbrev G.mk : (Σj, F.obj j) → G :=
  Quot.mk (types.quot.rel (F ⋙ forget Groupₓₓ))

@[toAdditive]
theorem G.mk_eq (x y : Σj, F.obj j) (h : ∃ (k : J)(f : x.1 ⟶ k)(g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  G.mk x = G.mk y :=
  Quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget Groupₓₓ) x y h)

/-- The "unlifted" version of taking inverses in the colimit. -/
@[toAdditive "The \"unlifted\" version of negation in the colimit."]
def colimit_inv_aux (x : Σj, F.obj j) : G :=
  G.mk ⟨x.1, x.2⁻¹⟩

@[toAdditive]
theorem colimit_inv_aux_eq_of_rel (x y : Σj, F.obj j) (h : types.filtered_colimit.rel (F ⋙ forget Groupₓₓ) x y) :
  colimit_inv_aux x = colimit_inv_aux y :=
  by 
    apply G.mk_eq 
    obtain ⟨k, f, g, hfg⟩ := h 
    use k, f, g 
    rw [MonoidHom.map_inv, MonoidHom.map_inv, inv_inj]
    exact hfg

/-- Taking inverses in the colimit. See also `colimit_inv_aux`. -/
@[toAdditive "Negation in the colimit. See also `colimit_neg_aux`."]
instance colimit_has_inv : HasInv G :=
  { inv :=
      fun x =>
        by 
          refine' Quot.lift (colimit_inv_aux F) _ x 
          intro x y h 
          apply colimit_inv_aux_eq_of_rel 
          apply types.filtered_colimit.rel_of_quot_rel 
          exact h }

@[simp, toAdditive]
theorem colimit_inv_mk_eq (x : Σj, F.obj j) : G.mk x⁻¹ = G.mk ⟨x.1, x.2⁻¹⟩ :=
  rfl

@[toAdditive]
instance colimit_group : Groupₓ G :=
  { G.monoid, colimit_has_inv with
    mul_left_inv :=
      fun x =>
        by 
          apply Quot.induction_on x 
          clear x 
          intro x 
          cases' x with j x 
          erw [colimit_inv_mk_eq, colimit_mul_mk_eq (F ⋙ forget₂ Groupₓₓ Mon) ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
            colimit_one_eq (F ⋙ forget₂ Groupₓₓ Mon) j]
          dsimp 
          simp only [CategoryTheory.Functor.map_id, id_apply, mul_left_invₓ] }

/-- The bundled group giving the filtered colimit of a diagram. -/
@[toAdditive "The bundled additive group giving the filtered colimit of a diagram."]
def colimit : Groupₓₓ :=
  Groupₓₓ.of G

/-- The cocone over the proposed colimit group. -/
@[toAdditive "The cocone over the proposed colimit additive group."]
def colimit_cocone : cocone F :=
  { x := colimit, ι := { (Mon.FilteredColimits.colimitCocone (F ⋙ forget₂ Groupₓₓ Mon)).ι with  } }

/-- The proposed colimit cocone is a colimit in `Group`. -/
@[toAdditive "The proposed colimit cocone is a colimit in `AddGroup`."]
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
  { desc := fun t => Mon.FilteredColimits.colimitDesc (F ⋙ forget₂ Groupₓₓ Mon) ((forget₂ Groupₓₓ Mon).mapCocone t),
    fac' :=
      fun t j =>
        MonoidHom.coe_inj$ (types.colimit_cocone_is_colimit (F ⋙ forget Groupₓₓ)).fac ((forget Groupₓₓ).mapCocone t) j,
    uniq' :=
      fun t m h =>
        MonoidHom.coe_inj$
          (types.colimit_cocone_is_colimit (F ⋙ forget Groupₓₓ)).uniq ((forget Groupₓₓ).mapCocone t) m
            fun j => funext$ fun x => MonoidHom.congr_fun (h j) x }

@[toAdditive forget₂_AddMon_preserves_filtered_colimits]
instance forget₂_Mon_preserves_filtered_colimits : preserves_filtered_colimits (forget₂ Groupₓₓ Mon.{v}) :=
  { PreservesFilteredColimits :=
      fun J _ _ =>
        by 
          exactI
            { PreservesColimit :=
                fun F =>
                  preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
                    (Mon.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ Groupₓₓ Mon.{v})) } }

@[toAdditive]
instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget Groupₓₓ) :=
  limits.comp_preserves_filtered_colimits (forget₂ Groupₓₓ Mon) (forget Mon)

end 

end Groupₓₓ.FilteredColimits

namespace CommGroupₓₓ.FilteredColimits

section 

parameter {J : Type v}[small_category J][is_filtered J](F : J ⥤ CommGroupₓₓ.{v})

/--
The colimit of `F ⋙ forget₂ CommGroup Group` in the category `Group`.
In the following, we will show that this has the structure of a _commutative_ group.
-/
@[toAdditive
      "The colimit of `F ⋙ forget₂ AddCommGroup AddGroup` in the category `AddGroup`.\nIn the following, we will show that this has the structure of a _commutative_ additive group."]
abbrev G : Groupₓₓ :=
  Groupₓₓ.FilteredColimits.colimit (F ⋙ forget₂ CommGroupₓₓ Groupₓₓ.{v})

@[toAdditive]
instance colimit_comm_group : CommGroupₓ G :=
  { G.group, CommMon.FilteredColimits.colimitCommMonoid (F ⋙ forget₂ CommGroupₓₓ CommMon.{v}) with  }

/-- The bundled commutative group giving the filtered colimit of a diagram. -/
@[toAdditive "The bundled additive commutative group giving the filtered colimit of a diagram."]
def colimit : CommGroupₓₓ :=
  CommGroupₓₓ.of G

/-- The cocone over the proposed colimit commutative group. -/
@[toAdditive "The cocone over the proposed colimit additive commutative group."]
def colimit_cocone : cocone F :=
  { x := colimit, ι := { (Groupₓₓ.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGroupₓₓ Groupₓₓ)).ι with  } }

/-- The proposed colimit cocone is a colimit in `CommGroup`. -/
@[toAdditive "The proposed colimit cocone is a colimit in `AddCommGroup`."]
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
  { desc :=
      fun t =>
        (Groupₓₓ.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGroupₓₓ Groupₓₓ.{v})).desc
          ((forget₂ CommGroupₓₓ Groupₓₓ.{v}).mapCocone t),
    fac' :=
      fun t j =>
        MonoidHom.coe_inj$
          (types.colimit_cocone_is_colimit (F ⋙ forget CommGroupₓₓ)).fac ((forget CommGroupₓₓ).mapCocone t) j,
    uniq' :=
      fun t m h =>
        MonoidHom.coe_inj$
          (types.colimit_cocone_is_colimit (F ⋙ forget CommGroupₓₓ)).uniq ((forget CommGroupₓₓ).mapCocone t) m
            fun j => funext$ fun x => MonoidHom.congr_fun (h j) x }

@[toAdditive forget₂_AddGroup_preserves_filtered_colimits]
instance forget₂_Group_preserves_filtered_colimits : preserves_filtered_colimits (forget₂ CommGroupₓₓ Groupₓₓ.{v}) :=
  { PreservesFilteredColimits :=
      fun J _ _ =>
        by 
          exactI
            { PreservesColimit :=
                fun F =>
                  preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
                    (Groupₓₓ.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGroupₓₓ Groupₓₓ.{v})) } }

@[toAdditive]
instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget CommGroupₓₓ) :=
  limits.comp_preserves_filtered_colimits (forget₂ CommGroupₓₓ Groupₓₓ) (forget Groupₓₓ)

end 

end CommGroupₓₓ.FilteredColimits

