import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Sites.Sheafification

/-!

# Limits and colimits of sheaves

## Limits

We prove that the forgetful functor from `Sheaf J D` to presheaves creates limits.
If the target category `D` has limits (of a certain shape),
this then implies that `Sheaf J D` has limits of the same shape and that the forgetful
functor preserves these limits.

## Colimits

Given a diagram `F : K ⥤ Sheaf J D` of sheaves, and a colimit cocone on the level of presheaves,
we show that the cocone obtained by sheafifying the cocone point is a colimit cocone of sheaves.

This allows us to show that `Sheaf J D` has colimits (of a certain shape) as soon as `D` does.

-/


namespace CategoryTheory

namespace Sheaf

open CategoryTheory.Limits

open Opposite

section Limits

universe w v u

variable {C : Type max v u} [category.{v} C] {J : grothendieck_topology C}

variable {D : Type w} [category.{max v u} D]

variable {K : Type max v u} [small_category K]

noncomputable section

section

/--  An auxiliary definition to be used below.

Whenever `E` is a cone of shape `K` of sheaves, and `S` is the multifork associated to a
covering `W` of an object `X`, with respect to the cone point `E.X`, this provides a cone of
shape `K` of objects in `D`, with cone point `S.X`.

See `is_limit_multifork_of_is_limit` for more on how this definition is used.
-/
def multifork_evaluation_cone (F : K ⥤ Sheaf J D) (E : cone (F ⋙ Sheaf_to_presheaf J D)) (X : C) (W : J.cover X)
    (S : multifork (W.index E.X)) : cone (F ⋙ Sheaf_to_presheaf J D ⋙ (evaluation (Cᵒᵖ) D).obj (op X)) :=
  { x := S.X,
    π :=
      { app := fun k =>
          (presheaf.is_limit_of_is_sheaf J (F.obj k).1 W (F.obj k).2).lift $
            multifork.of_ι _ S.X (fun i => S.ι i ≫ (E.π.app k).app (op i.Y))
              (by
                intro i
                simp only [category.assoc]
                erw [← (E.π.app k).naturality, ← (E.π.app k).naturality]
                dsimp
                simp only [← category.assoc]
                congr 1
                apply S.condition),
        naturality' := by
          intro i j f
          dsimp [presheaf.is_limit_of_is_sheaf]
          rw [category.id_comp]
          apply presheaf.is_sheaf.hom_ext (F.obj j).2 W
          intro ii
          rw [presheaf.is_sheaf.amalgamate_map, category.assoc, ← (F.map f).val.naturality, ← category.assoc,
            presheaf.is_sheaf.amalgamate_map]
          dsimp [multifork.of_ι]
          rw [category.assoc, ← E.w f]
          simp } }

variable [has_limits_of_shape K D]

/--  If `E` is a cone of shape `K` of sheaves, which is a limit on the level of presheves,
this definition shows that the limit presheaf satisfies the multifork variant of the sheaf
condition, at a given covering `W`.

This is used below in `is_sheaf_of_is_limit` to show that the limit presheaf is indeed a sheaf.
-/
def is_limit_multifork_of_is_limit (F : K ⥤ Sheaf J D) (E : cone (F ⋙ Sheaf_to_presheaf J D)) (hE : is_limit E) (X : C)
    (W : J.cover X) : is_limit (W.multifork E.X) :=
  multifork.is_limit.mk _
    (fun S => (is_limit_of_preserves ((evaluation (Cᵒᵖ) D).obj (op X)) hE).lift $ multifork_evaluation_cone F E X W S)
    (by
      intro S i
      apply (is_limit_of_preserves ((evaluation (Cᵒᵖ) D).obj (op i.Y)) hE).hom_ext
      intro k
      dsimp [multifork.of_ι]
      erw [category.assoc, (E.π.app k).naturality]
      dsimp
      rw [← category.assoc]
      erw [(is_limit_of_preserves ((evaluation (Cᵒᵖ) D).obj (op X)) hE).fac (multifork_evaluation_cone F E X W S)]
      dsimp [multifork_evaluation_cone, presheaf.is_limit_of_is_sheaf]
      erw [presheaf.is_sheaf.amalgamate_map]
      rfl)
    (by
      intro S m hm
      apply (is_limit_of_preserves ((evaluation (Cᵒᵖ) D).obj (op X)) hE).hom_ext
      intro k
      dsimp
      erw [(is_limit_of_preserves ((evaluation (Cᵒᵖ) D).obj (op X)) hE).fac]
      apply presheaf.is_sheaf.hom_ext (F.obj k).2 W
      intro i
      erw [presheaf.is_sheaf.amalgamate_map]
      dsimp [multifork.of_ι]
      change _ = S.ι i ≫ _
      erw [← hm, category.assoc, ← (E.π.app k).naturality, category.assoc]
      rfl)

/--  If `E` is a cone which is a limit on the level of presheaves,
then the limit presheaf is again a sheaf.

This is used to show that the forgetful functor from sheaves to presheaves creates limits.
-/
theorem is_sheaf_of_is_limit (F : K ⥤ Sheaf J D) (E : cone (F ⋙ Sheaf_to_presheaf J D)) (hE : is_limit E) :
    presheaf.is_sheaf J E.X := by
  rw [presheaf.is_sheaf_iff_multifork]
  intro X S
  exact ⟨is_limit_multifork_of_is_limit _ _ hE _ _⟩

instance (F : K ⥤ Sheaf J D) : creates_limit F (Sheaf_to_presheaf J D) :=
  creates_limit_of_reflects_iso $ fun E hE =>
    { liftedCone :=
        ⟨⟨E.X, is_sheaf_of_is_limit _ _ hE⟩, ⟨fun t => ⟨E.π.app _⟩, fun u v e => Sheaf.hom.ext _ _ $ E.π.naturality _⟩⟩,
      validLift :=
        cones.ext (eq_to_iso rfl) $ fun j => by
          dsimp
          simp ,
      makesLimit :=
        { lift := fun S => ⟨hE.lift ((Sheaf_to_presheaf J D).mapCone S)⟩,
          fac' := fun S j => by
            ext1
            apply hE.fac ((Sheaf_to_presheaf J D).mapCone S) j,
          uniq' := fun S m hm => by
            ext1
            exact hE.uniq ((Sheaf_to_presheaf J D).mapCone S) m.val fun j => congr_argₓ hom.val (hm j) } }

instance : creates_limits_of_shape K (Sheaf_to_presheaf J D) :=
  {  }

instance : has_limits_of_shape K (Sheaf J D) :=
  has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (Sheaf_to_presheaf J D)

end

instance [has_limits D] : creates_limits (Sheaf_to_presheaf J D) :=
  ⟨⟩

instance [has_limits D] : has_limits (Sheaf J D) :=
  has_limits_of_has_limits_creates_limits (Sheaf_to_presheaf J D)

end Limits

section Colimits

universe w v u

variable {C : Type max v u} [category.{v} C] {J : grothendieck_topology C}

variable {D : Type w} [category.{max v u} D]

variable {K : Type max v u} [small_category K]

variable [concrete_category.{max v u} D]

variable [∀ P : Cᵒᵖ ⥤ D X : C S : J.cover X, has_multiequalizer (S.index P)]

variable [preserves_limits (forget D)]

variable [∀ X : C, has_colimits_of_shape (J.cover Xᵒᵖ) D]

variable [∀ X : C, preserves_colimits_of_shape (J.cover Xᵒᵖ) (forget D)]

variable [reflects_isomorphisms (forget D)]

/--  Construct a cocone by sheafifying a cocone point of a cocone `E` of presheaves
over a functor which factors through sheaves.
In `is_colimit_sheafify_cocone`, we show that this is a colimit cocone when `E` is a colimit. -/
@[simps]
def sheafify_cocone {F : K ⥤ Sheaf J D} (E : cocone (F ⋙ Sheaf_to_presheaf J D)) : cocone F :=
  { x := ⟨J.sheafify E.X, grothendieck_topology.plus.is_sheaf_plus_plus _ _⟩,
    ι :=
      { app := fun k => ⟨E.ι.app k ≫ J.to_sheafify E.X⟩,
        naturality' := fun i j f => by
          ext1
          dsimp
          erw [category.comp_id, ← category.assoc, E.w f] } }

/--  If `E` is a colimit cocone of presheaves, over a diagram factoring through sheaves,
then `sheafify_cocone E` is a colimit cocone. -/
@[simps]
def is_colimit_sheafify_cocone {F : K ⥤ Sheaf J D} (E : cocone (F ⋙ Sheaf_to_presheaf J D)) (hE : is_colimit E) :
    is_colimit (sheafify_cocone E) :=
  { desc := fun S => ⟨J.sheafify_lift (hE.desc ((Sheaf_to_presheaf J D).mapCocone S)) S.X.2⟩,
    fac' := by
      intro S j
      ext1
      dsimp [sheafify_cocone]
      erw [category.assoc, J.to_sheafify_sheafify_lift, hE.fac]
      rfl,
    uniq' := by
      intro S m hm
      ext1
      apply J.sheafify_lift_unique
      apply hE.uniq ((Sheaf_to_presheaf J D).mapCocone S)
      intro j
      dsimp
      simpa only [← category.assoc, ← hm] }

instance [has_colimits_of_shape K D] : has_colimits_of_shape K (Sheaf J D) :=
  ⟨fun F => has_colimit.mk ⟨sheafify_cocone (colimit.cocone _), is_colimit_sheafify_cocone _ (colimit.is_colimit _)⟩⟩

instance [has_colimits D] : has_colimits (Sheaf J D) :=
  ⟨inferInstance⟩

end Colimits

end Sheaf

end CategoryTheory

