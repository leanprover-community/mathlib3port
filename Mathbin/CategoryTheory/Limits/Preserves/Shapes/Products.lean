import Mathbin.CategoryTheory.Limits.Shapes.Products 
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving products

Constructions to relate the notions of preserving products and reflecting products
to concrete fans.

In particular, we show that `pi_comparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/


noncomputable section 

universe v u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [category.{v} C]

variable {D : Type u₂} [category.{v} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable {J : Type v} (f : J → C)

/--
The map of a fan is a limit iff the fan consisting of the mapped morphisms is a limit. This
essentially lets us commute `fan.mk` with `functor.map_cone`.
-/
def is_limit_map_cone_fan_mk_equiv {P : C} (g : ∀ j, P ⟶ f j) :
  is_limit (G.map_cone (fan.mk P g)) ≃ is_limit (fan.mk _ fun j => G.map (g j) : fan fun j => G.obj (f j)) :=
  by 
    refine' (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _)
    refine' discrete.nat_iso fun j => iso.refl (G.obj (f j))
    refine'
      cones.ext (iso.refl _)
        fun j =>
          by 
            dsimp 
            simp 

/-- The property of preserving products expressed in terms of fans. -/
def is_limit_fan_mk_obj_of_is_limit [preserves_limit (discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
  (t : is_limit (fan.mk _ g)) : is_limit (fan.mk (G.obj P) fun j => G.map (g j) : fan fun j => G.obj (f j)) :=
  is_limit_map_cone_fan_mk_equiv _ _ _ (preserves_limit.preserves t)

/-- The property of reflecting products expressed in terms of fans. -/
def is_limit_of_is_limit_fan_mk_obj [reflects_limit (discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
  (t : is_limit (fan.mk _ fun j => G.map (g j) : fan fun j => G.obj (f j))) : is_limit (fan.mk P g) :=
  reflects_limit.reflects ((is_limit_map_cone_fan_mk_equiv _ _ _).symm t)

section 

variable [has_product f]

/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
def is_limit_of_has_product_of_preserves_limit [preserves_limit (discrete.functor f) G] :
  is_limit (fan.mk _ fun j : J => G.map (pi.π f j) : fan fun j => G.obj (f j)) :=
  is_limit_fan_mk_obj_of_is_limit G f _ (product_is_product _)

variable [has_product fun j : J => G.obj (f j)]

/-- If `pi_comparison G f` is an isomorphism, then `G` preserves the limit of `f`. -/
def preserves_product.of_iso_comparison [i : is_iso (pi_comparison G f)] : preserves_limit (discrete.functor f) G :=
  by 
    apply preserves_limit_of_preserves_limit_cone (product_is_product f)
    apply (is_limit_map_cone_fan_mk_equiv _ _ _).symm _ 
    apply is_limit.of_point_iso (limit.is_limit (discrete.functor fun j : J => G.obj (f j)))
    apply i

variable [preserves_limit (discrete.functor f) G]

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
def preserves_product.iso : G.obj (∏ f) ≅ ∏ fun j => G.obj (f j) :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_product_of_preserves_limit G f) (limit.is_limit _)

@[simp]
theorem preserves_product.iso_hom : (preserves_product.iso G f).Hom = pi_comparison G f :=
  rfl

instance : is_iso (pi_comparison G f) :=
  by 
    rw [←preserves_product.iso_hom]
    infer_instance

end 

/--
The map of a cofan is a colimit iff the cofan consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cofan.mk` with `functor.map_cocone`.
-/
def is_colimit_map_cocone_cofan_mk_equiv {P : C} (g : ∀ j, f j ⟶ P) :
  is_colimit (G.map_cocone (cofan.mk P g)) ≃
    is_colimit (cofan.mk _ fun j => G.map (g j) : cofan fun j => G.obj (f j)) :=
  by 
    refine' (is_colimit.precompose_hom_equiv _ _).symm.trans (is_colimit.equiv_iso_colimit _)
    refine' discrete.nat_iso fun j => iso.refl (G.obj (f j))
    refine'
      cocones.ext (iso.refl _)
        fun j =>
          by 
            dsimp 
            simp 

/-- The property of preserving coproducts expressed in terms of cofans. -/
def is_colimit_cofan_mk_obj_of_is_colimit [preserves_colimit (discrete.functor f) G] {P : C} (g : ∀ j, f j ⟶ P)
  (t : is_colimit (cofan.mk _ g)) : is_colimit (cofan.mk (G.obj P) fun j => G.map (g j) : cofan fun j => G.obj (f j)) :=
  is_colimit_map_cocone_cofan_mk_equiv _ _ _ (preserves_colimit.preserves t)

/-- The property of reflecting coproducts expressed in terms of cofans. -/
def is_colimit_of_is_colimit_cofan_mk_obj [reflects_colimit (discrete.functor f) G] {P : C} (g : ∀ j, f j ⟶ P)
  (t : is_colimit (cofan.mk _ fun j => G.map (g j) : cofan fun j => G.obj (f j))) : is_colimit (cofan.mk P g) :=
  reflects_colimit.reflects ((is_colimit_map_cocone_cofan_mk_equiv _ _ _).symm t)

section 

variable [has_coproduct f]

/--
If `G` preserves coproducts and `C` has them,
then the cofan constructed of the mapped inclusion of a coproduct is a colimit.
-/
def is_colimit_of_has_coproduct_of_preserves_colimit [preserves_colimit (discrete.functor f) G] :
  is_colimit (cofan.mk _ fun j : J => G.map (sigma.ι f j) : cofan fun j => G.obj (f j)) :=
  is_colimit_cofan_mk_obj_of_is_colimit G f _ (coproduct_is_coproduct _)

variable [has_coproduct fun j : J => G.obj (f j)]

/-- If `sigma_comparison G f` is an isomorphism, then `G` preserves the colimit of `f`. -/
def preserves_coproduct.of_iso_comparison [i : is_iso (sigma_comparison G f)] :
  preserves_colimit (discrete.functor f) G :=
  by 
    apply preserves_colimit_of_preserves_colimit_cocone (coproduct_is_coproduct f)
    apply (is_colimit_map_cocone_cofan_mk_equiv _ _ _).symm _ 
    apply is_colimit.of_point_iso (colimit.is_colimit (discrete.functor fun j : J => G.obj (f j)))
    apply i

variable [preserves_colimit (discrete.functor f) G]

/--
If `G` preserves colimits,
we have an isomorphism from the image of a coproduct to the coproduct of the images.
-/
def preserves_coproduct.iso : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j) :=
  is_colimit.cocone_point_unique_up_to_iso (is_colimit_of_has_coproduct_of_preserves_colimit G f) (colimit.is_colimit _)

@[simp]
theorem preserves_coproduct.inv_hom : (preserves_coproduct.iso G f).inv = sigma_comparison G f :=
  rfl

instance : is_iso (sigma_comparison G f) :=
  by 
    rw [←preserves_coproduct.inv_hom]
    infer_instance

end 

end CategoryTheory.Limits

