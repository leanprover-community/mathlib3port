import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks 
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving pullbacks

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullback_comparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

The dual is also given.

## TODO

* Generalise to wide pullbacks

-/


noncomputable section 

universe v u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [category.{v} C]

variable {D : Type u₂} [category.{v} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section Pullback

variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

/-- The map of a pullback cone is a limit iff the fork consisting of the mapped morphisms is a
limit. This essentially lets us commute `pullback_cone.mk` with `functor.map_cone`. -/
def is_limit_map_cone_pullback_cone_equiv :
  is_limit (G.map_cone (pullback_cone.mk h k comm)) ≃
    is_limit
      (pullback_cone.mk (G.map h) (G.map k)
        (by 
          simp only [←G.map_comp, comm]) :
      pullback_cone (G.map f) (G.map g)) :=
  (is_limit.postcompose_hom_equiv (diagram_iso_cospan.{v} _) _).symm.trans
    (is_limit.equiv_iso_limit
      (cones.ext (iso.refl _)
        (by 
          rintro (_ | _ | _)
          tidy)))

/-- The property of preserving pullbacks expressed in terms of binary fans. -/
def is_limit_pullback_cone_map_of_is_limit [preserves_limit (cospan f g) G] (l : is_limit (pullback_cone.mk h k comm)) :
  is_limit (pullback_cone.mk (G.map h) (G.map k) _) :=
  is_limit_map_cone_pullback_cone_equiv G comm (preserves_limit.preserves l)

/-- The property of reflecting pullbacks expressed in terms of binary fans. -/
def is_limit_of_is_limit_pullback_cone_map [reflects_limit (cospan f g) G]
  (l : is_limit (pullback_cone.mk (G.map h) (G.map k) _)) : is_limit (pullback_cone.mk h k comm) :=
  reflects_limit.reflects ((is_limit_map_cone_pullback_cone_equiv G comm).symm l)

variable (f g) [has_pullback f g]

/-- If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit. -/
def is_limit_of_has_pullback_of_preserves_limit [preserves_limit (cospan f g) G] :
  is_limit (pullback_cone.mk (G.map pullback.fst) (G.map pullback.snd) _) :=
  is_limit_pullback_cone_map_of_is_limit G _ (pullback_is_pullback f g)

variable [has_pullback (G.map f) (G.map g)]

/-- If the pullback comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pullback of `(f,g)`. -/
def preserves_pullback.of_iso_comparison [i : is_iso (pullback_comparison G f g)] : preserves_limit (cospan f g) G :=
  by 
    apply preserves_limit_of_preserves_limit_cone (pullback_is_pullback f g)
    apply (is_limit_map_cone_pullback_cone_equiv _ _).symm _ 
    apply is_limit.of_point_iso (limit.is_limit (cospan (G.map f) (G.map g)))
    apply i

/-- If `F` preserves the pullback of `f, g`, it also preserves the pullback of `g, f`. -/
def preserves_pullback_symmetry {D : Type _} [category D] (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [preserves_limit (cospan f g) F] : preserves_limit (cospan g f) F :=
  { preserves :=
      fun c hc =>
        by 
          apply (is_limit.postcompose_hom_equiv (diagram_iso_cospan.{v} _) _).toFun 
          apply is_limit.of_iso_limit _ (pullback_cone.iso_mk _).symm 
          apply pullback_cone.flip_is_limit 
          apply (is_limit_map_cone_pullback_cone_equiv _ _).toFun
          ·
            apply preserves_limit.preserves with { instances := ff }
            ·
              dsimp 
              infer_instance 
            apply pullback_cone.flip_is_limit 
            apply is_limit.of_iso_limit _ (pullback_cone.iso_mk _)
            exact (is_limit.postcompose_hom_equiv (diagram_iso_cospan.{v} _) _).invFun hc
          ·
            exact (c.π.naturality walking_cospan.hom.inr).symm.trans (c.π.naturality walking_cospan.hom.inl : _) }

variable [preserves_limit (cospan f g) G]

/-- If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `G` at `(f,g)` is
an isomorphism. -/
def preserves_pullback.iso : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_pullback_of_preserves_limit G f g) (limit.is_limit _)

@[simp]
theorem preserves_pullback.iso_hom : (preserves_pullback.iso G f g).Hom = pullback_comparison G f g :=
  rfl

instance : is_iso (pullback_comparison G f g) :=
  by 
    rw [←preserves_pullback.iso_hom]
    infer_instance

@[reassoc]
theorem preserves_pullback.iso_hom_fst : (preserves_pullback.iso G f g).Hom ≫ pullback.fst = G.map pullback.fst :=
  by 
    simp 

@[reassoc]
theorem preserves_pullback.iso_hom_snd : (preserves_pullback.iso G f g).Hom ≫ pullback.snd = G.map pullback.snd :=
  by 
    simp 

@[simp, reassoc]
theorem preserves_pullback.iso_inv_fst : (preserves_pullback.iso G f g).inv ≫ G.map pullback.fst = pullback.fst :=
  by 
    simp [iso.inv_comp_eq]

@[simp, reassoc]
theorem preserves_pullback.iso_inv_snd : (preserves_pullback.iso G f g).inv ≫ G.map pullback.snd = pullback.snd :=
  by 
    simp [iso.inv_comp_eq]

end Pullback

section Pushout

variable {W X Y Z : C} {h : X ⟶ Z} {k : Y ⟶ Z} {f : W ⟶ X} {g : W ⟶ Y} (comm : f ≫ h = g ≫ k)

/-- The map of a pushout cocone is a colimit iff the cofork consisting of the mapped morphisms is a
colimit. This essentially lets us commute `pushout_cocone.mk` with `functor.map_cocone`. -/
def is_colimit_map_cocone_pushout_cocone_equiv :
  is_colimit (G.map_cocone (pushout_cocone.mk h k comm)) ≃
    is_colimit
      (pushout_cocone.mk (G.map h) (G.map k)
        (by 
          simp only [←G.map_comp, comm]) :
      pushout_cocone (G.map f) (G.map g)) :=
  (is_colimit.precompose_hom_equiv (diagram_iso_span.{v} _).symm _).symm.trans
    (is_colimit.equiv_iso_colimit
      (cocones.ext (iso.refl _)
        (by 
          rintro (_ | _ | _)
          tidy)))

/-- The property of preserving pushouts expressed in terms of binary cofans. -/
def is_colimit_pushout_cocone_map_of_is_colimit [preserves_colimit (span f g) G]
  (l : is_colimit (pushout_cocone.mk h k comm)) : is_colimit (pushout_cocone.mk (G.map h) (G.map k) _) :=
  is_colimit_map_cocone_pushout_cocone_equiv G comm (preserves_colimit.preserves l)

/-- The property of reflecting pushouts expressed in terms of binary cofans. -/
def is_colimit_of_is_colimit_pushout_cocone_map [reflects_colimit (span f g) G]
  (l : is_colimit (pushout_cocone.mk (G.map h) (G.map k) _)) : is_colimit (pushout_cocone.mk h k comm) :=
  reflects_colimit.reflects ((is_colimit_map_cocone_pushout_cocone_equiv G comm).symm l)

variable (f g) [has_pushout f g]

/-- If `G` preserves pushouts and `C` has them, then the pushout cocone constructed of the mapped
morphisms of the pushout cocone is a colimit. -/
def is_colimit_of_has_pushout_of_preserves_colimit [preserves_colimit (span f g) G] :
  is_colimit (pushout_cocone.mk (G.map pushout.inl) (G.map pushout.inr) _) :=
  is_colimit_pushout_cocone_map_of_is_colimit G _ (pushout_is_pushout f g)

variable [has_pushout (G.map f) (G.map g)]

/-- If the pushout comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pushout of `(f,g)`. -/
def preserves_pushout.of_iso_comparison [i : is_iso (pushout_comparison G f g)] : preserves_colimit (span f g) G :=
  by 
    apply preserves_colimit_of_preserves_colimit_cocone (pushout_is_pushout f g)
    apply (is_colimit_map_cocone_pushout_cocone_equiv _ _).symm _ 
    apply is_colimit.of_point_iso (colimit.is_colimit (span (G.map f) (G.map g)))
    apply i

/-- If `F` preserves the pushout of `f, g`, it also preserves the pushout of `g, f`. -/
def preserves_pushout_symmetry {D : Type _} [category D] (F : C ⥤ D) (f : X ⟶ Y) (g : X ⟶ Z)
  [preserves_colimit (span f g) F] : preserves_colimit (span g f) F :=
  { preserves :=
      fun c hc =>
        by 
          apply (is_colimit.precompose_hom_equiv (diagram_iso_span.{v} _).symm _).toFun 
          apply is_colimit.of_iso_colimit _ (pushout_cocone.iso_mk _).symm 
          apply pushout_cocone.flip_is_colimit 
          apply (is_colimit_map_cocone_pushout_cocone_equiv _ _).toFun
          ·
            apply preserves_colimit.preserves with { instances := ff }
            ·
              dsimp 
              infer_instance 
            apply pushout_cocone.flip_is_colimit 
            apply is_colimit.of_iso_colimit _ (pushout_cocone.iso_mk _)
            exact (is_colimit.precompose_hom_equiv (diagram_iso_span.{v} _) _).invFun hc
          ·
            exact (c.ι.naturality walking_span.hom.snd).trans (c.ι.naturality walking_span.hom.fst).symm }

variable [preserves_colimit (span f g) G]

/-- If `G` preserves the pushout of `(f,g)`, then the pushout comparison map for `G` at `(f,g)` is
an isomorphism. -/
def preserves_pushout.iso : pushout (G.map f) (G.map g) ≅ G.obj (pushout f g) :=
  is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) (is_colimit_of_has_pushout_of_preserves_colimit G f g)

@[simp]
theorem preserves_pushout.iso_hom : (preserves_pushout.iso G f g).Hom = pushout_comparison G f g :=
  rfl

instance : is_iso (pushout_comparison G f g) :=
  by 
    rw [←preserves_pushout.iso_hom]
    infer_instance

@[reassoc]
theorem preserves_pushout.inl_iso_hom : pushout.inl ≫ (preserves_pushout.iso G f g).Hom = G.map pushout.inl :=
  by 
    simp 

@[reassoc]
theorem preserves_pushout.inr_iso_hom : pushout.inr ≫ (preserves_pushout.iso G f g).Hom = G.map pushout.inr :=
  by 
    simp 

@[simp, reassoc]
theorem preserves_pushout.inl_iso_inv : G.map pushout.inl ≫ (preserves_pushout.iso G f g).inv = pushout.inl :=
  by 
    simp [iso.comp_inv_eq]

@[simp, reassoc]
theorem preserves_pushout.inr_iso_inv : G.map pushout.inr ≫ (preserves_pushout.iso G f g).inv = pushout.inr :=
  by 
    simp [iso.comp_inv_eq]

end Pushout

end CategoryTheory.Limits

