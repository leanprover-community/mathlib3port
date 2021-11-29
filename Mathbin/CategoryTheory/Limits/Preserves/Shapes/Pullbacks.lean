import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks 
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving pullbacks

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullback_comparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

## TODO

* Dualise to pushouts
* Generalise to wide pullbacks

-/


noncomputable theory

universe v u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [category.{v} C]

variable {D : Type u₂} [category.{v} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

/--
The map of a pullback cone is a limit iff the fork consisting of the mapped morphisms is a limit.
This essentially lets us commute `pullback_cone.mk` with `functor.map_cone`.
-/
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

/--
If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit.
-/
def is_limit_of_has_pullback_of_preserves_limit [preserves_limit (cospan f g) G] :
  is_limit (pullback_cone.mk (G.map pullback.fst) (G.map pullback.snd) _) :=
  is_limit_pullback_cone_map_of_is_limit G _ (pullback_is_pullback f g)

variable [has_pullback (G.map f) (G.map g)]

/--
If the pullback comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pullback of `(f,g)`.
-/
def preserves_pullback.of_iso_comparison [i : is_iso (pullback_comparison G f g)] : preserves_limit (cospan f g) G :=
  by 
    apply preserves_limit_of_preserves_limit_cone (pullback_is_pullback f g)
    apply (is_limit_map_cone_pullback_cone_equiv _ _).symm _ 
    apply is_limit.of_point_iso (limit.is_limit (cospan (G.map f) (G.map g)))
    apply i

variable [preserves_limit (cospan f g) G]

/--
If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def preserves_pullback.iso : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_pullback_of_preserves_limit G f g) (limit.is_limit _)

@[simp]
theorem preserves_pullback.iso_hom : (preserves_pullback.iso G f g).Hom = pullback_comparison G f g :=
  rfl

instance : is_iso (pullback_comparison G f g) :=
  by 
    rw [←preserves_pullback.iso_hom]
    infer_instance

end CategoryTheory.Limits

