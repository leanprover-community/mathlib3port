import Mathbin.CategoryTheory.Limits.Shapes.SplitCoequalizer 
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving (co)equalizers

Constructions to relate the notions of preserving (co)equalizers and reflecting (co)equalizers
to concrete (co)forks.

In particular, we show that `equalizer_comparison G f` is an isomorphism iff `G` preserves
the limit of `f` as well as the dual.
-/


noncomputable section 

universe v u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [category.{v} C]

variable {D : Type u₂} [category.{v} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section Equalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

/--
The map of a fork is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `fork.of_ι` with `functor.map_cone`.
-/
def is_limit_map_cone_fork_equiv :
  is_limit (G.map_cone (fork.of_ι h w)) ≃
    is_limit
      (fork.of_ι (G.map h)
        (by 
          simp only [←G.map_comp, w]) :
      fork (G.map f) (G.map g)) :=
  (is_limit.postcompose_hom_equiv (diagram_iso_parallel_pair.{v} _) _).symm.trans
    (is_limit.equiv_iso_limit
      (fork.ext (iso.refl _)
        (by 
          simp )))

/-- The property of preserving equalizers expressed in terms of forks. -/
def is_limit_fork_map_of_is_limit [preserves_limit (parallel_pair f g) G] (l : is_limit (fork.of_ι h w)) :
  is_limit
    (fork.of_ι (G.map h)
      (by 
        simp only [←G.map_comp, w]) :
    fork (G.map f) (G.map g)) :=
  is_limit_map_cone_fork_equiv G w (preserves_limit.preserves l)

/-- The property of reflecting equalizers expressed in terms of forks. -/
def is_limit_of_is_limit_fork_map [reflects_limit (parallel_pair f g) G]
  (l :
    is_limit
      (fork.of_ι (G.map h)
        (by 
          simp only [←G.map_comp, w]) :
      fork (G.map f) (G.map g))) :
  is_limit (fork.of_ι h w) :=
  reflects_limit.reflects ((is_limit_map_cone_fork_equiv G w).symm l)

variable (f g) [has_equalizer f g]

/--
If `G` preserves equalizers and `C` has them, then the fork constructed of the mapped morphisms of
a fork is a limit.
-/
def is_limit_of_has_equalizer_of_preserves_limit [preserves_limit (parallel_pair f g) G] :
  is_limit
    (fork.of_ι (G.map (equalizer.ι f g))
      (by 
        simp only [←G.map_comp, equalizer.condition])) :=
  is_limit_fork_map_of_is_limit G _ (equalizer_is_equalizer f g)

variable [has_equalizer (G.map f) (G.map g)]

/--
If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
equalizer of `(f,g)`.
-/
def preserves_equalizer.of_iso_comparison [i : is_iso (equalizer_comparison f g G)] :
  preserves_limit (parallel_pair f g) G :=
  by 
    apply preserves_limit_of_preserves_limit_cone (equalizer_is_equalizer f g)
    apply (is_limit_map_cone_fork_equiv _ _).symm _ 
    apply is_limit.of_point_iso (limit.is_limit (parallel_pair (G.map f) (G.map g)))
    apply i

variable [preserves_limit (parallel_pair f g) G]

/--
If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def preserves_equalizer.iso : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_equalizer_of_preserves_limit G f g) (limit.is_limit _)

@[simp]
theorem preserves_equalizer.iso_hom : (preserves_equalizer.iso G f g).Hom = equalizer_comparison f g G :=
  rfl

instance : is_iso (equalizer_comparison f g G) :=
  by 
    rw [←preserves_equalizer.iso_hom]
    infer_instance

end Equalizers

section Coequalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h)

/--
The map of a cofork is a colimit iff the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cofork.of_π` with `functor.map_cocone`.
-/
def is_colimit_map_cocone_cofork_equiv :
  is_colimit (G.map_cocone (cofork.of_π h w)) ≃
    is_colimit
      (cofork.of_π (G.map h)
        (by 
          simp only [←G.map_comp, w]) :
      cofork (G.map f) (G.map g)) :=
  (is_colimit.precompose_inv_equiv (diagram_iso_parallel_pair.{v} _) _).symm.trans
    (is_colimit.equiv_iso_colimit
      (cofork.ext (iso.refl _)
        (by 
          dsimp 
          simp )))

/-- The property of preserving coequalizers expressed in terms of coforks. -/
def is_colimit_cofork_map_of_is_colimit [preserves_colimit (parallel_pair f g) G] (l : is_colimit (cofork.of_π h w)) :
  is_colimit
    (cofork.of_π (G.map h)
      (by 
        simp only [←G.map_comp, w]) :
    cofork (G.map f) (G.map g)) :=
  is_colimit_map_cocone_cofork_equiv G w (preserves_colimit.preserves l)

/-- The property of reflecting coequalizers expressed in terms of coforks. -/
def is_colimit_of_is_colimit_cofork_map [reflects_colimit (parallel_pair f g) G]
  (l :
    is_colimit
      (cofork.of_π (G.map h)
        (by 
          simp only [←G.map_comp, w]) :
      cofork (G.map f) (G.map g))) :
  is_colimit (cofork.of_π h w) :=
  reflects_colimit.reflects ((is_colimit_map_cocone_cofork_equiv G w).symm l)

variable (f g) [has_coequalizer f g]

/--
If `G` preserves coequalizers and `C` has them, then the cofork constructed of the mapped morphisms
of a cofork is a colimit.
-/
def is_colimit_of_has_coequalizer_of_preserves_colimit [preserves_colimit (parallel_pair f g) G] :
  is_colimit (cofork.of_π (G.map (coequalizer.π f g)) _) :=
  is_colimit_cofork_map_of_is_colimit G _ (coequalizer_is_coequalizer f g)

variable [has_coequalizer (G.map f) (G.map g)]

/--
If the coequalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
coequalizer of `(f,g)`.
-/
def of_iso_comparison [i : is_iso (coequalizer_comparison f g G)] : preserves_colimit (parallel_pair f g) G :=
  by 
    apply preserves_colimit_of_preserves_colimit_cocone (coequalizer_is_coequalizer f g)
    apply (is_colimit_map_cocone_cofork_equiv _ _).symm _ 
    apply is_colimit.of_point_iso (colimit.is_colimit (parallel_pair (G.map f) (G.map g)))
    apply i

variable [preserves_colimit (parallel_pair f g) G]

/--
If `G` preserves the coequalizer of `(f,g)`, then the coequalizer comparison map for `G` at `(f,g)`
is an isomorphism.
-/
def preserves_coequalizer.iso : coequalizer (G.map f) (G.map g) ≅ G.obj (coequalizer f g) :=
  is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
    (is_colimit_of_has_coequalizer_of_preserves_colimit G f g)

@[simp]
theorem preserves_coequalizer.iso_hom : (preserves_coequalizer.iso G f g).Hom = coequalizer_comparison f g G :=
  rfl

instance : is_iso (coequalizer_comparison f g G) :=
  by 
    rw [←preserves_coequalizer.iso_hom]
    infer_instance

/-- Any functor preserves coequalizers of split pairs. -/
instance (priority := 1) preserves_split_coequalizers (f g : X ⟶ Y) [has_split_coequalizer f g] :
  preserves_colimit (parallel_pair f g) G :=
  by 
    apply preserves_colimit_of_preserves_colimit_cocone (has_split_coequalizer.is_split_coequalizer f g).isCoequalizer 
    apply
      (is_colimit_map_cocone_cofork_equiv G _).symm
        ((has_split_coequalizer.is_split_coequalizer f g).map G).isCoequalizer

end Coequalizers

end CategoryTheory.Limits

