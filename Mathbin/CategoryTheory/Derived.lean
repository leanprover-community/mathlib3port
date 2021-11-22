import Mathbin.CategoryTheory.Preadditive.ProjectiveResolution

/-!
# Left-derived functors

We define the left-derived functors `F.left_derived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.

The definition is
```
projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
```
that is, we pick a projective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these left-derived functors can be calculated
on objects using any choice of projective resolution,
and on morphisms by any choice of lift to a chain map between chosen projective resolutions.

Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Implementation

We don't assume the categories involved are abelian
(just preadditive, and have equalizers, cokernels, and image maps),
or that the functors are right exact.
None of these assumptions are needed yet.

It is often convenient, of course, to work with `[abelian C] [enough_projectives C] [abelian D]`
which (assuming the results from `category_theory.abelian.projective`) are enough to
provide all the typeclass hypotheses assumed here.
-/


noncomputable theory

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable{C : Type u}[category.{v} C]{D : Type _}[category D]

variable[preadditive C][has_zero_object C][has_equalizers C][has_images C][has_projective_resolutions C]

variable[preadditive D][has_zero_object D][has_equalizers D][has_cokernels D][has_images D][has_image_maps D]

/-- The left derived functors of an additive functor. -/
def functor.left_derived (F : C ⥤ D) [F.additive] (n : ℕ) : C ⥤ D :=
  projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ HomotopyCategory.homologyFunctor D _ n

/-- We can compute a left derived functor using a chosen projective resolution. -/
@[simps]
def functor.left_derived_obj_iso (F : C ⥤ D) [F.additive] (n : ℕ) {X : C} (P : ProjectiveResolution X) :
  (F.left_derived n).obj X ≅ (homologyFunctor D _ n).obj ((F.map_homological_complex _).obj P.complex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
      (HomotopyCategory.isoOfHomotopyEquiv (F.map_homotopy_equiv (ProjectiveResolution.homotopy_equiv _ P))) ≪≫
    (HomotopyCategory.homologyFactors D _ n).app _

/-- The 0-th derived functor of `F` on a projective object `X` is just `F.obj X`. -/
@[simps]
def functor.left_derived_obj_projective_zero (F : C ⥤ D) [F.additive] (X : C) [projective X] :
  (F.left_derived 0).obj X ≅ F.obj X :=
  F.left_derived_obj_iso 0 (ProjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((ChainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (ChainComplex.homologyFunctor0Single₀ D).app (F.obj X)

open_locale ZeroObject

/-- The higher derived functors vanish on projective objects. -/
@[simps]
def functor.left_derived_obj_projective_succ (F : C ⥤ D) [F.additive] (n : ℕ) (X : C) [projective X] :
  (F.left_derived (n+1)).obj X ≅ 0 :=
  F.left_derived_obj_iso (n+1) (ProjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((ChainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (ChainComplex.homologyFunctorSuccSingle₀ D n).app (F.obj X)

/--
We can compute a left derived functor on a morphism using a lift of that morphism
to a chain map between chosen projective resolutions.
-/
theorem functor.left_derived_map_eq (F : C ⥤ D) [F.additive] (n : ℕ) {X Y : C} (f : X ⟶ Y) {P : ProjectiveResolution X}
  {Q : ProjectiveResolution Y} (g : P.complex ⟶ Q.complex) (w : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
  (F.left_derived n).map f =
    (F.left_derived_obj_iso n P).Hom ≫
      (homologyFunctor D _ n).map ((F.map_homological_complex _).map g) ≫ (F.left_derived_obj_iso n Q).inv :=
  by 
    dsimp only [functor.left_derived, functor.left_derived_obj_iso]
    dsimp 
    simp only [category.comp_id, category.id_comp]
    rw [←homology_functor_map, HomotopyCategory.homology_functor_map_factors]
    simp only [←functor.map_comp]
    congr 1
    apply HomotopyCategory.eq_of_homotopy 
    apply functor.map_homotopy 
    apply Homotopy.trans 
    exact HomotopyCategory.homotopyOutMap _ 
    apply ProjectiveResolution.lift_homotopy f
    ·
      simp 
    ·
      simp [w]

/-- The natural transformation between left-derived functors induced by a natural transformation. -/
@[simps]
def nat_trans.left_derived {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ) :
  F.left_derived n ⟶ G.left_derived n :=
  whisker_left (projective_resolutions C)
    (whisker_right (nat_trans.map_homotopy_category α _) (HomotopyCategory.homologyFunctor D _ n))

@[simp]
theorem nat_trans.left_derived_id (F : C ⥤ D) [F.additive] (n : ℕ) :
  nat_trans.left_derived (𝟙 F) n = 𝟙 (F.left_derived n) :=
  by 
    simp [nat_trans.left_derived]
    rfl

@[simp, nolint simp_nf]
theorem nat_trans.left_derived_comp {F G H : C ⥤ D} [F.additive] [G.additive] [H.additive] (α : F ⟶ G) (β : G ⟶ H)
  (n : ℕ) : nat_trans.left_derived (α ≫ β) n = nat_trans.left_derived α n ≫ nat_trans.left_derived β n :=
  by 
    simp [nat_trans.left_derived]

/--
A component of the natural transformation between left-derived functors can be computed
using a chosen projective resolution.
-/
theorem nat_trans.left_derived_eq {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ) {X : C}
  (P : ProjectiveResolution X) :
  (nat_trans.left_derived α n).app X =
    (F.left_derived_obj_iso n P).Hom ≫
      (homologyFunctor D _ n).map ((nat_trans.map_homological_complex α _).app P.complex) ≫
        (G.left_derived_obj_iso n P).inv :=
  by 
    symm 
    dsimp [nat_trans.left_derived, functor.left_derived_obj_iso]
    simp only [category.comp_id, category.id_comp]
    rw [←homology_functor_map, HomotopyCategory.homology_functor_map_factors]
    simp only [←functor.map_comp]
    congr 1
    apply HomotopyCategory.eq_of_homotopy 
    simp only [nat_trans.map_homological_complex_naturality_assoc, ←functor.map_comp]
    apply Homotopy.compLeftId 
    rw [←Functor.map_id]
    apply functor.map_homotopy 
    apply HomotopyEquiv.homotopyHomInvId

end CategoryTheory

