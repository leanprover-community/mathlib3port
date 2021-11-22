import Mathbin.Algebra.Homology.ImageToKernel 
import Mathbin.Algebra.Homology.HomologicalComplex 
import Mathbin.CategoryTheory.GradedObject

/-!
# The homology of a complex

Given `C : homological_complex V c`, we have `C.cycles i` and `C.boundaries i`,
both defined as subobjects of `C.X i`.

We show these are functorial with respect to chain maps,
as `C.cycles_map f i` and `C.boundaries_map f i`.

As a consequence we construct `homology_functor i : homological_complex V c ⥤ V`,
computing the `i`-th homology.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

variable{ι : Type _}

variable{V : Type u}[category.{v} V][has_zero_morphisms V]

variable{c : ComplexShape ι}(C : HomologicalComplex V c)

open_locale Classical ZeroObject

noncomputable theory

namespace HomologicalComplex

variable[has_zero_object V]

section Cycles

variable[has_kernels V]

/-- The cycles at index `i`, as a subobject. -/
def cycles (i : ι) : subobject (C.X i) :=
  kernel_subobject (C.d_from i)

@[simp, reassoc]
theorem cycles_arrow_d_from (i : ι) : (C.cycles i).arrow ≫ C.d_from i = 0 :=
  by 
    dsimp [cycles]
    simp 

theorem cycles_eq_kernel_subobject {i j : ι} (r : c.rel i j) : C.cycles i = kernel_subobject (C.d i j) :=
  C.kernel_from_eq_kernel r

/--
The underlying object of `C.cycles i` is isomorphic to `kernel (C.d i j)`,
for any `j` such that `rel i j`.
-/
def cycles_iso_kernel {i j : ι} (r : c.rel i j) : (C.cycles i : V) ≅ kernel (C.d i j) :=
  subobject.iso_of_eq _ _ (C.cycles_eq_kernel_subobject r) ≪≫ kernel_subobject_iso (C.d i j)

theorem cycles_eq_top {i} (h : c.next i = none) : C.cycles i = ⊤ :=
  by 
    rw [eq_top_iff]
    apply le_kernel_subobject 
    rw [C.d_from_eq_zero h, comp_zero]

end Cycles

section Boundaries

variable[has_images V]

/-- The boundaries at index `i`, as a subobject. -/
abbrev boundaries (C : HomologicalComplex V c) (j : ι) : subobject (C.X j) :=
  image_subobject (C.d_to j)

theorem boundaries_eq_image_subobject [has_equalizers V] {i j : ι} (r : c.rel i j) :
  C.boundaries j = image_subobject (C.d i j) :=
  C.image_to_eq_image r

/--
The underlying object of `C.boundaries j` is isomorphic to `image (C.d i j)`,
for any `i` such that `rel i j`.
-/
def boundaries_iso_image [has_equalizers V] {i j : ι} (r : c.rel i j) : (C.boundaries j : V) ≅ image (C.d i j) :=
  subobject.iso_of_eq _ _ (C.boundaries_eq_image_subobject r) ≪≫ image_subobject_iso (C.d i j)

theorem boundaries_eq_bot {j} (h : c.prev j = none) : C.boundaries j = ⊥ :=
  by 
    rw [eq_bot_iff]
    refine' image_subobject_le _ 0 _ 
    rw [C.d_to_eq_zero h, zero_comp]

end Boundaries

section 

variable[has_kernels V][has_images V]

theorem boundaries_le_cycles (C : HomologicalComplex V c) (i : ι) : C.boundaries i ≤ C.cycles i :=
  image_le_kernel _ _ (C.d_to_comp_d_from i)

/--
The canonical map from `boundaries i` to `cycles i`.
-/
abbrev boundaries_to_cycles (C : HomologicalComplex V c) (i : ι) : (C.boundaries i : V) ⟶ (C.cycles i : V) :=
  imageToKernel _ _ (C.d_to_comp_d_from i)

/-- Prefer `boundaries_to_cycles`. -/
@[simp]
theorem image_to_kernel_as_boundaries_to_cycles (C : HomologicalComplex V c) (i : ι) h :
  (C.boundaries i).ofLe (C.cycles i) h = C.boundaries_to_cycles i :=
  rfl

@[simp, reassoc]
theorem boundaries_to_cycles_arrow (C : HomologicalComplex V c) (i : ι) :
  C.boundaries_to_cycles i ≫ (C.cycles i).arrow = (C.boundaries i).arrow :=
  by 
    dsimp [cycles]
    simp 

variable[has_cokernels V]

/--
The homology of a complex at index `i`.
-/
abbrev homology (C : HomologicalComplex V c) (i : ι) : V :=
  homology (C.d_to i) (C.d_from i) (C.d_to_comp_d_from i)

end 

end HomologicalComplex

open HomologicalComplex

/-! Computing the cycles is functorial. -/


section 

variable[has_zero_object V][has_kernels V]

variable{C₁ C₂ C₃ : HomologicalComplex V c}(f : C₁ ⟶ C₂)

/--
The morphism between cycles induced by a chain map.
-/
abbrev cyclesMap (f : C₁ ⟶ C₂) (i : ι) : (C₁.cycles i : V) ⟶ (C₂.cycles i : V) :=
  subobject.factor_thru _ ((C₁.cycles i).arrow ≫ f.f i)
    (kernel_subobject_factors _ _
      (by 
        simp ))

@[simp]
theorem cycles_map_arrow (f : C₁ ⟶ C₂) (i : ι) : cyclesMap f i ≫ (C₂.cycles i).arrow = (C₁.cycles i).arrow ≫ f.f i :=
  by 
    simp 

@[simp]
theorem cycles_map_id (i : ι) : cyclesMap (𝟙 C₁) i = 𝟙 _ :=
  by 
    dunfold cyclesMap 
    simp 

@[simp]
theorem cycles_map_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : cyclesMap (f ≫ g) i = cyclesMap f i ≫ cyclesMap g i :=
  by 
    dunfold cyclesMap 
    simp [subobject.factor_thru_right]

variable(V c)

/-- Cycles as a functor. -/
@[simps]
def cyclesFunctor (i : ι) : HomologicalComplex V c ⥤ V :=
  { obj := fun C => C.cycles i, map := fun C₁ C₂ f => cyclesMap f i }

end 

/-! Computing the boundaries is functorial. -/


section 

variable[has_zero_object V][has_images V][has_image_maps V]

variable{C₁ C₂ C₃ : HomologicalComplex V c}(f : C₁ ⟶ C₂)

/--
The morphism between boundaries induced by a chain map.
-/
abbrev boundariesMap (f : C₁ ⟶ C₂) (i : ι) : (C₁.boundaries i : V) ⟶ (C₂.boundaries i : V) :=
  image_subobject_map (f.sq_to i)

variable(V c)

/-- Boundaries as a functor. -/
@[simps]
def boundariesFunctor (i : ι) : HomologicalComplex V c ⥤ V :=
  { obj := fun C => C.boundaries i, map := fun C₁ C₂ f => image_subobject_map (f.sq_to i) }

end 

section 

/-! The `boundaries_to_cycles` morphisms are natural. -/


variable[has_zero_object V][has_equalizers V][has_images V][has_image_maps V]

variable{C₁ C₂ : HomologicalComplex V c}(f : C₁ ⟶ C₂)

@[simp, reassoc]
theorem boundaries_to_cycles_naturality (i : ι) :
  boundariesMap f i ≫ C₂.boundaries_to_cycles i = C₁.boundaries_to_cycles i ≫ cyclesMap f i :=
  by 
    ext 
    simp 

variable(V c)

/-- The natural transformation from the boundaries functor to the cycles functor. -/
@[simps]
def boundariesToCyclesNatTrans (i : ι) : boundariesFunctor V c i ⟶ cyclesFunctor V c i :=
  { app := fun C => C.boundaries_to_cycles i, naturality' := fun C₁ C₂ f => boundaries_to_cycles_naturality f i }

/-- The `i`-th homology, as a functor to `V`. -/
@[simps]
def homologyFunctor [has_cokernels V] (i : ι) : HomologicalComplex V c ⥤ V :=
  { obj := fun C => C.homology i, map := fun C₁ C₂ f => _root_.homology.map _ _ (f.sq_to i) (f.sq_from i) rfl,
    map_id' :=
      by 
        intros 
        ext1 
        simp only [homology.π_map, kernel_subobject_map_id, hom.sq_from_id, category.id_comp, category.comp_id],
    map_comp' :=
      by 
        intros 
        ext1 
        simp only [hom.sq_from_comp, kernel_subobject_map_comp, homology.π_map_assoc, homology.π_map, category.assoc] }

/-- The homology functor from `ι`-indexed complexes to `ι`-graded objects in `V`. -/
@[simps]
def gradedHomologyFunctor [has_cokernels V] : HomologicalComplex V c ⥤ graded_object ι V :=
  { obj := fun C i => C.homology i, map := fun C C' f i => (homologyFunctor V c i).map f,
    map_id' :=
      by 
        intros 
        ext 
        simp only [pi.id_apply, homology.π_map, homology_functor_map, kernel_subobject_map_id, hom.sq_from_id,
          category.id_comp, category.comp_id],
    map_comp' :=
      by 
        intros 
        ext 
        simp only [hom.sq_from_comp, kernel_subobject_map_comp, homology.π_map_assoc, pi.comp_apply, homology.π_map,
          homology_functor_map, category.assoc] }

end 

