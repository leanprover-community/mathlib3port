import Mathbin.Algebra.Homology.Homology
import Mathbin.Algebra.Homology.Single
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homology is an additive functor

When `V` is preadditive, `homological_complex V c` is also preadditive,
and `homology_functor` is additive.

TODO: similarly for `R`-linear.
-/


universe v u

open_locale Classical

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable {V : Type u} [category.{v} V] [preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

namespace HomologicalComplex

instance : Zero (C ⟶ D) :=
  ⟨{ f := fun i => 0 }⟩

instance : Add (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i + g.f i }⟩

instance : Neg (C ⟶ D) :=
  ⟨fun f => { f := fun i => -f.f i }⟩

instance : Sub (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i - g.f i }⟩

@[simp]
theorem zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl

@[simp]
theorem add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i :=
  rfl

@[simp]
theorem neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -f.f i :=
  rfl

@[simp]
theorem sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i :=
  rfl

instance : AddCommGroupₓ (C ⟶ D) :=
  Function.Injective.addCommGroup hom.f HomologicalComplex.hom_f_injective
    (by
      tidy)
    (by
      tidy)
    (by
      tidy)
    (by
      tidy)

instance : preadditive (HomologicalComplex V c) :=
  {  }

/-- The `i`-th component of a chain map, as an additive map from chain maps to morphisms. -/
@[simps]
def hom.f_add_monoid_hom {C₁ C₂ : HomologicalComplex V c} (i : ι) : (C₁ ⟶ C₂) →+ (C₁.X i ⟶ C₂.X i) :=
  AddMonoidHom.mk' (fun f => hom.f f i) fun _ _ => rfl

end HomologicalComplex

namespace HomologicalComplex

instance eval_additive (i : ι) : (eval V c i).Additive :=
  {  }

variable [has_zero_object V]

instance cycles_additive [has_equalizers V] : (cyclesFunctor V c i).Additive :=
  {  }

variable [has_images V] [has_image_maps V]

instance boundaries_additive : (boundariesFunctor V c i).Additive :=
  {  }

variable [has_equalizers V] [has_cokernels V]

instance homology_additive : (homologyFunctor V c i).Additive where
  map_add' := fun C D f g => by
    dsimp [homologyFunctor]
    ext
    simp only [homology.π_map, preadditive.comp_add, ← preadditive.add_comp]
    congr
    ext
    simp

end HomologicalComplex

namespace CategoryTheory

variable {W : Type _} [category W] [preadditive W]

/-- An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
@[simps]
def functor.map_homological_complex (F : V ⥤ W) [F.additive] (c : ComplexShape ι) :
    HomologicalComplex V c ⥤ HomologicalComplex W c where
  obj := fun C =>
    { x := fun i => F.obj (C.X i), d := fun i j => F.map (C.d i j),
      shape' := fun i j w => by
        rw [C.shape _ _ w, F.map_zero],
      d_comp_d' := fun i j k _ _ => by
        rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map := fun C D f =>
    { f := fun i => F.map (f.f i),
      comm' := fun i j h => by
        dsimp
        rw [← F.map_comp, ← F.map_comp, f.comm] }

instance functor.map_homogical_complex_additive (F : V ⥤ W) [F.additive] (c : ComplexShape ι) :
    (F.map_homological_complex c).Additive :=
  {  }

/-- A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
@[simps]
def nat_trans.map_homological_complex {F G : V ⥤ W} [F.additive] [G.additive] (α : F ⟶ G) (c : ComplexShape ι) :
    F.map_homological_complex c ⟶ G.map_homological_complex c where
  app := fun C => { f := fun i => α.app _ }

@[simp]
theorem nat_trans.map_homological_complex_id (c : ComplexShape ι) (F : V ⥤ W) [F.additive] :
    nat_trans.map_homological_complex (𝟙 F) c = 𝟙 (F.map_homological_complex c) := by
  tidy

@[simp]
theorem nat_trans.map_homological_complex_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.additive] [G.additive]
    [H.additive] (α : F ⟶ G) (β : G ⟶ H) :
    nat_trans.map_homological_complex (α ≫ β) c =
      nat_trans.map_homological_complex α c ≫ nat_trans.map_homological_complex β c :=
  by
  tidy

@[simp, reassoc]
theorem nat_trans.map_homological_complex_naturality {c : ComplexShape ι} {F G : V ⥤ W} [F.additive] [G.additive]
    (α : F ⟶ G) {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (F.map_homological_complex c).map f ≫ (nat_trans.map_homological_complex α c).app D =
      (nat_trans.map_homological_complex α c).app C ≫ (G.map_homological_complex c).map f :=
  by
  tidy

end CategoryTheory

variable [has_zero_object V] {W : Type _} [category W] [preadditive W] [has_zero_object W]

namespace HomologicalComplex

/-- Turning an object into a complex supported at `j` then applying a functor is
the same as applying the functor then forming the complex.
-/
def single_map_homological_complex (F : V ⥤ W) [F.additive] (c : ComplexShape ι) (j : ι) :
    single V c j ⋙ F.map_homological_complex _ ≅ F ⋙ single W c j :=
  nat_iso.of_components
    (fun X =>
      { Hom :=
          { f := fun i =>
              if h : i = j then
                eq_to_hom
                  (by
                    simp [h])
              else 0 },
        inv :=
          { f := fun i =>
              if h : i = j then
                eq_to_hom
                  (by
                    simp [h])
              else 0 },
        hom_inv_id' := by
          ext i
          dsimp
          split_ifs with h
          · simp [h]
            
          · rw [zero_comp, if_neg h]
            exact (zero_of_source_iso_zero _ F.map_zero_object).symm
            ,
        inv_hom_id' := by
          ext i
          dsimp
          split_ifs with h
          · simp [h]
            
          · rw [zero_comp, if_neg h]
            simp
             })
    fun X Y f => by
    ext i
    dsimp
    split_ifs with h <;> simp [h]

variable (F : V ⥤ W) [functor.additive F] (c)

@[simp]
theorem single_map_homological_complex_hom_app_self (j : ι) (X : V) :
    ((single_map_homological_complex F c j).Hom.app X).f j =
      eq_to_hom
        (by
          simp ) :=
  by
  simp [single_map_homological_complex]

@[simp]
theorem single_map_homological_complex_hom_app_ne {i j : ι} (h : i ≠ j) (X : V) :
    ((single_map_homological_complex F c j).Hom.app X).f i = 0 := by
  simp [single_map_homological_complex, h]

@[simp]
theorem single_map_homological_complex_inv_app_self (j : ι) (X : V) :
    ((single_map_homological_complex F c j).inv.app X).f j =
      eq_to_hom
        (by
          simp ) :=
  by
  simp [single_map_homological_complex]

@[simp]
theorem single_map_homological_complex_inv_app_ne {i j : ι} (h : i ≠ j) (X : V) :
    ((single_map_homological_complex F c j).inv.app X).f i = 0 := by
  simp [single_map_homological_complex, h]

end HomologicalComplex

namespace ChainComplex

/-- Turning an object into a chain complex supported at zero then applying a functor is
the same as applying the functor then forming the complex.
-/
def single₀_map_homological_complex (F : V ⥤ W) [F.additive] :
    single₀ V ⋙ F.map_homological_complex _ ≅ F ⋙ single₀ W :=
  nat_iso.of_components
    (fun X =>
      { Hom :=
          { f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.map_zero_object.hom },
        inv :=
          { f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.map_zero_object.inv },
        hom_inv_id' := by
          ext (_ | i)
          · unfold_aux
            simp
            
          · unfold_aux
            dsimp
            simp only [comp_f, id_f, zero_comp]
            exact (zero_of_source_iso_zero _ F.map_zero_object).symm
            ,
        inv_hom_id' := by
          ext (_ | i) <;>
            · unfold_aux
              dsimp
              simp
               })
    fun X Y f => by
    ext (_ | i) <;>
      · unfold_aux
        dsimp
        simp
        

@[simp]
theorem single₀_map_homological_complex_hom_app_zero (F : V ⥤ W) [F.additive] (X : V) :
    ((single₀_map_homological_complex F).Hom.app X).f 0 = 𝟙 _ :=
  rfl

@[simp]
theorem single₀_map_homological_complex_hom_app_succ (F : V ⥤ W) [F.additive] (X : V) (n : ℕ) :
    ((single₀_map_homological_complex F).Hom.app X).f (n + 1) = 0 :=
  rfl

@[simp]
theorem single₀_map_homological_complex_inv_app_zero (F : V ⥤ W) [F.additive] (X : V) :
    ((single₀_map_homological_complex F).inv.app X).f 0 = 𝟙 _ :=
  rfl

@[simp]
theorem single₀_map_homological_complex_inv_app_succ (F : V ⥤ W) [F.additive] (X : V) (n : ℕ) :
    ((single₀_map_homological_complex F).inv.app X).f (n + 1) = 0 :=
  rfl

end ChainComplex

