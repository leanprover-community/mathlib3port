import Mathbin.CategoryTheory.Shift

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, zero morphisms and zero objects, and the shift functor
on differential objects.
-/


open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (C : Type u) [category.{v} C]

variable [has_zero_morphisms C] [has_shift C ℤ]

/-- A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.
-/
@[nolint has_inhabited_instance]
structure differential_object where
  x : C
  d : X ⟶ X⟦1⟧
  d_squared' : d ≫ d⟦(1 : ℤ)⟧' = 0 := by
    run_tac
      obviously

restate_axiom differential_object.d_squared'

attribute [simp] differential_object.d_squared

variable {C}

namespace DifferentialObject

/-- A morphism of differential objects is a morphism commuting with the differentials.
-/
@[ext, nolint has_inhabited_instance]
structure hom (X Y : differential_object C) where
  f : X.X ⟶ Y.X
  comm' : X.d ≫ f⟦1⟧' = f ≫ Y.d := by
    run_tac
      obviously

restate_axiom hom.comm'

attribute [simp, reassoc] hom.comm

namespace Hom

/-- The identity morphism of a differential object. -/
@[simps]
def id (X : differential_object C) : hom X X where
  f := 𝟙 X.X

/-- The composition of morphisms of differential objects. -/
@[simps]
def comp {X Y Z : differential_object C} (f : hom X Y) (g : hom Y Z) : hom X Z where
  f := f.f ≫ g.f

end Hom

instance category_of_differential_objects : category (differential_object C) where
  Hom := hom
  id := hom.id
  comp := fun X Y Z f g => hom.comp f g

@[simp]
theorem id_f (X : differential_object C) : (𝟙 X : X ⟶ X).f = 𝟙 X.X :=
  rfl

@[simp]
theorem comp_f {X Y Z : differential_object C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

@[simp]
theorem eq_to_hom_f {X Y : differential_object C} (h : X = Y) : hom.f (eq_to_hom h) = eq_to_hom (congr_argₓ _ h) := by
  subst h
  rw [eq_to_hom_refl, eq_to_hom_refl]
  rfl

variable (C)

/-- The forgetful functor taking a differential object to its underlying object. -/
def forget : differential_object C ⥤ C where
  obj := fun X => X.X
  map := fun X Y f => f.f

instance forget_faithful : faithful (forget C) :=
  {  }

instance has_zero_morphisms : has_zero_morphisms (differential_object C) where
  HasZero := fun X Y => ⟨{ f := 0 }⟩

variable {C}

@[simp]
theorem zero_f (P Q : differential_object C) : (0 : P ⟶ Q).f = 0 :=
  rfl

/-- An isomorphism of differential objects gives an isomorphism of the underlying objects.
-/
@[simps]
def iso_app {X Y : differential_object C} (f : X ≅ Y) : X.X ≅ Y.X :=
  ⟨f.hom.f, f.inv.f, by
    dsimp
    rw [← comp_f, iso.hom_inv_id, id_f], by
    dsimp
    rw [← comp_f, iso.inv_hom_id, id_f]⟩

@[simp]
theorem iso_app_refl (X : differential_object C) : iso_app (iso.refl X) = iso.refl X.X :=
  rfl

@[simp]
theorem iso_app_symm {X Y : differential_object C} (f : X ≅ Y) : iso_app f.symm = (iso_app f).symm :=
  rfl

@[simp]
theorem iso_app_trans {X Y Z : differential_object C} (f : X ≅ Y) (g : Y ≅ Z) :
    iso_app (f ≪≫ g) = iso_app f ≪≫ iso_app g :=
  rfl

/-- An isomorphism of differential objects can be constructed
from an isomorphism of the underlying objects that commutes with the differentials. -/
@[simps]
def mk_iso {X Y : differential_object C} (f : X.X ≅ Y.X) (hf : X.d ≫ f.hom⟦1⟧' = f.hom ≫ Y.d) : X ≅ Y where
  Hom := ⟨f.hom, hf⟩
  inv :=
    ⟨f.inv, by
      dsimp
      rw [← functor.map_iso_inv, iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, functor.map_iso_hom, hf]⟩
  hom_inv_id' := by
    ext1
    dsimp
    exact f.hom_inv_id
  inv_hom_id' := by
    ext1
    dsimp
    exact f.inv_hom_id

end DifferentialObject

namespace Functor

universe v' u'

variable (D : Type u') [category.{v'} D]

variable [has_zero_morphisms D] [has_shift D ℤ]

/-- A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero morphisms
can be lifted to a functor `differential_object C ⥤ differential_object D`.
-/
@[simps]
def map_differential_object (F : C ⥤ D) (η : (shift_functor C (1 : ℤ)).comp F ⟶ F.comp (shift_functor D (1 : ℤ)))
    (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) : differential_object C ⥤ differential_object D where
  obj := fun X =>
    { x := F.obj X.X, d := F.map X.d ≫ η.app X.X,
      d_squared' := by
        rw [functor.map_comp, ← functor.comp_map F (shift_functor D (1 : ℤ))]
        slice_lhs 2 3 => rw [← η.naturality X.d]
        rw [functor.comp_map]
        slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
        rw [zero_comp, zero_comp] }
  map := fun X Y f =>
    { f := F.map f.f,
      comm' := by
        dsimp
        slice_lhs 2 3 => rw [← functor.comp_map F (shift_functor D (1 : ℤ)), ← η.naturality f.f]
        slice_lhs 1 2 => rw [functor.comp_map, ← F.map_comp, f.comm, F.map_comp]
        rw [category.assoc] }
  map_id' := by
    intros
    ext
    simp
  map_comp' := by
    intros
    ext
    simp

end Functor

end CategoryTheory

namespace CategoryTheory

namespace DifferentialObject

variable (C : Type u) [category.{v} C]

variable [has_zero_object C] [has_zero_morphisms C] [has_shift C ℤ]

open_locale ZeroObject

instance has_zero_object : has_zero_object (differential_object C) where
  zero := { x := (0 : C), d := 0 }
  uniqueTo := fun X =>
    ⟨⟨{ f := 0 }⟩, fun f => by
      ext⟩
  uniqueFrom := fun X =>
    ⟨⟨{ f := 0 }⟩, fun f => by
      ext⟩

end DifferentialObject

namespace DifferentialObject

variable (C : Type (u + 1)) [large_category C] [concrete_category C] [has_zero_morphisms C] [has_shift C ℤ]

instance concrete_category_of_differential_objects : concrete_category (differential_object C) where
  forget := forget C ⋙ CategoryTheory.forget C

instance : has_forget₂ (differential_object C) C where
  forget₂ := forget C

end DifferentialObject

/-! The category of differential objects itself has a shift functor. -/


namespace DifferentialObject

variable (C : Type u) [category.{v} C]

variable [has_zero_morphisms C] [has_shift C ℤ]

noncomputable section

/-- The shift functor on `differential_object C`. -/
@[simps]
def shift_functor (n : ℤ) : differential_object C ⥤ differential_object C where
  obj := fun X =>
    { x := X.X⟦n⟧, d := X.d⟦n⟧' ≫ (shift_comm _ _ _).Hom,
      d_squared' := by
        rw [functor.map_comp, category.assoc, shift_comm_hom_comp_assoc, ← functor.map_comp_assoc, X.d_squared,
          is_equivalence_preserves_zero_morphisms, zero_comp] }
  map := fun X Y f =>
    { f := f.f⟦n⟧',
      comm' := by
        dsimp
        rw [category.assoc, shift_comm_hom_comp, ← functor.map_comp_assoc, f.comm, functor.map_comp_assoc] }
  map_id' := by
    intro X
    ext1
    dsimp
    rw [Functor.map_id]
  map_comp' := by
    intro X Y Z f g
    ext1
    dsimp
    rw [functor.map_comp]

attribute [local instance] endofunctor_monoidal_category Discrete.addMonoidal

attribute [local reducible] endofunctor_monoidal_category Discrete.addMonoidal shift_comm

/-- The shift functor on `differential_object C` is additive. -/
@[simps]
def shift_functor_add (m n : ℤ) : shift_functor C (m + n) ≅ shift_functor C m ⋙ shift_functor C n := by
  refine' nat_iso.of_components (fun X => mk_iso (shift_add X.X _ _) _) _
  · dsimp
    simp only [obj_μ_app, μ_naturality_assoc, μ_naturalityₗ_assoc, μ_inv_hom_app_assoc, category.assoc, obj_μ_inv_app,
      functor.map_comp, μ_inv_naturalityᵣ_assoc]
    simp [opaque_eq_to_iso]
    
  · intro X Y f
    ext
    dsimp
    exact nat_trans.naturality _ _
    

/-- The shift by zero is naturally isomorphic to the identity. -/
@[simps]
def shift_ε : 𝟭 (differential_object C) ≅ shift_functor C 0 := by
  refine' nat_iso.of_components (fun X => mk_iso ((shift_monoidal_functor C ℤ).εIso.app X.X) _) _
  · dsimp
    simp
    dsimp
    simp
    
  · introv
    ext
    dsimp
    simp
    

instance : has_shift (differential_object C) ℤ :=
  has_shift_mk _ _ { f := shift_functor C, ε := shift_ε C, μ := fun m n => (shift_functor_add C m n).symm }

end DifferentialObject

end CategoryTheory

