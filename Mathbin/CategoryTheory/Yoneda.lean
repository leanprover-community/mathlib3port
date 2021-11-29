import Mathbin.CategoryTheory.HomFunctor 
import Mathbin.CategoryTheory.Currying 
import Mathbin.CategoryTheory.Products.Basic

/-!
# The Yoneda embedding

The Yoneda embedding as a functor `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)`,
along with an instance that it is `fully_faithful`.

Also the Yoneda lemma, `yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/


namespace CategoryTheory

open Opposite

universe v₁ u₁ u₂

variable {C : Type u₁} [category.{v₁} C]

/--
The Yoneda embedding, as a functor from `C` into presheaves on `C`.

See https://stacks.math.columbia.edu/tag/001O.
-/
@[simps]
def yoneda : C ⥤ «expr ᵒᵖ» C ⥤ Type v₁ :=
  { obj :=
      fun X =>
        { obj := fun Y => unop Y ⟶ X, map := fun Y Y' f g => f.unop ≫ g,
          map_comp' :=
            fun _ _ _ f g =>
              by 
                ext 
                dsimp 
                erw [category.assoc],
          map_id' :=
            fun Y =>
              by 
                ext 
                dsimp 
                erw [category.id_comp] },
    map := fun X X' f => { app := fun Y g => g ≫ f } }

/--
The co-Yoneda embedding, as a functor from `Cᵒᵖ` into co-presheaves on `C`.
-/
@[simps]
def coyoneda : «expr ᵒᵖ» C ⥤ C ⥤ Type v₁ :=
  { obj := fun X => { obj := fun Y => unop X ⟶ Y, map := fun Y Y' f g => g ≫ f },
    map := fun X X' f => { app := fun Y g => f.unop ≫ g } }

namespace Yoneda

theorem obj_map_id {X Y : C} (f : op X ⟶ op Y) : (yoneda.obj X).map f (𝟙 X) = (yoneda.map f.unop).app (op Y) (𝟙 Y) :=
  by 
    dsimp 
    simp 

@[simp]
theorem naturality {X Y : C} (α : yoneda.obj X ⟶ yoneda.obj Y) {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) :
  f ≫ α.app (op Z') h = α.app (op Z) (f ≫ h) :=
  (functor_to_types.naturality _ _ α f.op h).symm

/--
The Yoneda embedding is full.

See https://stacks.math.columbia.edu/tag/001P.
-/
instance yoneda_full : full (yoneda : C ⥤ «expr ᵒᵖ» C ⥤ Type v₁) :=
  { Preimage := fun X Y f => f.app (op X) (𝟙 X) }

/--
The Yoneda embedding is faithful.

See https://stacks.math.columbia.edu/tag/001P.
-/
instance yoneda_faithful : faithful (yoneda : C ⥤ «expr ᵒᵖ» C ⥤ Type v₁) :=
  { map_injective' :=
      fun X Y f g p =>
        by 
          convert congr_funₓ (congr_app p (op X)) (𝟙 X) <;> dsimp <;> simp  }

/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply yoneda.ext,
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C) (p : ∀ {Z : C}, (Z ⟶ X) → (Z ⟶ Y)) (q : ∀ {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
  (h₁ : ∀ {Z : C} f : Z ⟶ X, q (p f) = f) (h₂ : ∀ {Z : C} f : Z ⟶ Y, p (q f) = f)
  (n : ∀ {Z Z' : C} f : Z' ⟶ Z g : Z ⟶ X, p (f ≫ g) = f ≫ p g) : X ≅ Y :=
  @preimage_iso _ _ _ _ yoneda _ _ _ _
    (nat_iso.of_components (fun Z => { Hom := p, inv := q })
      (by 
        tidy))

/--
If `yoneda.map f` is an isomorphism, so was `f`.
-/
theorem is_iso {X Y : C} (f : X ⟶ Y) [is_iso (yoneda.map f)] : is_iso f :=
  is_iso_of_fully_faithful yoneda f

end Yoneda

namespace Coyoneda

@[simp]
theorem naturality {X Y : «expr ᵒᵖ» C} (α : coyoneda.obj X ⟶ coyoneda.obj Y) {Z Z' : C} (f : Z' ⟶ Z) (h : unop X ⟶ Z') :
  α.app Z' h ≫ f = α.app Z (h ≫ f) :=
  (functor_to_types.naturality _ _ α f h).symm

instance coyoneda_full : full (coyoneda : «expr ᵒᵖ» C ⥤ C ⥤ Type v₁) :=
  { Preimage := fun X Y f => (f.app _ (𝟙 X.unop)).op }

-- error in CategoryTheory.Yoneda: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance coyoneda_faithful : faithful (coyoneda : «expr ⥤ »(«expr ᵒᵖ»(C), «expr ⥤ »(C, Type v₁))) :=
{ map_injective' := λ X Y f g p, begin
    have [ident t] [] [":=", expr congr_fun (congr_app p X.unop) («expr𝟙»() _)],
    simpa [] [] [] [] [] ["using", expr congr_arg quiver.hom.op t]
  end }

/--
If `coyoneda.map f` is an isomorphism, so was `f`.
-/
theorem is_iso {X Y : «expr ᵒᵖ» C} (f : X ⟶ Y) [is_iso (coyoneda.map f)] : is_iso f :=
  is_iso_of_fully_faithful coyoneda f

/-- The identity functor on `Type` is isomorphic to the coyoneda functor coming from `punit`. -/
def punit_iso : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁) :=
  nat_iso.of_components (fun X => { Hom := fun f => f ⟨⟩, inv := fun x _ => x })
    (by 
      tidy)

end Coyoneda

namespace Functor

/--
A functor `F : Cᵒᵖ ⥤ Type v₁` is representable if there is object `X` so `F ≅ yoneda.obj X`.

See https://stacks.math.columbia.edu/tag/001Q.
-/
class representable (F : «expr ᵒᵖ» C ⥤ Type v₁) : Prop where 
  has_representation : ∃ (X : _)(f : yoneda.obj X ⟶ F), is_iso f

instance {X : C} : representable (yoneda.obj X) :=
  { has_representation := ⟨X, 𝟙 _, inferInstance⟩ }

/--
A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ coyoneda.obj X`.

See https://stacks.math.columbia.edu/tag/001Q.
-/
class corepresentable (F : C ⥤ Type v₁) : Prop where 
  has_corepresentation : ∃ (X : _)(f : coyoneda.obj X ⟶ F), is_iso f

instance {X : «expr ᵒᵖ» C} : corepresentable (coyoneda.obj X) :=
  { has_corepresentation := ⟨X, 𝟙 _, inferInstance⟩ }

section Representable

variable (F : «expr ᵒᵖ» C ⥤ Type v₁)

variable [F.representable]

/-- The representing object for the representable functor `F`. -/
noncomputable def repr_X : C :=
  (representable.has_representation : ∃ (X : _)(f : _ ⟶ F), _).some

/-- The (forward direction of the) isomorphism witnessing `F` is representable. -/
noncomputable def repr_f : yoneda.obj F.repr_X ⟶ F :=
  representable.has_representation.some_spec.some

/--
The representing element for the representable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def repr_x : F.obj (op F.repr_X) :=
  F.repr_f.app (op F.repr_X) (𝟙 F.repr_X)

instance : is_iso F.repr_f :=
  representable.has_representation.some_spec.some_spec

/--
An isomorphism between `F` and a functor of the form `C(-, F.repr_X)`.  Note the components
`F.repr_w.app X` definitionally have type `(X.unop ⟶ F.repr_X) ≅ F.obj X`.
-/
noncomputable def repr_w : yoneda.obj F.repr_X ≅ F :=
  as_iso F.repr_f

@[simp]
theorem repr_w_hom : F.repr_w.hom = F.repr_f :=
  rfl

theorem repr_w_app_hom (X : «expr ᵒᵖ» C) (f : unop X ⟶ F.repr_X) : (F.repr_w.app X).Hom f = F.map f.op F.repr_x :=
  by 
    change F.repr_f.app X f = (F.repr_f.app (op F.repr_X) ≫ F.map f.op) (𝟙 F.repr_X)
    rw [←F.repr_f.naturality]
    dsimp 
    simp 

end Representable

section Corepresentable

variable (F : C ⥤ Type v₁)

variable [F.corepresentable]

/-- The representing object for the corepresentable functor `F`. -/
noncomputable def corepr_X : C :=
  (corepresentable.has_corepresentation : ∃ (X : _)(f : _ ⟶ F), _).some.unop

/-- The (forward direction of the) isomorphism witnessing `F` is corepresentable. -/
noncomputable def corepr_f : coyoneda.obj (op F.corepr_X) ⟶ F :=
  corepresentable.has_corepresentation.some_spec.some

/--
The representing element for the corepresentable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def corepr_x : F.obj F.corepr_X :=
  F.corepr_f.app F.corepr_X (𝟙 F.corepr_X)

instance : is_iso F.corepr_f :=
  corepresentable.has_corepresentation.some_spec.some_spec

/--
An isomorphism between `F` and a functor of the form `C(F.corepr X, -)`. Note the components
`F.corepr_w.app X` definitionally have type `F.corepr_X ⟶ X ≅ F.obj X`.
-/
noncomputable def corepr_w : coyoneda.obj (op F.corepr_X) ≅ F :=
  as_iso F.corepr_f

theorem corepr_w_app_hom (X : C) (f : F.corepr_X ⟶ X) : (F.corepr_w.app X).Hom f = F.map f F.corepr_x :=
  by 
    change F.corepr_f.app X f = (F.corepr_f.app F.corepr_X ≫ F.map f) (𝟙 F.corepr_X)
    rw [←F.corepr_f.naturality]
    dsimp 
    simp 

end Corepresentable

end Functor

theorem representable_of_nat_iso (F : «expr ᵒᵖ» C ⥤ Type v₁) {G} (i : F ≅ G) [F.representable] : G.representable :=
  { has_representation := ⟨F.repr_X, F.repr_f ≫ i.hom, inferInstance⟩ }

theorem corepresentable_of_nat_iso (F : C ⥤ Type v₁) {G} (i : F ≅ G) [F.corepresentable] : G.corepresentable :=
  { has_corepresentation := ⟨op F.corepr_X, F.corepr_f ≫ i.hom, inferInstance⟩ }

instance : functor.corepresentable (𝟭 (Type v₁)) :=
  corepresentable_of_nat_iso (coyoneda.obj (op PUnit)) coyoneda.punit_iso

open Opposite

variable (C)

instance prod_category_instance_1 : category ((«expr ᵒᵖ» C ⥤ Type v₁) × «expr ᵒᵖ» C) :=
  CategoryTheory.prod.{max u₁ v₁, v₁} («expr ᵒᵖ» C ⥤ Type v₁) («expr ᵒᵖ» C)

instance prod_category_instance_2 : category («expr ᵒᵖ» C × («expr ᵒᵖ» C ⥤ Type v₁)) :=
  CategoryTheory.prod.{v₁, max u₁ v₁} («expr ᵒᵖ» C) («expr ᵒᵖ» C ⥤ Type v₁)

open Yoneda

/--
The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def yoneda_evaluation : «expr ᵒᵖ» C × («expr ᵒᵖ» C ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluation_uncurried («expr ᵒᵖ» C) (Type v₁) ⋙ ulift_functor.{u₁}

@[simp]
theorem yoneda_evaluation_map_down (P Q : «expr ᵒᵖ» C × («expr ᵒᵖ» C ⥤ Type v₁)) (α : P ⟶ Q)
  (x : (yoneda_evaluation C).obj P) : ((yoneda_evaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/--
The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def yoneda_pairing : «expr ᵒᵖ» C × («expr ᵒᵖ» C ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  functor.prod yoneda.op (𝟭 («expr ᵒᵖ» C ⥤ Type v₁)) ⋙ functor.hom («expr ᵒᵖ» C ⥤ Type v₁)

@[simp]
theorem yoneda_pairing_map (P Q : «expr ᵒᵖ» C × («expr ᵒᵖ» C ⥤ Type v₁)) (α : P ⟶ Q) (β : (yoneda_pairing C).obj P) :
  (yoneda_pairing C).map α β = yoneda.map α.1.unop ≫ β ≫ α.2 :=
  rfl

/--
The Yoneda lemma asserts that that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.

See https://stacks.math.columbia.edu/tag/001P.
-/
def yoneda_lemma : yoneda_pairing C ≅ yoneda_evaluation C :=
  { Hom :=
      { app := fun F x => Ulift.up ((x.app F.1) (𝟙 (unop F.1))),
        naturality' :=
          by 
            intro X Y f 
            ext 
            dsimp 
            erw [category.id_comp, ←functor_to_types.naturality]
            simp only [category.comp_id, yoneda_obj_map] },
    inv :=
      { app :=
          fun F x =>
            { app := fun X a => (F.2.map a.op) x.down,
              naturality' :=
                by 
                  intro X Y f 
                  ext 
                  dsimp 
                  rw [functor_to_types.map_comp_apply] },
        naturality' :=
          by 
            intro X Y f 
            ext 
            dsimp 
            rw [←functor_to_types.naturality, functor_to_types.map_comp_apply] },
    hom_inv_id' :=
      by 
        ext 
        dsimp 
        erw [←functor_to_types.naturality, obj_map_id]
        simp only [yoneda_map_app, Quiver.Hom.unop_op]
        erw [category.id_comp],
    inv_hom_id' :=
      by 
        ext 
        dsimp 
        rw [functor_to_types.map_id_apply] }

variable {C}

/--
The isomorphism between `yoneda.obj X ⟶ F` and `F.obj (op X)`
(we need to insert a `ulift` to get the universes right!)
given by the Yoneda lemma.
-/
@[simps]
def yoneda_sections (X : C) (F : «expr ᵒᵖ» C ⥤ Type v₁) : (yoneda.obj X ⟶ F) ≅ Ulift.{u₁} (F.obj (op X)) :=
  (yoneda_lemma C).app (op X, F)

/--
We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def yoneda_equiv {X : C} {F : «expr ᵒᵖ» C ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) :=
  (yoneda_sections X F).toEquiv.trans Equiv.ulift

@[simp]
theorem yoneda_equiv_apply {X : C} {F : «expr ᵒᵖ» C ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
  yoneda_equiv f = f.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yoneda_equiv_symm_app_apply {X : C} {F : «expr ᵒᵖ» C ⥤ Type v₁} (x : F.obj (op X)) (Y : «expr ᵒᵖ» C)
  (f : Y.unop ⟶ X) : (yoneda_equiv.symm x).app Y f = F.map f.op x :=
  rfl

theorem yoneda_equiv_naturality {X Y : C} {F : «expr ᵒᵖ» C ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : Y ⟶ X) :
  F.map g.op (yoneda_equiv f) = yoneda_equiv (yoneda.map g ≫ f) :=
  by 
    change (f.app (op X) ≫ F.map g.op) (𝟙 X) = f.app (op Y) (𝟙 Y ≫ g)
    rw [←f.naturality]
    dsimp 
    simp 

/--
When `C` is a small category, we can restate the isomorphism from `yoneda_sections`
without having to change universes.
-/
def yoneda_sections_small {C : Type u₁} [small_category C] (X : C) (F : «expr ᵒᵖ» C ⥤ Type u₁) :
  (yoneda.obj X ⟶ F) ≅ F.obj (op X) :=
  yoneda_sections X F ≪≫ ulift_trivial _

@[simp]
theorem yoneda_sections_small_hom {C : Type u₁} [small_category C] (X : C) (F : «expr ᵒᵖ» C ⥤ Type u₁)
  (f : yoneda.obj X ⟶ F) : (yoneda_sections_small X F).Hom f = f.app _ (𝟙 _) :=
  rfl

@[simp]
theorem yoneda_sections_small_inv_app_apply {C : Type u₁} [small_category C] (X : C) (F : «expr ᵒᵖ» C ⥤ Type u₁)
  (t : F.obj (op X)) (Y : «expr ᵒᵖ» C) (f : Y.unop ⟶ X) : ((yoneda_sections_small X F).inv t).app Y f = F.map f.op t :=
  rfl

attribute [local ext] Functor.ext

/-- The curried version of yoneda lemma when `C` is small. -/
def curried_yoneda_lemma {C : Type u₁} [small_category C] :
  (yoneda.op ⋙ coyoneda : «expr ᵒᵖ» C ⥤ («expr ᵒᵖ» C ⥤ Type u₁) ⥤ Type u₁) ≅ evaluation («expr ᵒᵖ» C) (Type u₁) :=
  eq_to_iso
      (by 
        tidy) ≪≫
    curry.mapIso
        (yoneda_lemma C ≪≫ iso_whisker_left (evaluation_uncurried («expr ᵒᵖ» C) (Type u₁)) ulift_functor_trivial) ≪≫
      eq_to_iso
        (by 
          tidy)

/-- The curried version of yoneda lemma when `C` is small. -/
def curried_yoneda_lemma' {C : Type u₁} [small_category C] :
  yoneda ⋙ (whiskering_left («expr ᵒᵖ» C) («expr ᵒᵖ» («expr ᵒᵖ» C ⥤ Type u₁)) (Type u₁)).obj yoneda.op ≅
    𝟭 («expr ᵒᵖ» C ⥤ Type u₁) :=
  eq_to_iso
      (by 
        tidy) ≪≫
    curry.mapIso
        (iso_whisker_left (Prod.swap _ _)
          (yoneda_lemma C ≪≫ iso_whisker_left (evaluation_uncurried («expr ᵒᵖ» C) (Type u₁)) ulift_functor_trivial :
          _)) ≪≫
      eq_to_iso
        (by 
          tidy)

end CategoryTheory

