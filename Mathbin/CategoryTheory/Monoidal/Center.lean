import Mathbin.CategoryTheory.Monoidal.Braided 
import Mathbin.CategoryTheory.ReflectsIsomorphisms

/-!
# Half braidings and the Drinfeld center of a monoidal category

We define `center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.

We show that `center C` is braided monoidal,
and provide the monoidal functor `center.forget` from `center C` back to `C`.

## Future work

Verifying the various axioms here is done by tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.

More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial;
   I'm unsure if the monoidal coherence theorem is even usable in dependent type theory).
3. Automating these proofs using `rewrite_search` or some relative.

-/


open CategoryTheory

open CategoryTheory.MonoidalCategory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable theory

namespace CategoryTheory

variable{C : Type u₁}[category.{v₁} C][monoidal_category C]

/--
A half-braiding on `X : C` is a family of isomorphisms `X ⊗ U ≅ U ⊗ X`,
monoidally natural in `U : C`.

Thinking of `C` as a 2-category with a single `0`-morphism, these are the same as natural
transformations (in the pseudo- sense) of the identity 2-functor on `C`, which send the unique
`0`-morphism to `X`.
-/
@[nolint has_inhabited_instance]
structure half_braiding(X : C) where 
  β : ∀ U, X ⊗ U ≅ U ⊗ X 
  monoidal' :
  ∀ U U',
    (β (U ⊗ U')).Hom = (α_ _ _ _).inv ≫ ((β U).Hom ⊗ 𝟙 U') ≫ (α_ _ _ _).Hom ≫ (𝟙 U ⊗ (β U').Hom) ≫ (α_ _ _ _).inv :=
   by 
  runTac 
    obviously 
  naturality' : ∀ {U U'} (f : U ⟶ U'), (𝟙 X ⊗ f) ≫ (β U').Hom = (β U).Hom ≫ (f ⊗ 𝟙 X) :=  by 
  runTac 
    obviously

restate_axiom half_braiding.monoidal'

attribute [reassoc, simp] half_braiding.monoidal

restate_axiom half_braiding.naturality'

attribute [simp, reassoc] half_braiding.naturality

variable(C)

/--
The Drinfeld center of a monoidal category `C` has as objects pairs `⟨X, b⟩`, where `X : C`
and `b` is a half-braiding on `X`.
-/
@[nolint has_inhabited_instance]
def center :=
  ΣX : C, half_braiding X

namespace Center

variable{C}

/-- A morphism in the Drinfeld center of `C`. -/
@[ext, nolint has_inhabited_instance]
structure hom(X Y : center C) where 
  f : X.1 ⟶ Y.1
  comm' : ∀ U, (f ⊗ 𝟙 U) ≫ (Y.2.β U).Hom = (X.2.β U).Hom ≫ (𝟙 U ⊗ f) :=  by 
  runTac 
    obviously

restate_axiom hom.comm'

attribute [simp, reassoc] hom.comm

instance  : category (center C) :=
  { Hom := hom, id := fun X => { f := 𝟙 X.1 }, comp := fun X Y Z f g => { f := f.f ≫ g.f } }

@[simp]
theorem id_f (X : center C) : hom.f (𝟙 X) = 𝟙 X.1 :=
  rfl

@[simp]
theorem comp_f {X Y Z : center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

@[ext]
theorem ext {X Y : center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g :=
  by 
    cases f 
    cases g 
    congr 
    exact w

/--
Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
def iso_mk {X Y : center C} (f : X ⟶ Y) [is_iso f.f] : X ≅ Y :=
  { Hom := f,
    inv :=
      ⟨inv f.f,
        fun U =>
          by 
            simp [←cancel_epi (f.f ⊗ 𝟙 U), ←comp_tensor_id_assoc, ←id_tensor_comp]⟩ }

instance is_iso_of_f_is_iso {X Y : center C} (f : X ⟶ Y) [is_iso f.f] : is_iso f :=
  by 
    change is_iso (iso_mk f).Hom 
    infer_instance

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_obj (X Y : center C) : center C :=
  ⟨X.1 ⊗ Y.1,
    { β := fun U => α_ _ _ _ ≪≫ (iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm ≪≫ (X.2.β U ⊗ iso.refl Y.1) ≪≫ α_ _ _ _,
      monoidal' :=
        fun U U' =>
          by 
            dsimp 
            simp only [comp_tensor_id, id_tensor_comp, category.assoc, half_braiding.monoidal]
            rw [pentagon_assoc, pentagon_inv_assoc, iso.eq_inv_comp, ←pentagon_assoc, ←id_tensor_comp_assoc,
              iso.hom_inv_id, tensor_id, category.id_comp, ←associator_naturality_assoc, cancel_epi, cancel_epi,
              ←associator_inv_naturality_assoc (X.2.β U).Hom, associator_inv_naturality_assoc _ _ (Y.2.β U').Hom,
              tensor_id, tensor_id, id_tensor_comp_tensor_id_assoc, associator_naturality_assoc (X.2.β U).Hom,
              ←associator_naturality_assoc _ _ (Y.2.β U').Hom, tensor_id, tensor_id, tensor_id_comp_id_tensor_assoc,
              ←id_tensor_comp_tensor_id, tensor_id, category.comp_id, ←is_iso.inv_comp_eq, inv_tensor, is_iso.inv_id,
              is_iso.iso.inv_inv, pentagon_assoc, iso.hom_inv_id_assoc, cancel_epi, cancel_epi, ←is_iso.inv_comp_eq,
              is_iso.iso.inv_hom, ←pentagon_inv_assoc, ←comp_tensor_id_assoc, iso.inv_hom_id, tensor_id,
              category.id_comp, ←associator_inv_naturality_assoc, cancel_epi, cancel_epi, ←is_iso.inv_comp_eq,
              inv_tensor, is_iso.iso.inv_hom, is_iso.inv_id, pentagon_inv_assoc, iso.inv_hom_id, category.comp_id],
      naturality' :=
        fun U U' f =>
          by 
            dsimp 
            rw [category.assoc, category.assoc, category.assoc, category.assoc, id_tensor_associator_naturality_assoc,
              ←id_tensor_comp_assoc, half_braiding.naturality, id_tensor_comp_assoc, associator_inv_naturality_assoc,
              ←comp_tensor_id_assoc, half_braiding.naturality, comp_tensor_id_assoc, associator_naturality,
              ←tensor_id] }⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_hom {X₁ Y₁ X₂ Y₂ : center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tensor_obj X₁ X₂ ⟶ tensor_obj Y₁ Y₂ :=
  { f := f.f ⊗ g.f,
    comm' :=
      fun U =>
        by 
          dsimp 
          rw [category.assoc, category.assoc, category.assoc, category.assoc, associator_naturality_assoc,
            ←tensor_id_comp_id_tensor, category.assoc, ←id_tensor_comp_assoc, g.comm, id_tensor_comp_assoc,
            tensor_id_comp_id_tensor_assoc, ←id_tensor_comp_tensor_id, category.assoc, associator_inv_naturality_assoc,
            id_tensor_associator_inv_naturality_assoc, tensor_id, id_tensor_comp_tensor_id_assoc,
            ←tensor_id_comp_id_tensor g.f, category.assoc, ←comp_tensor_id_assoc, f.comm, comp_tensor_id_assoc,
            id_tensor_associator_naturality, associator_naturality_assoc, ←id_tensor_comp, tensor_id_comp_id_tensor] }

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensor_unit : center C :=
  ⟨𝟙_ C,
    { β := fun U => λ_ U ≪≫ (ρ_ U).symm,
      monoidal' :=
        fun U U' =>
          by 
            simp ,
      naturality' :=
        fun U U' f =>
          by 
            dsimp 
            rw [left_unitor_naturality_assoc, right_unitor_inv_naturality, category.assoc] }⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def associator (X Y Z : center C) : tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z) :=
  iso_mk
    ⟨(α_ X.1 Y.1 Z.1).Hom,
      fun U =>
        by 
          dsimp 
          simp only [category.assoc, comp_tensor_id, id_tensor_comp]
          rw [pentagon, pentagon_assoc, ←associator_naturality_assoc (𝟙 X.1) (𝟙 Y.1), tensor_id, cancel_epi, cancel_epi,
            iso.eq_inv_comp, ←pentagon_assoc, ←id_tensor_comp_assoc, iso.hom_inv_id, tensor_id, category.id_comp,
            ←associator_naturality_assoc, cancel_epi, cancel_epi, ←is_iso.inv_comp_eq, inv_tensor, is_iso.inv_id,
            is_iso.iso.inv_inv, pentagon_assoc, iso.hom_inv_id_assoc, ←tensor_id, ←associator_naturality_assoc]⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def left_unitor (X : center C) : tensor_obj tensor_unit X ≅ X :=
  iso_mk
    ⟨(λ_ X.1).Hom,
      fun U =>
        by 
          dsimp 
          simp only [category.comp_id, category.assoc, tensor_inv_hom_id, comp_tensor_id, tensor_id_comp_id_tensor,
            triangle_assoc_comp_right_inv]
          rw [←left_unitor_tensor, left_unitor_naturality, left_unitor_tensor'_assoc]⟩

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def right_unitor (X : center C) : tensor_obj X tensor_unit ≅ X :=
  iso_mk
    ⟨(ρ_ X.1).Hom,
      fun U =>
        by 
          dsimp 
          simp only [tensor_id_comp_id_tensor_assoc, triangle_assoc, id_tensor_comp, category.assoc]
          rw [←tensor_id_comp_id_tensor_assoc (ρ_ U).inv, cancel_epi, ←right_unitor_tensor_inv_assoc,
            ←right_unitor_inv_naturality_assoc]
          simp ⟩

section 

attribute [local simp] associator_naturality left_unitor_naturality right_unitor_naturality pentagon

attribute [local simp] center.associator center.left_unitor center.right_unitor

instance  : monoidal_category (center C) :=
  { tensorObj := fun X Y => tensor_obj X Y, tensorHom := fun X₁ Y₁ X₂ Y₂ f g => tensor_hom f g,
    tensorUnit := tensor_unit, associator := associator, leftUnitor := left_unitor, rightUnitor := right_unitor }

@[simp]
theorem tensor_fst (X Y : center C) : (X ⊗ Y).1 = X.1 ⊗ Y.1 :=
  rfl

@[simp]
theorem tensor_β (X Y : center C) (U : C) :
  (X ⊗ Y).2.β U = α_ _ _ _ ≪≫ (iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm ≪≫ (X.2.β U ⊗ iso.refl Y.1) ≪≫ α_ _ _ _ :=
  rfl

@[simp]
theorem tensor_f {X₁ Y₁ X₂ Y₂ : center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ g).f = f.f ⊗ g.f :=
  rfl

@[simp]
theorem tensor_unit_β (U : C) : (𝟙_ (center C)).2.β U = λ_ U ≪≫ (ρ_ U).symm :=
  rfl

@[simp]
theorem associator_hom_f (X Y Z : center C) : hom.f (α_ X Y Z).Hom = (α_ X.1 Y.1 Z.1).Hom :=
  rfl

@[simp]
theorem associator_inv_f (X Y Z : center C) : hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv :=
  by 
    ext 
    rw [←associator_hom_f, ←comp_f, iso.hom_inv_id]
    rfl

@[simp]
theorem left_unitor_hom_f (X : center C) : hom.f (λ_ X).Hom = (λ_ X.1).Hom :=
  rfl

@[simp]
theorem left_unitor_inv_f (X : center C) : hom.f (λ_ X).inv = (λ_ X.1).inv :=
  by 
    ext 
    rw [←left_unitor_hom_f, ←comp_f, iso.hom_inv_id]
    rfl

@[simp]
theorem right_unitor_hom_f (X : center C) : hom.f (ρ_ X).Hom = (ρ_ X.1).Hom :=
  rfl

@[simp]
theorem right_unitor_inv_f (X : center C) : hom.f (ρ_ X).inv = (ρ_ X.1).inv :=
  by 
    ext 
    rw [←right_unitor_hom_f, ←comp_f, iso.hom_inv_id]
    rfl

end 

section 

variable(C)

/-- The forgetful monoidal functor from the Drinfeld center to the original category. -/
@[simps]
def forget : monoidal_functor (center C) C :=
  { obj := fun X => X.1, map := fun X Y f => f.f, ε := 𝟙 (𝟙_ C), μ := fun X Y => 𝟙 (X.1 ⊗ Y.1) }

instance  : reflects_isomorphisms (forget C).toFunctor :=
  { reflects :=
      fun A B f i =>
        by 
          dsimp  at i 
          skip 
          change is_iso (iso_mk f).Hom 
          infer_instance }

end 

/-- Auxiliary definition for the `braided_category` instance on `center C`. -/
@[simps]
def braiding (X Y : center C) : X ⊗ Y ≅ Y ⊗ X :=
  iso_mk
    ⟨(X.2.β Y.1).Hom,
      fun U =>
        by 
          dsimp 
          simp only [category.assoc]
          rw [←is_iso.inv_comp_eq, is_iso.iso.inv_hom, ←half_braiding.monoidal_assoc, ←half_braiding.naturality_assoc,
            half_braiding.monoidal]
          simp ⟩

instance braided_category_center : braided_category (center C) :=
  { braiding := braiding,
    braiding_naturality' :=
      fun X Y X' Y' f g =>
        by 
          ext 
          dsimp 
          rw [←tensor_id_comp_id_tensor, category.assoc, half_braiding.naturality, f.comm_assoc,
            id_tensor_comp_tensor_id] }

section 

variable[braided_category C]

open BraidedCategory

/-- Auxiliary construction for `of_braided`. -/
@[simps]
def of_braided_obj (X : C) : center C :=
  ⟨X,
    { β := fun Y => β_ X Y,
      monoidal' :=
        fun U U' =>
          by 
            rw [iso.eq_inv_comp, ←category.assoc, ←category.assoc, iso.eq_comp_inv, category.assoc, category.assoc]
            exact hexagon_forward X U U' }⟩

variable(C)

/--
The functor lifting a braided category to its center, using the braiding as the half-braiding.
-/
@[simps]
def of_braided : monoidal_functor C (center C) :=
  { obj := of_braided_obj, map := fun X X' f => { f, comm' := fun U => braiding_naturality _ _ },
    ε :=
      { f := 𝟙 _,
        comm' :=
          fun U =>
            by 
              dsimp 
              rw [tensor_id, category.id_comp, tensor_id, category.comp_id, ←braiding_right_unitor, category.assoc,
                iso.hom_inv_id, category.comp_id] },
    μ :=
      fun X Y =>
        { f := 𝟙 _,
          comm' :=
            fun U =>
              by 
                dsimp 
                rw [tensor_id, tensor_id, category.id_comp, category.comp_id, ←iso.inv_comp_eq, ←category.assoc,
                  ←category.assoc, ←iso.comp_inv_eq, category.assoc, hexagon_reverse, category.assoc] } }

end 

end Center

end CategoryTheory

