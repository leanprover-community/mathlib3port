import Mathbin.CategoryTheory.Monoidal.Types 
import Mathbin.CategoryTheory.Monoidal.Center

/-!
# Enriched categories

We set up the basic theory of `V`-enriched categories,
for `V` an arbitrary monoidal category.

We do not assume here that `V` is a concrete category,
so there does not need to be a "honest" underlying category!

Use `X ⟶[V] Y` to obtain the `V` object of morphisms from `X` to `Y`.

This file contains the definitions of `V`-enriched categories and
`V`-functors.

We don't yet define the `V`-object of natural transformations
between a pair of `V`-functors (this requires limits in `V`),
but we do provide a presheaf isomorphic to the Yoneda embedding of this object.

We verify that when `V = Type v`, all these notion reduce to the usual ones.
-/


universe w v u₁ u₂ u₃

noncomputable theory

namespace CategoryTheory

open Opposite

open MonoidalCategory

variable(V : Type v)[category.{w} V][monoidal_category V]

-- error in CategoryTheory.Enriched.Basic: ././Mathport/Syntax/Translate/Basic.lean:990:29: unsupported: (notation) in structure
/--
A `V`-category is a category enriched in a monoidal category `V`.

Note that we do not assume that `V` is a concrete category,
so there may not be an "honest" underlying category at all!
-/
class enriched_category
(C : Type u₁) :=
  (hom : C → C → V)
  (notation X ` ⟶[] ` Y:10 := hom X Y)
  (id : ∀ X, «expr ⟶ »(«expr𝟙_»() V, «expr ⟶[] »(X, X)))
  (comp : ∀ X Y Z, «expr ⟶ »([«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](«expr ⟶[] »(X, Y), «expr ⟶[] »(Y, Z)), «expr ⟶[] »(X, Z)))
  (id_comp : ∀
   X
   Y, «expr = »(«expr ≫ »((«exprλ_»() «expr ⟶[] »(X, Y)).inv, «expr ≫ »([«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](id X, «expr𝟙»() _), comp X X Y)), «expr𝟙»() _) . obviously)
  (comp_id : ∀
   X
   Y, «expr = »(«expr ≫ »((exprρ_() «expr ⟶[] »(X, Y)).inv, «expr ≫ »([«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](«expr𝟙»() _, id Y), comp X Y Y)), «expr𝟙»() _) . obviously)
  (assoc : ∀
   W
   X
   Y
   Z, «expr = »(«expr ≫ »((exprα_() _ _ _).inv, «expr ≫ »([«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](comp W X Y, «expr𝟙»() _), comp W Y Z)), «expr ≫ »([«expr ⊗ »/«expr ⊗ »/«expr ⊗ »](«expr𝟙»() _, comp X Y Z), comp W X Z)) . obviously)

notation X " ⟶[" V "] " Y:10 => (enriched_category.hom X Y : V)

variable(V){C : Type u₁}[enriched_category V C]

/--
The `𝟙_ V`-shaped generalized element giving the identity in a `V`-enriched category.
-/
def e_id (X : C) : 𝟙_ V ⟶ X ⟶[V] X :=
  enriched_category.id X

/--
The composition `V`-morphism for a `V`-enriched category.
-/
def e_comp (X Y Z : C) : ((X ⟶[V] Y) ⊗ Y ⟶[V] Z) ⟶ X ⟶[V] Z :=
  enriched_category.comp X Y Z

@[simp, reassoc]
theorem e_id_comp (X Y : C) : (λ_ (X ⟶[V] Y)).inv ≫ (e_id V X ⊗ 𝟙 _) ≫ e_comp V X X Y = 𝟙 (X ⟶[V] Y) :=
  enriched_category.id_comp X Y

@[simp, reassoc]
theorem e_comp_id (X Y : C) : (ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 _ ⊗ e_id V Y) ≫ e_comp V X Y Y = 𝟙 (X ⟶[V] Y) :=
  enriched_category.comp_id X Y

@[simp, reassoc]
theorem e_assoc (W X Y Z : C) :
  (α_ _ _ _).inv ≫ (e_comp V W X Y ⊗ 𝟙 _) ≫ e_comp V W Y Z = (𝟙 _ ⊗ e_comp V X Y Z) ≫ e_comp V W X Z :=
  enriched_category.assoc W X Y Z

section 

variable{V}{W : Type v}[category.{w} W][monoidal_category W]

/--
A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the `W`-enriched category structure
obtained by applying the functor `F : lax_monoidal_functor V W` to each hom object.
-/
@[nolint has_inhabited_instance unused_arguments]
def transport_enrichment (F : lax_monoidal_functor V W) (C : Type u₁) :=
  C

instance  (F : lax_monoidal_functor V W) : enriched_category W (transport_enrichment F C) :=
  { Hom := fun X Y : C => F.obj (X ⟶[V] Y), id := fun X : C => F.ε ≫ F.map (e_id V X),
    comp := fun X Y Z : C => F.μ _ _ ≫ F.map (e_comp V X Y Z),
    id_comp :=
      fun X Y =>
        by 
          rw [comp_tensor_id, category.assoc, ←F.to_functor.map_id, F.μ_natural_assoc, F.to_functor.map_id,
            F.left_unitality_inv_assoc, ←F.to_functor.map_comp, ←F.to_functor.map_comp, e_id_comp, F.to_functor.map_id],
    comp_id :=
      fun X Y =>
        by 
          rw [id_tensor_comp, category.assoc, ←F.to_functor.map_id, F.μ_natural_assoc, F.to_functor.map_id,
            F.right_unitality_inv_assoc, ←F.to_functor.map_comp, ←F.to_functor.map_comp, e_comp_id,
            F.to_functor.map_id],
    assoc :=
      fun P Q R S =>
        by 
          rw [comp_tensor_id, category.assoc, ←F.to_functor.map_id, F.μ_natural_assoc, F.to_functor.map_id,
            ←F.associativity_inv_assoc, ←F.to_functor.map_comp, ←F.to_functor.map_comp, e_assoc, id_tensor_comp,
            category.assoc, ←F.to_functor.map_id, F.μ_natural_assoc, F.to_functor.map_comp] }

end 

/--
Construct an honest category from a `Type v`-enriched category.
-/
def category_of_enriched_category_Type (C : Type u₁) [𝒞 : enriched_category (Type v) C] : category.{v} C :=
  { Hom := 𝒞.hom, id := fun X => e_id (Type v) X PUnit.unit, comp := fun X Y Z f g => e_comp (Type v) X Y Z ⟨f, g⟩,
    id_comp' := fun X Y f => congr_funₓ (e_id_comp (Type v) X Y) f,
    comp_id' := fun X Y f => congr_funₓ (e_comp_id (Type v) X Y) f,
    assoc' := fun W X Y Z f g h => (congr_funₓ (e_assoc (Type v) W X Y Z) ⟨f, g, h⟩ : _) }

/--
Construct a `Type v`-enriched category from an honest category.
-/
def enriched_category_Type_of_category (C : Type u₁) [𝒞 : category.{v} C] : enriched_category (Type v) C :=
  { Hom := 𝒞.hom, id := fun X p => 𝟙 X, comp := fun X Y Z p => p.1 ≫ p.2,
    id_comp :=
      fun X Y =>
        by 
          ext 
          simp ,
    comp_id :=
      fun X Y =>
        by 
          ext 
          simp ,
    assoc :=
      fun W X Y Z =>
        by 
          ext ⟨f, g, h⟩
          simp  }

/--
We verify that an enriched category in `Type u` is just the same thing as an honest category.
-/
def enriched_category_Type_equiv_category (C : Type u₁) : enriched_category (Type v) C ≃ category.{v} C :=
  { toFun :=
      fun 𝒞 =>
        by 
          exact category_of_enriched_category_Type C,
    invFun :=
      fun 𝒞 =>
        by 
          exact enriched_category_Type_of_category C,
    left_inv :=
      fun 𝒞 =>
        by 
          cases 𝒞 
          dsimp [enriched_category_Type_of_category]
          congr
          ·
            ext X ⟨⟩
            rfl
          ·
            ext X Y Z ⟨f, g⟩
            rfl,
    right_inv :=
      fun 𝒞 =>
        by 
          rcases 𝒞 with ⟨⟨⟨⟩⟩⟩
          dsimp 
          congr }

section 

variable{W : Type (v + 1)}[category.{v} W][monoidal_category W][enriched_category W C]

/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the (honest) category structure
so that `X ⟶ Y` is `(𝟙_ W) ⟶ (X ⟶[W] Y)`.

We obtain this category by
transporting the enrichment in `V` along the lax monoidal functor `coyoneda_tensor_unit`,
then using the equivalence of `Type`-enriched categories with honest categories.

This is sometimes called the "underlying" category of an enriched category,
although some care is needed as the functor `coyoneda_tensor_unit`,
which always exists, does not necessarily coincide with
"the forgetful functor" from `V` to `Type`, if such exists.
When `V` is any of `Type`, `Top`, `AddCommGroup`, or `Module R`,
`coyoneda_tensor_unit` is just the usual forgetful functor, however.
For `V = Algebra R`, the usual forgetful functor is coyoneda of `polynomial R`, not of `R`.
(Perhaps we should have a typeclass for this situation: `concrete_monoidal`?)
-/
@[nolint has_inhabited_instance unused_arguments]
def forget_enrichment (W : Type (v + 1)) [category.{v} W] [monoidal_category W] (C : Type u₁) [enriched_category W C] :=
  C

variable(W)

/-- Typecheck an object of `C` as an object of `forget_enrichment W C`. -/
def forget_enrichment.of (X : C) : forget_enrichment W C :=
  X

/-- Typecheck an object of `forget_enrichment W C` as an object of `C`. -/
def forget_enrichment.to (X : forget_enrichment W C) : C :=
  X

@[simp]
theorem forget_enrichment.to_of (X : C) : forget_enrichment.to W (forget_enrichment.of W X) = X :=
  rfl

@[simp]
theorem forget_enrichment.of_to (X : forget_enrichment W C) : forget_enrichment.of W (forget_enrichment.to W X) = X :=
  rfl

instance category_forget_enrichment : category (forget_enrichment W C) :=
  by 
    let I : enriched_category (Type v) (transport_enrichment (coyoneda_tensor_unit W) C) := inferInstance 
    exact enriched_category_Type_equiv_category C I

/--
We verify that the morphism types in `forget_enrichment W C` are `(𝟙_ W) ⟶ (X ⟶[W] Y)`.
-/
example  (X Y : forget_enrichment W C) : (X ⟶ Y) = (𝟙_ W ⟶ forget_enrichment.to W X ⟶[W] forget_enrichment.to W Y) :=
  rfl

/-- Typecheck a `(𝟙_ W)`-shaped `W`-morphism as a morphism in `forget_enrichment W C`. -/
def forget_enrichment.hom_of {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) : forget_enrichment.of W X ⟶ forget_enrichment.of W Y :=
  f

/-- Typecheck a morphism in `forget_enrichment W C` as a `(𝟙_ W)`-shaped `W`-morphism. -/
def forget_enrichment.hom_to {X Y : forget_enrichment W C} (f : X ⟶ Y) :
  𝟙_ W ⟶ forget_enrichment.to W X ⟶[W] forget_enrichment.to W Y :=
  f

@[simp]
theorem forget_enrichment.hom_to_hom_of {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
  forget_enrichment.hom_to W (forget_enrichment.hom_of W f) = f :=
  rfl

@[simp]
theorem forget_enrichment.hom_of_hom_to {X Y : forget_enrichment W C} (f : X ⟶ Y) :
  forget_enrichment.hom_of W (forget_enrichment.hom_to W f) = f :=
  rfl

/-- The identity in the "underlying" category of an enriched category. -/
@[simp]
theorem forget_enrichment_id (X : forget_enrichment W C) :
  forget_enrichment.hom_to W (𝟙 X) = e_id W (forget_enrichment.to W X : C) :=
  category.id_comp _

@[simp]
theorem forget_enrichment_id' (X : C) : forget_enrichment.hom_of W (e_id W X) = 𝟙 (forget_enrichment.of W X : C) :=
  (forget_enrichment_id W (forget_enrichment.of W X)).symm

/-- Composition in the "underlying" category of an enriched category. -/
@[simp]
theorem forget_enrichment_comp {X Y Z : forget_enrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  forget_enrichment.hom_to W (f ≫ g) =
    ((λ_ (𝟙_ W)).inv ≫ (forget_enrichment.hom_to W f ⊗ forget_enrichment.hom_to W g)) ≫ e_comp W _ _ _ :=
  rfl

end 

/--
A `V`-functor `F` between `V`-enriched categories
has a `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`,
satisfying the usual axioms.
-/
structure enriched_functor(C : Type u₁)[enriched_category V C](D : Type u₂)[enriched_category V D] where 
  obj : C → D 
  map : ∀ X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y 
  map_id' : ∀ X : C, e_id V X ≫ map X X = e_id V (obj X) :=  by 
  runTac 
    obviously 
  map_comp' : ∀ X Y Z : C, e_comp V X Y Z ≫ map X Z = (map X Y ⊗ map Y Z) ≫ e_comp V (obj X) (obj Y) (obj Z) :=  by 
  runTac 
    obviously

restate_axiom enriched_functor.map_id'

restate_axiom enriched_functor.map_comp'

attribute [simp, reassoc] enriched_functor.map_id

attribute [simp, reassoc] enriched_functor.map_comp

/-- The identity enriched functor. -/
@[simps]
def enriched_functor.id (C : Type u₁) [enriched_category V C] : enriched_functor V C C :=
  { obj := fun X => X, map := fun X Y => 𝟙 _ }

instance  : Inhabited (enriched_functor V C C) :=
  ⟨enriched_functor.id V C⟩

/-- Composition of enriched functors. -/
@[simps]
def enriched_functor.comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [enriched_category V C] [enriched_category V D]
  [enriched_category V E] (F : enriched_functor V C D) (G : enriched_functor V D E) : enriched_functor V C E :=
  { obj := fun X => G.obj (F.obj X), map := fun X Y => F.map _ _ ≫ G.map _ _ }

section 

variable{W : Type (v + 1)}[category.{v} W][monoidal_category W]

/--
An enriched functor induces an honest functor of the underlying categories,
by mapping the `(𝟙_ W)`-shaped morphisms.
-/
def enriched_functor.forget {C : Type u₁} {D : Type u₂} [enriched_category W C] [enriched_category W D]
  (F : enriched_functor W C D) : forget_enrichment W C ⥤ forget_enrichment W D :=
  { obj := fun X => forget_enrichment.of W (F.obj (forget_enrichment.to W X)),
    map :=
      fun X Y f =>
        forget_enrichment.hom_of W
          (forget_enrichment.hom_to W f ≫ F.map (forget_enrichment.to W X) (forget_enrichment.to W Y)),
    map_comp' :=
      fun X Y Z f g =>
        by 
          dsimp 
          applyFun forget_enrichment.hom_to W
          ·
            simp only [iso.cancel_iso_inv_left, category.assoc, tensor_comp, forget_enrichment.hom_to_hom_of,
              enriched_functor.map_comp, forget_enrichment_comp]
            rfl
          ·
            intro f g w 
            applyFun forget_enrichment.hom_of W  at w 
            simpa using w }

end 

section 

variable{V}

variable{D : Type u₂}[enriched_category V D]

/-!
We now turn to natural transformations between `V`-functors.

The mostly commonly encountered definition of an enriched natural transformation
is a collection of morphisms
```
(𝟙_ W) ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying an appropriate analogue of the naturality square.
(c.f. https://ncatlab.org/nlab/show/enriched+natural+transformation)

This is the same thing as a natural transformation `F.forget ⟶ G.forget`.

We formalize this as `enriched_nat_trans F G`, which is a `Type`.

However, there's also something much nicer: with appropriate additional hypotheses,
there is a `V`-object `enriched_nat_trans_obj F G` which contains more information,
and from which one can recover `enriched_nat_trans F G ≃ (𝟙_ V) ⟶ enriched_nat_trans_obj F G`.

Using these as the hom-objects, we can build a `V`-enriched category
with objects the `V`-functors.

For `enriched_nat_trans_obj` to exist, it suffices to have `V` braided and complete.

Before assuming `V` is complete, we assume it is braided and
define a presheaf `enriched_nat_trans_yoneda F G`
which is isomorphic to the Yoneda embedding of `enriched_nat_trans_obj F G`
whether or not that object actually exists.

This presheaf has components `(enriched_nat_trans_yoneda F G).obj A`
what we call the `A`-graded enriched natural transformations,
which are collections of morphisms
```
A ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying a similar analogue of the naturality square,
this time incorporating a half-braiding on `A`.

(We actually define `enriched_nat_trans F G`
as the special case `A := 𝟙_ V` with the trivial half-braiding,
and when defining `enriched_nat_trans_yoneda F G` we use the half-braidings
coming from the ambient braiding on `V`.)
-/


/--
The type of `A`-graded natural transformations between `V`-functors `F` and `G`.
This is the type of morphisms in `V` from `A` to the `V`-object of natural transformations.
-/
@[ext, nolint has_inhabited_instance]
structure graded_nat_trans(A : center V)(F G : enriched_functor V C D) where 
  app : ∀ X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X 
  naturality :
  ∀ X Y : C, (A.2.β (X ⟶[V] Y)).Hom ≫ (F.map X Y ⊗ app Y) ≫ e_comp V _ _ _ = (app X ⊗ G.map X Y) ≫ e_comp V _ _ _

variable[braided_category V]

open BraidedCategory

-- error in CategoryTheory.Enriched.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A presheaf isomorphic to the Yoneda embedding of
the `V`-object of natural transformations from `F` to `G`.
-/ @[simps #[]] def enriched_nat_trans_yoneda (F G : enriched_functor V C D) : «expr ⥤ »(«expr ᵒᵖ»(V), Type max u₁ w) :=
{ obj := λ A, graded_nat_trans ((center.of_braided V).obj (unop A)) F G,
  map := λ
  A
  A'
  f
  σ, { app := λ X, «expr ≫ »(f.unop, σ.app X),
    naturality := λ X Y, begin
      have [ident p] [] [":=", expr σ.naturality X Y],
      dsimp [] [] [] ["at", ident p, "⊢"],
      rw ["[", "<-", expr id_tensor_comp_tensor_id «expr ≫ »(f.unop, σ.app Y) _, ",", expr id_tensor_comp, ",", expr category.assoc, ",", expr category.assoc, ",", "<-", expr braiding_naturality_assoc, ",", expr id_tensor_comp_tensor_id_assoc, ",", expr p, ",", "<-", expr tensor_comp_assoc, ",", expr category.id_comp, "]"] []
    end } }

end 

section 

attribute [local instance] category_of_enriched_category_Type

/--
We verify that an enriched functor between `Type v` enriched categories
is just the same thing as an honest functor.
-/
@[simps]
def enriched_functor_Type_equiv_functor {C : Type u₁} [𝒞 : enriched_category (Type v) C] {D : Type u₂}
  [𝒟 : enriched_category (Type v) D] : enriched_functor (Type v) C D ≃ C ⥤ D :=
  { toFun :=
      fun F =>
        { obj := fun X => F.obj X, map := fun X Y f => F.map X Y f,
          map_id' := fun X => congr_funₓ (F.map_id X) PUnit.unit,
          map_comp' := fun X Y Z f g => congr_funₓ (F.map_comp X Y Z) ⟨f, g⟩ },
    invFun :=
      fun F =>
        { obj := fun X => F.obj X, map := fun X Y f => F.map f,
          map_id' :=
            fun X =>
              by 
                ext ⟨⟩
                exact F.map_id X,
          map_comp' :=
            fun X Y Z =>
              by 
                ext ⟨f, g⟩
                exact F.map_comp f g },
    left_inv :=
      fun F =>
        by 
          cases F 
          simp ,
    right_inv :=
      fun F =>
        by 
          cases F 
          simp  }

/--
We verify that the presheaf representing natural transformations
between `Type v`-enriched functors is actually represented by
the usual type of natural transformations!
-/
def enriched_nat_trans_yoneda_Type_iso_yoneda_nat_trans {C : Type v} [enriched_category (Type v) C] {D : Type v}
  [enriched_category (Type v) D] (F G : enriched_functor (Type v) C D) :
  enriched_nat_trans_yoneda F G ≅
    yoneda.obj (enriched_functor_Type_equiv_functor F ⟶ enriched_functor_Type_equiv_functor G) :=
  nat_iso.of_components
    (fun α =>
      { Hom :=
          fun σ x => { app := fun X => σ.app X x, naturality' := fun X Y f => congr_funₓ (σ.naturality X Y) ⟨x, f⟩ },
        inv :=
          fun σ =>
            { app := fun X x => (σ x).app X,
              naturality :=
                fun X Y =>
                  by 
                    ext ⟨x, f⟩
                    exact (σ x).naturality f } })
    (by 
      tidy)

end 

end CategoryTheory

