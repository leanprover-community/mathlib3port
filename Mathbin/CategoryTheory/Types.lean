/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl
-/
import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Functor.FullyFaithful
import Mathbin.Logic.Equiv.Defs

/-!
# The category `Type`.

In this section we set up the theory so that Lean's types and functions between them
can be viewed as a `large_category` in our framework.

Lean can not transparently view a function as a morphism in this category, and needs a hint in
order to be able to type check. We provide the abbreviation `as_hom f` to guide type checking,
as well as a corresponding notation `↾ f`. (Entered as `\upr `.) The notation is enabled using
`open_locale category_theory.Type`.

We provide various simplification lemmas for functors and natural transformations valued in `Type`.

We define `ulift_functor`, from `Type u` to `Type (max u v)`, and show that it is fully faithful
(but not, of course, essentially surjective).

We prove some basic facts about the category `Type`:
*  epimorphisms are surjections and monomorphisms are injections,
* `iso` is both `iso` and `equiv` to `equiv` (at least within a fixed universe),
* every type level `is_lawful_functor` gives a categorical functor `Type ⥤ Type`
  (the corresponding fact about monads is in `src/category_theory/monad/types.lean`).
-/


namespace CategoryTheory

-- morphism levels before object levels. See note [category_theory universes].
universe v v' w u u'

/- The `@[to_additive]` attribute is just a hint that expressions involving this instance can
  still be additivized. -/
@[to_additive CategoryTheory.types]
instance types : LargeCategory (Type u) where
  Hom a b := a → b
  id a := id
  comp _ _ _ f g := g ∘ f
#align category_theory.types CategoryTheory.types

theorem types_hom {α β : Type u} : (α ⟶ β) = (α → β) :=
  rfl
#align category_theory.types_hom CategoryTheory.types_hom

theorem types_id (X : Type u) : 𝟙 X = id :=
  rfl
#align category_theory.types_id CategoryTheory.types_id

theorem types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f :=
  rfl
#align category_theory.types_comp CategoryTheory.types_comp

@[simp]
theorem types_id_apply (X : Type u) (x : X) : (𝟙 X : X → X) x = x :=
  rfl
#align category_theory.types_id_apply CategoryTheory.types_id_apply

@[simp]
theorem types_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl
#align category_theory.types_comp_apply CategoryTheory.types_comp_apply

@[simp]
theorem hom_inv_id_apply {X Y : Type u} (f : X ≅ Y) (x : X) : f.inv (f.Hom x) = x :=
  congr_fun f.hom_inv_id x
#align category_theory.hom_inv_id_apply CategoryTheory.hom_inv_id_apply

@[simp]
theorem inv_hom_id_apply {X Y : Type u} (f : X ≅ Y) (y : Y) : f.Hom (f.inv y) = y :=
  congr_fun f.inv_hom_id y
#align category_theory.inv_hom_id_apply CategoryTheory.inv_hom_id_apply

-- Unfortunately without this wrapper we can't use `category_theory` idioms, such as `is_iso f`.
/-- `as_hom f` helps Lean type check a function as a morphism in the category `Type`. -/
abbrev asHom {α β : Type u} (f : α → β) : α ⟶ β :=
  f
#align category_theory.as_hom CategoryTheory.asHom

-- mathport name: category_theory.as_hom
-- If you don't mind some notation you can use fewer keystrokes:
scoped[CategoryTheory.TypeCat] notation "↾" f:200 => CategoryTheory.asHom f

-- type as \upr in VScode
section

-- We verify the expected type checking behaviour of `as_hom`.
variable (α β γ : Type u) (f : α → β) (g : β → γ)

example : α → γ :=
  ↾f ≫ ↾g

example [IsIso (↾f)] : Mono (↾f) := by infer_instance

example [IsIso (↾f)] : ↾f ≫ inv (↾f) = 𝟙 α := by simp

end

namespace Functor

variable {J : Type u} [Category.{v} J]

/-- The sections of a functor `J ⥤ Type` are
the choices of a point `u j : F.obj j` for each `j`,
such that `F.map f (u j) = u j` for every morphism `f : j ⟶ j'`.

We later use these to define limits in `Type` and in many concrete categories.
-/
def sections (F : J ⥤ Type w) : Set (∀ j, F.obj j) :=
  { u | ∀ {j j'} (f : j ⟶ j'), F.map f (u j) = u j' }
#align category_theory.functor.sections CategoryTheory.Functor.sections

end Functor

namespace FunctorToTypes

variable {C : Type u} [Category.{v} C] (F G H : C ⥤ Type w) {X Y Z : C}

variable (σ : F ⟶ G) (τ : G ⟶ H)

@[simp]
theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) : (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) := by
  simp [types_comp]
#align category_theory.functor_to_types.map_comp_apply CategoryTheory.FunctorToTypes.map_comp_apply

@[simp]
theorem map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a := by simp [types_id]
#align category_theory.functor_to_types.map_id_apply CategoryTheory.FunctorToTypes.map_id_apply

theorem naturality (f : X ⟶ Y) (x : F.obj X) : σ.app Y ((F.map f) x) = (G.map f) (σ.app X x) :=
  congr_fun (σ.naturality f) x
#align category_theory.functor_to_types.naturality CategoryTheory.FunctorToTypes.naturality

@[simp]
theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
  rfl
#align category_theory.functor_to_types.comp CategoryTheory.FunctorToTypes.comp

variable {D : Type u'} [𝒟 : Category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}

@[simp]
theorem hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) :=
  rfl
#align category_theory.functor_to_types.hcomp CategoryTheory.FunctorToTypes.hcomp

@[simp]
theorem map_inv_map_hom_apply (f : X ≅ Y) (x : F.obj X) : F.map f.inv (F.map f.Hom x) = x :=
  congr_fun (F.mapIso f).hom_inv_id x
#align category_theory.functor_to_types.map_inv_map_hom_apply CategoryTheory.FunctorToTypes.map_inv_map_hom_apply

@[simp]
theorem map_hom_map_inv_apply (f : X ≅ Y) (y : F.obj Y) : F.map f.Hom (F.map f.inv y) = y :=
  congr_fun (F.mapIso f).inv_hom_id y
#align category_theory.functor_to_types.map_hom_map_inv_apply CategoryTheory.FunctorToTypes.map_hom_map_inv_apply

@[simp]
theorem hom_inv_id_app_apply (α : F ≅ G) (X) (x) : α.inv.app X (α.Hom.app X x) = x :=
  congr_fun (α.hom_inv_id_app X) x
#align category_theory.functor_to_types.hom_inv_id_app_apply CategoryTheory.FunctorToTypes.hom_inv_id_app_apply

@[simp]
theorem inv_hom_id_app_apply (α : F ≅ G) (X) (x) : α.Hom.app X (α.inv.app X x) = x :=
  congr_fun (α.inv_hom_id_app X) x
#align category_theory.functor_to_types.inv_hom_id_app_apply CategoryTheory.FunctorToTypes.inv_hom_id_app_apply

end FunctorToTypes

/-- The isomorphism between a `Type` which has been `ulift`ed to the same universe,
and the original type.
-/
def uliftTrivial (V : Type u) : ULift.{u} V ≅ V := by tidy
#align category_theory.ulift_trivial CategoryTheory.uliftTrivial

/-- The functor embedding `Type u` into `Type (max u v)`.
Write this as `ulift_functor.{5 2}` to get `Type 2 ⥤ Type 5`.
-/
def uliftFunctor : Type u ⥤ Type max u v where
  obj X := ULift.{v} X
  map X Y f := fun x : ULift.{v} X => ULift.up (f x.down)
#align category_theory.ulift_functor CategoryTheory.uliftFunctor

@[simp]
theorem ulift_functor_map {X Y : Type u} (f : X ⟶ Y) (x : ULift.{v} X) : uliftFunctor.map f x = ULift.up (f x.down) :=
  rfl
#align category_theory.ulift_functor_map CategoryTheory.ulift_functor_map

instance uliftFunctorFull : Full.{u} uliftFunctor where preimage X Y f x := (f (ULift.up x)).down
#align category_theory.ulift_functor_full CategoryTheory.uliftFunctorFull

instance ulift_functor_faithful :
    Faithful
      uliftFunctor where map_injective' X Y f g p :=
    funext $ fun x => congr_arg ULift.down (congr_fun p (ULift.up x) : ULift.up (f x) = ULift.up (g x))
#align category_theory.ulift_functor_faithful CategoryTheory.ulift_functor_faithful

/-- The functor embedding `Type u` into `Type u` via `ulift` is isomorphic to the identity functor.
 -/
def uliftFunctorTrivial : ulift_functor.{u, u} ≅ 𝟭 _ :=
  NatIso.ofComponents uliftTrivial (by tidy)
#align category_theory.ulift_functor_trivial CategoryTheory.uliftFunctorTrivial

-- TODO We should connect this to a general story about concrete categories
-- whose forgetful functor is representable.
/-- Any term `x` of a type `X` corresponds to a morphism `punit ⟶ X`. -/
def homOfElement {X : Type u} (x : X) : PUnit ⟶ X := fun _ => x
#align category_theory.hom_of_element CategoryTheory.homOfElement

theorem hom_of_element_eq_iff {X : Type u} (x y : X) : homOfElement x = homOfElement y ↔ x = y :=
  ⟨fun H => congr_fun H PUnit.unit, by cc⟩
#align category_theory.hom_of_element_eq_iff CategoryTheory.hom_of_element_eq_iff

/-- A morphism in `Type` is a monomorphism if and only if it is injective.

See <https://stacks.math.columbia.edu/tag/003C>.
-/
theorem mono_iff_injective {X Y : Type u} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  constructor
  · intro H x x' h
    skip
    rw [← hom_of_element_eq_iff] at h⊢
    exact (cancel_mono f).mp h
    
  · exact fun H => ⟨fun Z => H.compLeft⟩
    
#align category_theory.mono_iff_injective CategoryTheory.mono_iff_injective

theorem injective_of_mono {X Y : Type u} (f : X ⟶ Y) [hf : Mono f] : Function.Injective f :=
  (mono_iff_injective f).1 hf
#align category_theory.injective_of_mono CategoryTheory.injective_of_mono

/-- A morphism in `Type` is an epimorphism if and only if it is surjective.

See <https://stacks.math.columbia.edu/tag/003C>.
-/
theorem epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · rintro ⟨H⟩
    refine' Function.surjective_of_right_cancellable_Prop fun g₁ g₂ hg => _
    rw [← equiv.ulift.symm.injective.comp_left.eq_iff]
    apply H
    change ULift.up ∘ g₁ ∘ f = ULift.up ∘ g₂ ∘ f
    rw [hg]
    
  · exact fun H => ⟨fun Z => H.injective_comp_right⟩
    
#align category_theory.epi_iff_surjective CategoryTheory.epi_iff_surjective

theorem surjective_of_epi {X Y : Type u} (f : X ⟶ Y) [hf : Epi f] : Function.Surjective f :=
  (epi_iff_surjective f).1 hf
#align category_theory.surjective_of_epi CategoryTheory.surjective_of_epi

section

/-- `of_type_functor m` converts from Lean's `Type`-based `category` to `category_theory`. This
allows us to use these functors in category theory. -/
def ofTypeFunctor (m : Type u → Type v) [Functor m] [IsLawfulFunctor m] : Type u ⥤ Type v where
  obj := m
  map α β := Functor.map
  map_id' α := Functor.map_id
  map_comp' α β γ f g := funext $ fun a => IsLawfulFunctor.comp_map f g _
#align category_theory.of_type_functor CategoryTheory.ofTypeFunctor

variable (m : Type u → Type v) [Functor m] [IsLawfulFunctor m]

@[simp]
theorem of_type_functor_obj : (ofTypeFunctor m).obj = m :=
  rfl
#align category_theory.of_type_functor_obj CategoryTheory.of_type_functor_obj

@[simp]
theorem of_type_functor_map {α β} (f : α → β) : (ofTypeFunctor m).map f = (Functor.map f : m α → m β) :=
  rfl
#align category_theory.of_type_functor_map CategoryTheory.of_type_functor_map

end

end CategoryTheory

-- Isomorphisms in Type and equivalences.
namespace Equiv

universe u

variable {X Y : Type u}

/-- Any equivalence between types in the same universe gives
a categorical isomorphism between those types.
-/
def toIso (e : X ≃ Y) : X ≅ Y where
  Hom := e.toFun
  inv := e.invFun
  hom_inv_id' := funext e.left_inv
  inv_hom_id' := funext e.right_inv
#align equiv.to_iso Equiv.toIso

@[simp]
theorem to_iso_hom {e : X ≃ Y} : e.toIso.Hom = e :=
  rfl
#align equiv.to_iso_hom Equiv.to_iso_hom

@[simp]
theorem to_iso_inv {e : X ≃ Y} : e.toIso.inv = e.symm :=
  rfl
#align equiv.to_iso_inv Equiv.to_iso_inv

end Equiv

universe u

namespace CategoryTheory.Iso

open CategoryTheory

variable {X Y : Type u}

/-- Any isomorphism between types gives an equivalence.
-/
def toEquiv (i : X ≅ Y) : X ≃ Y where
  toFun := i.Hom
  invFun := i.inv
  left_inv x := congr_fun i.hom_inv_id x
  right_inv y := congr_fun i.inv_hom_id y
#align category_theory.iso.to_equiv CategoryTheory.Iso.toEquiv

@[simp]
theorem to_equiv_fun (i : X ≅ Y) : (i.toEquiv : X → Y) = i.Hom :=
  rfl
#align category_theory.iso.to_equiv_fun CategoryTheory.Iso.to_equiv_fun

@[simp]
theorem to_equiv_symm_fun (i : X ≅ Y) : (i.toEquiv.symm : Y → X) = i.inv :=
  rfl
#align category_theory.iso.to_equiv_symm_fun CategoryTheory.Iso.to_equiv_symm_fun

@[simp]
theorem to_equiv_id (X : Type u) : (Iso.refl X).toEquiv = Equiv.refl X :=
  rfl
#align category_theory.iso.to_equiv_id CategoryTheory.Iso.to_equiv_id

@[simp]
theorem to_equiv_comp {X Y Z : Type u} (f : X ≅ Y) (g : Y ≅ Z) : (f ≪≫ g).toEquiv = f.toEquiv.trans g.toEquiv :=
  rfl
#align category_theory.iso.to_equiv_comp CategoryTheory.Iso.to_equiv_comp

end CategoryTheory.Iso

namespace CategoryTheory

/-- A morphism in `Type u` is an isomorphism if and only if it is bijective. -/
theorem is_iso_iff_bijective {X Y : Type u} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f :=
  Iff.intro (fun i => (as_iso f : X ≅ Y).toEquiv.Bijective) fun b => IsIso.of_iso (Equiv.ofBijective f b).toIso
#align category_theory.is_iso_iff_bijective CategoryTheory.is_iso_iff_bijective

instance :
    SplitEpiCategory
      (Type
        u) where is_split_epi_of_epi X Y f hf :=
    IsSplitEpi.mk'
      { section_ := Function.surjInv $ (epi_iff_surjective f).1 hf,
        id' := funext $ Function.right_inverse_surj_inv $ (epi_iff_surjective f).1 hf }

end CategoryTheory

-- We prove `equiv_iso_iso` and then use that to sneakily construct `equiv_equiv_iso`.
-- (In this order the proofs are handled by `obviously`.)
/-- Equivalences (between types in the same universe) are the same as (isomorphic to) isomorphisms
of types. -/
@[simps]
def equivIsoIso {X Y : Type u} : X ≃ Y ≅ X ≅ Y where
  Hom e := e.toIso
  inv i := i.toEquiv
#align equiv_iso_iso equivIsoIso

/-- Equivalences (between types in the same universe) are the same as (equivalent to) isomorphisms
of types. -/
def equivEquivIso {X Y : Type u} : X ≃ Y ≃ (X ≅ Y) :=
  equivIsoIso.toEquiv
#align equiv_equiv_iso equivEquivIso

@[simp]
theorem equiv_equiv_iso_hom {X Y : Type u} (e : X ≃ Y) : equivEquivIso e = e.toIso :=
  rfl
#align equiv_equiv_iso_hom equiv_equiv_iso_hom

@[simp]
theorem equiv_equiv_iso_inv {X Y : Type u} (e : X ≅ Y) : equivEquivIso.symm e = e.toEquiv :=
  rfl
#align equiv_equiv_iso_inv equiv_equiv_iso_inv

