/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathbin.CategoryTheory.EqToHom
import Mathbin.Data.Ulift

/-!
# Discrete categories

We define `discrete α := α` for any type `α`, and use this type alias
to provide a `small_category` instance whose only morphisms are the identities.

There is an annoying technical difficulty that it has turned out to be inconvenient
to allow categories with morphisms living in `Prop`,
so instead of defining `X ⟶ Y` in `discrete α` as `X = Y`,
one might define it as `plift (X = Y)`.
In fact, to allow `discrete α` to be a `small_category`
(i.e. with morphisms in the same universe as the objects),
we actually define the hom type `X ⟶ Y` as `ulift (plift (X = Y))`.

`discrete.functor` promotes a function `f : I → C` (for any category `C`) to a functor
`discrete.functor f : discrete I ⥤ C`.

Similarly, `discrete.nat_trans` and `discrete.nat_iso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We show equivalences of types are the same as (categorical) equivalences of the corresponding
discrete categories.
-/


namespace CategoryTheory

-- morphism levels before object levels. See note [category_theory universes].
universe v₁ v₂ v₃ u₁ u₂ u₃

/-- A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
def Discrete (α : Type u₁) :=
  α

/-- The "discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ulift (plift (X = Y))`.

See <https://stacks.math.columbia.edu/tag/001A>
-/
instance discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where
  Hom := fun X Y => ULift (Plift (X = Y))
  id := fun X => ULift.up (Plift.up rfl)
  comp := fun X Y Z g f => by
    rcases f with ⟨⟨rfl⟩⟩
    exact g

namespace Discrete

variable {α : Type u₁}

instance [Inhabited α] : Inhabited (Discrete α) := by
  dsimp' [discrete]
  infer_instance

instance [Subsingleton α] : Subsingleton (Discrete α) := by
  dsimp' [discrete]
  infer_instance

/-- Extract the equation from a morphism in a discrete category. -/
theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X = Y :=
  i.down.down

@[simp]
theorem id_def (X : Discrete α) : ULift.up (Plift.up (Eq.refl X)) = 𝟙 X :=
  rfl

variable {C : Type u₂} [Category.{v₂} C]

instance {I : Type u₁} {i j : Discrete I} (f : i ⟶ j) : IsIso f :=
  ⟨⟨eqToHom (eq_of_hom f).symm, by
      tidy⟩⟩

/-- Any function `I → C` gives a functor `discrete I ⥤ C`.
-/
def functor {I : Type u₁} (F : I → C) : Discrete I ⥤ C where
  obj := F
  map := fun X Y f => by
    cases f
    cases f
    cases f
    exact 𝟙 (F X)

@[simp]
theorem functor_obj {I : Type u₁} (F : I → C) (i : I) : (Discrete.functor F).obj i = F i :=
  rfl

theorem functor_map {I : Type u₁} (F : I → C) {i : Discrete I} (f : i ⟶ i) : (Discrete.functor F).map f = 𝟙 (F i) := by
  cases f
  cases f
  cases f
  rfl

/-- For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
def natTrans {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ⟶ G.obj i) : F ⟶ G where
  app := f

@[simp]
theorem nat_trans_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ⟶ G.obj i) i :
    (Discrete.natTrans f).app i = f i :=
  rfl

/-- For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
def natIso {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) : F ≅ G :=
  NatIso.ofComponents f
    (by
      tidy)

@[simp]
theorem nat_iso_hom_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) (i : I) :
    (Discrete.natIso f).Hom.app i = (f i).Hom :=
  rfl

@[simp]
theorem nat_iso_inv_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) (i : I) :
    (Discrete.natIso f).inv.app i = (f i).inv :=
  rfl

@[simp]
theorem nat_iso_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) (i : I) :
    (Discrete.natIso f).app i = f i := by
  tidy

/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `discrete.functor (F.obj)`. -/
@[simp]
def natIsoFunctor {I : Type u₁} {F : Discrete I ⥤ C} : F ≅ Discrete.functor F.obj :=
  nat_iso fun i => Iso.refl _

/-- Composing `discrete.functor F` with another functor `G` amounts to composing `F` with `G.obj` -/
@[simp]
def compNatIsoDiscrete {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I → C) (G : C ⥤ D) :
    Discrete.functor F ⋙ G ≅ Discrete.functor (G.obj ∘ F) :=
  nat_iso fun i => Iso.refl _

/-- We can promote a type-level `equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
def equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : Discrete I ≌ Discrete J where
  Functor := Discrete.functor (e : I → J)
  inverse := Discrete.functor (e.symm : J → I)
  unitIso :=
    Discrete.natIso fun i =>
      eqToIso
        (by
          simp )
  counitIso :=
    Discrete.natIso fun j =>
      eqToIso
        (by
          simp )

/-- We can convert an equivalence of `discrete` categories to a type-level `equiv`. -/
@[simps]
def equivOfEquivalence {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete β) : α ≃ β where
  toFun := h.Functor.obj
  invFun := h.inverse.obj
  left_inv := fun a => eq_of_hom (h.unitIso.app a).2
  right_inv := fun a => eq_of_hom (h.counitIso.app a).1

end Discrete

namespace Discrete

variable {J : Type v₁}

open Opposite

/-- A discrete category is equivalent to its opposite category. -/
protected def opposite (α : Type u₁) : (Discrete α)ᵒᵖ ≌ Discrete α := by
  let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op x
  refine'
    equivalence.mk (functor.left_op F) F _
      (discrete.nat_iso fun X => by
        simp [F])
  refine'
    nat_iso.of_components
      (fun X => by
        simp [F])
      _
  tidy

variable {C : Type u₂} [Category.{v₂} C]

@[simp]
theorem functor_map_id (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j) := by
  have h : f = 𝟙 j := by
    cases f
    cases f
    ext
  rw [h]
  simp

end Discrete

end CategoryTheory

