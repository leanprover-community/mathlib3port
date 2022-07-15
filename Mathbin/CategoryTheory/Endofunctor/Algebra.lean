/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Johan Commelin, Reid Barton, Rob Lewis, Joseph Hua
-/
import Mathbin.CategoryTheory.Limits.Final
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-!
# Algebras of endofunctors
This file defines algebras of an endofunctor,
and provides the category instance for them.
This extends to Eilenberg-Moore (co)algebras for a (co)monad.
It also defines the forgetful functor from the category of algebras.
It is shown that the structure map of the initial algebra of an endofunctor
is an isomorphism.
-/


universe v u

namespace CategoryTheory

namespace Endofunctor

variable {C : Type u} [Category.{v} C]

/-- An algebra of an endofunctor; `str` stands for "structure morphism" -/
structure Algebra (F : C ⥤ C) where
  A : C
  str : F.obj A ⟶ A

instance [Inhabited C] : Inhabited (Algebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Algebra

variable {F : C ⥤ C} (A : Algebra F) {A₀ A₁ A₂ : Algebra F}

/-- A morphism between algebras of endofunctor `F` -/
/-
```
        str
   F A₀ -----> A₀
    |          |
F f |          | f
    V          V
   F A₁ -----> A₁
        str
```
-/
@[ext]
structure Hom (A₀ A₁ : Algebra F) where
  f : A₀.1 ⟶ A₁.1
  h' : F.map f ≫ A₁.str = A₀.str ≫ f := by
    run_tac
      obviously

restate_axiom hom.h'

attribute [simp, reassoc] hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : Hom A A where f := 𝟙 _

instance : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Algebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[simp]
theorem id_eq_id : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
theorem id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 :=
  rfl

variable {A₀ A₁ A₂} (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp]
theorem comp_eq_comp : Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Algebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Algebra F) where

/-- To construct an isomorphism of algebras, it suffices to give an isomorphism of the As which
commutes with the structure morphisms.
-/
@[simps]
def isoMk (h : A₀.1 ≅ A₁.1) (w : F.map h.Hom ≫ A₁.str = A₀.str ≫ h.Hom) : A₀ ≅ A₁ where
  Hom := { f := h.Hom }
  inv :=
    { f := h.inv,
      h' := by
        rw [h.eq_comp_inv, category.assoc, ← w, ← functor.map_comp_assoc]
        simp }

/-- The forgetful functor from the category of algebras, forgetting the algebraic structure. -/
@[simps]
def forget (F : C ⥤ C) : Algebra F ⥤ C where
  obj := fun A => A.1
  map := fun A B f => f.1

/-- An algebra morphism with an underlying isomorphism hom in `C` is an algebra isomorphism. -/
theorem iso_of_iso (f : A₀ ⟶ A₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1,
        h' := by
          rw [is_iso.eq_comp_inv f.1, category.assoc, ← f.h]
          simp },
      by
      tidy⟩⟩

instance forget_reflects_iso : ReflectsIsomorphisms (forget F) where reflects := fun A B => iso_of_iso

instance forget_faithful : Faithful (forget F) where

/-- From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : G ⟶ F) : Algebra F ⥤ Algebra G where
  obj := fun A => { A := A.1, str := α.app A.1 ≫ A.str }
  map := fun A₀ A₁ f => { f := f.1 }

/-- The identity transformation induces the identity endofunctor on the category of algebras. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp ))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans β ⋙ functorOfNatTrans α :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp ))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- If `α` and `β` are two equal natural transformations, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) : functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp [← h]))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- Naturally isomorphic endofunctors give equivalent categories of algebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Algebra F ≌ Algebra G where
  Functor := functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.Hom
  unitIso :=
    functorOfNatTransId.symm ≪≫
      functorOfNatTransEq
          (by
            simp ) ≪≫
        functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫
      functorOfNatTransEq
          (by
            simp ) ≪≫
        functor_of_nat_trans_id

namespace Initial

variable {A} (h : Limits.IsInitial A)

/-- The inverse of the structure map of an initial algebra -/
@[simp]
def strInv : A.1 ⟶ F.obj A.1 :=
  (h.to ⟨F.obj A.1, F.map A.str⟩).1

theorem left_inv' : (⟨strInv h ≫ A.str⟩ : A ⟶ A) = 𝟙 A :=
  Limits.IsInitial.hom_ext h _ (𝟙 A)

theorem left_inv : strInv h ≫ A.str = 𝟙 _ :=
  congr_arg Hom.f (left_inv' h)

theorem right_inv : A.str ≫ strInv h = 𝟙 _ := by
  rw [str_inv, ← (h.to ⟨F.obj A.1, F.map A.str⟩).h, ← F.map_id, ← F.map_comp]
  congr
  exact left_inv h

/-- The structure map of the inital algebra is an isomorphism,
hence endofunctors preserve their initial algebras
-/
theorem str_is_iso (h : Limits.IsInitial A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩ }

end Initial

end Algebra

end Endofunctor

end CategoryTheory

