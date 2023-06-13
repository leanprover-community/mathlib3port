/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno

! This file was ported from Lean 3 source module category_theory.bicategory.coherence_tactic
! leanprover-community/mathlib commit 7e5137f579de09a059a5ce98f364a04e221aabf0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Bicategory.Coherence

/-!
# A `coherence` tactic for bicategories, and `⊗≫` (composition up to associators)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide a `coherence` tactic,
which proves that any two 2-morphisms (with the same source and target)
in a bicategory which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `bicategorical_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.

This file mainly deals with the type class setup for the coherence tactic. The actual front end
tactic is given in `category_theory/monooidal/coherence.lean` at the same time as the coherence
tactic for monoidal categories.
-/


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.FreeBicategory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

namespace CategoryTheory.Bicategory

#print Mathlib.Tactic.BicategoryCoherence.LiftHom /-
/-- A typeclass carrying a choice of lift of a 1-morphism from `B` to `free_bicategory B`. -/
class Mathlib.Tactic.BicategoryCoherence.LiftHom {a b : B} (f : a ⟶ b) where
  lift : of.obj a ⟶ of.obj b
#align category_theory.bicategory.lift_hom Mathlib.Tactic.BicategoryCoherence.LiftHom
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHomId /-
instance Mathlib.Tactic.BicategoryCoherence.liftHomId :
    Mathlib.Tactic.BicategoryCoherence.LiftHom (𝟙 a) where lift := 𝟙 (of.obj a)
#align category_theory.bicategory.lift_hom_id Mathlib.Tactic.BicategoryCoherence.liftHomId
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHomComp /-
instance Mathlib.Tactic.BicategoryCoherence.liftHomComp (f : a ⟶ b) (g : b ⟶ c)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom (f ≫ g)
    where lift :=
    Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f ≫
      Mathlib.Tactic.BicategoryCoherence.LiftHom.lift g
#align category_theory.bicategory.lift_hom_comp Mathlib.Tactic.BicategoryCoherence.liftHomComp
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHomOf /-
instance (priority := 100) Mathlib.Tactic.BicategoryCoherence.liftHomOf (f : a ⟶ b) :
    Mathlib.Tactic.BicategoryCoherence.LiftHom f where lift := of.map f
#align category_theory.bicategory.lift_hom_of Mathlib.Tactic.BicategoryCoherence.liftHomOf
-/

#print Mathlib.Tactic.BicategoryCoherence.LiftHom₂ /-
/-- A typeclass carrying a choice of lift of a 2-morphism from `B` to `free_bicategory B`. -/
class Mathlib.Tactic.BicategoryCoherence.LiftHom₂ {f g : a ⟶ b}
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    (η : f ⟶ g) where
  lift :
    Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f ⟶
      Mathlib.Tactic.BicategoryCoherence.LiftHom.lift g
#align category_theory.bicategory.lift_hom₂ Mathlib.Tactic.BicategoryCoherence.LiftHom₂
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂Id /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂Id (f : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (𝟙 f) where lift := 𝟙 _
#align category_theory.bicategory.lift_hom₂_id Mathlib.Tactic.BicategoryCoherence.liftHom₂Id
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂LeftUnitorHom /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂LeftUnitorHom (f : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (λ_ f).Hom
    where lift := (λ_ (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f)).Hom
#align category_theory.bicategory.lift_hom₂_left_unitor_hom Mathlib.Tactic.BicategoryCoherence.liftHom₂LeftUnitorHom
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂LeftUnitorInv /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂LeftUnitorInv (f : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (λ_ f).inv
    where lift := (λ_ (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f)).inv
#align category_theory.bicategory.lift_hom₂_left_unitor_inv Mathlib.Tactic.BicategoryCoherence.liftHom₂LeftUnitorInv
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂RightUnitorHom /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂RightUnitorHom (f : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (ρ_ f).Hom
    where lift := (ρ_ (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f)).Hom
#align category_theory.bicategory.lift_hom₂_right_unitor_hom Mathlib.Tactic.BicategoryCoherence.liftHom₂RightUnitorHom
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂RightUnitorInv /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂RightUnitorInv (f : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (ρ_ f).inv
    where lift := (ρ_ (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f)).inv
#align category_theory.bicategory.lift_hom₂_right_unitor_inv Mathlib.Tactic.BicategoryCoherence.liftHom₂RightUnitorInv
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂AssociatorHom /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂AssociatorHom (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (α_ f g h).Hom
    where lift :=
    (α_ (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f)
        (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift g)
        (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift h)).Hom
#align category_theory.bicategory.lift_hom₂_associator_hom Mathlib.Tactic.BicategoryCoherence.liftHom₂AssociatorHom
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂AssociatorInv /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂AssociatorInv (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (α_ f g h).inv
    where lift :=
    (α_ (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f)
        (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift g)
        (Mathlib.Tactic.BicategoryCoherence.LiftHom.lift h)).inv
#align category_theory.bicategory.lift_hom₂_associator_inv Mathlib.Tactic.BicategoryCoherence.liftHom₂AssociatorInv
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂Comp /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂Comp {f g h : a ⟶ b}
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom h] (η : f ⟶ g) (θ : g ⟶ h)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom₂ η]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom₂ θ] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (η ≫ θ)
    where lift :=
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂.lift η ≫
      Mathlib.Tactic.BicategoryCoherence.LiftHom₂.lift θ
#align category_theory.bicategory.lift_hom₂_comp Mathlib.Tactic.BicategoryCoherence.liftHom₂Comp
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂WhiskerLeft /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂WhiskerLeft (f : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] {g h : b ⟶ c} (η : g ⟶ h)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom₂ η] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (f ◁ η)
    where lift :=
    Mathlib.Tactic.BicategoryCoherence.LiftHom.lift f ◁
      Mathlib.Tactic.BicategoryCoherence.LiftHom₂.lift η
#align category_theory.bicategory.lift_hom₂_whisker_left Mathlib.Tactic.BicategoryCoherence.liftHom₂WhiskerLeft
-/

#print Mathlib.Tactic.BicategoryCoherence.liftHom₂WhiskerRight /-
instance Mathlib.Tactic.BicategoryCoherence.liftHom₂WhiskerRight {f g : a ⟶ b} (η : f ⟶ g)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom₂ η] {h : b ⟶ c}
    [Mathlib.Tactic.BicategoryCoherence.LiftHom h] :
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂ (η ▷ h)
    where lift :=
    Mathlib.Tactic.BicategoryCoherence.LiftHom₂.lift η ▷
      Mathlib.Tactic.BicategoryCoherence.LiftHom.lift h
#align category_theory.bicategory.lift_hom₂_whisker_right Mathlib.Tactic.BicategoryCoherence.liftHom₂WhiskerRight
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`Hom] [] -/
/-- A typeclass carrying a choice of bicategorical structural isomorphism between two objects.
Used by the `⊗≫` bicategorical composition operator, and the `coherence` tactic.
-/
class Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence (f g : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] where
  Hom : f ⟶ g
  [IsIso : IsIso hom]
#align category_theory.bicategory.bicategorical_coherence Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence
-/

attribute [instance] bicategorical_coherence.is_iso

namespace BicategoricalCoherence

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.refl /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.refl (f : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f f :=
  ⟨𝟙 _⟩
#align category_theory.bicategory.bicategorical_coherence.refl Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.refl
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.whiskerLeft /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.whiskerLeft (f : a ⟶ b)
    (g h : b ⟶ c) [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence g h] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence (f ≫ g) (f ≫ h) :=
  ⟨f ◁ Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom g h⟩
#align category_theory.bicategory.bicategorical_coherence.whisker_left Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.whiskerLeft
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.whiskerRight /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.whiskerRight (f g : a ⟶ b)
    (h : b ⟶ c) [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f g] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence (f ≫ h) (g ≫ h) :=
  ⟨Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom f g ▷ h⟩
#align category_theory.bicategory.bicategorical_coherence.whisker_right Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.whiskerRight
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.tensorRight /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.tensorRight (f : a ⟶ b)
    (g : b ⟶ b) [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence (𝟙 b) g] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f (f ≫ g) :=
  ⟨(ρ_ f).inv ≫ f ◁ Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom (𝟙 b) g⟩
#align category_theory.bicategory.bicategorical_coherence.tensor_right Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.tensorRight
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.tensorRight' /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.tensorRight' (f : a ⟶ b)
    (g : b ⟶ b) [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence g (𝟙 b)] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence (f ≫ g) f :=
  ⟨f ◁ Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom g (𝟙 b) ≫ (ρ_ f).Hom⟩
#align category_theory.bicategory.bicategorical_coherence.tensor_right' Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.tensorRight'
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.left /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.left (f g : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f g] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence (𝟙 a ≫ f) g :=
  ⟨(λ_ f).Hom ≫ Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom f g⟩
#align category_theory.bicategory.bicategorical_coherence.left Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.left
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.left' /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.left' (f g : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f g] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f (𝟙 a ≫ g) :=
  ⟨Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom f g ≫ (λ_ g).inv⟩
#align category_theory.bicategory.bicategorical_coherence.left' Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.left'
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.right /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.right (f g : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f g] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence (f ≫ 𝟙 b) g :=
  ⟨(ρ_ f).Hom ≫ Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom f g⟩
#align category_theory.bicategory.bicategorical_coherence.right Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.right
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.right' /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.right' (f g : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f g] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f (g ≫ 𝟙 b) :=
  ⟨Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom f g ≫ (ρ_ g).inv⟩
#align category_theory.bicategory.bicategorical_coherence.right' Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.right'
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.assoc /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.assoc (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (i : a ⟶ d) [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom i]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence (f ≫ g ≫ h) i] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence ((f ≫ g) ≫ h) i :=
  ⟨(α_ f g h).Hom ≫ Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom (f ≫ g ≫ h) i⟩
#align category_theory.bicategory.bicategorical_coherence.assoc Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.assoc
-/

#print Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.assoc' /-
@[simps]
instance Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.assoc' (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (i : a ⟶ d) [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom i]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence i (f ≫ g ≫ h)] :
    Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence i ((f ≫ g) ≫ h) :=
  ⟨Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom i (f ≫ g ≫ h) ≫ (α_ f g h).inv⟩
#align category_theory.bicategory.bicategorical_coherence.assoc' Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.assoc'
-/

end BicategoricalCoherence

#print Mathlib.Tactic.BicategoryCoherence.bicategoricalIso /-
/-- Construct an isomorphism between two objects in a bicategorical category
out of unitors and associators. -/
def Mathlib.Tactic.BicategoryCoherence.bicategoricalIso (f g : a ⟶ b)
    [Mathlib.Tactic.BicategoryCoherence.LiftHom f] [Mathlib.Tactic.BicategoryCoherence.LiftHom g]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence f g] : f ≅ g :=
  asIso (Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom f g)
#align category_theory.bicategory.bicategorical_iso Mathlib.Tactic.BicategoryCoherence.bicategoricalIso
-/

#print Mathlib.Tactic.BicategoryCoherence.bicategoricalComp /-
/-- Compose two morphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def Mathlib.Tactic.BicategoryCoherence.bicategoricalComp {f g h i : a ⟶ b}
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence g h] (η : f ⟶ g) (θ : h ⟶ i) :
    f ⟶ i :=
  η ≫ Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom g h ≫ θ
#align category_theory.bicategory.bicategorical_comp Mathlib.Tactic.BicategoryCoherence.bicategoricalComp
-/

scoped[Bicategory] infixr:80 " ⊗≫ " => Mathlib.Tactic.BicategoryCoherence.bicategoricalComp

#print Mathlib.Tactic.BicategoryCoherence.bicategoricalIsoComp /-
-- type as \ot \gg
/-- Compose two isomorphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def Mathlib.Tactic.BicategoryCoherence.bicategoricalIsoComp {f g h i : a ⟶ b}
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h]
    [Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence g h] (η : f ≅ g) (θ : h ≅ i) :
    f ≅ i :=
  η ≪≫ asIso (Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom g h) ≪≫ θ
#align category_theory.bicategory.bicategorical_iso_comp Mathlib.Tactic.BicategoryCoherence.bicategoricalIsoComp
-/

scoped[Bicategory] infixr:80 " ≪⊗≫ " => Mathlib.Tactic.BicategoryCoherence.bicategoricalIsoComp

-- type as \ot \gg
example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {h' : a ⟶ d} (η : f' ⟶ f ≫ g ≫ h)
    (θ : (f ≫ g) ≫ h ⟶ h') : f' ⟶ h' :=
  η ⊗≫ θ

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `η ⊗≫ 𝟙 _`
example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} (η : f' ⟶ (f ≫ g) ≫ h) : f' ⟶ f ≫ g ≫ h :=
  η ⊗≫ 𝟙 _

#print Mathlib.Tactic.BicategoryCoherence.bicategoricalComp_refl /-
@[simp]
theorem Mathlib.Tactic.BicategoryCoherence.bicategoricalComp_refl {f g h : a ⟶ b} (η : f ⟶ g)
    (θ : g ⟶ h) : η ⊗≫ θ = η ≫ θ := by dsimp [bicategorical_comp]; simp
#align category_theory.bicategory.bicategorical_comp_refl Mathlib.Tactic.BicategoryCoherence.bicategoricalComp_refl
-/

end CategoryTheory.Bicategory

open CategoryTheory.Bicategory

namespace Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Coherence tactic for bicategories. -/ unsafe
  def
    bicategorical_coherence
    : tactic Unit
    :=
      focus1
        do
          let o ← get_options
            set_options <| o `class.instance_max_depth 128
            try sorry
            let q( $ ( lhs ) = $ ( rhs ) ) ← target
            to_expr
                `
                  `(
                    ( FreeBicategory.lift ( Prefunctor.id _ ) ) . zipWith
                        ( Mathlib.Tactic.BicategoryCoherence.LiftHom₂.lift $ ( lhs ) )
                      =
                      ( FreeBicategory.lift ( Prefunctor.id _ ) ) . zipWith
                        ( Mathlib.Tactic.BicategoryCoherence.LiftHom₂.lift $ ( rhs ) )
                    )
              >>=
              tactic.change
            congr
#align tactic.bicategorical_coherence tactic.bicategorical_coherence

namespace Bicategory

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
/-- Simp lemmas for rewriting a 2-morphism into a normal form. -/
unsafe def whisker_simps : tactic Unit :=
  sorry
#align tactic.bicategory.whisker_simps tactic.bicategory.whisker_simps

namespace Coherence

#print Mathlib.Tactic.BicategoryCoherence.assoc_liftHom₂ /-
-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_lift_hom₂]` only left associates
-- bicategorical structural morphisms.
/-- Auxiliary simp lemma for the `coherence` tactic:
this move brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
@[nolint unused_arguments]
theorem assoc_liftHom₂ {f g h i : a ⟶ b} [Mathlib.Tactic.BicategoryCoherence.LiftHom f]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom g] [Mathlib.Tactic.BicategoryCoherence.LiftHom h]
    (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i) [Mathlib.Tactic.BicategoryCoherence.LiftHom₂ η]
    [Mathlib.Tactic.BicategoryCoherence.LiftHom₂ θ] : η ≫ θ ≫ ι = (η ≫ θ) ≫ ι :=
  (Category.assoc _ _ _).symm
#align tactic.bicategory.coherence.assoc_lift_hom₂ Mathlib.Tactic.BicategoryCoherence.assoc_liftHom₂
-/

end Coherence

end Bicategory

end Tactic

