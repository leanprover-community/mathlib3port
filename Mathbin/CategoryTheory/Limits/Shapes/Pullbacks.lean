/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang

! This file was ported from Lean 3 source module category_theory.limits.shapes.pullbacks
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Pullbacks

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define a category `walking_cospan` (resp. `walking_span`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

We define `pullback f g` and `pushout f g` as limits and colimits of such functors.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/


noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe w v₁ v₂ v u u₂

attribute [local tidy] tactic.case_bash

#print CategoryTheory.Limits.WalkingCospan /-
/-- The type of objects for the diagram indexing a pullback, defined as a special case of
`wide_pullback_shape`.
-/
abbrev WalkingCospan : Type :=
  WidePullbackShape WalkingPair
#align category_theory.limits.walking_cospan CategoryTheory.Limits.WalkingCospan
-/

#print CategoryTheory.Limits.WalkingCospan.left /-
/-- The left point of the walking cospan. -/
@[match_pattern]
abbrev WalkingCospan.left : WalkingCospan :=
  some WalkingPair.left
#align category_theory.limits.walking_cospan.left CategoryTheory.Limits.WalkingCospan.left
-/

#print CategoryTheory.Limits.WalkingCospan.right /-
/-- The right point of the walking cospan. -/
@[match_pattern]
abbrev WalkingCospan.right : WalkingCospan :=
  some WalkingPair.right
#align category_theory.limits.walking_cospan.right CategoryTheory.Limits.WalkingCospan.right
-/

#print CategoryTheory.Limits.WalkingCospan.one /-
/-- The central point of the walking cospan. -/
@[match_pattern]
abbrev WalkingCospan.one : WalkingCospan :=
  none
#align category_theory.limits.walking_cospan.one CategoryTheory.Limits.WalkingCospan.one
-/

#print CategoryTheory.Limits.WalkingSpan /-
/-- The type of objects for the diagram indexing a pushout, defined as a special case of
`wide_pushout_shape`.
-/
abbrev WalkingSpan : Type :=
  WidePushoutShape WalkingPair
#align category_theory.limits.walking_span CategoryTheory.Limits.WalkingSpan
-/

#print CategoryTheory.Limits.WalkingSpan.left /-
/-- The left point of the walking span. -/
@[match_pattern]
abbrev WalkingSpan.left : WalkingSpan :=
  some WalkingPair.left
#align category_theory.limits.walking_span.left CategoryTheory.Limits.WalkingSpan.left
-/

#print CategoryTheory.Limits.WalkingSpan.right /-
/-- The right point of the walking span. -/
@[match_pattern]
abbrev WalkingSpan.right : WalkingSpan :=
  some WalkingPair.right
#align category_theory.limits.walking_span.right CategoryTheory.Limits.WalkingSpan.right
-/

#print CategoryTheory.Limits.WalkingSpan.zero /-
/-- The central point of the walking span. -/
@[match_pattern]
abbrev WalkingSpan.zero : WalkingSpan :=
  none
#align category_theory.limits.walking_span.zero CategoryTheory.Limits.WalkingSpan.zero
-/

namespace WalkingCospan

#print CategoryTheory.Limits.WalkingCospan.Hom /-
/-- The type of arrows for the diagram indexing a pullback. -/
abbrev Hom : WalkingCospan → WalkingCospan → Type :=
  WidePullbackShape.Hom
#align category_theory.limits.walking_cospan.hom CategoryTheory.Limits.WalkingCospan.Hom
-/

#print CategoryTheory.Limits.WalkingCospan.Hom.inl /-
/-- The left arrow of the walking cospan. -/
@[match_pattern]
abbrev Hom.inl : left ⟶ one :=
  WidePullbackShape.Hom.term _
#align category_theory.limits.walking_cospan.hom.inl CategoryTheory.Limits.WalkingCospan.Hom.inl
-/

#print CategoryTheory.Limits.WalkingCospan.Hom.inr /-
/-- The right arrow of the walking cospan. -/
@[match_pattern]
abbrev Hom.inr : right ⟶ one :=
  WidePullbackShape.Hom.term _
#align category_theory.limits.walking_cospan.hom.inr CategoryTheory.Limits.WalkingCospan.Hom.inr
-/

#print CategoryTheory.Limits.WalkingCospan.Hom.id /-
/-- The identity arrows of the walking cospan. -/
@[match_pattern]
abbrev Hom.id (X : WalkingCospan) : X ⟶ X :=
  WidePullbackShape.Hom.id X
#align category_theory.limits.walking_cospan.hom.id CategoryTheory.Limits.WalkingCospan.Hom.id
-/

instance (X Y : WalkingCospan) : Subsingleton (X ⟶ Y) := by tidy

end WalkingCospan

namespace WalkingSpan

#print CategoryTheory.Limits.WalkingSpan.Hom /-
/-- The type of arrows for the diagram indexing a pushout. -/
abbrev Hom : WalkingSpan → WalkingSpan → Type :=
  WidePushoutShape.Hom
#align category_theory.limits.walking_span.hom CategoryTheory.Limits.WalkingSpan.Hom
-/

#print CategoryTheory.Limits.WalkingSpan.Hom.fst /-
/-- The left arrow of the walking span. -/
@[match_pattern]
abbrev Hom.fst : zero ⟶ left :=
  WidePushoutShape.Hom.init _
#align category_theory.limits.walking_span.hom.fst CategoryTheory.Limits.WalkingSpan.Hom.fst
-/

#print CategoryTheory.Limits.WalkingSpan.Hom.snd /-
/-- The right arrow of the walking span. -/
@[match_pattern]
abbrev Hom.snd : zero ⟶ right :=
  WidePushoutShape.Hom.init _
#align category_theory.limits.walking_span.hom.snd CategoryTheory.Limits.WalkingSpan.Hom.snd
-/

#print CategoryTheory.Limits.WalkingSpan.Hom.id /-
/-- The identity arrows of the walking span. -/
@[match_pattern]
abbrev Hom.id (X : WalkingSpan) : X ⟶ X :=
  WidePushoutShape.Hom.id X
#align category_theory.limits.walking_span.hom.id CategoryTheory.Limits.WalkingSpan.Hom.id
-/

instance (X Y : WalkingSpan) : Subsingleton (X ⟶ Y) := by tidy

end WalkingSpan

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C]

/- warning: category_theory.limits.walking_cospan.ext -> CategoryTheory.Limits.WalkingCospan.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.walking_cospan.ext CategoryTheory.Limits.WalkingCospan.extₓ'. -/
/-- To construct an isomorphism of cones over the walking cospan,
it suffices to construct an isomorphism
of the cone points and check it commutes with the legs to `left` and `right`. -/
def WalkingCospan.ext {F : WalkingCospan ⥤ C} {s t : Cone F} (i : s.pt ≅ t.pt)
    (w₁ : s.π.app WalkingCospan.left = i.Hom ≫ t.π.app WalkingCospan.left)
    (w₂ : s.π.app WalkingCospan.right = i.Hom ≫ t.π.app WalkingCospan.right) : s ≅ t :=
  by
  apply cones.ext i
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.π.naturality walking_cospan.hom.inl
    dsimp at h₁
    simp only [category.id_comp] at h₁
    have h₂ := t.π.naturality walking_cospan.hom.inl
    dsimp at h₂
    simp only [category.id_comp] at h₂
    simp_rw [h₂, ← category.assoc, ← w₁, ← h₁]
  · exact w₁
  · exact w₂
#align category_theory.limits.walking_cospan.ext CategoryTheory.Limits.WalkingCospan.ext

/- warning: category_theory.limits.walking_span.ext -> CategoryTheory.Limits.WalkingSpan.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.walking_span.ext CategoryTheory.Limits.WalkingSpan.extₓ'. -/
/-- To construct an isomorphism of cocones over the walking span,
it suffices to construct an isomorphism
of the cocone points and check it commutes with the legs from `left` and `right`. -/
def WalkingSpan.ext {F : WalkingSpan ⥤ C} {s t : Cocone F} (i : s.pt ≅ t.pt)
    (w₁ : s.ι.app WalkingCospan.left ≫ i.Hom = t.ι.app WalkingCospan.left)
    (w₂ : s.ι.app WalkingCospan.right ≫ i.Hom = t.ι.app WalkingCospan.right) : s ≅ t :=
  by
  apply cocones.ext i
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.ι.naturality walking_span.hom.fst
    dsimp at h₁
    simp only [category.comp_id] at h₁
    have h₂ := t.ι.naturality walking_span.hom.fst
    dsimp at h₂
    simp only [category.comp_id] at h₂
    simp_rw [← h₁, category.assoc, w₁, h₂]
  · exact w₁
  · exact w₂
#align category_theory.limits.walking_span.ext CategoryTheory.Limits.WalkingSpan.ext

#print CategoryTheory.Limits.cospan /-
/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : WalkingCospan ⥤ C :=
  WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j =>
    WalkingPair.casesOn j f g
#align category_theory.limits.cospan CategoryTheory.Limits.cospan
-/

#print CategoryTheory.Limits.span /-
/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : WalkingSpan ⥤ C :=
  WidePushoutShape.wideSpan X (fun j => WalkingPair.casesOn j Y Z) fun j =>
    WalkingPair.casesOn j f g
#align category_theory.limits.span CategoryTheory.Limits.span
-/

/- warning: category_theory.limits.cospan_left -> CategoryTheory.Limits.cospan_left is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u2} C (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.left) X
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u2} C (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.left) X
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_left CategoryTheory.Limits.cospan_leftₓ'. -/
@[simp]
theorem cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.left = X :=
  rfl
#align category_theory.limits.cospan_left CategoryTheory.Limits.cospan_left

/- warning: category_theory.limits.span_left -> CategoryTheory.Limits.span_left is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u2} C (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.left) Y
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u2} C (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.left) Y
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_left CategoryTheory.Limits.span_leftₓ'. -/
@[simp]
theorem span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.left = Y :=
  rfl
#align category_theory.limits.span_left CategoryTheory.Limits.span_left

/- warning: category_theory.limits.cospan_right -> CategoryTheory.Limits.cospan_right is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u2} C (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.right) Y
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u2} C (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.right) Y
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_right CategoryTheory.Limits.cospan_rightₓ'. -/
@[simp]
theorem cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).obj WalkingCospan.right = Y :=
  rfl
#align category_theory.limits.cospan_right CategoryTheory.Limits.cospan_right

/- warning: category_theory.limits.span_right -> CategoryTheory.Limits.span_right is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u2} C (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.right) Z
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u2} C (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.right) Z
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_right CategoryTheory.Limits.span_rightₓ'. -/
@[simp]
theorem span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.right = Z :=
  rfl
#align category_theory.limits.span_right CategoryTheory.Limits.span_right

/- warning: category_theory.limits.cospan_one -> CategoryTheory.Limits.cospan_one is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u2} C (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.one) Z
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u2} C (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.one) Z
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_one CategoryTheory.Limits.cospan_oneₓ'. -/
@[simp]
theorem cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.one = Z :=
  rfl
#align category_theory.limits.cospan_one CategoryTheory.Limits.cospan_one

/- warning: category_theory.limits.span_zero -> CategoryTheory.Limits.span_zero is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u2} C (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.zero) X
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u2} C (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.zero) X
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_zero CategoryTheory.Limits.span_zeroₓ'. -/
@[simp]
theorem span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.zero = X :=
  rfl
#align category_theory.limits.span_zero CategoryTheory.Limits.span_zero

/- warning: category_theory.limits.cospan_map_inl -> CategoryTheory.Limits.cospan_map_inl is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.one)) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.left CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inl) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.one)) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.left CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inl) f
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_map_inl CategoryTheory.Limits.cospan_map_inlₓ'. -/
@[simp]
theorem cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inl = f :=
  rfl
#align category_theory.limits.cospan_map_inl CategoryTheory.Limits.cospan_map_inl

/- warning: category_theory.limits.span_map_fst -> CategoryTheory.Limits.span_map_fst is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.left)) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.left CategoryTheory.Limits.WalkingSpan.Hom.fst) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.left)) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.left CategoryTheory.Limits.WalkingSpan.Hom.fst) f
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_map_fst CategoryTheory.Limits.span_map_fstₓ'. -/
@[simp]
theorem span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.fst = f :=
  rfl
#align category_theory.limits.span_map_fst CategoryTheory.Limits.span_map_fst

/- warning: category_theory.limits.cospan_map_inr -> CategoryTheory.Limits.cospan_map_inr is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.right) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.one)) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.right CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inr) g
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.right) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.one)) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.right CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inr) g
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_map_inr CategoryTheory.Limits.cospan_map_inrₓ'. -/
@[simp]
theorem cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inr = g :=
  rfl
#align category_theory.limits.cospan_map_inr CategoryTheory.Limits.cospan_map_inr

/- warning: category_theory.limits.span_map_snd -> CategoryTheory.Limits.span_map_snd is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.right)) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.right CategoryTheory.Limits.WalkingSpan.Hom.snd) g
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.right)) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.right CategoryTheory.Limits.WalkingSpan.Hom.snd) g
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_map_snd CategoryTheory.Limits.span_map_sndₓ'. -/
@[simp]
theorem span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.snd = g :=
  rfl
#align category_theory.limits.span_map_snd CategoryTheory.Limits.span_map_snd

/- warning: category_theory.limits.cospan_map_id -> CategoryTheory.Limits.cospan_map_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z) (w : CategoryTheory.Limits.WalkingCospan), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) w) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) w)) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) w w (CategoryTheory.Limits.WalkingCospan.Hom.id w)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) w))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z) (w : CategoryTheory.Limits.WalkingCospan), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) w) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) w)) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) w w (CategoryTheory.Limits.WalkingCospan.Hom.id w)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) w))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_map_id CategoryTheory.Limits.cospan_map_idₓ'. -/
theorem cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan) :
    (cospan f g).map (WalkingCospan.Hom.id w) = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_map_id CategoryTheory.Limits.cospan_map_id

/- warning: category_theory.limits.span_map_id -> CategoryTheory.Limits.span_map_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (w : CategoryTheory.Limits.WalkingSpan), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) w) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) w)) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) w w (CategoryTheory.Limits.WalkingSpan.Hom.id w)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) w))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z) (w : CategoryTheory.Limits.WalkingSpan), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) w) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) w)) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) w w (CategoryTheory.Limits.WalkingSpan.Hom.id w)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) w))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_map_id CategoryTheory.Limits.span_map_idₓ'. -/
theorem span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan) :
    (span f g).map (WalkingSpan.Hom.id w) = 𝟙 _ :=
  rfl
#align category_theory.limits.span_map_id CategoryTheory.Limits.span_map_id

/- warning: category_theory.limits.diagram_iso_cospan -> CategoryTheory.Limits.diagramIsoCospan is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1), CategoryTheory.Iso.{u1, max u1 u2} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) F (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.right) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.one) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.left CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inl) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.right CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inr))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1), CategoryTheory.Iso.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) F (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.right) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.one) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.left CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inl) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.right CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inr))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.diagram_iso_cospan CategoryTheory.Limits.diagramIsoCospanₓ'. -/
/-- Every diagram indexing an pullback is naturally isomorphic (actually, equal) to a `cospan` -/
@[simps (config := { rhsMd := semireducible })]
def diagramIsoCospan (F : WalkingCospan ⥤ C) : F ≅ cospan (F.map inl) (F.map inr) :=
  NatIso.ofComponents (fun j => eqToIso (by tidy)) (by tidy)
#align category_theory.limits.diagram_iso_cospan CategoryTheory.Limits.diagramIsoCospan

/- warning: category_theory.limits.diagram_iso_span -> CategoryTheory.Limits.diagramIsoSpan is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1), CategoryTheory.Iso.{u1, max u1 u2} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) F (CategoryTheory.Limits.span.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.right) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.left CategoryTheory.Limits.WalkingSpan.Hom.fst) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.right CategoryTheory.Limits.WalkingSpan.Hom.snd))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1), CategoryTheory.Iso.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) F (CategoryTheory.Limits.span.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.right) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.left CategoryTheory.Limits.WalkingSpan.Hom.fst) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.right CategoryTheory.Limits.WalkingSpan.Hom.snd))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.diagram_iso_span CategoryTheory.Limits.diagramIsoSpanₓ'. -/
/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
@[simps (config := { rhsMd := semireducible })]
def diagramIsoSpan (F : WalkingSpan ⥤ C) : F ≅ span (F.map fst) (F.map snd) :=
  NatIso.ofComponents (fun j => eqToIso (by tidy)) (by tidy)
#align category_theory.limits.diagram_iso_span CategoryTheory.Limits.diagramIsoSpan

variable {D : Type u₂} [Category.{v₂} D]

/- warning: category_theory.limits.cospan_comp_iso -> CategoryTheory.Limits.cospanCompIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} D] (F : CategoryTheory.Functor.{u2, u1, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Z) (g : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Y Z), CategoryTheory.Iso.{u1, max u1 u4} (CategoryTheory.Functor.{0, u1, 0, u4} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) D _inst_2) (CategoryTheory.Functor.category.{0, u1, 0, u4} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) D _inst_2) (CategoryTheory.Functor.comp.{0, u2, u1, 0, u3, u4} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 D _inst_2 (CategoryTheory.Limits.cospan.{u2, u3} C _inst_1 X Y Z f g) F) (CategoryTheory.Limits.cospan.{u1, u4} D _inst_2 (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 F Z) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 F X Z f) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 F Y Z g))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} D] (F : CategoryTheory.Functor.{u2, u1, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Z) (g : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Y Z), CategoryTheory.Iso.{u1, max u4 u1} (CategoryTheory.Functor.{0, u1, 0, u4} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) D _inst_2) (CategoryTheory.Functor.category.{0, u1, 0, u4} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) D _inst_2) (CategoryTheory.Functor.comp.{0, u2, u1, 0, u3, u4} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 D _inst_2 (CategoryTheory.Limits.cospan.{u2, u3} C _inst_1 X Y Z f g) F) (CategoryTheory.Limits.cospan.{u1, u4} D _inst_2 (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) Z) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) X Z f) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) Y Z g))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso CategoryTheory.Limits.cospanCompIsoₓ'. -/
/-- A functor applied to a cospan is a cospan. -/
def cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨⟩ <;> repeat' dsimp; simp)
#align category_theory.limits.cospan_comp_iso CategoryTheory.Limits.cospanCompIso

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/- warning: category_theory.limits.cospan_comp_iso_app_left -> CategoryTheory.Limits.cospanCompIso_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_app_left CategoryTheory.Limits.cospanCompIso_app_leftₓ'. -/
@[simp]
theorem cospanCompIso_app_left : (cospanCompIso F f g).app WalkingCospan.left = Iso.refl _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_app_left CategoryTheory.Limits.cospanCompIso_app_left

/- warning: category_theory.limits.cospan_comp_iso_app_right -> CategoryTheory.Limits.cospanCompIso_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_app_right CategoryTheory.Limits.cospanCompIso_app_rightₓ'. -/
@[simp]
theorem cospanCompIso_app_right : (cospanCompIso F f g).app WalkingCospan.right = Iso.refl _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_app_right CategoryTheory.Limits.cospanCompIso_app_right

/- warning: category_theory.limits.cospan_comp_iso_app_one -> CategoryTheory.Limits.cospanCompIso_app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_app_one CategoryTheory.Limits.cospanCompIso_app_oneₓ'. -/
@[simp]
theorem cospanCompIso_app_one : (cospanCompIso F f g).app WalkingCospan.one = Iso.refl _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_app_one CategoryTheory.Limits.cospanCompIso_app_one

/- warning: category_theory.limits.cospan_comp_iso_hom_app_left -> CategoryTheory.Limits.cospanCompIso_hom_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_hom_app_left CategoryTheory.Limits.cospanCompIso_hom_app_leftₓ'. -/
@[simp]
theorem cospanCompIso_hom_app_left : (cospanCompIso F f g).Hom.app WalkingCospan.left = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_hom_app_left CategoryTheory.Limits.cospanCompIso_hom_app_left

/- warning: category_theory.limits.cospan_comp_iso_hom_app_right -> CategoryTheory.Limits.cospanCompIso_hom_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_hom_app_right CategoryTheory.Limits.cospanCompIso_hom_app_rightₓ'. -/
@[simp]
theorem cospanCompIso_hom_app_right : (cospanCompIso F f g).Hom.app WalkingCospan.right = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_hom_app_right CategoryTheory.Limits.cospanCompIso_hom_app_right

/- warning: category_theory.limits.cospan_comp_iso_hom_app_one -> CategoryTheory.Limits.cospanCompIso_hom_app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_hom_app_one CategoryTheory.Limits.cospanCompIso_hom_app_oneₓ'. -/
@[simp]
theorem cospanCompIso_hom_app_one : (cospanCompIso F f g).Hom.app WalkingCospan.one = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_hom_app_one CategoryTheory.Limits.cospanCompIso_hom_app_one

/- warning: category_theory.limits.cospan_comp_iso_inv_app_left -> CategoryTheory.Limits.cospanCompIso_inv_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_inv_app_left CategoryTheory.Limits.cospanCompIso_inv_app_leftₓ'. -/
@[simp]
theorem cospanCompIso_inv_app_left : (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_inv_app_left CategoryTheory.Limits.cospanCompIso_inv_app_left

/- warning: category_theory.limits.cospan_comp_iso_inv_app_right -> CategoryTheory.Limits.cospanCompIso_inv_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_inv_app_right CategoryTheory.Limits.cospanCompIso_inv_app_rightₓ'. -/
@[simp]
theorem cospanCompIso_inv_app_right : (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_inv_app_right CategoryTheory.Limits.cospanCompIso_inv_app_right

/- warning: category_theory.limits.cospan_comp_iso_inv_app_one -> CategoryTheory.Limits.cospanCompIso_inv_app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_comp_iso_inv_app_one CategoryTheory.Limits.cospanCompIso_inv_app_oneₓ'. -/
@[simp]
theorem cospanCompIso_inv_app_one : (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_inv_app_one CategoryTheory.Limits.cospanCompIso_inv_app_one

end

/- warning: category_theory.limits.span_comp_iso -> CategoryTheory.Limits.spanCompIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} D] (F : CategoryTheory.Functor.{u2, u1, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Z), CategoryTheory.Iso.{u1, max u1 u4} (CategoryTheory.Functor.{0, u1, 0, u4} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) D _inst_2) (CategoryTheory.Functor.category.{0, u1, 0, u4} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) D _inst_2) (CategoryTheory.Functor.comp.{0, u2, u1, 0, u3, u4} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 D _inst_2 (CategoryTheory.Limits.span.{u2, u3} C _inst_1 X Y Z f g) F) (CategoryTheory.Limits.span.{u1, u4} D _inst_2 (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 F Z) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 F X Y f) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 F X Z g))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} D] (F : CategoryTheory.Functor.{u2, u1, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Z), CategoryTheory.Iso.{u1, max u4 u1} (CategoryTheory.Functor.{0, u1, 0, u4} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) D _inst_2) (CategoryTheory.Functor.category.{0, u1, 0, u4} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) D _inst_2) (CategoryTheory.Functor.comp.{0, u2, u1, 0, u3, u4} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 D _inst_2 (CategoryTheory.Limits.span.{u2, u3} C _inst_1 X Y Z f g) F) (CategoryTheory.Limits.span.{u1, u4} D _inst_2 (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) Z) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) X Y f) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 F) X Z g))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso CategoryTheory.Limits.spanCompIsoₓ'. -/
/-- A functor applied to a span is a span. -/
def spanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    span f g ⋙ F ≅ span (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨⟩ <;> repeat' dsimp; simp)
#align category_theory.limits.span_comp_iso CategoryTheory.Limits.spanCompIso

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

/- warning: category_theory.limits.span_comp_iso_app_left -> CategoryTheory.Limits.spanCompIso_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_app_left CategoryTheory.Limits.spanCompIso_app_leftₓ'. -/
@[simp]
theorem spanCompIso_app_left : (spanCompIso F f g).app WalkingSpan.left = Iso.refl _ :=
  rfl
#align category_theory.limits.span_comp_iso_app_left CategoryTheory.Limits.spanCompIso_app_left

/- warning: category_theory.limits.span_comp_iso_app_right -> CategoryTheory.Limits.spanCompIso_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_app_right CategoryTheory.Limits.spanCompIso_app_rightₓ'. -/
@[simp]
theorem spanCompIso_app_right : (spanCompIso F f g).app WalkingSpan.right = Iso.refl _ :=
  rfl
#align category_theory.limits.span_comp_iso_app_right CategoryTheory.Limits.spanCompIso_app_right

/- warning: category_theory.limits.span_comp_iso_app_zero -> CategoryTheory.Limits.spanCompIso_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_app_zero CategoryTheory.Limits.spanCompIso_app_zeroₓ'. -/
@[simp]
theorem spanCompIso_app_zero : (spanCompIso F f g).app WalkingSpan.zero = Iso.refl _ :=
  rfl
#align category_theory.limits.span_comp_iso_app_zero CategoryTheory.Limits.spanCompIso_app_zero

/- warning: category_theory.limits.span_comp_iso_hom_app_left -> CategoryTheory.Limits.spanCompIso_hom_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_hom_app_left CategoryTheory.Limits.spanCompIso_hom_app_leftₓ'. -/
@[simp]
theorem spanCompIso_hom_app_left : (spanCompIso F f g).Hom.app WalkingSpan.left = 𝟙 _ :=
  rfl
#align category_theory.limits.span_comp_iso_hom_app_left CategoryTheory.Limits.spanCompIso_hom_app_left

/- warning: category_theory.limits.span_comp_iso_hom_app_right -> CategoryTheory.Limits.spanCompIso_hom_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_hom_app_right CategoryTheory.Limits.spanCompIso_hom_app_rightₓ'. -/
@[simp]
theorem spanCompIso_hom_app_right : (spanCompIso F f g).Hom.app WalkingSpan.right = 𝟙 _ :=
  rfl
#align category_theory.limits.span_comp_iso_hom_app_right CategoryTheory.Limits.spanCompIso_hom_app_right

/- warning: category_theory.limits.span_comp_iso_hom_app_zero -> CategoryTheory.Limits.spanCompIso_hom_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_hom_app_zero CategoryTheory.Limits.spanCompIso_hom_app_zeroₓ'. -/
@[simp]
theorem spanCompIso_hom_app_zero : (spanCompIso F f g).Hom.app WalkingSpan.zero = 𝟙 _ :=
  rfl
#align category_theory.limits.span_comp_iso_hom_app_zero CategoryTheory.Limits.spanCompIso_hom_app_zero

/- warning: category_theory.limits.span_comp_iso_inv_app_left -> CategoryTheory.Limits.spanCompIso_inv_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_inv_app_left CategoryTheory.Limits.spanCompIso_inv_app_leftₓ'. -/
@[simp]
theorem spanCompIso_inv_app_left : (spanCompIso F f g).inv.app WalkingSpan.left = 𝟙 _ :=
  rfl
#align category_theory.limits.span_comp_iso_inv_app_left CategoryTheory.Limits.spanCompIso_inv_app_left

/- warning: category_theory.limits.span_comp_iso_inv_app_right -> CategoryTheory.Limits.spanCompIso_inv_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_inv_app_right CategoryTheory.Limits.spanCompIso_inv_app_rightₓ'. -/
@[simp]
theorem spanCompIso_inv_app_right : (spanCompIso F f g).inv.app WalkingSpan.right = 𝟙 _ :=
  rfl
#align category_theory.limits.span_comp_iso_inv_app_right CategoryTheory.Limits.spanCompIso_inv_app_right

/- warning: category_theory.limits.span_comp_iso_inv_app_zero -> CategoryTheory.Limits.spanCompIso_inv_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_comp_iso_inv_app_zero CategoryTheory.Limits.spanCompIso_inv_app_zeroₓ'. -/
@[simp]
theorem spanCompIso_inv_app_zero : (spanCompIso F f g).inv.app WalkingSpan.zero = 𝟙 _ :=
  rfl
#align category_theory.limits.span_comp_iso_inv_app_zero CategoryTheory.Limits.spanCompIso_inv_app_zero

end

section

variable {X Y Z X' Y' Z' : C} (iX : X ≅ X') (iY : Y ≅ Y') (iZ : Z ≅ Z')

section

variable {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

#print CategoryTheory.Limits.cospanExt /-
/-- Construct an isomorphism of cospans from components. -/
def cospanExt (wf : iX.Hom ≫ f' = f ≫ iZ.Hom) (wg : iY.Hom ≫ g' = g ≫ iZ.Hom) :
    cospan f g ≅ cospan f' g' :=
  NatIso.ofComponents
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩)
      exacts[iZ, iX, iY])
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨⟩ <;> repeat' dsimp; simp [wf, wg])
#align category_theory.limits.cospan_ext CategoryTheory.Limits.cospanExt
-/

variable (wf : iX.Hom ≫ f' = f ≫ iZ.Hom) (wg : iY.Hom ≫ g' = g ≫ iZ.Hom)

/- warning: category_theory.limits.cospan_ext_app_left -> CategoryTheory.Limits.cospanExt_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_app_left CategoryTheory.Limits.cospanExt_app_leftₓ'. -/
@[simp]
theorem cospanExt_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_app_left CategoryTheory.Limits.cospanExt_app_left

/- warning: category_theory.limits.cospan_ext_app_right -> CategoryTheory.Limits.cospanExt_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_app_right CategoryTheory.Limits.cospanExt_app_rightₓ'. -/
@[simp]
theorem cospanExt_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_app_right CategoryTheory.Limits.cospanExt_app_right

/- warning: category_theory.limits.cospan_ext_app_one -> CategoryTheory.Limits.cospanExt_app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_app_one CategoryTheory.Limits.cospanExt_app_oneₓ'. -/
@[simp]
theorem cospanExt_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_app_one CategoryTheory.Limits.cospanExt_app_one

/- warning: category_theory.limits.cospan_ext_hom_app_left -> CategoryTheory.Limits.cospanExt_hom_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_hom_app_left CategoryTheory.Limits.cospanExt_hom_app_leftₓ'. -/
@[simp]
theorem cospanExt_hom_app_left : (cospanExt iX iY iZ wf wg).Hom.app WalkingCospan.left = iX.Hom :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_hom_app_left CategoryTheory.Limits.cospanExt_hom_app_left

/- warning: category_theory.limits.cospan_ext_hom_app_right -> CategoryTheory.Limits.cospanExt_hom_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_hom_app_right CategoryTheory.Limits.cospanExt_hom_app_rightₓ'. -/
@[simp]
theorem cospanExt_hom_app_right : (cospanExt iX iY iZ wf wg).Hom.app WalkingCospan.right = iY.Hom :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_hom_app_right CategoryTheory.Limits.cospanExt_hom_app_right

/- warning: category_theory.limits.cospan_ext_hom_app_one -> CategoryTheory.Limits.cospanExt_hom_app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_hom_app_one CategoryTheory.Limits.cospanExt_hom_app_oneₓ'. -/
@[simp]
theorem cospanExt_hom_app_one : (cospanExt iX iY iZ wf wg).Hom.app WalkingCospan.one = iZ.Hom :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_hom_app_one CategoryTheory.Limits.cospanExt_hom_app_one

/- warning: category_theory.limits.cospan_ext_inv_app_left -> CategoryTheory.Limits.cospanExt_inv_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_inv_app_left CategoryTheory.Limits.cospanExt_inv_app_leftₓ'. -/
@[simp]
theorem cospanExt_inv_app_left : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.left = iX.inv :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_inv_app_left CategoryTheory.Limits.cospanExt_inv_app_left

/- warning: category_theory.limits.cospan_ext_inv_app_right -> CategoryTheory.Limits.cospanExt_inv_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_inv_app_right CategoryTheory.Limits.cospanExt_inv_app_rightₓ'. -/
@[simp]
theorem cospanExt_inv_app_right : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.right = iY.inv :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_inv_app_right CategoryTheory.Limits.cospanExt_inv_app_right

/- warning: category_theory.limits.cospan_ext_inv_app_one -> CategoryTheory.Limits.cospanExt_inv_app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cospan_ext_inv_app_one CategoryTheory.Limits.cospanExt_inv_app_oneₓ'. -/
@[simp]
theorem cospanExt_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv :=
  by
  dsimp [cospan_ext]
  simp
#align category_theory.limits.cospan_ext_inv_app_one CategoryTheory.Limits.cospanExt_inv_app_one

end

section

variable {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

#print CategoryTheory.Limits.spanExt /-
/-- Construct an isomorphism of spans from components. -/
def spanExt (wf : iX.Hom ≫ f' = f ≫ iY.Hom) (wg : iX.Hom ≫ g' = g ≫ iZ.Hom) :
    span f g ≅ span f' g' :=
  NatIso.ofComponents
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩)
      exacts[iX, iY, iZ])
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨⟩ <;> repeat' dsimp; simp [wf, wg])
#align category_theory.limits.span_ext CategoryTheory.Limits.spanExt
-/

variable (wf : iX.Hom ≫ f' = f ≫ iY.Hom) (wg : iX.Hom ≫ g' = g ≫ iZ.Hom)

/- warning: category_theory.limits.span_ext_app_left -> CategoryTheory.Limits.spanExt_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_app_left CategoryTheory.Limits.spanExt_app_leftₓ'. -/
@[simp]
theorem spanExt_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_app_left CategoryTheory.Limits.spanExt_app_left

/- warning: category_theory.limits.span_ext_app_right -> CategoryTheory.Limits.spanExt_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_app_right CategoryTheory.Limits.spanExt_app_rightₓ'. -/
@[simp]
theorem spanExt_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_app_right CategoryTheory.Limits.spanExt_app_right

/- warning: category_theory.limits.span_ext_app_one -> CategoryTheory.Limits.spanExt_app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_app_one CategoryTheory.Limits.spanExt_app_oneₓ'. -/
@[simp]
theorem spanExt_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_app_one CategoryTheory.Limits.spanExt_app_one

/- warning: category_theory.limits.span_ext_hom_app_left -> CategoryTheory.Limits.spanExt_hom_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_hom_app_left CategoryTheory.Limits.spanExt_hom_app_leftₓ'. -/
@[simp]
theorem spanExt_hom_app_left : (spanExt iX iY iZ wf wg).Hom.app WalkingSpan.left = iY.Hom :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_hom_app_left CategoryTheory.Limits.spanExt_hom_app_left

/- warning: category_theory.limits.span_ext_hom_app_right -> CategoryTheory.Limits.spanExt_hom_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_hom_app_right CategoryTheory.Limits.spanExt_hom_app_rightₓ'. -/
@[simp]
theorem spanExt_hom_app_right : (spanExt iX iY iZ wf wg).Hom.app WalkingSpan.right = iZ.Hom :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_hom_app_right CategoryTheory.Limits.spanExt_hom_app_right

/- warning: category_theory.limits.span_ext_hom_app_zero -> CategoryTheory.Limits.spanExt_hom_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_hom_app_zero CategoryTheory.Limits.spanExt_hom_app_zeroₓ'. -/
@[simp]
theorem spanExt_hom_app_zero : (spanExt iX iY iZ wf wg).Hom.app WalkingSpan.zero = iX.Hom :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_hom_app_zero CategoryTheory.Limits.spanExt_hom_app_zero

/- warning: category_theory.limits.span_ext_inv_app_left -> CategoryTheory.Limits.spanExt_inv_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_inv_app_left CategoryTheory.Limits.spanExt_inv_app_leftₓ'. -/
@[simp]
theorem spanExt_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_inv_app_left CategoryTheory.Limits.spanExt_inv_app_left

/- warning: category_theory.limits.span_ext_inv_app_right -> CategoryTheory.Limits.spanExt_inv_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_inv_app_right CategoryTheory.Limits.spanExt_inv_app_rightₓ'. -/
@[simp]
theorem spanExt_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_inv_app_right CategoryTheory.Limits.spanExt_inv_app_right

/- warning: category_theory.limits.span_ext_inv_app_zero -> CategoryTheory.Limits.spanExt_inv_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.span_ext_inv_app_zero CategoryTheory.Limits.spanExt_inv_app_zeroₓ'. -/
@[simp]
theorem spanExt_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv :=
  by
  dsimp [span_ext]
  simp
#align category_theory.limits.span_ext_inv_app_zero CategoryTheory.Limits.spanExt_inv_app_zero

end

end

variable {W X Y Z : C}

#print CategoryTheory.Limits.PullbackCone /-
/-- A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z` and
    `g : Y ⟶ Z`.-/
abbrev PullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :=
  Cone (cospan f g)
#align category_theory.limits.pullback_cone CategoryTheory.Limits.PullbackCone
-/

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

#print CategoryTheory.Limits.PullbackCone.fst /-
/-- The first projection of a pullback cone. -/
abbrev fst (t : PullbackCone f g) : t.pt ⟶ X :=
  t.π.app WalkingCospan.left
#align category_theory.limits.pullback_cone.fst CategoryTheory.Limits.PullbackCone.fst
-/

#print CategoryTheory.Limits.PullbackCone.snd /-
/-- The second projection of a pullback cone. -/
abbrev snd (t : PullbackCone f g) : t.pt ⟶ Y :=
  t.π.app WalkingCospan.right
#align category_theory.limits.pullback_cone.snd CategoryTheory.Limits.PullbackCone.snd
-/

/- warning: category_theory.limits.pullback_cone.π_app_left -> CategoryTheory.Limits.PullbackCone.π_app_left is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z} (c : CategoryTheory.Limits.PullbackCone.{u1, u2} C _inst_1 X Y Z f g), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c)) CategoryTheory.Limits.WalkingCospan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.left)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c)) (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) (CategoryTheory.Limits.Cone.π.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c) CategoryTheory.Limits.WalkingCospan.left) (CategoryTheory.Limits.PullbackCone.fst.{u1, u2} C _inst_1 X Y Z f g c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z} (c : CategoryTheory.Limits.PullbackCone.{u1, u2} C _inst_1 X Y Z f g), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c))) CategoryTheory.Limits.WalkingCospan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.left)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c)) (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) (CategoryTheory.Limits.Cone.π.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c) CategoryTheory.Limits.WalkingCospan.left) (CategoryTheory.Limits.PullbackCone.fst.{u1, u2} C _inst_1 X Y Z f g c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.π_app_left CategoryTheory.Limits.PullbackCone.π_app_leftₓ'. -/
@[simp]
theorem π_app_left (c : PullbackCone f g) : c.π.app WalkingCospan.left = c.fst :=
  rfl
#align category_theory.limits.pullback_cone.π_app_left CategoryTheory.Limits.PullbackCone.π_app_left

/- warning: category_theory.limits.pullback_cone.π_app_right -> CategoryTheory.Limits.PullbackCone.π_app_right is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z} (c : CategoryTheory.Limits.PullbackCone.{u1, u2} C _inst_1 X Y Z f g), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c)) CategoryTheory.Limits.WalkingCospan.right) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingCospan.right)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c)) (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) (CategoryTheory.Limits.Cone.π.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c) CategoryTheory.Limits.WalkingCospan.right) (CategoryTheory.Limits.PullbackCone.snd.{u1, u2} C _inst_1 X Y Z f g c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z} (c : CategoryTheory.Limits.PullbackCone.{u1, u2} C _inst_1 X Y Z f g), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c))) CategoryTheory.Limits.WalkingCospan.right) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingCospan.right)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c)) (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) (CategoryTheory.Limits.Cone.π.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.cospan.{u1, u2} C _inst_1 X Y Z f g) c) CategoryTheory.Limits.WalkingCospan.right) (CategoryTheory.Limits.PullbackCone.snd.{u1, u2} C _inst_1 X Y Z f g c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.π_app_right CategoryTheory.Limits.PullbackCone.π_app_rightₓ'. -/
@[simp]
theorem π_app_right (c : PullbackCone f g) : c.π.app WalkingCospan.right = c.snd :=
  rfl
#align category_theory.limits.pullback_cone.π_app_right CategoryTheory.Limits.PullbackCone.π_app_right

/- warning: category_theory.limits.pullback_cone.condition_one -> CategoryTheory.Limits.PullbackCone.condition_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.condition_one CategoryTheory.Limits.PullbackCone.condition_oneₓ'. -/
@[simp]
theorem condition_one (t : PullbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫ f :=
  by
  have w := t.π.naturality walking_cospan.hom.inl
  dsimp at w; simpa using w
#align category_theory.limits.pullback_cone.condition_one CategoryTheory.Limits.PullbackCone.condition_one

/- warning: category_theory.limits.pullback_cone.is_limit_aux -> CategoryTheory.Limits.PullbackCone.isLimitAux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.is_limit_aux CategoryTheory.Limits.PullbackCone.isLimitAuxₓ'. -/
/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def isLimitAux (t : PullbackCone f g) (lift : ∀ s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ t.snd = s.snd)
    (uniq :
      ∀ (s : PullbackCone f g) (m : s.pt ⟶ t.pt)
        (w : ∀ j : WalkingCospan, m ≫ t.π.app j = s.π.app j), m = lift s) :
    IsLimit t :=
  { lift
    fac := fun s j =>
      Option.casesOn j
        (by
          rw [← s.w inl, ← t.w inl, ← category.assoc]
          congr
          exact fac_left s)
        fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }
#align category_theory.limits.pullback_cone.is_limit_aux CategoryTheory.Limits.PullbackCone.isLimitAux

#print CategoryTheory.Limits.PullbackCone.isLimitAux' /-
/-- This is another convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def isLimitAux' (t : PullbackCone f g)
    (create :
      ∀ s : PullbackCone f g,
        { l //
          l ≫ t.fst = s.fst ∧
            l ≫ t.snd = s.snd ∧ ∀ {m}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l }) :
    Limits.IsLimit t :=
  PullbackCone.isLimitAux t (fun s => (create s).1) (fun s => (create s).2.1)
    (fun s => (create s).2.2.1) fun s m w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)
#align category_theory.limits.pullback_cone.is_limit_aux' CategoryTheory.Limits.PullbackCone.isLimitAux'
-/

#print CategoryTheory.Limits.PullbackCone.mk /-
/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
    such that `fst ≫ f = snd ≫ g`. -/
@[simps]
def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : PullbackCone f g
    where
  pt := W
  π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd }
#align category_theory.limits.pullback_cone.mk CategoryTheory.Limits.PullbackCone.mk
-/

/- warning: category_theory.limits.pullback_cone.mk_π_app_left -> CategoryTheory.Limits.PullbackCone.mk_π_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.mk_π_app_left CategoryTheory.Limits.PullbackCone.mk_π_app_leftₓ'. -/
@[simp]
theorem mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd Eq).π.app WalkingCospan.left = fst :=
  rfl
#align category_theory.limits.pullback_cone.mk_π_app_left CategoryTheory.Limits.PullbackCone.mk_π_app_left

/- warning: category_theory.limits.pullback_cone.mk_π_app_right -> CategoryTheory.Limits.PullbackCone.mk_π_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.mk_π_app_right CategoryTheory.Limits.PullbackCone.mk_π_app_rightₓ'. -/
@[simp]
theorem mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd Eq).π.app WalkingCospan.right = snd :=
  rfl
#align category_theory.limits.pullback_cone.mk_π_app_right CategoryTheory.Limits.PullbackCone.mk_π_app_right

/- warning: category_theory.limits.pullback_cone.mk_π_app_one -> CategoryTheory.Limits.PullbackCone.mk_π_app_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.mk_π_app_one CategoryTheory.Limits.PullbackCone.mk_π_app_oneₓ'. -/
@[simp]
theorem mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd Eq).π.app WalkingCospan.one = fst ≫ f :=
  rfl
#align category_theory.limits.pullback_cone.mk_π_app_one CategoryTheory.Limits.PullbackCone.mk_π_app_one

#print CategoryTheory.Limits.PullbackCone.mk_fst /-
@[simp]
theorem mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd Eq).fst = fst :=
  rfl
#align category_theory.limits.pullback_cone.mk_fst CategoryTheory.Limits.PullbackCone.mk_fst
-/

#print CategoryTheory.Limits.PullbackCone.mk_snd /-
@[simp]
theorem mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd Eq).snd = snd :=
  rfl
#align category_theory.limits.pullback_cone.mk_snd CategoryTheory.Limits.PullbackCone.mk_snd
-/

#print CategoryTheory.Limits.PullbackCone.condition /-
@[reassoc]
theorem condition (t : PullbackCone f g) : fst t ≫ f = snd t ≫ g :=
  (t.w inl).trans (t.w inr).symm
#align category_theory.limits.pullback_cone.condition CategoryTheory.Limits.PullbackCone.condition
-/

/- warning: category_theory.limits.pullback_cone.equalizer_ext -> CategoryTheory.Limits.PullbackCone.equalizer_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.equalizer_ext CategoryTheory.Limits.PullbackCone.equalizer_extₓ'. -/
/-- To check whether a morphism is equalized by the maps of a pullback cone, it suffices to check
  it for `fst t` and `snd t` -/
theorem equalizer_ext (t : PullbackCone f g) {W : C} {k l : W ⟶ t.pt} (h₀ : k ≫ fst t = l ≫ fst t)
    (h₁ : k ≫ snd t = l ≫ snd t) : ∀ j : WalkingCospan, k ≫ t.π.app j = l ≫ t.π.app j
  | some walking_pair.left => h₀
  | some walking_pair.right => h₁
  | none => by rw [← t.w inl, reassoc_of h₀]
#align category_theory.limits.pullback_cone.equalizer_ext CategoryTheory.Limits.PullbackCone.equalizer_ext

#print CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext /-
theorem IsLimit.hom_ext {t : PullbackCone f g} (ht : IsLimit t) {W : C} {k l : W ⟶ t.pt}
    (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
  ht.hom_ext <| equalizer_ext _ h₀ h₁
#align category_theory.limits.pullback_cone.is_limit.hom_ext CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext
-/

#print CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono /-
theorem mono_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono f] :
    Mono t.snd :=
  ⟨fun W h k i => IsLimit.hom_ext ht (by simp [← cancel_mono f, t.condition, reassoc_of i]) i⟩
#align category_theory.limits.pullback_cone.mono_snd_of_is_pullback_of_mono CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono
-/

#print CategoryTheory.Limits.PullbackCone.mono_fst_of_is_pullback_of_mono /-
theorem mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] :
    Mono t.fst :=
  ⟨fun W h k i => IsLimit.hom_ext ht i (by simp [← cancel_mono g, ← t.condition, reassoc_of i])⟩
#align category_theory.limits.pullback_cone.mono_fst_of_is_pullback_of_mono CategoryTheory.Limits.PullbackCone.mono_fst_of_is_pullback_of_mono
-/

#print CategoryTheory.Limits.PullbackCone.ext /-
/-- To construct an isomorphism of pullback cones, it suffices to construct an isomorphism
of the cone points and check it commutes with `fst` and `snd`. -/
def ext {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.Hom ≫ t.fst)
    (w₂ : s.snd = i.Hom ≫ t.snd) : s ≅ t :=
  WalkingCospan.ext i w₁ w₂
#align category_theory.limits.pullback_cone.ext CategoryTheory.Limits.PullbackCone.ext
-/

#print CategoryTheory.Limits.PullbackCone.IsLimit.lift' /-
/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
    `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.X` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
    -/
def IsLimit.lift' {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : { l : W ⟶ t.pt // l ≫ fst t = h ∧ l ≫ snd t = k } :=
  ⟨ht.lift <| PullbackCone.mk _ _ w, ht.fac _ _, ht.fac _ _⟩
#align category_theory.limits.pullback_cone.is_limit.lift' CategoryTheory.Limits.PullbackCone.IsLimit.lift'
-/

#print CategoryTheory.Limits.PullbackCone.IsLimit.mk /-
/-- This is a more convenient formulation to show that a `pullback_cone` constructed using
`pullback_cone.mk` is a limit cone.
-/
def IsLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : PullbackCone f g) (m : s.pt ⟶ W) (w_fst : m ≫ fst = s.fst) (w_snd : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (mk fst snd Eq) :=
  isLimitAux _ lift fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)
#align category_theory.limits.pullback_cone.is_limit.mk CategoryTheory.Limits.PullbackCone.IsLimit.mk
-/

#print CategoryTheory.Limits.PullbackCone.flipIsLimit /-
/-- The flip of a pullback square is a pullback square. -/
def flipIsLimit {W : C} {h : W ⟶ X} {k : W ⟶ Y} {comm : h ≫ f = k ≫ g}
    (t : IsLimit (mk _ _ comm.symm)) : IsLimit (mk _ _ comm) :=
  isLimitAux' _ fun s =>
    by
    refine'
      ⟨(is_limit.lift' t _ _ s.condition.symm).1, (is_limit.lift' t _ _ _).2.2,
        (is_limit.lift' t _ _ _).2.1, fun m m₁ m₂ => t.hom_ext _⟩
    apply (mk k h _).equalizer_ext
    · rwa [(is_limit.lift' t _ _ _).2.1]
    · rwa [(is_limit.lift' t _ _ _).2.2]
#align category_theory.limits.pullback_cone.flip_is_limit CategoryTheory.Limits.PullbackCone.flipIsLimit
-/

#print CategoryTheory.Limits.PullbackCone.isLimitMkIdId /-
/--
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
def isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f) :=
  IsLimit.mk _ (fun s => s.fst) (fun s => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, category.comp_id, s.condition]) fun s m m₁ m₂ => by
    simpa using m₁
#align category_theory.limits.pullback_cone.is_limit_mk_id_id CategoryTheory.Limits.PullbackCone.isLimitMkIdId
-/

#print CategoryTheory.Limits.PullbackCone.mono_of_isLimitMkIdId /-
/--
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `pullback_cone.is_id_of_mono`.
-/
theorem mono_of_isLimitMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) :
    Mono f :=
  ⟨fun Z g h eq => by
    rcases pullback_cone.is_limit.lift' t _ _ Eq with ⟨_, rfl, rfl⟩
    rfl⟩
#align category_theory.limits.pullback_cone.mono_of_is_limit_mk_id_id CategoryTheory.Limits.PullbackCone.mono_of_isLimitMkIdId
-/

#print CategoryTheory.Limits.PullbackCone.isLimitOfFactors /-
/-- Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit cone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomorphism `h` via
    `x` and `y`, respectively.  Then `s` is also a limit cone over the diagram formed by `x` and
    `y`.  -/
def isLimitOfFactors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W)
    (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : PullbackCone f g) (hs : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ x = s.snd ≫ y from
          (cancel_mono h).1 <| by simp only [category.assoc, hxh, hyh, s.condition])) :=
  PullbackCone.isLimitAux' _ fun t =>
    ⟨hs.lift (PullbackCone.mk t.fst t.snd <| by rw [← hxh, ← hyh, reassoc_of t.condition]),
      ⟨hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right, fun r hr hr' =>
        by
        apply pullback_cone.is_limit.hom_ext hs <;>
              simp only [pullback_cone.mk_fst, pullback_cone.mk_snd] at hr hr'⊢ <;>
            simp only [hr, hr'] <;>
          symm
        exacts[hs.fac _ walking_cospan.left, hs.fac _ walking_cospan.right]⟩⟩
#align category_theory.limits.pullback_cone.is_limit_of_factors CategoryTheory.Limits.PullbackCone.isLimitOfFactors
-/

#print CategoryTheory.Limits.PullbackCone.isLimitOfCompMono /-
/-- If `W` is the pullback of `f, g`,
it is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
def isLimitOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g)
    (H : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ f ≫ i = s.snd ≫ g ≫ i by
          rw [← category.assoc, ← category.assoc, s.condition])) :=
  by
  apply pullback_cone.is_limit_aux'
  intro s
  rcases pullback_cone.is_limit.lift' H s.fst s.snd
      ((cancel_mono i).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine' ⟨l, h₁, h₂, _⟩
  intro m hm₁ hm₂
  exact (pullback_cone.is_limit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)
#align category_theory.limits.pullback_cone.is_limit_of_comp_mono CategoryTheory.Limits.PullbackCone.isLimitOfCompMono
-/

end PullbackCone

#print CategoryTheory.Limits.PushoutCocone /-
/-- A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y` and
    `g : X ⟶ Z`.-/
abbrev PushoutCocone (f : X ⟶ Y) (g : X ⟶ Z) :=
  Cocone (span f g)
#align category_theory.limits.pushout_cocone CategoryTheory.Limits.PushoutCocone
-/

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

#print CategoryTheory.Limits.PushoutCocone.inl /-
/-- The first inclusion of a pushout cocone. -/
abbrev inl (t : PushoutCocone f g) : Y ⟶ t.pt :=
  t.ι.app WalkingSpan.left
#align category_theory.limits.pushout_cocone.inl CategoryTheory.Limits.PushoutCocone.inl
-/

#print CategoryTheory.Limits.PushoutCocone.inr /-
/-- The second inclusion of a pushout cocone. -/
abbrev inr (t : PushoutCocone f g) : Z ⟶ t.pt :=
  t.ι.app WalkingSpan.right
#align category_theory.limits.pushout_cocone.inr CategoryTheory.Limits.PushoutCocone.inr
-/

/- warning: category_theory.limits.pushout_cocone.ι_app_left -> CategoryTheory.Limits.PushoutCocone.ι_app_left is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z} (c : CategoryTheory.Limits.PushoutCocone.{u1, u2} C _inst_1 X Y Z f g), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c)) CategoryTheory.Limits.WalkingSpan.left)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c)) (CategoryTheory.Limits.Cocone.ι.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c) CategoryTheory.Limits.WalkingSpan.left) (CategoryTheory.Limits.PushoutCocone.inl.{u1, u2} C _inst_1 X Y Z f g c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z} (c : CategoryTheory.Limits.PushoutCocone.{u1, u2} C _inst_1 X Y Z f g), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c))) CategoryTheory.Limits.WalkingSpan.left)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c)) (CategoryTheory.Limits.Cocone.ι.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c) CategoryTheory.Limits.WalkingSpan.left) (CategoryTheory.Limits.PushoutCocone.inl.{u1, u2} C _inst_1 X Y Z f g c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.ι_app_left CategoryTheory.Limits.PushoutCocone.ι_app_leftₓ'. -/
@[simp]
theorem ι_app_left (c : PushoutCocone f g) : c.ι.app WalkingSpan.left = c.inl :=
  rfl
#align category_theory.limits.pushout_cocone.ι_app_left CategoryTheory.Limits.PushoutCocone.ι_app_left

/- warning: category_theory.limits.pushout_cocone.ι_app_right -> CategoryTheory.Limits.PushoutCocone.ι_app_right is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z} (c : CategoryTheory.Limits.PushoutCocone.{u1, u2} C _inst_1 X Y Z f g), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) CategoryTheory.Limits.WalkingSpan.right) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c)) CategoryTheory.Limits.WalkingSpan.right)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c)) (CategoryTheory.Limits.Cocone.ι.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c) CategoryTheory.Limits.WalkingSpan.right) (CategoryTheory.Limits.PushoutCocone.inr.{u1, u2} C _inst_1 X Y Z f g c)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Z} (c : CategoryTheory.Limits.PushoutCocone.{u1, u2} C _inst_1 X Y Z f g), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g)) CategoryTheory.Limits.WalkingSpan.right) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c))) CategoryTheory.Limits.WalkingSpan.right)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.category.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1) (CategoryTheory.Functor.const.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1)) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c)) (CategoryTheory.Limits.Cocone.ι.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 (CategoryTheory.Limits.span.{u1, u2} C _inst_1 X Y Z f g) c) CategoryTheory.Limits.WalkingSpan.right) (CategoryTheory.Limits.PushoutCocone.inr.{u1, u2} C _inst_1 X Y Z f g c)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.ι_app_right CategoryTheory.Limits.PushoutCocone.ι_app_rightₓ'. -/
@[simp]
theorem ι_app_right (c : PushoutCocone f g) : c.ι.app WalkingSpan.right = c.inr :=
  rfl
#align category_theory.limits.pushout_cocone.ι_app_right CategoryTheory.Limits.PushoutCocone.ι_app_right

/- warning: category_theory.limits.pushout_cocone.condition_zero -> CategoryTheory.Limits.PushoutCocone.condition_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.condition_zero CategoryTheory.Limits.PushoutCocone.condition_zeroₓ'. -/
@[simp]
theorem condition_zero (t : PushoutCocone f g) : t.ι.app WalkingSpan.zero = f ≫ t.inl :=
  by
  have w := t.ι.naturality walking_span.hom.fst
  dsimp at w; simpa using w.symm
#align category_theory.limits.pushout_cocone.condition_zero CategoryTheory.Limits.PushoutCocone.condition_zero

/- warning: category_theory.limits.pushout_cocone.is_colimit_aux -> CategoryTheory.Limits.PushoutCocone.isColimitAux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.is_colimit_aux CategoryTheory.Limits.PushoutCocone.isColimitAuxₓ'. -/
/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
    It only asks for a proof of facts that carry any mathematical content -/
def isColimitAux (t : PushoutCocone f g) (desc : ∀ s : PushoutCocone f g, t.pt ⟶ s.pt)
    (fac_left : ∀ s : PushoutCocone f g, t.inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, t.inr ≫ desc s = s.inr)
    (uniq :
      ∀ (s : PushoutCocone f g) (m : t.pt ⟶ s.pt)
        (w : ∀ j : WalkingSpan, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
    IsColimit t :=
  { desc
    fac := fun s j =>
      Option.casesOn j (by simp [← s.w fst, ← t.w fst, fac_left s]) fun j' =>
        WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }
#align category_theory.limits.pushout_cocone.is_colimit_aux CategoryTheory.Limits.PushoutCocone.isColimitAux

#print CategoryTheory.Limits.PushoutCocone.isColimitAux' /-
/-- This is another convenient method to verify that a pushout cocone is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def isColimitAux' (t : PushoutCocone f g)
    (create :
      ∀ s : PushoutCocone f g,
        { l //
          t.inl ≫ l = s.inl ∧
            t.inr ≫ l = s.inr ∧ ∀ {m}, t.inl ≫ m = s.inl → t.inr ≫ m = s.inr → m = l }) :
    IsColimit t :=
  isColimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s m w => (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)
#align category_theory.limits.pushout_cocone.is_colimit_aux' CategoryTheory.Limits.PushoutCocone.isColimitAux'
-/

#print CategoryTheory.Limits.PushoutCocone.mk /-
/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
    that `f ≫ inl = g ↠ inr`. -/
@[simps]
def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : PushoutCocone f g
    where
  pt := W
  ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => WalkingPair.casesOn j' inl inr }
#align category_theory.limits.pushout_cocone.mk CategoryTheory.Limits.PushoutCocone.mk
-/

/- warning: category_theory.limits.pushout_cocone.mk_ι_app_left -> CategoryTheory.Limits.PushoutCocone.mk_ι_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.mk_ι_app_left CategoryTheory.Limits.PushoutCocone.mk_ι_app_leftₓ'. -/
@[simp]
theorem mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr Eq).ι.app WalkingSpan.left = inl :=
  rfl
#align category_theory.limits.pushout_cocone.mk_ι_app_left CategoryTheory.Limits.PushoutCocone.mk_ι_app_left

/- warning: category_theory.limits.pushout_cocone.mk_ι_app_right -> CategoryTheory.Limits.PushoutCocone.mk_ι_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.mk_ι_app_right CategoryTheory.Limits.PushoutCocone.mk_ι_app_rightₓ'. -/
@[simp]
theorem mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr Eq).ι.app WalkingSpan.right = inr :=
  rfl
#align category_theory.limits.pushout_cocone.mk_ι_app_right CategoryTheory.Limits.PushoutCocone.mk_ι_app_right

/- warning: category_theory.limits.pushout_cocone.mk_ι_app_zero -> CategoryTheory.Limits.PushoutCocone.mk_ι_app_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.mk_ι_app_zero CategoryTheory.Limits.PushoutCocone.mk_ι_app_zeroₓ'. -/
@[simp]
theorem mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr Eq).ι.app WalkingSpan.zero = f ≫ inl :=
  rfl
#align category_theory.limits.pushout_cocone.mk_ι_app_zero CategoryTheory.Limits.PushoutCocone.mk_ι_app_zero

#print CategoryTheory.Limits.PushoutCocone.mk_inl /-
@[simp]
theorem mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr Eq).inl = inl :=
  rfl
#align category_theory.limits.pushout_cocone.mk_inl CategoryTheory.Limits.PushoutCocone.mk_inl
-/

#print CategoryTheory.Limits.PushoutCocone.mk_inr /-
@[simp]
theorem mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr Eq).inr = inr :=
  rfl
#align category_theory.limits.pushout_cocone.mk_inr CategoryTheory.Limits.PushoutCocone.mk_inr
-/

#print CategoryTheory.Limits.PushoutCocone.condition /-
@[reassoc]
theorem condition (t : PushoutCocone f g) : f ≫ inl t = g ≫ inr t :=
  (t.w fst).trans (t.w snd).symm
#align category_theory.limits.pushout_cocone.condition CategoryTheory.Limits.PushoutCocone.condition
-/

/- warning: category_theory.limits.pushout_cocone.coequalizer_ext -> CategoryTheory.Limits.PushoutCocone.coequalizer_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.coequalizer_ext CategoryTheory.Limits.PushoutCocone.coequalizer_extₓ'. -/
/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
theorem coequalizer_ext (t : PushoutCocone f g) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) :
    ∀ j : WalkingSpan, t.ι.app j ≫ k = t.ι.app j ≫ l
  | some walking_pair.left => h₀
  | some walking_pair.right => h₁
  | none => by rw [← t.w fst, category.assoc, category.assoc, h₀]
#align category_theory.limits.pushout_cocone.coequalizer_ext CategoryTheory.Limits.PushoutCocone.coequalizer_ext

#print CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext /-
theorem IsColimit.hom_ext {t : PushoutCocone f g} (ht : IsColimit t) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
  ht.hom_ext <| coequalizer_ext _ h₀ h₁
#align category_theory.limits.pushout_cocone.is_colimit.hom_ext CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext
-/

#print CategoryTheory.Limits.PushoutCocone.IsColimit.desc' /-
/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
    morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.X ⟶ W` such that
    `inl t ≫ l = h` and `inr t ≫ l = k`. -/
def IsColimit.desc' {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : { l : t.pt ⟶ W // inl t ≫ l = h ∧ inr t ≫ l = k } :=
  ⟨ht.desc <| PushoutCocone.mk _ _ w, ht.fac _ _, ht.fac _ _⟩
#align category_theory.limits.pushout_cocone.is_colimit.desc' CategoryTheory.Limits.PushoutCocone.IsColimit.desc'
-/

#print CategoryTheory.Limits.PushoutCocone.epi_inr_of_is_pushout_of_epi /-
theorem epi_inr_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi f] :
    Epi t.inr :=
  ⟨fun W h k i => IsColimit.hom_ext ht (by simp [← cancel_epi f, t.condition_assoc, i]) i⟩
#align category_theory.limits.pushout_cocone.epi_inr_of_is_pushout_of_epi CategoryTheory.Limits.PushoutCocone.epi_inr_of_is_pushout_of_epi
-/

#print CategoryTheory.Limits.PushoutCocone.epi_inl_of_is_pushout_of_epi /-
theorem epi_inl_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi g] :
    Epi t.inl :=
  ⟨fun W h k i => IsColimit.hom_ext ht i (by simp [← cancel_epi g, ← t.condition_assoc, i])⟩
#align category_theory.limits.pushout_cocone.epi_inl_of_is_pushout_of_epi CategoryTheory.Limits.PushoutCocone.epi_inl_of_is_pushout_of_epi
-/

#print CategoryTheory.Limits.PushoutCocone.ext /-
/-- To construct an isomorphism of pushout cocones, it suffices to construct an isomorphism
of the cocone points and check it commutes with `inl` and `inr`. -/
def ext {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.Hom = t.inl)
    (w₂ : s.inr ≫ i.Hom = t.inr) : s ≅ t :=
  WalkingSpan.ext i w₁ w₂
#align category_theory.limits.pushout_cocone.ext CategoryTheory.Limits.PushoutCocone.ext
-/

#print CategoryTheory.Limits.PushoutCocone.IsColimit.mk /-
/-- This is a more convenient formulation to show that a `pushout_cocone` constructed using
`pushout_cocone.mk` is a colimit cocone.
-/
def IsColimit.mk {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
    (desc : ∀ s : PushoutCocone f g, W ⟶ s.pt)
    (fac_left : ∀ s : PushoutCocone f g, inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, inr ≫ desc s = s.inr)
    (uniq :
      ∀ (s : PushoutCocone f g) (m : W ⟶ s.pt) (w_inl : inl ≫ m = s.inl) (w_inr : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (mk inl inr Eq) :=
  isColimitAux _ desc fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)
#align category_theory.limits.pushout_cocone.is_colimit.mk CategoryTheory.Limits.PushoutCocone.IsColimit.mk
-/

#print CategoryTheory.Limits.PushoutCocone.flipIsColimit /-
/-- The flip of a pushout square is a pushout square. -/
def flipIsColimit {W : C} {h : Y ⟶ W} {k : Z ⟶ W} {comm : f ≫ h = g ≫ k}
    (t : IsColimit (mk _ _ comm.symm)) : IsColimit (mk _ _ comm) :=
  isColimitAux' _ fun s =>
    by
    refine'
      ⟨(is_colimit.desc' t _ _ s.condition.symm).1, (is_colimit.desc' t _ _ _).2.2,
        (is_colimit.desc' t _ _ _).2.1, fun m m₁ m₂ => t.hom_ext _⟩
    apply (mk k h _).coequalizer_ext
    · rwa [(is_colimit.desc' t _ _ _).2.1]
    · rwa [(is_colimit.desc' t _ _ _).2.2]
#align category_theory.limits.pushout_cocone.flip_is_colimit CategoryTheory.Limits.PushoutCocone.flipIsColimit
-/

#print CategoryTheory.Limits.PushoutCocone.isColimitMkIdId /-
/--
The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an epi. The converse is
shown in `epi_of_is_colimit_mk_id_id`.
-/
def isColimitMkIdId (f : X ⟶ Y) [Epi f] : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
  IsColimit.mk _ (fun s => s.inl) (fun s => Category.id_comp _)
    (fun s => by rw [← cancel_epi f, category.id_comp, s.condition]) fun s m m₁ m₂ => by
    simpa using m₁
#align category_theory.limits.pushout_cocone.is_colimit_mk_id_id CategoryTheory.Limits.PushoutCocone.isColimitMkIdId
-/

#print CategoryTheory.Limits.PushoutCocone.epi_of_isColimitMkIdId /-
/-- `f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, f)`.
The converse is given in `pushout_cocone.is_colimit_mk_id_id`.
-/
theorem epi_of_isColimitMkIdId (f : X ⟶ Y)
    (t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) : Epi f :=
  ⟨fun Z g h eq =>
    by
    rcases pushout_cocone.is_colimit.desc' t _ _ Eq with ⟨_, rfl, rfl⟩
    rfl⟩
#align category_theory.limits.pushout_cocone.epi_of_is_colimit_mk_id_id CategoryTheory.Limits.PushoutCocone.epi_of_isColimitMkIdId
-/

#print CategoryTheory.Limits.PushoutCocone.isColimitOfFactors /-
/-- Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit cocone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimorphism `h` via
    `x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram formed by `x` and
    `y`.  -/
def isColimitOfFactors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y) (y : W ⟶ Z)
    (hhx : h ≫ x = f) (hhy : h ≫ y = g) (s : PushoutCocone f g) (hs : IsColimit s) :
    IsColimit
      (PushoutCocone.mk _ _
        (show x ≫ s.inl = y ≫ s.inr from
          (cancel_epi h).1 <| by rw [reassoc_of hhx, reassoc_of hhy, s.condition])) :=
  PushoutCocone.isColimitAux' _ fun t =>
    ⟨hs.desc
        (PushoutCocone.mk t.inl t.inr <| by
          rw [← hhx, ← hhy, category.assoc, category.assoc, t.condition]),
      ⟨hs.fac _ WalkingSpan.left, hs.fac _ WalkingSpan.right, fun r hr hr' =>
        by
        apply pushout_cocone.is_colimit.hom_ext hs <;>
              simp only [pushout_cocone.mk_inl, pushout_cocone.mk_inr] at hr hr'⊢ <;>
            simp only [hr, hr'] <;>
          symm
        exacts[hs.fac _ walking_span.left, hs.fac _ walking_span.right]⟩⟩
#align category_theory.limits.pushout_cocone.is_colimit_of_factors CategoryTheory.Limits.PushoutCocone.isColimitOfFactors
-/

#print CategoryTheory.Limits.PushoutCocone.isColimitOfEpiComp /-
/-- If `W` is the pushout of `f, g`,
it is also the pushout of `h ≫ f, h ≫ g` for any epi `h`. -/
def isColimitOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : PushoutCocone f g)
    (H : IsColimit s) :
    IsColimit
      (PushoutCocone.mk _ _
        (show (h ≫ f) ≫ s.inl = (h ≫ g) ≫ s.inr by
          rw [category.assoc, category.assoc, s.condition])) :=
  by
  apply pushout_cocone.is_colimit_aux'
  intro s
  rcases pushout_cocone.is_colimit.desc' H s.inl s.inr
      ((cancel_epi h).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine' ⟨l, h₁, h₂, _⟩
  intro m hm₁ hm₂
  exact (pushout_cocone.is_colimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)
#align category_theory.limits.pushout_cocone.is_colimit_of_epi_comp CategoryTheory.Limits.PushoutCocone.isColimitOfEpiComp
-/

end PushoutCocone

/- warning: category_theory.limits.cone.of_pullback_cone -> CategoryTheory.Limits.Cone.ofPullbackCone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1}, (CategoryTheory.Limits.PullbackCone.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.right) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.one) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.left CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inl) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.right CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inr)) -> (CategoryTheory.Limits.Cone.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1}, (CategoryTheory.Limits.PullbackCone.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.right) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.one) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.left CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inl) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.right CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inr)) -> (CategoryTheory.Limits.Cone.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cone.of_pullback_cone CategoryTheory.Limits.Cone.ofPullbackConeₓ'. -/
/-- This is a helper construction that can be useful when verifying that a category has all
    pullbacks. Given `F : walking_cospan ⥤ C`, which is really the same as
    `cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
    get a cone on `F`.

    If you're thinking about using this, have a look at `has_pullbacks_of_has_limit_cospan`,
    which you may find to be an easier way of achieving your goal. -/
@[simps]
def Cone.ofPullbackCone {F : WalkingCospan ⥤ C} (t : PullbackCone (F.map inl) (F.map inr)) : Cone F
    where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).inv
#align category_theory.limits.cone.of_pullback_cone CategoryTheory.Limits.Cone.ofPullbackCone

/- warning: category_theory.limits.cocone.of_pushout_cocone -> CategoryTheory.Limits.Cocone.ofPushoutCocone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1}, (CategoryTheory.Limits.PushoutCocone.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.right) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.left CategoryTheory.Limits.WalkingSpan.Hom.fst) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.right CategoryTheory.Limits.WalkingSpan.Hom.snd)) -> (CategoryTheory.Limits.Cocone.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1}, (CategoryTheory.Limits.PushoutCocone.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.right) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.left CategoryTheory.Limits.WalkingSpan.Hom.fst) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.right CategoryTheory.Limits.WalkingSpan.Hom.snd)) -> (CategoryTheory.Limits.Cocone.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.cocone.of_pushout_cocone CategoryTheory.Limits.Cocone.ofPushoutCoconeₓ'. -/
/-- This is a helper construction that can be useful when verifying that a category has all
    pushout. Given `F : walking_span ⥤ C`, which is really the same as
    `span (F.map fst) (F.mal snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at `has_pushouts_of_has_colimit_span`, which
    you may find to be an easiery way of achieving your goal.  -/
@[simps]
def Cocone.ofPushoutCocone {F : WalkingSpan ⥤ C} (t : PushoutCocone (F.map fst) (F.map snd)) :
    Cocone F where
  pt := t.pt
  ι := (diagramIsoSpan F).Hom ≫ t.ι
#align category_theory.limits.cocone.of_pushout_cocone CategoryTheory.Limits.Cocone.ofPushoutCocone

/- warning: category_theory.limits.pullback_cone.of_cone -> CategoryTheory.Limits.PullbackCone.ofCone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1}, (CategoryTheory.Limits.Cone.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) -> (CategoryTheory.Limits.PullbackCone.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.right) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.one) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.left CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inl) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingCospan.right CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inr))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1}, (CategoryTheory.Limits.Cone.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) -> (CategoryTheory.Limits.PullbackCone.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.right) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.one) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.left CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inl) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingCospan.right CategoryTheory.Limits.WalkingCospan.one CategoryTheory.Limits.WalkingCospan.Hom.inr))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.of_cone CategoryTheory.Limits.PullbackCone.ofConeₓ'. -/
/-- Given `F : walking_cospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
    and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simps]
def PullbackCone.ofCone {F : WalkingCospan ⥤ C} (t : Cone F) : PullbackCone (F.map inl) (F.map inr)
    where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).Hom
#align category_theory.limits.pullback_cone.of_cone CategoryTheory.Limits.PullbackCone.ofCone

/- warning: category_theory.limits.pullback_cone.iso_mk -> CategoryTheory.Limits.PullbackCone.isoMk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone.iso_mk CategoryTheory.Limits.PullbackCone.isoMkₓ'. -/
/-- A diagram `walking_cospan ⥤ C` is isomorphic to some `pullback_cone.mk` after
composing with `diagram_iso_cospan`. -/
@[simps]
def PullbackCone.isoMk {F : WalkingCospan ⥤ C} (t : Cone F) :
    (Cones.postcompose (diagramIsoCospan.{v} _).Hom).obj t ≅
      PullbackCone.mk (t.π.app WalkingCospan.left) (t.π.app WalkingCospan.right)
        ((t.π.naturality inl).symm.trans (t.π.naturality inr : _)) :=
  Cones.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;>
      · dsimp
        simp
#align category_theory.limits.pullback_cone.iso_mk CategoryTheory.Limits.PullbackCone.isoMk

/- warning: category_theory.limits.pushout_cocone.of_cocone -> CategoryTheory.Limits.PushoutCocone.ofCocone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1}, (CategoryTheory.Limits.Cocone.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) -> (CategoryTheory.Limits.PushoutCocone.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.left) (CategoryTheory.Functor.obj.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.right) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.left CategoryTheory.Limits.WalkingSpan.Hom.fst) (CategoryTheory.Functor.map.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.right CategoryTheory.Limits.WalkingSpan.Hom.snd))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {F : CategoryTheory.Functor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1}, (CategoryTheory.Limits.Cocone.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) -> (CategoryTheory.Limits.PushoutCocone.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.left) (Prefunctor.obj.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.right) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.left CategoryTheory.Limits.WalkingSpan.Hom.fst) (Prefunctor.map.{1, succ u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.CategoryStruct.toQuiver.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.toCategoryStruct.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) C _inst_1 F) CategoryTheory.Limits.WalkingSpan.zero CategoryTheory.Limits.WalkingSpan.right CategoryTheory.Limits.WalkingSpan.Hom.snd))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.of_cocone CategoryTheory.Limits.PushoutCocone.ofCoconeₓ'. -/
/-- Given `F : walking_span ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
    and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
def PushoutCocone.ofCocone {F : WalkingSpan ⥤ C} (t : Cocone F) :
    PushoutCocone (F.map fst) (F.map snd)
    where
  pt := t.pt
  ι := (diagramIsoSpan F).inv ≫ t.ι
#align category_theory.limits.pushout_cocone.of_cocone CategoryTheory.Limits.PushoutCocone.ofCocone

/- warning: category_theory.limits.pushout_cocone.iso_mk -> CategoryTheory.Limits.PushoutCocone.isoMk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone.iso_mk CategoryTheory.Limits.PushoutCocone.isoMkₓ'. -/
/-- A diagram `walking_span ⥤ C` is isomorphic to some `pushout_cocone.mk` after composing with
`diagram_iso_span`. -/
@[simps]
def PushoutCocone.isoMk {F : WalkingSpan ⥤ C} (t : Cocone F) :
    (Cocones.precompose (diagramIsoSpan.{v} _).inv).obj t ≅
      PushoutCocone.mk (t.ι.app WalkingSpan.left) (t.ι.app WalkingSpan.right)
        ((t.ι.naturality fst).trans (t.ι.naturality snd).symm) :=
  Cocones.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;>
      · dsimp
        simp
#align category_theory.limits.pushout_cocone.iso_mk CategoryTheory.Limits.PushoutCocone.isoMk

#print CategoryTheory.Limits.HasPullback /-
/-- `has_pullback f g` represents a particular choice of limiting cone
for the pair of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`.
-/
abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)
#align category_theory.limits.has_pullback CategoryTheory.Limits.HasPullback
-/

#print CategoryTheory.Limits.HasPushout /-
/-- `has_pushout f g` represents a particular choice of colimiting cocone
for the pair of morphisms `f : X ⟶ Y` and `g : X ⟶ Z`.
-/
abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)
#align category_theory.limits.has_pushout CategoryTheory.Limits.HasPushout
-/

#print CategoryTheory.Limits.pullback /-
/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)
#align category_theory.limits.pullback CategoryTheory.Limits.pullback
-/

#print CategoryTheory.Limits.pushout /-
/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)
#align category_theory.limits.pushout CategoryTheory.Limits.pushout
-/

#print CategoryTheory.Limits.pullback.fst /-
/-- The first projection of the pullback of `f` and `g`. -/
abbrev pullback.fst {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left
#align category_theory.limits.pullback.fst CategoryTheory.Limits.pullback.fst
-/

#print CategoryTheory.Limits.pullback.snd /-
/-- The second projection of the pullback of `f` and `g`. -/
abbrev pullback.snd {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right
#align category_theory.limits.pullback.snd CategoryTheory.Limits.pullback.snd
-/

#print CategoryTheory.Limits.pushout.inl /-
/-- The first inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inl {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left
#align category_theory.limits.pushout.inl CategoryTheory.Limits.pushout.inl
-/

#print CategoryTheory.Limits.pushout.inr /-
/-- The second inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inr {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right
#align category_theory.limits.pushout.inr CategoryTheory.Limits.pushout.inr
-/

#print CategoryTheory.Limits.pullback.lift /-
/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `pullback.lift : W ⟶ pullback f g`. -/
abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)
#align category_theory.limits.pullback.lift CategoryTheory.Limits.pullback.lift
-/

#print CategoryTheory.Limits.pushout.desc /-
/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `pushout.desc : pushout f g ⟶ W`. -/
abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)
#align category_theory.limits.pushout.desc CategoryTheory.Limits.pushout.desc
-/

#print CategoryTheory.Limits.PullbackCone.fst_colimit_cocone /-
@[simp]
theorem PullbackCone.fst_colimit_cocone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasLimit (cospan f g)] : PullbackCone.fst (limit.cone (cospan f g)) = pullback.fst :=
  rfl
#align category_theory.limits.pullback_cone.fst_colimit_cocone CategoryTheory.Limits.PullbackCone.fst_colimit_cocone
-/

#print CategoryTheory.Limits.PullbackCone.snd_colimit_cocone /-
@[simp]
theorem PullbackCone.snd_colimit_cocone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasLimit (cospan f g)] : PullbackCone.snd (limit.cone (cospan f g)) = pullback.snd :=
  rfl
#align category_theory.limits.pullback_cone.snd_colimit_cocone CategoryTheory.Limits.PullbackCone.snd_colimit_cocone
-/

#print CategoryTheory.Limits.PushoutCocone.inl_colimit_cocone /-
@[simp]
theorem PushoutCocone.inl_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inl (colimit.cocone (span f g)) = pushout.inl :=
  rfl
#align category_theory.limits.pushout_cocone.inl_colimit_cocone CategoryTheory.Limits.PushoutCocone.inl_colimit_cocone
-/

#print CategoryTheory.Limits.PushoutCocone.inr_colimit_cocone /-
@[simp]
theorem PushoutCocone.inr_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inr (colimit.cocone (span f g)) = pushout.inr :=
  rfl
#align category_theory.limits.pushout_cocone.inr_colimit_cocone CategoryTheory.Limits.PushoutCocone.inr_colimit_cocone
-/

#print CategoryTheory.Limits.pullback.lift_fst /-
@[simp, reassoc]
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst = h :=
  limit.lift_π _ _
#align category_theory.limits.pullback.lift_fst CategoryTheory.Limits.pullback.lift_fst
-/

#print CategoryTheory.Limits.pullback.lift_snd /-
@[simp, reassoc]
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd = k :=
  limit.lift_π _ _
#align category_theory.limits.pullback.lift_snd CategoryTheory.Limits.pullback.lift_snd
-/

#print CategoryTheory.Limits.pushout.inl_desc /-
@[simp, reassoc]
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inl ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _
#align category_theory.limits.pushout.inl_desc CategoryTheory.Limits.pushout.inl_desc
-/

#print CategoryTheory.Limits.pushout.inr_desc /-
@[simp, reassoc]
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inr ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _
#align category_theory.limits.pushout.inr_desc CategoryTheory.Limits.pushout.inr_desc
-/

#print CategoryTheory.Limits.pullback.lift' /-
/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : { l : W ⟶ pullback f g // l ≫ pullback.fst = h ∧ l ≫ pullback.snd = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
#align category_theory.limits.pullback.lift' CategoryTheory.Limits.pullback.lift'
-/

#print CategoryTheory.Limits.pullback.desc' /-
/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `l : pushout f g ⟶ W` such that `pushout.inl ≫ l = h` and `pushout.inr ≫ l = k`. -/
def pullback.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : { l : pushout f g ⟶ W // pushout.inl ≫ l = h ∧ pushout.inr ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩
#align category_theory.limits.pullback.desc' CategoryTheory.Limits.pullback.desc'
-/

#print CategoryTheory.Limits.pullback.condition /-
@[reassoc]
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    (pullback.fst : pullback f g ⟶ X) ≫ f = pullback.snd ≫ g :=
  PullbackCone.condition _
#align category_theory.limits.pullback.condition CategoryTheory.Limits.pullback.condition
-/

#print CategoryTheory.Limits.pushout.condition /-
@[reassoc]
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    f ≫ (pushout.inl : Y ⟶ pushout f g) = g ≫ pushout.inr :=
  PushoutCocone.condition _
#align category_theory.limits.pushout.condition CategoryTheory.Limits.pushout.condition
-/

#print CategoryTheory.Limits.pullback.map /-
/-- Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

    W  ⟶  Y
      ↘      ↘
        S  ⟶  T
      ↗      ↗
    X  ⟶  Z

-/
abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ i₂)
    (by simp [← eq₁, ← eq₂, pullback.condition_assoc])
#align category_theory.limits.pullback.map CategoryTheory.Limits.pullback.map
-/

#print CategoryTheory.Limits.pullback.mapDesc /-
/-- The canonical map `X ×ₛ Y ⟶ X ×ₜ Y` given `S ⟶ T`. -/
abbrev pullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
    [HasPullback (f ≫ i) (g ≫ i)] : pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
  pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm
#align category_theory.limits.pullback.map_desc CategoryTheory.Limits.pullback.mapDesc
-/

#print CategoryTheory.Limits.pushout.map /-
/-- Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

        W  ⟶  Y
      ↗      ↗
    S  ⟶  T
      ↘      ↘
        X  ⟶  Z

-/
abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
    (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl) (i₂ ≫ pushout.inr)
    (by
      simp only [← category.assoc, eq₁, eq₂]
      simp [pushout.condition])
#align category_theory.limits.pushout.map CategoryTheory.Limits.pushout.map
-/

#print CategoryTheory.Limits.pushout.mapLift /-
/-- The canonical map `X ⨿ₛ Y ⟶ X ⨿ₜ Y` given `S ⟶ T`. -/
abbrev pushout.mapLift {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
    [HasPushout (i ≫ f) (i ≫ g)] : pushout (i ≫ f) (i ≫ g) ⟶ pushout f g :=
  pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)
#align category_theory.limits.pushout.map_lift CategoryTheory.Limits.pushout.mapLift
-/

#print CategoryTheory.Limits.pullback.hom_ext /-
/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
    equal -/
@[ext]
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
    {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst = l ≫ pullback.fst)
    (h₁ : k ≫ pullback.snd = l ≫ pullback.snd) : k = l :=
  limit.hom_ext <| PullbackCone.equalizer_ext _ h₀ h₁
#align category_theory.limits.pullback.hom_ext CategoryTheory.Limits.pullback.hom_ext
-/

#print CategoryTheory.Limits.pullbackIsPullback /-
/-- The pullback cone built from the pullback projections is a pullback. -/
def pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (PullbackCone.mk (pullback.fst : pullback f g ⟶ _) pullback.snd pullback.condition) :=
  PullbackCone.IsLimit.mk _ (fun s => pullback.lift s.fst s.snd s.condition) (by simp) (by simp)
    (by tidy)
#align category_theory.limits.pullback_is_pullback CategoryTheory.Limits.pullbackIsPullback
-/

#print CategoryTheory.Limits.pullback.fst_of_mono /-
/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g] :
    Mono (pullback.fst : pullback f g ⟶ X) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)
#align category_theory.limits.pullback.fst_of_mono CategoryTheory.Limits.pullback.fst_of_mono
-/

#print CategoryTheory.Limits.pullback.snd_of_mono /-
/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f] :
    Mono (pullback.snd : pullback f g ⟶ Y) :=
  PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)
#align category_theory.limits.pullback.snd_of_mono CategoryTheory.Limits.pullback.snd_of_mono
-/

#print CategoryTheory.Limits.mono_pullback_to_prod /-
/-- The map `X ×[Z] Y ⟶ X × Y` is mono. -/
instance mono_pullback_to_prod {C : Type _} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasBinaryProduct X Y] :
    Mono (prod.lift pullback.fst pullback.snd : pullback f g ⟶ _) :=
  ⟨fun W i₁ i₂ h => by
    ext
    · simpa using congr_arg (fun f => f ≫ Prod.fst) h
    · simpa using congr_arg (fun f => f ≫ Prod.snd) h⟩
#align category_theory.limits.mono_pullback_to_prod CategoryTheory.Limits.mono_pullback_to_prod
-/

#print CategoryTheory.Limits.pushout.hom_ext /-
/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
@[ext]
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
    {k l : pushout f g ⟶ W} (h₀ : pushout.inl ≫ k = pushout.inl ≫ l)
    (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
  colimit.hom_ext <| PushoutCocone.coequalizer_ext _ h₀ h₁
#align category_theory.limits.pushout.hom_ext CategoryTheory.Limits.pushout.hom_ext
-/

#print CategoryTheory.Limits.pushoutIsPushout /-
/-- The pushout cocone built from the pushout coprojections is a pushout. -/
def pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (PushoutCocone.mk (pushout.inl : _ ⟶ pushout f g) pushout.inr pushout.condition) :=
  PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
    (by tidy)
#align category_theory.limits.pushout_is_pushout CategoryTheory.Limits.pushoutIsPushout
-/

#print CategoryTheory.Limits.pushout.inl_of_epi /-
/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g] :
    Epi (pushout.inl : Y ⟶ pushout f g) :=
  PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)
#align category_theory.limits.pushout.inl_of_epi CategoryTheory.Limits.pushout.inl_of_epi
-/

#print CategoryTheory.Limits.pushout.inr_of_epi /-
/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f] :
    Epi (pushout.inr : Z ⟶ pushout f g) :=
  PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)
#align category_theory.limits.pushout.inr_of_epi CategoryTheory.Limits.pushout.inr_of_epi
-/

#print CategoryTheory.Limits.epi_coprod_to_pushout /-
/-- The map ` X ⨿ Y ⟶ X ⨿[Z] Y` is epi. -/
instance epi_coprod_to_pushout {C : Type _} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
    [HasPushout f g] [HasBinaryCoproduct Y Z] :
    Epi (coprod.desc pushout.inl pushout.inr : _ ⟶ pushout f g) :=
  ⟨fun W i₁ i₂ h => by
    ext
    · simpa using congr_arg (fun f => coprod.inl ≫ f) h
    · simpa using congr_arg (fun f => coprod.inr ≫ f) h⟩
#align category_theory.limits.epi_coprod_to_pushout CategoryTheory.Limits.epi_coprod_to_pushout
-/

#print CategoryTheory.Limits.pullback.map_isIso /-
instance pullback.map_isIso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
  by
  refine' ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _, _, _⟩⟩
  · rw [is_iso.comp_inv_eq, category.assoc, eq₁, is_iso.inv_hom_id_assoc]
  · rw [is_iso.comp_inv_eq, category.assoc, eq₂, is_iso.inv_hom_id_assoc]
  tidy
#align category_theory.limits.pullback.map_is_iso CategoryTheory.Limits.pullback.map_isIso
-/

#print CategoryTheory.Limits.pullback.congrHom /-
/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps Hom]
def pullback.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] : pullback f₁ g₁ ≅ pullback f₂ g₂ :=
  asIso <| pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])
#align category_theory.limits.pullback.congr_hom CategoryTheory.Limits.pullback.congrHom
-/

#print CategoryTheory.Limits.pullback.congrHom_inv /-
@[simp]
theorem pullback.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv =
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) :=
  by
  apply pullback.hom_ext
  · erw [pullback.lift_fst]
    rw [iso.inv_comp_eq]
    erw [pullback.lift_fst_assoc]
    rw [category.comp_id, category.comp_id]
  · erw [pullback.lift_snd]
    rw [iso.inv_comp_eq]
    erw [pullback.lift_snd_assoc]
    rw [category.comp_id, category.comp_id]
#align category_theory.limits.pullback.congr_hom_inv CategoryTheory.Limits.pullback.congrHom_inv
-/

#print CategoryTheory.Limits.pushout.map_isIso /-
instance pushout.map_isIso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
  by
  refine' ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _, _, _⟩⟩
  · rw [is_iso.comp_inv_eq, category.assoc, eq₁, is_iso.inv_hom_id_assoc]
  · rw [is_iso.comp_inv_eq, category.assoc, eq₂, is_iso.inv_hom_id_assoc]
  tidy
#align category_theory.limits.pushout.map_is_iso CategoryTheory.Limits.pushout.map_isIso
-/

#print CategoryTheory.Limits.pullback.mapDesc_comp /-
theorem pullback.mapDesc_comp {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] [HasPullback (f ≫ i ≫ i') (g ≫ i ≫ i')]
    [HasPullback ((f ≫ i) ≫ i') ((g ≫ i) ≫ i')] :
    pullback.mapDesc f g (i ≫ i') =
      pullback.mapDesc f g i ≫
        pullback.mapDesc _ _ i' ≫
          (pullback.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).Hom :=
  by ext <;> simp
#align category_theory.limits.pullback.map_desc_comp CategoryTheory.Limits.pullback.mapDesc_comp
-/

#print CategoryTheory.Limits.pushout.congrHom /-
/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps Hom]
def pushout.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] : pushout f₁ g₁ ≅ pushout f₂ g₂ :=
  asIso <| pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])
#align category_theory.limits.pushout.congr_hom CategoryTheory.Limits.pushout.congrHom
-/

#print CategoryTheory.Limits.pushout.congrHom_inv /-
@[simp]
theorem pushout.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    (pushout.congrHom h₁ h₂).inv =
      pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) :=
  by
  apply pushout.hom_ext
  · erw [pushout.inl_desc]
    rw [iso.comp_inv_eq, category.id_comp]
    erw [pushout.inl_desc]
    rw [category.id_comp]
  · erw [pushout.inr_desc]
    rw [iso.comp_inv_eq, category.id_comp]
    erw [pushout.inr_desc]
    rw [category.id_comp]
#align category_theory.limits.pushout.congr_hom_inv CategoryTheory.Limits.pushout.congrHom_inv
-/

#print CategoryTheory.Limits.pushout.mapLift_comp /-
theorem pushout.mapLift_comp {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
    [HasPushout f g] [HasPushout (i ≫ f) (i ≫ g)] [HasPushout (i' ≫ i ≫ f) (i' ≫ i ≫ g)]
    [HasPushout ((i' ≫ i) ≫ f) ((i' ≫ i) ≫ g)] :
    pushout.mapLift f g (i' ≫ i) =
      (pushout.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).Hom ≫
        pushout.mapLift _ _ i' ≫ pushout.mapLift f g i :=
  by ext <;> simp
#align category_theory.limits.pushout.map_lift_comp CategoryTheory.Limits.pushout.mapLift_comp
-/

section

variable (G : C ⥤ D)

/- warning: category_theory.limits.pullback_comparison -> CategoryTheory.Limits.pullbackComparison is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} D] {X : C} {Y : C} {Z : C} (G : CategoryTheory.Functor.{u2, u1, u3, u4} C _inst_1 D _inst_2) (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Z) (g : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Y Z) [_inst_3 : CategoryTheory.Limits.HasPullback.{u2, u3} C _inst_1 X Y Z f g] [_inst_4 : CategoryTheory.Limits.HasPullback.{u1, u4} D _inst_2 (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Z) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X Z f) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Y Z g)], Quiver.Hom.{succ u1, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.pullback.{u2, u3} C _inst_1 X Y Z f g _inst_3)) (CategoryTheory.Limits.pullback.{u1, u4} D _inst_2 (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Z) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X Z f) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Y Z g) _inst_4)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} D] {X : C} {Y : C} {Z : C} (G : CategoryTheory.Functor.{u2, u1, u3, u4} C _inst_1 D _inst_2) (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Z) (g : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Y Z) [_inst_3 : CategoryTheory.Limits.HasPullback.{u2, u3} C _inst_1 X Y Z f g] [_inst_4 : CategoryTheory.Limits.HasPullback.{u1, u4} D _inst_2 (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Z) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X Z f) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Y Z g)], Quiver.Hom.{succ u1, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.pullback.{u2, u3} C _inst_1 X Y Z f g _inst_3)) (CategoryTheory.Limits.pullback.{u1, u4} D _inst_2 (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Z) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X Z f) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Y Z g) _inst_4)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_comparison CategoryTheory.Limits.pullbackComparisonₓ'. -/
/-- The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`category_theory/limits/preserves/shapes/pullbacks.lean`
-/
def pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map pullback.fst) (G.map pullback.snd)
    (by simp only [← G.map_comp, pullback.condition])
#align category_theory.limits.pullback_comparison CategoryTheory.Limits.pullbackComparison

/- warning: category_theory.limits.pullback_comparison_comp_fst -> CategoryTheory.Limits.pullbackComparison_comp_fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_comparison_comp_fst CategoryTheory.Limits.pullbackComparison_comp_fstₓ'. -/
@[simp, reassoc]
theorem pullbackComparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.fst = G.map pullback.fst :=
  pullback.lift_fst _ _ _
#align category_theory.limits.pullback_comparison_comp_fst CategoryTheory.Limits.pullbackComparison_comp_fst

/- warning: category_theory.limits.pullback_comparison_comp_snd -> CategoryTheory.Limits.pullbackComparison_comp_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_comparison_comp_snd CategoryTheory.Limits.pullbackComparison_comp_sndₓ'. -/
@[simp, reassoc]
theorem pullbackComparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.snd = G.map pullback.snd :=
  pullback.lift_snd _ _ _
#align category_theory.limits.pullback_comparison_comp_snd CategoryTheory.Limits.pullbackComparison_comp_snd

/- warning: category_theory.limits.map_lift_pullback_comparison -> CategoryTheory.Limits.map_lift_pullbackComparison is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.map_lift_pullback_comparison CategoryTheory.Limits.map_lift_pullbackComparisonₓ'. -/
@[simp, reassoc]
theorem map_lift_pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g =
      pullback.lift (G.map h) (G.map k) (by simp only [← G.map_comp, w]) :=
  by ext <;> simp [← G.map_comp]
#align category_theory.limits.map_lift_pullback_comparison CategoryTheory.Limits.map_lift_pullbackComparison

/- warning: category_theory.limits.pushout_comparison -> CategoryTheory.Limits.pushoutComparison is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} D] {X : C} {Y : C} {Z : C} (G : CategoryTheory.Functor.{u2, u1, u3, u4} C _inst_1 D _inst_2) (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Z) [_inst_3 : CategoryTheory.Limits.HasPushout.{u2, u3} C _inst_1 X Y Z f g] [_inst_4 : CategoryTheory.Limits.HasPushout.{u1, u4} D _inst_2 (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Z) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X Z g)], Quiver.Hom.{succ u1, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Limits.pushout.{u1, u4} D _inst_2 (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Y) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G Z) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X Y f) (CategoryTheory.Functor.map.{u2, u1, u3, u4} C _inst_1 D _inst_2 G X Z g) _inst_4) (CategoryTheory.Functor.obj.{u2, u1, u3, u4} C _inst_1 D _inst_2 G (CategoryTheory.Limits.pushout.{u2, u3} C _inst_1 X Y Z f g _inst_3))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u1, u4} D] {X : C} {Y : C} {Z : C} (G : CategoryTheory.Functor.{u2, u1, u3, u4} C _inst_1 D _inst_2) (f : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Y) (g : Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) X Z) [_inst_3 : CategoryTheory.Limits.HasPushout.{u2, u3} C _inst_1 X Y Z f g] [_inst_4 : CategoryTheory.Limits.HasPushout.{u1, u4} D _inst_2 (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Z) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X Z g)], Quiver.Hom.{succ u1, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Limits.pushout.{u1, u4} D _inst_2 (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Y) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) Z) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X Y f) (Prefunctor.map.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) X Z g) _inst_4) (Prefunctor.obj.{succ u2, succ u1, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} D (CategoryTheory.Category.toCategoryStruct.{u1, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, u4} C _inst_1 D _inst_2 G) (CategoryTheory.Limits.pushout.{u2, u3} C _inst_1 X Y Z f g _inst_3))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_comparison CategoryTheory.Limits.pushoutComparisonₓ'. -/
/-- The comparison morphism for the pushout of `f,g`.
This is an isomorphism iff `G` preserves the pushout of `f,g`; see
`category_theory/limits/preserves/shapes/pullbacks.lean`
-/
def pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
  pushout.desc (G.map pushout.inl) (G.map pushout.inr)
    (by simp only [← G.map_comp, pushout.condition])
#align category_theory.limits.pushout_comparison CategoryTheory.Limits.pushoutComparison

/- warning: category_theory.limits.inl_comp_pushout_comparison -> CategoryTheory.Limits.inl_comp_pushoutComparison is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.inl_comp_pushout_comparison CategoryTheory.Limits.inl_comp_pushoutComparisonₓ'. -/
@[simp, reassoc]
theorem inl_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inl ≫ pushoutComparison G f g = G.map pushout.inl :=
  pushout.inl_desc _ _ _
#align category_theory.limits.inl_comp_pushout_comparison CategoryTheory.Limits.inl_comp_pushoutComparison

/- warning: category_theory.limits.inr_comp_pushout_comparison -> CategoryTheory.Limits.inr_comp_pushoutComparison is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.inr_comp_pushout_comparison CategoryTheory.Limits.inr_comp_pushoutComparisonₓ'. -/
@[simp, reassoc]
theorem inr_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inr ≫ pushoutComparison G f g = G.map pushout.inr :=
  pushout.inr_desc _ _ _
#align category_theory.limits.inr_comp_pushout_comparison CategoryTheory.Limits.inr_comp_pushoutComparison

/- warning: category_theory.limits.pushout_comparison_map_desc -> CategoryTheory.Limits.pushoutComparison_map_desc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_comparison_map_desc CategoryTheory.Limits.pushoutComparison_map_descₓ'. -/
@[simp, reassoc]
theorem pushoutComparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k) (by simp only [← G.map_comp, w]) :=
  by ext <;> simp [← G.map_comp]
#align category_theory.limits.pushout_comparison_map_desc CategoryTheory.Limits.pushoutComparison_map_desc

end

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

#print CategoryTheory.Limits.hasPullback_symmetry /-
/-- Making this a global instance would make the typeclass seach go in an infinite loop. -/
theorem hasPullback_symmetry [HasPullback f g] : HasPullback g f :=
  ⟨⟨⟨PullbackCone.mk _ _ pullback.condition.symm,
        PullbackCone.flipIsLimit (pullbackIsPullback _ _)⟩⟩⟩
#align category_theory.limits.has_pullback_symmetry CategoryTheory.Limits.hasPullback_symmetry
-/

attribute [local instance] has_pullback_symmetry

#print CategoryTheory.Limits.pullbackSymmetry /-
/-- The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`. -/
def pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f :=
  IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g) :
      IsLimit (PullbackCone.mk _ _ pullback.condition.symm))
    (limit.isLimit _)
#align category_theory.limits.pullback_symmetry CategoryTheory.Limits.pullbackSymmetry
-/

#print CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst /-
@[simp, reassoc]
theorem pullbackSymmetry_hom_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).Hom ≫ pullback.fst = pullback.snd := by simp [pullback_symmetry]
#align category_theory.limits.pullback_symmetry_hom_comp_fst CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst
-/

#print CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd /-
@[simp, reassoc]
theorem pullbackSymmetry_hom_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).Hom ≫ pullback.snd = pullback.fst := by simp [pullback_symmetry]
#align category_theory.limits.pullback_symmetry_hom_comp_snd CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd
-/

#print CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst /-
@[simp, reassoc]
theorem pullbackSymmetry_inv_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.fst = pullback.snd := by simp [iso.inv_comp_eq]
#align category_theory.limits.pullback_symmetry_inv_comp_fst CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst
-/

#print CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd /-
@[simp, reassoc]
theorem pullbackSymmetry_inv_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.snd = pullback.fst := by simp [iso.inv_comp_eq]
#align category_theory.limits.pullback_symmetry_inv_comp_snd CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd
-/

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

#print CategoryTheory.Limits.hasPushout_symmetry /-
/-- Making this a global instance would make the typeclass seach go in an infinite loop. -/
theorem hasPushout_symmetry [HasPushout f g] : HasPushout g f :=
  ⟨⟨⟨PushoutCocone.mk _ _ pushout.condition.symm,
        PushoutCocone.flipIsColimit (pushoutIsPushout _ _)⟩⟩⟩
#align category_theory.limits.has_pushout_symmetry CategoryTheory.Limits.hasPushout_symmetry
-/

attribute [local instance] has_pushout_symmetry

#print CategoryTheory.Limits.pushoutSymmetry /-
/-- The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`. -/
def pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f :=
  IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g) :
      IsColimit (PushoutCocone.mk _ _ pushout.condition.symm))
    (colimit.isColimit _)
#align category_theory.limits.pushout_symmetry CategoryTheory.Limits.pushoutSymmetry
-/

#print CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom /-
@[simp, reassoc]
theorem inl_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inl ≫ (pushoutSymmetry f g).Hom = pushout.inr :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _
#align category_theory.limits.inl_comp_pushout_symmetry_hom CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom
-/

#print CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom /-
@[simp, reassoc]
theorem inr_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inr ≫ (pushoutSymmetry f g).Hom = pushout.inl :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _
#align category_theory.limits.inr_comp_pushout_symmetry_hom CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom
-/

#print CategoryTheory.Limits.inl_comp_pushoutSymmetry_inv /-
@[simp, reassoc]
theorem inl_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inl ≫ (pushoutSymmetry f g).inv = pushout.inr := by simp [iso.comp_inv_eq]
#align category_theory.limits.inl_comp_pushout_symmetry_inv CategoryTheory.Limits.inl_comp_pushoutSymmetry_inv
-/

#print CategoryTheory.Limits.inr_comp_pushoutSymmetry_inv /-
@[simp, reassoc]
theorem inr_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inr ≫ (pushoutSymmetry f g).inv = pushout.inl := by simp [iso.comp_inv_eq]
#align category_theory.limits.inr_comp_pushout_symmetry_inv CategoryTheory.Limits.inr_comp_pushoutSymmetry_inv
-/

end PushoutSymmetry

section PullbackLeftIso

open WalkingCospan

#print CategoryTheory.Limits.pullbackIsPullbackOfCompMono /-
/-- The pullback of `f, g` is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
noncomputable def pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
    [HasPullback f g] : IsLimit (PullbackCone.mk pullback.fst pullback.snd _) :=
  PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))
#align category_theory.limits.pullback_is_pullback_of_comp_mono CategoryTheory.Limits.pullbackIsPullbackOfCompMono
-/

#print CategoryTheory.Limits.hasPullback_of_comp_mono /-
instance hasPullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    HasPullback (f ≫ i) (g ≫ i) :=
  ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩
#align category_theory.limits.has_pullback_of_comp_mono CategoryTheory.Limits.hasPullback_of_comp_mono
-/

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f]

#print CategoryTheory.Limits.pullbackConeOfLeftIso /-
/-- If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone. -/
def pullbackConeOfLeftIso : PullbackCone f g :=
  PullbackCone.mk (g ≫ inv f) (𝟙 _) <| by simp
#align category_theory.limits.pullback_cone_of_left_iso CategoryTheory.Limits.pullbackConeOfLeftIso
-/

#print CategoryTheory.Limits.pullbackConeOfLeftIso_x /-
@[simp]
theorem pullbackConeOfLeftIso_x : (pullbackConeOfLeftIso f g).pt = Y :=
  rfl
#align category_theory.limits.pullback_cone_of_left_iso_X CategoryTheory.Limits.pullbackConeOfLeftIso_x
-/

#print CategoryTheory.Limits.pullbackConeOfLeftIso_fst /-
@[simp]
theorem pullbackConeOfLeftIso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f :=
  rfl
#align category_theory.limits.pullback_cone_of_left_iso_fst CategoryTheory.Limits.pullbackConeOfLeftIso_fst
-/

#print CategoryTheory.Limits.pullbackConeOfLeftIso_snd /-
@[simp]
theorem pullbackConeOfLeftIso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _ :=
  rfl
#align category_theory.limits.pullback_cone_of_left_iso_snd CategoryTheory.Limits.pullbackConeOfLeftIso_snd
-/

/- warning: category_theory.limits.pullback_cone_of_left_iso_π_app_none -> CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_none is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone_of_left_iso_π_app_none CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_noneₓ'. -/
@[simp]
theorem pullbackConeOfLeftIso_π_app_none : (pullbackConeOfLeftIso f g).π.app none = g :=
  by
  delta pullback_cone_of_left_iso
  simp
#align category_theory.limits.pullback_cone_of_left_iso_π_app_none CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_none

/- warning: category_theory.limits.pullback_cone_of_left_iso_π_app_left -> CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone_of_left_iso_π_app_left CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_leftₓ'. -/
@[simp]
theorem pullbackConeOfLeftIso_π_app_left : (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f :=
  rfl
#align category_theory.limits.pullback_cone_of_left_iso_π_app_left CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_left

/- warning: category_theory.limits.pullback_cone_of_left_iso_π_app_right -> CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone_of_left_iso_π_app_right CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_rightₓ'. -/
@[simp]
theorem pullbackConeOfLeftIso_π_app_right : (pullbackConeOfLeftIso f g).π.app right = 𝟙 _ :=
  rfl
#align category_theory.limits.pullback_cone_of_left_iso_π_app_right CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_right

#print CategoryTheory.Limits.pullbackConeOfLeftIsoIsLimit /-
/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩
#align category_theory.limits.pullback_cone_of_left_iso_is_limit CategoryTheory.Limits.pullbackConeOfLeftIsoIsLimit
-/

#print CategoryTheory.Limits.hasPullback_of_left_iso /-
theorem hasPullback_of_left_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pullback_of_left_iso CategoryTheory.Limits.hasPullback_of_left_iso
-/

attribute [local instance] has_pullback_of_left_iso

#print CategoryTheory.Limits.pullback_snd_iso_of_left_iso /-
instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd : pullback f g ⟶ _) :=
  by
  refine' ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), _, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp [pullback.condition_assoc]
#align category_theory.limits.pullback_snd_iso_of_left_iso CategoryTheory.Limits.pullback_snd_iso_of_left_iso
-/

variable (i : Z ⟶ W) [Mono i]

#print CategoryTheory.Limits.hasPullback_of_right_factors_mono /-
instance hasPullback_of_right_factors_mono (f : X ⟶ Z) : HasPullback i (f ≫ i) :=
  by
  conv =>
    congr
    rw [← category.id_comp i]
  infer_instance
#align category_theory.limits.has_pullback_of_right_factors_mono CategoryTheory.Limits.hasPullback_of_right_factors_mono
-/

#print CategoryTheory.Limits.pullback_snd_iso_of_right_factors_mono /-
instance pullback_snd_iso_of_right_factors_mono (f : X ⟶ Z) :
    IsIso (pullback.snd : pullback i (f ≫ i) ⟶ _) := by
  convert(congr_arg is_iso
            (show _ ≫ pullback.snd = _ from
              limit.iso_limit_cone_hom_π ⟨_, pullback_is_pullback_of_comp_mono (𝟙 _) f i⟩
                walking_cospan.right)).mp
        inferInstance <;>
    exact (category.id_comp _).symm
#align category_theory.limits.pullback_snd_iso_of_right_factors_mono CategoryTheory.Limits.pullback_snd_iso_of_right_factors_mono
-/

end PullbackLeftIso

section PullbackRightIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g]

#print CategoryTheory.Limits.pullbackConeOfRightIso /-
/-- If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone. -/
def pullbackConeOfRightIso : PullbackCone f g :=
  PullbackCone.mk (𝟙 _) (f ≫ inv g) <| by simp
#align category_theory.limits.pullback_cone_of_right_iso CategoryTheory.Limits.pullbackConeOfRightIso
-/

#print CategoryTheory.Limits.pullbackConeOfRightIso_x /-
@[simp]
theorem pullbackConeOfRightIso_x : (pullbackConeOfRightIso f g).pt = X :=
  rfl
#align category_theory.limits.pullback_cone_of_right_iso_X CategoryTheory.Limits.pullbackConeOfRightIso_x
-/

#print CategoryTheory.Limits.pullbackConeOfRightIso_fst /-
@[simp]
theorem pullbackConeOfRightIso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _ :=
  rfl
#align category_theory.limits.pullback_cone_of_right_iso_fst CategoryTheory.Limits.pullbackConeOfRightIso_fst
-/

#print CategoryTheory.Limits.pullbackConeOfRightIso_snd /-
@[simp]
theorem pullbackConeOfRightIso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g :=
  rfl
#align category_theory.limits.pullback_cone_of_right_iso_snd CategoryTheory.Limits.pullbackConeOfRightIso_snd
-/

/- warning: category_theory.limits.pullback_cone_of_right_iso_π_app_none -> CategoryTheory.Limits.pullbackConeOfRightIso_π_app_none is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone_of_right_iso_π_app_none CategoryTheory.Limits.pullbackConeOfRightIso_π_app_noneₓ'. -/
@[simp]
theorem pullbackConeOfRightIso_π_app_none : (pullbackConeOfRightIso f g).π.app none = f :=
  Category.id_comp _
#align category_theory.limits.pullback_cone_of_right_iso_π_app_none CategoryTheory.Limits.pullbackConeOfRightIso_π_app_none

/- warning: category_theory.limits.pullback_cone_of_right_iso_π_app_left -> CategoryTheory.Limits.pullbackConeOfRightIso_π_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone_of_right_iso_π_app_left CategoryTheory.Limits.pullbackConeOfRightIso_π_app_leftₓ'. -/
@[simp]
theorem pullbackConeOfRightIso_π_app_left : (pullbackConeOfRightIso f g).π.app left = 𝟙 _ :=
  rfl
#align category_theory.limits.pullback_cone_of_right_iso_π_app_left CategoryTheory.Limits.pullbackConeOfRightIso_π_app_left

/- warning: category_theory.limits.pullback_cone_of_right_iso_π_app_right -> CategoryTheory.Limits.pullbackConeOfRightIso_π_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pullback_cone_of_right_iso_π_app_right CategoryTheory.Limits.pullbackConeOfRightIso_π_app_rightₓ'. -/
@[simp]
theorem pullbackConeOfRightIso_π_app_right : (pullbackConeOfRightIso f g).π.app right = f ≫ inv g :=
  rfl
#align category_theory.limits.pullback_cone_of_right_iso_π_app_right CategoryTheory.Limits.pullbackConeOfRightIso_π_app_right

#print CategoryTheory.Limits.pullbackConeOfRightIsoIsLimit /-
/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩
#align category_theory.limits.pullback_cone_of_right_iso_is_limit CategoryTheory.Limits.pullbackConeOfRightIsoIsLimit
-/

#print CategoryTheory.Limits.hasPullback_of_right_iso /-
theorem hasPullback_of_right_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pullback_of_right_iso CategoryTheory.Limits.hasPullback_of_right_iso
-/

attribute [local instance] has_pullback_of_right_iso

#print CategoryTheory.Limits.pullback_snd_iso_of_right_iso /-
instance pullback_snd_iso_of_right_iso : IsIso (pullback.fst : pullback f g ⟶ _) :=
  by
  refine' ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), _, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]
#align category_theory.limits.pullback_snd_iso_of_right_iso CategoryTheory.Limits.pullback_snd_iso_of_right_iso
-/

variable (i : Z ⟶ W) [Mono i]

#print CategoryTheory.Limits.hasPullback_of_left_factors_mono /-
instance hasPullback_of_left_factors_mono (f : X ⟶ Z) : HasPullback (f ≫ i) i :=
  by
  conv =>
    congr
    skip
    rw [← category.id_comp i]
  infer_instance
#align category_theory.limits.has_pullback_of_left_factors_mono CategoryTheory.Limits.hasPullback_of_left_factors_mono
-/

#print CategoryTheory.Limits.pullback_snd_iso_of_left_factors_mono /-
instance pullback_snd_iso_of_left_factors_mono (f : X ⟶ Z) :
    IsIso (pullback.fst : pullback (f ≫ i) i ⟶ _) := by
  convert(congr_arg is_iso
            (show _ ≫ pullback.fst = _ from
              limit.iso_limit_cone_hom_π ⟨_, pullback_is_pullback_of_comp_mono f (𝟙 _) i⟩
                walking_cospan.left)).mp
        inferInstance <;>
    exact (category.id_comp _).symm
#align category_theory.limits.pullback_snd_iso_of_left_factors_mono CategoryTheory.Limits.pullback_snd_iso_of_left_factors_mono
-/

end PullbackRightIso

section PushoutLeftIso

open WalkingSpan

#print CategoryTheory.Limits.pushoutIsPushoutOfEpiComp /-
/-- The pushout of `f, g` is also the pullback of `h ≫ f, h ≫ g` for any epi `h`. -/
noncomputable def pushoutIsPushoutOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h]
    [HasPushout f g] : IsColimit (PushoutCocone.mk pushout.inl pushout.inr _) :=
  PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))
#align category_theory.limits.pushout_is_pushout_of_epi_comp CategoryTheory.Limits.pushoutIsPushoutOfEpiComp
-/

#print CategoryTheory.Limits.hasPushout_of_epi_comp /-
instance hasPushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g] :
    HasPushout (h ≫ f) (h ≫ g) :=
  ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩
#align category_theory.limits.has_pushout_of_epi_comp CategoryTheory.Limits.hasPushout_of_epi_comp
-/

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso f]

#print CategoryTheory.Limits.pushoutCoconeOfLeftIso /-
/-- If `f : X ⟶ Y` is iso, then `Y ⨿[X] Z ≅ Z`. This is the explicit colimit cocone. -/
def pushoutCoconeOfLeftIso : PushoutCocone f g :=
  PushoutCocone.mk (inv f ≫ g) (𝟙 _) <| by simp
#align category_theory.limits.pushout_cocone_of_left_iso CategoryTheory.Limits.pushoutCoconeOfLeftIso
-/

#print CategoryTheory.Limits.pushoutCoconeOfLeftIso_x /-
@[simp]
theorem pushoutCoconeOfLeftIso_x : (pushoutCoconeOfLeftIso f g).pt = Z :=
  rfl
#align category_theory.limits.pushout_cocone_of_left_iso_X CategoryTheory.Limits.pushoutCoconeOfLeftIso_x
-/

#print CategoryTheory.Limits.pushoutCoconeOfLeftIso_inl /-
@[simp]
theorem pushoutCoconeOfLeftIso_inl : (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g :=
  rfl
#align category_theory.limits.pushout_cocone_of_left_iso_inl CategoryTheory.Limits.pushoutCoconeOfLeftIso_inl
-/

#print CategoryTheory.Limits.pushoutCoconeOfLeftIso_inr /-
@[simp]
theorem pushoutCoconeOfLeftIso_inr : (pushoutCoconeOfLeftIso f g).inr = 𝟙 _ :=
  rfl
#align category_theory.limits.pushout_cocone_of_left_iso_inr CategoryTheory.Limits.pushoutCoconeOfLeftIso_inr
-/

/- warning: category_theory.limits.pushout_cocone_of_left_iso_ι_app_none -> CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_none is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_none CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_noneₓ'. -/
@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_none : (pushoutCoconeOfLeftIso f g).ι.app none = g :=
  by
  delta pushout_cocone_of_left_iso
  simp
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_none CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_none

/- warning: category_theory.limits.pushout_cocone_of_left_iso_ι_app_left -> CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_left CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_leftₓ'. -/
@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_left : (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g :=
  rfl
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_left CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_left

/- warning: category_theory.limits.pushout_cocone_of_left_iso_ι_app_right -> CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_right CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_rightₓ'. -/
@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_right : (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _ :=
  rfl
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_right CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_right

#print CategoryTheory.Limits.pushoutCoconeOfLeftIsoIsLimit /-
/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfLeftIsoIsLimit : IsColimit (pushoutCoconeOfLeftIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inr, by simp [← s.condition]⟩
#align category_theory.limits.pushout_cocone_of_left_iso_is_limit CategoryTheory.Limits.pushoutCoconeOfLeftIsoIsLimit
-/

#print CategoryTheory.Limits.hasPushout_of_left_iso /-
theorem hasPushout_of_left_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pushout_of_left_iso CategoryTheory.Limits.hasPushout_of_left_iso
-/

attribute [local instance] has_pushout_of_left_iso

#print CategoryTheory.Limits.pushout_inr_iso_of_left_iso /-
instance pushout_inr_iso_of_left_iso : IsIso (pushout.inr : _ ⟶ pushout f g) :=
  by
  refine' ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, _⟩⟩
  ext
  · simp [← pushout.condition]
  · simp [pushout.condition_assoc]
#align category_theory.limits.pushout_inr_iso_of_left_iso CategoryTheory.Limits.pushout_inr_iso_of_left_iso
-/

variable (h : W ⟶ X) [Epi h]

#print CategoryTheory.Limits.hasPushout_of_right_factors_epi /-
instance hasPushout_of_right_factors_epi (f : X ⟶ Y) : HasPushout h (h ≫ f) :=
  by
  conv =>
    congr
    rw [← category.comp_id h]
  infer_instance
#align category_theory.limits.has_pushout_of_right_factors_epi CategoryTheory.Limits.hasPushout_of_right_factors_epi
-/

#print CategoryTheory.Limits.pushout_inr_iso_of_right_factors_epi /-
instance pushout_inr_iso_of_right_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inr : _ ⟶ pushout h (h ≫ f)) := by
  convert(congr_arg is_iso
            (show pushout.inr ≫ _ = _ from
              colimit.iso_colimit_cocone_ι_inv ⟨_, pushout_is_pushout_of_epi_comp (𝟙 _) f h⟩
                walking_span.right)).mp
        inferInstance <;>
    exact (category.comp_id _).symm
#align category_theory.limits.pushout_inr_iso_of_right_factors_epi CategoryTheory.Limits.pushout_inr_iso_of_right_factors_epi
-/

end PushoutLeftIso

section PushoutRightIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso g]

#print CategoryTheory.Limits.pushoutCoconeOfRightIso /-
/-- If `f : X ⟶ Z` is iso, then `Y ⨿[X] Z ≅ Y`. This is the explicit colimit cocone. -/
def pushoutCoconeOfRightIso : PushoutCocone f g :=
  PushoutCocone.mk (𝟙 _) (inv g ≫ f) <| by simp
#align category_theory.limits.pushout_cocone_of_right_iso CategoryTheory.Limits.pushoutCoconeOfRightIso
-/

#print CategoryTheory.Limits.pushoutCoconeOfRightIso_x /-
@[simp]
theorem pushoutCoconeOfRightIso_x : (pushoutCoconeOfRightIso f g).pt = Y :=
  rfl
#align category_theory.limits.pushout_cocone_of_right_iso_X CategoryTheory.Limits.pushoutCoconeOfRightIso_x
-/

#print CategoryTheory.Limits.pushoutCoconeOfRightIso_inl /-
@[simp]
theorem pushoutCoconeOfRightIso_inl : (pushoutCoconeOfRightIso f g).inl = 𝟙 _ :=
  rfl
#align category_theory.limits.pushout_cocone_of_right_iso_inl CategoryTheory.Limits.pushoutCoconeOfRightIso_inl
-/

#print CategoryTheory.Limits.pushoutCoconeOfRightIso_inr /-
@[simp]
theorem pushoutCoconeOfRightIso_inr : (pushoutCoconeOfRightIso f g).inr = inv g ≫ f :=
  rfl
#align category_theory.limits.pushout_cocone_of_right_iso_inr CategoryTheory.Limits.pushoutCoconeOfRightIso_inr
-/

/- warning: category_theory.limits.pushout_cocone_of_right_iso_ι_app_none -> CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_none is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_none CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_noneₓ'. -/
@[simp]
theorem pushoutCoconeOfRightIso_ι_app_none : (pushoutCoconeOfRightIso f g).ι.app none = f :=
  by
  delta pushout_cocone_of_right_iso
  simp
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_none CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_none

/- warning: category_theory.limits.pushout_cocone_of_right_iso_ι_app_left -> CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_left CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_leftₓ'. -/
@[simp]
theorem pushoutCoconeOfRightIso_ι_app_left : (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _ :=
  rfl
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_left CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_left

/- warning: category_theory.limits.pushout_cocone_of_right_iso_ι_app_right -> CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_right CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_rightₓ'. -/
@[simp]
theorem pushoutCoconeOfRightIso_ι_app_right :
    (pushoutCoconeOfRightIso f g).ι.app right = inv g ≫ f :=
  rfl
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_right CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_right

#print CategoryTheory.Limits.pushoutCoconeOfRightIsoIsLimit /-
/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfRightIsoIsLimit : IsColimit (pushoutCoconeOfRightIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inl, by simp [← s.condition]⟩
#align category_theory.limits.pushout_cocone_of_right_iso_is_limit CategoryTheory.Limits.pushoutCoconeOfRightIsoIsLimit
-/

#print CategoryTheory.Limits.hasPushout_of_right_iso /-
theorem hasPushout_of_right_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pushout_of_right_iso CategoryTheory.Limits.hasPushout_of_right_iso
-/

attribute [local instance] has_pushout_of_right_iso

#print CategoryTheory.Limits.pushout_inl_iso_of_right_iso /-
instance pushout_inl_iso_of_right_iso : IsIso (pushout.inl : _ ⟶ pushout f g) :=
  by
  refine' ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, _⟩⟩
  ext
  · simp [← pushout.condition]
  · simp [pushout.condition]
#align category_theory.limits.pushout_inl_iso_of_right_iso CategoryTheory.Limits.pushout_inl_iso_of_right_iso
-/

variable (h : W ⟶ X) [Epi h]

#print CategoryTheory.Limits.hasPushout_of_left_factors_epi /-
instance hasPushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h :=
  by
  conv =>
    congr
    skip
    rw [← category.comp_id h]
  infer_instance
#align category_theory.limits.has_pushout_of_left_factors_epi CategoryTheory.Limits.hasPushout_of_left_factors_epi
-/

#print CategoryTheory.Limits.pushout_inl_iso_of_left_factors_epi /-
instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inl : _ ⟶ pushout (h ≫ f) h) := by
  convert(congr_arg is_iso
            (show pushout.inl ≫ _ = _ from
              colimit.iso_colimit_cocone_ι_inv ⟨_, pushout_is_pushout_of_epi_comp f (𝟙 _) h⟩
                walking_span.left)).mp
        inferInstance <;>
    exact (category.comp_id _).symm
#align category_theory.limits.pushout_inl_iso_of_left_factors_epi CategoryTheory.Limits.pushout_inl_iso_of_left_factors_epi
-/

end PushoutRightIso

section

open WalkingCospan

variable (f : X ⟶ Y)

#print CategoryTheory.Limits.has_kernel_pair_of_mono /-
instance has_kernel_pair_of_mono [Mono f] : HasPullback f f :=
  ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩
#align category_theory.limits.has_kernel_pair_of_mono CategoryTheory.Limits.has_kernel_pair_of_mono
-/

#print CategoryTheory.Limits.fst_eq_snd_of_mono_eq /-
theorem fst_eq_snd_of_mono_eq [Mono f] : (pullback.fst : pullback f f ⟶ _) = pullback.snd :=
  ((PullbackCone.isLimitMkIdId f).fac (getLimitCone (cospan f f)).Cone left).symm.trans
    ((PullbackCone.isLimitMkIdId f).fac (getLimitCone (cospan f f)).Cone right : _)
#align category_theory.limits.fst_eq_snd_of_mono_eq CategoryTheory.Limits.fst_eq_snd_of_mono_eq
-/

#print CategoryTheory.Limits.pullbackSymmetry_hom_of_mono_eq /-
@[simp]
theorem pullbackSymmetry_hom_of_mono_eq [Mono f] : (pullbackSymmetry f f).Hom = 𝟙 _ := by
  ext <;> simp [fst_eq_snd_of_mono_eq]
#align category_theory.limits.pullback_symmetry_hom_of_mono_eq CategoryTheory.Limits.pullbackSymmetry_hom_of_mono_eq
-/

#print CategoryTheory.Limits.fst_iso_of_mono_eq /-
instance fst_iso_of_mono_eq [Mono f] : IsIso (pullback.fst : pullback f f ⟶ _) :=
  by
  refine' ⟨⟨pullback.lift (𝟙 _) (𝟙 _) (by simp), _, by simp⟩⟩
  ext
  · simp
  · simp [fst_eq_snd_of_mono_eq]
#align category_theory.limits.fst_iso_of_mono_eq CategoryTheory.Limits.fst_iso_of_mono_eq
-/

#print CategoryTheory.Limits.snd_iso_of_mono_eq /-
instance snd_iso_of_mono_eq [Mono f] : IsIso (pullback.snd : pullback f f ⟶ _) :=
  by
  rw [← fst_eq_snd_of_mono_eq]
  infer_instance
#align category_theory.limits.snd_iso_of_mono_eq CategoryTheory.Limits.snd_iso_of_mono_eq
-/

end

section

open WalkingSpan

variable (f : X ⟶ Y)

#print CategoryTheory.Limits.has_cokernel_pair_of_epi /-
instance has_cokernel_pair_of_epi [Epi f] : HasPushout f f :=
  ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩
#align category_theory.limits.has_cokernel_pair_of_epi CategoryTheory.Limits.has_cokernel_pair_of_epi
-/

#print CategoryTheory.Limits.inl_eq_inr_of_epi_eq /-
theorem inl_eq_inr_of_epi_eq [Epi f] : (pushout.inl : _ ⟶ pushout f f) = pushout.inr :=
  ((PushoutCocone.isColimitMkIdId f).fac (getColimitCocone (span f f)).Cocone left).symm.trans
    ((PushoutCocone.isColimitMkIdId f).fac (getColimitCocone (span f f)).Cocone right : _)
#align category_theory.limits.inl_eq_inr_of_epi_eq CategoryTheory.Limits.inl_eq_inr_of_epi_eq
-/

#print CategoryTheory.Limits.pullback_symmetry_hom_of_epi_eq /-
@[simp]
theorem pullback_symmetry_hom_of_epi_eq [Epi f] : (pushoutSymmetry f f).Hom = 𝟙 _ := by
  ext <;> simp [inl_eq_inr_of_epi_eq]
#align category_theory.limits.pullback_symmetry_hom_of_epi_eq CategoryTheory.Limits.pullback_symmetry_hom_of_epi_eq
-/

#print CategoryTheory.Limits.inl_iso_of_epi_eq /-
instance inl_iso_of_epi_eq [Epi f] : IsIso (pushout.inl : _ ⟶ pushout f f) :=
  by
  refine' ⟨⟨pushout.desc (𝟙 _) (𝟙 _) (by simp), by simp, _⟩⟩
  ext
  · simp
  · simp [inl_eq_inr_of_epi_eq]
#align category_theory.limits.inl_iso_of_epi_eq CategoryTheory.Limits.inl_iso_of_epi_eq
-/

#print CategoryTheory.Limits.inr_iso_of_epi_eq /-
instance inr_iso_of_epi_eq [Epi f] : IsIso (pushout.inr : _ ⟶ pushout f f) :=
  by
  rw [← inl_eq_inr_of_epi_eq]
  infer_instance
#align category_theory.limits.inr_iso_of_epi_eq CategoryTheory.Limits.inr_iso_of_epi_eq
-/

end

section PasteLemma

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)

variable (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)

variable (h₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (h₂ : i₂ ≫ g₂ = f₂ ≫ i₃)

#print CategoryTheory.Limits.bigSquareIsPullback /-
/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pullback if both the small squares are.
-/
def bigSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' : IsLimit (PullbackCone.mk _ _ h₁)) :
    IsLimit
      (PullbackCone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) :=
  by
  fapply pullback_cone.is_limit_aux'
  intro s
  have : (s.fst ≫ g₁) ≫ g₂ = s.snd ≫ i₃ := by rw [← s.condition, category.assoc]
  rcases pullback_cone.is_limit.lift' H (s.fst ≫ g₁) s.snd this with ⟨l₁, hl₁, hl₁'⟩
  rcases pullback_cone.is_limit.lift' H' s.fst l₁ hl₁.symm with ⟨l₂, hl₂, hl₂'⟩
  use l₂
  use hl₂
  use
    show l₂ ≫ f₁ ≫ f₂ = s.snd by
      rw [← hl₁', ← hl₂', category.assoc]
      rfl
  intro m hm₁ hm₂
  apply pullback_cone.is_limit.hom_ext H'
  · erw [hm₁, hl₂]
  · apply pullback_cone.is_limit.hom_ext H
    · erw [category.assoc, ← h₁, ← category.assoc, hm₁, ← hl₂, category.assoc, category.assoc, h₁]
      rfl
    · erw [category.assoc, hm₂, ← hl₁', ← hl₂']
#align category_theory.limits.big_square_is_pullback CategoryTheory.Limits.bigSquareIsPullback
-/

#print CategoryTheory.Limits.bigSquareIsPushout /-
/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pushout if both the small squares are.
-/
def bigSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₂))
    (H' : IsColimit (PushoutCocone.mk _ _ h₁)) :
    IsColimit
      (PushoutCocone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) :=
  by
  fapply pushout_cocone.is_colimit_aux'
  intro s
  have : i₁ ≫ s.inl = f₁ ≫ f₂ ≫ s.inr := by rw [s.condition, category.assoc]
  rcases pushout_cocone.is_colimit.desc' H' s.inl (f₂ ≫ s.inr) this with ⟨l₁, hl₁, hl₁'⟩
  rcases pushout_cocone.is_colimit.desc' H l₁ s.inr hl₁' with ⟨l₂, hl₂, hl₂'⟩
  use l₂
  use
    show (g₁ ≫ g₂) ≫ l₂ = s.inl by
      rw [← hl₁, ← hl₂, category.assoc]
      rfl
  use hl₂'
  intro m hm₁ hm₂
  apply pushout_cocone.is_colimit.hom_ext H
  · apply pushout_cocone.is_colimit.hom_ext H'
    · erw [← category.assoc, hm₁, hl₂, hl₁]
    · erw [← category.assoc, h₂, category.assoc, hm₂, ← hl₂', ← category.assoc, ← category.assoc, ←
        h₂]
      rfl
  · erw [hm₂, hl₂']
#align category_theory.limits.big_square_is_pushout CategoryTheory.Limits.bigSquareIsPushout
-/

#print CategoryTheory.Limits.leftSquareIsPullback /-
/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the left square is a pullback if the right square and the big square are.
-/
def leftSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' :
      IsLimit
        (PullbackCone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← category.assoc, h₁, category.assoc, h₂, category.assoc]))) :
    IsLimit (PullbackCone.mk _ _ h₁) :=
  by
  fapply pullback_cone.is_limit_aux'
  intro s
  have : s.fst ≫ g₁ ≫ g₂ = (s.snd ≫ f₂) ≫ i₃ := by
    rw [← category.assoc, s.condition, category.assoc, category.assoc, h₂]
  rcases pullback_cone.is_limit.lift' H' s.fst (s.snd ≫ f₂) this with ⟨l₁, hl₁, hl₁'⟩
  use l₁
  use hl₁
  constructor
  · apply pullback_cone.is_limit.hom_ext H
    · erw [category.assoc, ← h₁, ← category.assoc, hl₁, s.condition]
      rfl
    · erw [category.assoc, hl₁']
      rfl
  · intro m hm₁ hm₂
    apply pullback_cone.is_limit.hom_ext H'
    · erw [hm₁, hl₁]
    · erw [hl₁', ← hm₂]
      exact (category.assoc _ _ _).symm
#align category_theory.limits.left_square_is_pullback CategoryTheory.Limits.leftSquareIsPullback
-/

#print CategoryTheory.Limits.rightSquareIsPushout /-
/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/
def rightSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₁))
    (H' :
      IsColimit
        (PushoutCocone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← category.assoc, h₁, category.assoc, h₂, category.assoc]))) :
    IsColimit (PushoutCocone.mk _ _ h₂) :=
  by
  fapply pushout_cocone.is_colimit_aux'
  intro s
  have : i₁ ≫ g₁ ≫ s.inl = (f₁ ≫ f₂) ≫ s.inr := by
    rw [category.assoc, ← s.condition, ← category.assoc, ← category.assoc, h₁]
  rcases pushout_cocone.is_colimit.desc' H' (g₁ ≫ s.inl) s.inr this with ⟨l₁, hl₁, hl₁'⟩
  dsimp at *
  use l₁
  refine' ⟨_, _, _⟩
  · apply pushout_cocone.is_colimit.hom_ext H
    · erw [← category.assoc, hl₁]
      rfl
    · erw [← category.assoc, h₂, category.assoc, hl₁', s.condition]
  · exact hl₁'
  · intro m hm₁ hm₂
    apply pushout_cocone.is_colimit.hom_ext H'
    · erw [hl₁, category.assoc, hm₁]
    · erw [hm₂, hl₁']
#align category_theory.limits.right_square_is_pushout CategoryTheory.Limits.rightSquareIsPushout
-/

end PasteLemma

section

variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)

variable [HasPullback f g] [HasPullback f' (pullback.fst : pullback f g ⟶ _)]

variable [HasPullback (f' ≫ f) g]

#print CategoryTheory.Limits.pullbackRightPullbackFstIso /-
/-- The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y` -/
noncomputable def pullbackRightPullbackFstIso :
    pullback f' (pullback.fst : pullback f g ⟶ _) ≅ pullback (f' ≫ f) g :=
  by
  let this :=
    big_square_is_pullback (pullback.snd : pullback f' (pullback.fst : pullback f g ⟶ _) ⟶ _)
      pullback.snd f' f pullback.fst pullback.fst g pullback.condition pullback.condition
      (pullback_is_pullback _ _) (pullback_is_pullback _ _)
  exact (this.cone_point_unique_up_to_iso (pullback_is_pullback _ _) : _)
#align category_theory.limits.pullback_right_pullback_fst_iso CategoryTheory.Limits.pullbackRightPullbackFstIso
-/

#print CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst /-
@[simp, reassoc]
theorem pullbackRightPullbackFstIso_hom_fst :
    (pullbackRightPullbackFstIso f g f').Hom ≫ pullback.fst = pullback.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left
#align category_theory.limits.pullback_right_pullback_fst_iso_hom_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst
-/

#print CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd /-
@[simp, reassoc]
theorem pullbackRightPullbackFstIso_hom_snd :
    (pullbackRightPullbackFstIso f g f').Hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
#align category_theory.limits.pullback_right_pullback_fst_iso_hom_snd CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd
-/

#print CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst /-
@[simp, reassoc]
theorem pullbackRightPullbackFstIso_inv_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst = pullback.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst
-/

#print CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd /-
@[simp, reassoc]
theorem pullbackRightPullbackFstIso_inv_snd_snd :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_snd_snd CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd
-/

#print CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst /-
@[simp, reassoc]
theorem pullbackRightPullbackFstIso_inv_snd_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ f' :=
  by
  rw [← pullback.condition]
  exact pullback_right_pullback_fst_iso_inv_fst_assoc _ _ _ _
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_snd_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst
-/

end

section

variable (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)

variable [HasPushout f g] [HasPushout (pushout.inr : _ ⟶ pushout f g) g']

variable [HasPushout f (g ≫ g')]

#print CategoryTheory.Limits.pushoutLeftPushoutInrIso /-
/-- The canonical isomorphism `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ×[X] W` -/
noncomputable def pushoutLeftPushoutInrIso :
    pushout (pushout.inr : _ ⟶ pushout f g) g' ≅ pushout f (g ≫ g') :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).coconePointUniqueUpToIso
      (pushoutIsPushout _ _) :
    _)
#align category_theory.limits.pushout_left_pushout_inr_iso CategoryTheory.Limits.pushoutLeftPushoutInrIso
-/

#print CategoryTheory.Limits.inl_pushoutLeftPushoutInrIso_inv /-
@[simp, reassoc]
theorem inl_pushoutLeftPushoutInrIso_inv :
    pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inl ≫ pushout.inl :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).comp_coconePointUniqueUpToIso_inv
      (pushoutIsPushout _ _) WalkingSpan.left :
    _)
#align category_theory.limits.inl_pushout_left_pushout_inr_iso_inv CategoryTheory.Limits.inl_pushoutLeftPushoutInrIso_inv
-/

#print CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_hom /-
@[simp, reassoc]
theorem inr_pushoutLeftPushoutInrIso_hom :
    pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').Hom = pushout.inr :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).comp_coconePointUniqueUpToIso_hom
      (pushoutIsPushout _ _) WalkingSpan.right :
    _)
#align category_theory.limits.inr_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_hom
-/

#print CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_inv /-
@[simp, reassoc]
theorem inr_pushoutLeftPushoutInrIso_inv :
    pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inr := by
  rw [iso.comp_inv_eq, inr_pushout_left_pushout_inr_iso_hom]
#align category_theory.limits.inr_pushout_left_pushout_inr_iso_inv CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_inv
-/

#print CategoryTheory.Limits.inl_inl_pushoutLeftPushoutInrIso_hom /-
@[simp, reassoc]
theorem inl_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inl ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').Hom = pushout.inl := by
  rw [← category.assoc, ← iso.eq_comp_inv, inl_pushout_left_pushout_inr_iso_inv]
#align category_theory.limits.inl_inl_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inl_inl_pushoutLeftPushoutInrIso_hom
-/

#print CategoryTheory.Limits.inr_inl_pushoutLeftPushoutInrIso_hom /-
@[simp, reassoc]
theorem inr_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inr ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').Hom = g' ≫ pushout.inr := by
  rw [← category.assoc, ← iso.eq_comp_inv, category.assoc, inr_pushout_left_pushout_inr_iso_inv,
    pushout.condition]
#align category_theory.limits.inr_inl_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inr_inl_pushoutLeftPushoutInrIso_hom
-/

end

section PullbackAssoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pullbacks.

We can then construct the pullback squares

W  - l₂ -> Z₂ - g₄ -> X₃
|                     |
l₁                    f₄
∨                     ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂

and

W' - l₂' -> Z₂
|           |
l₁'         g₃
∨           ∨
Z₁          X₂
|           |
g₁          f₂
∨           ∨
X₁ -  f₁ -> Y₁

We will show that both `W` and `W'` are pullbacks over `g₁, g₂`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)

variable (f₄ : X₃ ⟶ Y₂) [HasPullback f₁ f₂] [HasPullback f₃ f₄]

include f₁ f₂ f₃ f₄

-- mathport name: exprZ₁
local notation "Z₁" => pullback f₁ f₂

-- mathport name: exprZ₂
local notation "Z₂" => pullback f₃ f₄

-- mathport name: exprg₁
local notation "g₁" => (pullback.fst : Z₁ ⟶ X₁)

-- mathport name: exprg₂
local notation "g₂" => (pullback.snd : Z₁ ⟶ X₂)

-- mathport name: exprg₃
local notation "g₃" => (pullback.fst : Z₂ ⟶ X₂)

-- mathport name: exprg₄
local notation "g₄" => (pullback.snd : Z₂ ⟶ X₃)

-- mathport name: exprW
local notation "W" => pullback (g₂ ≫ f₃) f₄

-- mathport name: exprW'
local notation "W'" => pullback f₁ (g₃ ≫ f₂)

-- mathport name: exprl₁
local notation "l₁" => (pullback.fst : W ⟶ Z₁)

-- mathport name: exprl₂
local notation "l₂" =>
  (pullback.lift (pullback.fst ≫ g₂) pullback.snd
      ((Category.assoc _ _ _).trans pullback.condition) :
    W ⟶ Z₂)

-- mathport name: exprl₁'
local notation "l₁'" =>
  (pullback.lift pullback.fst (pullback.snd ≫ g₃)
      (pullback.condition.trans (Category.assoc _ _ _).symm) :
    W' ⟶ Z₁)

-- mathport name: exprl₂'
local notation "l₂'" => (pullback.snd : W' ⟶ Z₂)

#print CategoryTheory.Limits.pullbackPullbackLeftIsPullback /-
/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullbackPullbackLeftIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit (PullbackCone.mk l₁ l₂ (show l₁ ≫ g₂ = l₂ ≫ g₃ from (pullback.lift_fst _ _ _).symm)) :=
  by
  apply left_square_is_pullback
  exact pullback_is_pullback f₃ f₄
  convert pullback_is_pullback (g₂ ≫ f₃) f₄
  rw [pullback.lift_snd]
#align category_theory.limits.pullback_pullback_left_is_pullback CategoryTheory.Limits.pullbackPullbackLeftIsPullback
-/

#print CategoryTheory.Limits.pullbackAssocIsPullback /-
/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
def pullbackAssocIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit
      (PullbackCone.mk (l₁ ≫ g₁) l₂
        (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ g₃ ≫ f₂ by
          rw [pullback.lift_fst_assoc, category.assoc, category.assoc, pullback.condition])) :=
  by
  apply pullback_cone.flip_is_limit
  apply big_square_is_pullback
  · apply pullback_cone.flip_is_limit
    exact pullback_is_pullback f₁ f₂
  · apply pullback_cone.flip_is_limit
    apply pullback_pullback_left_is_pullback
  · exact pullback.lift_fst _ _ _
  · exact pullback.condition.symm
#align category_theory.limits.pullback_assoc_is_pullback CategoryTheory.Limits.pullbackAssocIsPullback
-/

#print CategoryTheory.Limits.hasPullback_assoc /-
theorem hasPullback_assoc [HasPullback (g₂ ≫ f₃) f₄] : HasPullback f₁ (g₃ ≫ f₂) :=
  ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩
#align category_theory.limits.has_pullback_assoc CategoryTheory.Limits.hasPullback_assoc
-/

#print CategoryTheory.Limits.pullbackPullbackRightIsPullback /-
/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullbackPullbackRightIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit (PullbackCone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃ from pullback.lift_snd _ _ _)) :=
  by
  apply pullback_cone.flip_is_limit
  apply left_square_is_pullback
  · apply pullback_cone.flip_is_limit
    exact pullback_is_pullback f₁ f₂
  · apply pullback_cone.flip_is_limit
    convert pullback_is_pullback f₁ (g₃ ≫ f₂)
    rw [pullback.lift_fst]
  · exact pullback.condition.symm
#align category_theory.limits.pullback_pullback_right_is_pullback CategoryTheory.Limits.pullbackPullbackRightIsPullback
-/

#print CategoryTheory.Limits.pullbackAssocSymmIsPullback /-
/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`. -/
def pullbackAssocSymmIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit
      (PullbackCone.mk l₁' (l₂' ≫ g₄)
        (show l₁' ≫ g₂ ≫ f₃ = (l₂' ≫ g₄) ≫ f₄ by
          rw [pullback.lift_snd_assoc, category.assoc, category.assoc, pullback.condition])) :=
  by
  apply big_square_is_pullback
  exact pullback_is_pullback f₃ f₄
  apply pullback_pullback_right_is_pullback
#align category_theory.limits.pullback_assoc_symm_is_pullback CategoryTheory.Limits.pullbackAssocSymmIsPullback
-/

#print CategoryTheory.Limits.hasPullback_assoc_symm /-
theorem hasPullback_assoc_symm [HasPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) f₄ :=
  ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩
#align category_theory.limits.has_pullback_assoc_symm CategoryTheory.Limits.hasPullback_assoc_symm
-/

variable [HasPullback (g₂ ≫ f₃) f₄] [HasPullback f₁ (g₃ ≫ f₂)]

#print CategoryTheory.Limits.pullbackAssoc /-
/-- The canonical isomorphism `(X₁ ×[Y₁] X₂) ×[Y₂] X₃ ≅ X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
noncomputable def pullbackAssoc :
    pullback (pullback.snd ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
      pullback f₁ (pullback.fst ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
  (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso
    (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)
#align category_theory.limits.pullback_assoc CategoryTheory.Limits.pullbackAssoc
-/

#print CategoryTheory.Limits.pullbackAssoc_inv_fst_fst /-
@[simp, reassoc]
theorem pullbackAssoc_inv_fst_fst :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.fst = pullback.fst :=
  by
  trans l₁' ≫ pullback.fst
  rw [← category.assoc]
  congr 1
  exact is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.left
  exact pullback.lift_fst _ _ _
#align category_theory.limits.pullback_assoc_inv_fst_fst CategoryTheory.Limits.pullbackAssoc_inv_fst_fst
-/

#print CategoryTheory.Limits.pullbackAssoc_hom_fst /-
@[simp, reassoc]
theorem pullbackAssoc_hom_fst :
    (pullbackAssoc f₁ f₂ f₃ f₄).Hom ≫ pullback.fst = pullback.fst ≫ pullback.fst := by
  rw [← iso.eq_inv_comp, pullback_assoc_inv_fst_fst]
#align category_theory.limits.pullback_assoc_hom_fst CategoryTheory.Limits.pullbackAssoc_hom_fst
-/

#print CategoryTheory.Limits.pullbackAssoc_hom_snd_fst /-
@[simp, reassoc]
theorem pullbackAssoc_hom_snd_fst :
    (pullbackAssoc f₁ f₂ f₃ f₄).Hom ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
  by
  trans l₂ ≫ pullback.fst
  rw [← category.assoc]
  congr 1
  exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right
  exact pullback.lift_fst _ _ _
#align category_theory.limits.pullback_assoc_hom_snd_fst CategoryTheory.Limits.pullbackAssoc_hom_snd_fst
-/

#print CategoryTheory.Limits.pullbackAssoc_hom_snd_snd /-
@[simp, reassoc]
theorem pullbackAssoc_hom_snd_snd :
    (pullbackAssoc f₁ f₂ f₃ f₄).Hom ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
  by
  trans l₂ ≫ pullback.snd
  rw [← category.assoc]
  congr 1
  exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right
  exact pullback.lift_snd _ _ _
#align category_theory.limits.pullback_assoc_hom_snd_snd CategoryTheory.Limits.pullbackAssoc_hom_snd_snd
-/

#print CategoryTheory.Limits.pullbackAssoc_inv_fst_snd /-
@[simp, reassoc]
theorem pullbackAssoc_inv_fst_snd :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.fst :=
  by rw [iso.inv_comp_eq, pullback_assoc_hom_snd_fst]
#align category_theory.limits.pullback_assoc_inv_fst_snd CategoryTheory.Limits.pullbackAssoc_inv_fst_snd
-/

#print CategoryTheory.Limits.pullbackAssoc_inv_snd /-
@[simp, reassoc]
theorem pullbackAssoc_inv_snd :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  rw [iso.inv_comp_eq, pullback_assoc_hom_snd_snd]
#align category_theory.limits.pullback_assoc_inv_snd CategoryTheory.Limits.pullbackAssoc_inv_snd
-/

end PullbackAssoc

section PushoutAssoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pushouts.

We can then construct the pushout squares

Z₁ - g₂ -> X₂ - f₃ -> Y₂
|                     |
g₁                    l₂
∨                     ∨
X₁ - f₁ -> Y₁ - l₁ -> W

and

Z₂ - g₄  -> X₃
|           |
g₃          f₄
∨           ∨
X₂          Y₂
|           |
f₂          l₂'
∨           ∨
Y₁ - l₁' -> W'

We will show that both `W` and `W'` are pushouts over `f₂, f₃`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Z₁ Z₂ : C} (g₁ : Z₁ ⟶ X₁) (g₂ : Z₁ ⟶ X₂) (g₃ : Z₂ ⟶ X₂)

variable (g₄ : Z₂ ⟶ X₃) [HasPushout g₁ g₂] [HasPushout g₃ g₄]

include g₁ g₂ g₃ g₄

-- mathport name: exprY₁
local notation "Y₁" => pushout g₁ g₂

-- mathport name: exprY₂
local notation "Y₂" => pushout g₃ g₄

-- mathport name: exprf₁
local notation "f₁" => (pushout.inl : X₁ ⟶ Y₁)

-- mathport name: exprf₂
local notation "f₂" => (pushout.inr : X₂ ⟶ Y₁)

-- mathport name: exprf₃
local notation "f₃" => (pushout.inl : X₂ ⟶ Y₂)

-- mathport name: exprf₄
local notation "f₄" => (pushout.inr : X₃ ⟶ Y₂)

-- mathport name: exprW
local notation "W" => pushout g₁ (g₂ ≫ f₃)

-- mathport name: exprW'
local notation "W'" => pushout (g₃ ≫ f₂) g₄

-- mathport name: exprl₁
local notation "l₁" =>
  (pushout.desc pushout.inl (f₃ ≫ pushout.inr) (pushout.condition.trans (Category.assoc _ _ _)) :
    Y₁ ⟶ W)

-- mathport name: exprl₂
local notation "l₂" => (pushout.inr : Y₂ ⟶ W)

-- mathport name: exprl₁'
local notation "l₁'" => (pushout.inl : Y₁ ⟶ W')

-- mathport name: exprl₂'
local notation "l₂'" =>
  (pushout.desc (f₂ ≫ pushout.inl) pushout.inr
      ((Category.assoc _ _ _).symm.trans pushout.condition) :
    Y₂ ⟶ W')

#print CategoryTheory.Limits.pushoutPushoutLeftIsPushout /-
/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutPushoutLeftIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk l₁' l₂' (show f₂ ≫ l₁' = f₃ ≫ l₂' from (pushout.inl_desc _ _ _).symm)) :=
  by
  apply pushout_cocone.flip_is_colimit
  apply right_square_is_pushout
  · apply pushout_cocone.flip_is_colimit
    exact pushout_is_pushout _ _
  · apply pushout_cocone.flip_is_colimit
    convert pushout_is_pushout (g₃ ≫ f₂) g₄
    exact pushout.inr_desc _ _ _
  · exact pushout.condition.symm
#align category_theory.limits.pushout_pushout_left_is_pushout CategoryTheory.Limits.pushoutPushoutLeftIsPushout
-/

#print CategoryTheory.Limits.pushoutAssocIsPushout /-
/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutAssocIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk (f₁ ≫ l₁') l₂'
        (show g₁ ≫ f₁ ≫ l₁' = (g₂ ≫ f₃) ≫ l₂' by
          rw [category.assoc, pushout.inl_desc, pushout.condition_assoc])) :=
  by
  apply big_square_is_pushout
  · apply pushout_pushout_left_is_pushout
  · exact pushout_is_pushout _ _
#align category_theory.limits.pushout_assoc_is_pushout CategoryTheory.Limits.pushoutAssocIsPushout
-/

#print CategoryTheory.Limits.hasPushout_assoc /-
theorem hasPushout_assoc [HasPushout (g₃ ≫ f₂) g₄] : HasPushout g₁ (g₂ ≫ f₃) :=
  ⟨⟨⟨_, pushoutAssocIsPushout g₁ g₂ g₃ g₄⟩⟩⟩
#align category_theory.limits.has_pushout_assoc CategoryTheory.Limits.hasPushout_assoc
-/

#print CategoryTheory.Limits.pushoutPushoutRightIsPushout /-
/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutPushoutRightIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit (PushoutCocone.mk l₁ l₂ (show f₂ ≫ l₁ = f₃ ≫ l₂ from pushout.inr_desc _ _ _)) :=
  by
  apply right_square_is_pushout
  · exact pushout_is_pushout _ _
  · convert pushout_is_pushout g₁ (g₂ ≫ f₃)
    rw [pushout.inl_desc]
#align category_theory.limits.pushout_pushout_right_is_pushout CategoryTheory.Limits.pushoutPushoutRightIsPushout
-/

#print CategoryTheory.Limits.pushoutAssocSymmIsPushout /-
/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃`. -/
def pushoutAssocSymmIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit
      (PushoutCocone.mk l₁ (f₄ ≫ l₂)
        (show (g₃ ≫ f₂) ≫ l₁ = g₄ ≫ f₄ ≫ l₂ by
          rw [category.assoc, pushout.inr_desc, pushout.condition_assoc])) :=
  by
  apply pushout_cocone.flip_is_colimit
  apply big_square_is_pushout
  · apply pushout_cocone.flip_is_colimit
    apply pushout_pushout_right_is_pushout
  · apply pushout_cocone.flip_is_colimit
    exact pushout_is_pushout _ _
  · exact pushout.condition.symm
  · exact (pushout.inr_desc _ _ _).symm
#align category_theory.limits.pushout_assoc_symm_is_pushout CategoryTheory.Limits.pushoutAssocSymmIsPushout
-/

#print CategoryTheory.Limits.hasPushout_assoc_symm /-
theorem hasPushout_assoc_symm [HasPushout g₁ (g₂ ≫ f₃)] : HasPushout (g₃ ≫ f₂) g₄ :=
  ⟨⟨⟨_, pushoutAssocSymmIsPushout g₁ g₂ g₃ g₄⟩⟩⟩
#align category_theory.limits.has_pushout_assoc_symm CategoryTheory.Limits.hasPushout_assoc_symm
-/

variable [HasPushout (g₃ ≫ f₂) g₄] [HasPushout g₁ (g₂ ≫ f₃)]

#print CategoryTheory.Limits.pushoutAssoc /-
/-- The canonical isomorphism `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃ ≅ X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
noncomputable def pushoutAssoc :
    pushout (g₃ ≫ pushout.inr : _ ⟶ pushout g₁ g₂) g₄ ≅
      pushout g₁ (g₂ ≫ pushout.inl : _ ⟶ pushout g₃ g₄) :=
  (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).coconePointUniqueUpToIso
    (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄)
#align category_theory.limits.pushout_assoc CategoryTheory.Limits.pushoutAssoc
-/

#print CategoryTheory.Limits.inl_inl_pushoutAssoc_hom /-
@[simp, reassoc]
theorem inl_inl_pushoutAssoc_hom :
    pushout.inl ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).Hom = pushout.inl :=
  by
  trans f₁ ≫ l₁
  · congr 1
    exact
      (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        walking_cospan.left
  · exact pushout.inl_desc _ _ _
#align category_theory.limits.inl_inl_pushout_assoc_hom CategoryTheory.Limits.inl_inl_pushoutAssoc_hom
-/

#print CategoryTheory.Limits.inr_inl_pushoutAssoc_hom /-
@[simp, reassoc]
theorem inr_inl_pushoutAssoc_hom :
    pushout.inr ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).Hom = pushout.inl ≫ pushout.inr :=
  by
  trans f₂ ≫ l₁
  · congr 1
    exact
      (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        walking_cospan.left
  · exact pushout.inr_desc _ _ _
#align category_theory.limits.inr_inl_pushout_assoc_hom CategoryTheory.Limits.inr_inl_pushoutAssoc_hom
-/

#print CategoryTheory.Limits.inr_inr_pushoutAssoc_inv /-
@[simp, reassoc]
theorem inr_inr_pushoutAssoc_inv :
    pushout.inr ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr :=
  by
  trans f₄ ≫ l₂'
  · congr 1
    exact
      (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_inv
        (pushout_pushout_right_is_pushout g₁ g₂ g₃ g₄) walking_cospan.right
  · exact pushout.inr_desc _ _ _
#align category_theory.limits.inr_inr_pushout_assoc_inv CategoryTheory.Limits.inr_inr_pushoutAssoc_inv
-/

#print CategoryTheory.Limits.inl_pushoutAssoc_inv /-
@[simp, reassoc]
theorem inl_pushoutAssoc_inv :
    pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inl ≫ pushout.inl := by
  rw [iso.comp_inv_eq, category.assoc, inl_inl_pushout_assoc_hom]
#align category_theory.limits.inl_pushout_assoc_inv CategoryTheory.Limits.inl_pushoutAssoc_inv
-/

#print CategoryTheory.Limits.inl_inr_pushoutAssoc_inv /-
@[simp, reassoc]
theorem inl_inr_pushoutAssoc_inv :
    pushout.inl ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr ≫ pushout.inl := by
  rw [← category.assoc, iso.comp_inv_eq, category.assoc, inr_inl_pushout_assoc_hom]
#align category_theory.limits.inl_inr_pushout_assoc_inv CategoryTheory.Limits.inl_inr_pushoutAssoc_inv
-/

#print CategoryTheory.Limits.inr_pushoutAssoc_hom /-
@[simp, reassoc]
theorem inr_pushoutAssoc_hom :
    pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).Hom = pushout.inr ≫ pushout.inr := by
  rw [← iso.eq_comp_inv, category.assoc, inr_inr_pushout_assoc_inv]
#align category_theory.limits.inr_pushout_assoc_hom CategoryTheory.Limits.inr_pushoutAssoc_hom
-/

end PushoutAssoc

variable (C)

#print CategoryTheory.Limits.HasPullbacks /-
/-- `has_pullbacks` represents a choice of pullback for every pair of morphisms

See <https://stacks.math.columbia.edu/tag/001W>
-/
abbrev HasPullbacks :=
  HasLimitsOfShape WalkingCospan C
#align category_theory.limits.has_pullbacks CategoryTheory.Limits.HasPullbacks
-/

#print CategoryTheory.Limits.HasPushouts /-
/-- `has_pushouts` represents a choice of pushout for every pair of morphisms -/
abbrev HasPushouts :=
  HasColimitsOfShape WalkingSpan C
#align category_theory.limits.has_pushouts CategoryTheory.Limits.HasPushouts
-/

#print CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan /-
/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
theorem hasPullbacks_of_hasLimit_cospan
    [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g)] : HasPullbacks C :=
  { HasLimit := fun F => hasLimitOfIso (diagramIsoCospan F).symm }
#align category_theory.limits.has_pullbacks_of_has_limit_cospan CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan
-/

#print CategoryTheory.Limits.hasPushouts_of_hasColimit_span /-
/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
theorem hasPushouts_of_hasColimit_span
    [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g)] : HasPushouts C :=
  { HasColimit := fun F => hasColimitOfIso (diagramIsoSpan F) }
#align category_theory.limits.has_pushouts_of_has_colimit_span CategoryTheory.Limits.hasPushouts_of_hasColimit_span
-/

/- warning: category_theory.limits.walking_span_op_equiv -> CategoryTheory.Limits.walkingSpanOpEquiv is a dubious translation:
lean 3 declaration is
  CategoryTheory.Equivalence.{0, 0, 0, 0} (Opposite.{1} CategoryTheory.Limits.WalkingSpan) (CategoryTheory.Category.opposite.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair)) CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair)
but is expected to have type
  CategoryTheory.Equivalence.{0, 0, 0, 0} (Opposite.{1} CategoryTheory.Limits.WalkingSpan) CategoryTheory.Limits.WalkingCospan (CategoryTheory.Category.opposite.{0, 0} CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair)) (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.walking_span_op_equiv CategoryTheory.Limits.walkingSpanOpEquivₓ'. -/
/-- The duality equivalence `walking_spanᵒᵖ ≌ walking_cospan` -/
@[simps]
def walkingSpanOpEquiv : WalkingSpanᵒᵖ ≌ WalkingCospan :=
  widePushoutShapeOpEquiv _
#align category_theory.limits.walking_span_op_equiv CategoryTheory.Limits.walkingSpanOpEquiv

/- warning: category_theory.limits.walking_cospan_op_equiv -> CategoryTheory.Limits.walkingCospanOpEquiv is a dubious translation:
lean 3 declaration is
  CategoryTheory.Equivalence.{0, 0, 0, 0} (Opposite.{1} CategoryTheory.Limits.WalkingCospan) (CategoryTheory.Category.opposite.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair)) CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair)
but is expected to have type
  CategoryTheory.Equivalence.{0, 0, 0, 0} (Opposite.{1} CategoryTheory.Limits.WalkingCospan) CategoryTheory.Limits.WalkingSpan (CategoryTheory.Category.opposite.{0, 0} CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair)) (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.walking_cospan_op_equiv CategoryTheory.Limits.walkingCospanOpEquivₓ'. -/
/-- The duality equivalence `walking_cospanᵒᵖ ≌ walking_span` -/
@[simps]
def walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan :=
  widePullbackShapeOpEquiv _
#align category_theory.limits.walking_cospan_op_equiv CategoryTheory.Limits.walkingCospanOpEquiv

#print CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks /-
-- see Note [lower instance priority]
/-- Having wide pullback at any universe level implies having binary pullbacks. -/
instance (priority := 100) hasPullbacks_of_hasWidePullbacks [HasWidePullbacks.{w} C] :
    HasPullbacks C := by
  haveI := hasWidePullbacks_shrink.{0, w} C
  infer_instance
#align category_theory.limits.has_pullbacks_of_has_wide_pullbacks CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks
-/

variable {C}

#print CategoryTheory.Limits.baseChange /-
/-- Given a morphism `f : X ⟶ Y`, we can take morphisms over `Y` to morphisms over `X` via
pullbacks. This is right adjoint to `over.map` (TODO) -/
@[simps (config :=
      { rhsMd := semireducible
        simpRhs := true }) obj_left obj_hom mapLeft]
def baseChange [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Over Y ⥤ Over X
    where
  obj g := Over.mk (pullback.snd : pullback g.Hom f ⟶ _)
  map g₁ g₂ i := Over.homMk (pullback.map _ _ _ _ i.left (𝟙 _) (𝟙 _) (by simp) (by simp)) (by simp)
#align category_theory.limits.base_change CategoryTheory.Limits.baseChange
-/

end CategoryTheory.Limits

