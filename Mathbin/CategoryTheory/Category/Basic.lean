/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton

! This file was ported from Lean 3 source module category_theory.category.basic
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Basic

/-!
# Categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Defines a category, as a type class parametrised by the type of objects.

## Notations

Introduces notations
* `X ⟶ Y` for the morphism spaces (type as `\hom`),
* `𝟙 X` for the identity morphism on `X` (type as `\b1`),
* `f ≫ g` for composition in the 'arrows' convention (type as `\gg`).

Users may like to add `f ⊚ g` for composition in the standard convention, using
```lean
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/


library_note "category_theory universes"/--
The typeclass `category C` describes morphisms associated to objects of type `C : Type u`.

The universe levels of the objects and morphisms are independent, and will often need to be
specified explicitly, as `category.{v} C`.

Typically any concrete example will either be a `small_category`, where `v = u`,
which can be introduced as
```
universes u
variables {C : Type u} [small_category C]
```
or a `large_category`, where `u = v+1`, which can be introduced as
```
universes u
variables {C : Type (u+1)} [large_category C]
```

In order for the library to handle these cases uniformly,
we generally work with the unconstrained `category.{v u}`,
for which objects live in `Type u` and morphisms live in `Type v`.

Because the universe parameter `u` for the objects can be inferred from `C`
when we write `category C`, while the universe parameter `v` for the morphisms
can not be automatically inferred, through the category theory library
we introduce universe parameters with morphism levels listed first,
as in
```
universes v u
```
or
```
universes v₁ v₂ u₁ u₂
```
when multiple independent universes are needed.

This has the effect that we can simply write `category.{v} C`
(that is, only specifying a single parameter) while `u` will be inferred.

Often, however, it's not even necessary to include the `.{v}`.
(Although it was in earlier versions of Lean.)
If it is omitted a "free" universe will be used.
-/


universe v u

namespace CategoryTheory

#print CategoryTheory.CategoryStruct /-
/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  id : ∀ X : obj, hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
#align category_theory.category_struct CategoryTheory.CategoryStruct
-/

-- mathport name: «expr𝟙»
notation "𝟙" => CategoryStruct.id

-- mathport name: «expr ≫ »
infixr:80
  " ≫ " =>-- type as \b1
  CategoryStruct.comp

#print CategoryTheory.Category /-
-- type as \gg
/-- The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `category.{v} C`. (See also `large_category` and `small_category`.)

See <https://stacks.math.columbia.edu/tag/0014>.
-/
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  id_comp' : ∀ {X Y : obj} (f : hom X Y), 𝟙 X ≫ f = f := by obviously
  comp_id' : ∀ {X Y : obj} (f : hom X Y), f ≫ 𝟙 Y = f := by obviously
  assoc' :
    ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    obviously
#align category_theory.category CategoryTheory.Category
-/

-- `restate_axiom` is a command that creates a lemma from a structure field,
-- discarding any auto_param wrappers from the type.
-- (It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".)
restate_axiom category.id_comp'

restate_axiom category.comp_id'

restate_axiom category.assoc'

attribute [simp] category.id_comp category.comp_id category.assoc

attribute [trans] category_struct.comp

#print CategoryTheory.LargeCategory /-
/-- A `large_category` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) :=
  Category.{u} C
#align category_theory.large_category CategoryTheory.LargeCategory
-/

#print CategoryTheory.SmallCategory /-
/-- A `small_category` has objects and morphisms in the same universe level.
-/
abbrev SmallCategory (C : Type u) : Type (u + 1) :=
  Category.{u} C
#align category_theory.small_category CategoryTheory.SmallCategory
-/

section

variable {C : Type u} [Category.{v} C] {X Y Z : C}

initialize_simps_projections category (to_category_struct_to_quiver_hom → Hom,
  to_category_struct_comp → comp, to_category_struct_id → id, -toCategoryStruct)

#print CategoryTheory.eq_whisker /-
/-- postcompose an equation between morphisms by another morphism -/
theorem eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h := by rw [w]
#align category_theory.eq_whisker CategoryTheory.eq_whisker
-/

#print CategoryTheory.whisker_eq /-
/-- precompose an equation between morphisms by another morphism -/
theorem whisker_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h := by rw [w]
#align category_theory.whisker_eq CategoryTheory.whisker_eq
-/

-- mathport name: «expr =≫ »
infixr:80 " =≫ " => eq_whisker

-- mathport name: «expr ≫= »
infixr:80 " ≫= " => whisker_eq

#print CategoryTheory.eq_of_comp_left_eq /-
theorem eq_of_comp_left_eq {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g :=
  by
  convert w (𝟙 Y)
  tidy
#align category_theory.eq_of_comp_left_eq CategoryTheory.eq_of_comp_left_eq
-/

#print CategoryTheory.eq_of_comp_right_eq /-
theorem eq_of_comp_right_eq {f g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) : f = g :=
  by
  convert w (𝟙 Y)
  tidy
#align category_theory.eq_of_comp_right_eq CategoryTheory.eq_of_comp_right_eq
-/

#print CategoryTheory.eq_of_comp_left_eq' /-
theorem eq_of_comp_left_eq' (f g : X ⟶ Y)
    (w : (fun {Z : C} (h : Y ⟶ Z) => f ≫ h) = fun {Z : C} (h : Y ⟶ Z) => g ≫ h) : f = g :=
  eq_of_comp_left_eq fun Z h => by convert congr_fun (congr_fun w Z) h
#align category_theory.eq_of_comp_left_eq' CategoryTheory.eq_of_comp_left_eq'
-/

#print CategoryTheory.eq_of_comp_right_eq' /-
theorem eq_of_comp_right_eq' (f g : Y ⟶ Z)
    (w : (fun {X : C} (h : X ⟶ Y) => h ≫ f) = fun {X : C} (h : X ⟶ Y) => h ≫ g) : f = g :=
  eq_of_comp_right_eq fun X h => by convert congr_fun (congr_fun w X) h
#align category_theory.eq_of_comp_right_eq' CategoryTheory.eq_of_comp_right_eq'
-/

#print CategoryTheory.id_of_comp_left_id /-
theorem id_of_comp_left_id (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X :=
  by
  convert w (𝟙 X)
  tidy
#align category_theory.id_of_comp_left_id CategoryTheory.id_of_comp_left_id
-/

#print CategoryTheory.id_of_comp_right_id /-
theorem id_of_comp_right_id (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X :=
  by
  convert w (𝟙 X)
  tidy
#align category_theory.id_of_comp_right_id CategoryTheory.id_of_comp_right_id
-/

#print CategoryTheory.comp_ite /-
theorem comp_ite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' := by split_ifs <;> rfl
#align category_theory.comp_ite CategoryTheory.comp_ite
-/

#print CategoryTheory.ite_comp /-
theorem ite_comp {P : Prop} [Decidable P] {X Y Z : C} (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (if P then f else f') ≫ g = if P then f ≫ g else f' ≫ g := by split_ifs <;> rfl
#align category_theory.ite_comp CategoryTheory.ite_comp
-/

#print CategoryTheory.comp_dite /-
theorem comp_dite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ≫ if h : P then g h else g' h) = if h : P then f ≫ g h else f ≫ g' h :=
  by split_ifs <;> rfl
#align category_theory.comp_dite CategoryTheory.comp_dite
-/

#print CategoryTheory.dite_comp /-
theorem dite_comp {P : Prop} [Decidable P] {X Y Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y))
    (g : Y ⟶ Z) : (if h : P then f h else f' h) ≫ g = if h : P then f h ≫ g else f' h ≫ g := by
  split_ifs <;> rfl
#align category_theory.dite_comp CategoryTheory.dite_comp
-/

#print CategoryTheory.Epi /-
/-- A morphism `f` is an epimorphism if it can be "cancelled" when precomposed:
`f ≫ g = f ≫ h` implies `g = h`.

See <https://stacks.math.columbia.edu/tag/003B>.
-/
class Epi (f : X ⟶ Y) : Prop where
  left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h
#align category_theory.epi CategoryTheory.Epi
-/

#print CategoryTheory.Mono /-
/-- A morphism `f` is a monomorphism if it can be "cancelled" when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`.

See <https://stacks.math.columbia.edu/tag/003B>.
-/
class Mono (f : X ⟶ Y) : Prop where
  right_cancellation : ∀ {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h
#align category_theory.mono CategoryTheory.Mono
-/

instance (X : C) : Epi (𝟙 X) :=
  ⟨fun Z g h w => by simpa using w⟩

instance (X : C) : Mono (𝟙 X) :=
  ⟨fun Z g h w => by simpa using w⟩

#print CategoryTheory.cancel_epi /-
theorem cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} : f ≫ g = f ≫ h ↔ g = h :=
  ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩
#align category_theory.cancel_epi CategoryTheory.cancel_epi
-/

#print CategoryTheory.cancel_mono /-
theorem cancel_mono (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X} : g ≫ f = h ≫ f ↔ g = h :=
  ⟨fun p => Mono.right_cancellation g h p, congr_arg _⟩
#align category_theory.cancel_mono CategoryTheory.cancel_mono
-/

#print CategoryTheory.cancel_epi_id /-
theorem cancel_epi_id (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y} : f ≫ h = f ↔ h = 𝟙 Y :=
  by
  convert cancel_epi f
  simp
#align category_theory.cancel_epi_id CategoryTheory.cancel_epi_id
-/

#print CategoryTheory.cancel_mono_id /-
theorem cancel_mono_id (f : X ⟶ Y) [Mono f] {g : X ⟶ X} : g ≫ f = f ↔ g = 𝟙 X :=
  by
  convert cancel_mono f
  simp
#align category_theory.cancel_mono_id CategoryTheory.cancel_mono_id
-/

#print CategoryTheory.epi_comp /-
theorem epi_comp {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g] : Epi (f ≫ g) :=
  by
  constructor; intro Z a b w
  apply (cancel_epi g).1
  apply (cancel_epi f).1
  simpa using w
#align category_theory.epi_comp CategoryTheory.epi_comp
-/

#print CategoryTheory.mono_comp /-
theorem mono_comp {X Y Z : C} (f : X ⟶ Y) [Mono f] (g : Y ⟶ Z) [Mono g] : Mono (f ≫ g) :=
  by
  constructor; intro Z a b w
  apply (cancel_mono f).1
  apply (cancel_mono g).1
  simpa using w
#align category_theory.mono_comp CategoryTheory.mono_comp
-/

#print CategoryTheory.mono_of_mono /-
theorem mono_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono (f ≫ g)] : Mono f :=
  by
  constructor; intro Z a b w
  replace w := congr_arg (fun k => k ≫ g) w
  dsimp at w
  rw [category.assoc, category.assoc] at w
  exact (cancel_mono _).1 w
#align category_theory.mono_of_mono CategoryTheory.mono_of_mono
-/

#print CategoryTheory.mono_of_mono_fac /-
theorem mono_of_mono_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Mono h] (w : f ≫ g = h) :
    Mono f := by
  subst h
  exact mono_of_mono f g
#align category_theory.mono_of_mono_fac CategoryTheory.mono_of_mono_fac
-/

#print CategoryTheory.epi_of_epi /-
theorem epi_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g :=
  by
  constructor; intro Z a b w
  replace w := congr_arg (fun k => f ≫ k) w
  dsimp at w
  rw [← category.assoc, ← category.assoc] at w
  exact (cancel_epi _).1 w
#align category_theory.epi_of_epi CategoryTheory.epi_of_epi
-/

#print CategoryTheory.epi_of_epi_fac /-
theorem epi_of_epi_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h] (w : f ≫ g = h) :
    Epi g := by subst h <;> exact epi_of_epi f g
#align category_theory.epi_of_epi_fac CategoryTheory.epi_of_epi_fac
-/

end

section

variable (C : Type u)

variable [Category.{v} C]

universe u'

#print CategoryTheory.uliftCategory /-
instance uliftCategory : Category.{v} (ULift.{u'} C)
    where
  Hom X Y := X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp _ _ _ f g := f ≫ g
#align category_theory.ulift_category CategoryTheory.uliftCategory
-/

-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := by infer_instance

end

end CategoryTheory

library_note "dsimp, simp"/--
Many proofs in the category theory library use the `dsimp, simp` pattern,
which typically isn't necessary elsewhere.

One would usually hope that the same effect could be achieved simply with `simp`.

The essential issue is that composition of morphisms involves dependent types.
When you have a chain of morphisms being composed, say `f : X ⟶ Y` and `g : Y ⟶ Z`,
then `simp` can operate succesfully on the morphisms
(e.g. if `f` is the identity it can strip that off).

However if we have an equality of objects, say `Y = Y'`,
then `simp` can't operate because it would break the typing of the composition operations.
We rarely have interesting equalities of objects
(because that would be "evil" --- anything interesting should be expressed as an isomorphism
and tracked explicitly),
except of course that we have plenty of definitional equalities of objects.

`dsimp` can apply these safely, even inside a composition.

After `dsimp` has cleared up the object level, `simp` can resume work on the morphism level ---
but without the `dsimp` step, because `simp` looks at expressions syntactically,
the relevant lemmas might not fire.

There's no bound on how many times you potentially could have to switch back and forth,
if the `simp` introduced new objects we again need to `dsimp`.
In practice this does occur, but only rarely, because `simp` tends to shorten chains of compositions
(i.e. not introduce new objects at all).
-/


