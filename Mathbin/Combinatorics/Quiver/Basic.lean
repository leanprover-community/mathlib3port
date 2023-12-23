/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import Data.Opposite

#align_import combinatorics.quiver.basic from "leanprover-community/mathlib"@"56adee5b5eef9e734d82272918300fca4f3e7cef"

/-!
# Quivers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.

## Implementation notes

Currently `quiver` is defined with `arrow : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/


open Opposite

-- We use the same universe order as in category theory.
-- See note [category_theory universes]
universe v v₁ v₂ u u₁ u₂

#print Quiver /-
/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `category` will later extend this class, we call the field `hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class Quiver (V : Type u) where
  Hom : V → V → Sort v
#align quiver Quiver
-/

infixr:10 " ⟶ " => Quiver.Hom

#print Prefunctor /-
/- ./././Mathport/Syntax/Translate/Command.lean:404:30: infer kinds are unsupported in Lean 4: #[`obj] [] -/
-- type as \h
/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)
#align prefunctor Prefunctor
-/

namespace Prefunctor

#print Prefunctor.ext /-
@[ext]
theorem ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map :
      ∀ (X Y : V) (f : X ⟶ Y),
        F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) :
    F = G := by
  cases' F with F_obj _; cases' G with G_obj _
  obtain rfl : F_obj = G_obj := by ext X; apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f
#align prefunctor.ext Prefunctor.ext
-/

#print Prefunctor.id /-
/-- The identity morphism between quivers.
-/
@[simps]
def id (V : Type _) [Quiver V] : Prefunctor V V
    where
  obj := id
  map X Y f := f
#align prefunctor.id Prefunctor.id
-/

instance (V : Type _) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

#print Prefunctor.comp /-
/-- Composition of morphisms between quivers.
-/
@[simps]
def comp {U : Type _} [Quiver U] {V : Type _} [Quiver V] {W : Type _} [Quiver W]
    (F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W
    where
  obj X := G.obj (F.obj X)
  map X Y f := G.map (F.map f)
#align prefunctor.comp Prefunctor.comp
-/

#print Prefunctor.comp_id /-
@[simp]
theorem comp_id {U : Type _} [Quiver U] {V : Type _} [Quiver V] (F : Prefunctor U V) :
    F.comp (id _) = F := by cases F; rfl
#align prefunctor.comp_id Prefunctor.comp_id
-/

#print Prefunctor.id_comp /-
@[simp]
theorem id_comp {U : Type _} [Quiver U] {V : Type _} [Quiver V] (F : Prefunctor U V) :
    (id _).comp F = F := by cases F; rfl
#align prefunctor.id_comp Prefunctor.id_comp
-/

#print Prefunctor.comp_assoc /-
@[simp]
theorem comp_assoc {U V W Z : Type _} [Quiver U] [Quiver V] [Quiver W] [Quiver Z]
    (F : Prefunctor U V) (G : Prefunctor V W) (H : Prefunctor W Z) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  rfl
#align prefunctor.comp_assoc Prefunctor.comp_assoc
-/

infixl:50 " ⥤q " => Prefunctor

infixl:60 " ⋙q " => Prefunctor.comp

notation "𝟭q" => id

end Prefunctor

namespace Quiver

#print Quiver.opposite /-
/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => unop b ⟶ unop a⟩
#align quiver.opposite Quiver.opposite
-/

#print Quiver.Hom.op /-
/-- The opposite of an arrow in `V`.
-/
def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X :=
  f
#align quiver.hom.op Quiver.Hom.op
-/

#print Quiver.Hom.unop /-
/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X :=
  f
#align quiver.hom.unop Quiver.Hom.unop
-/

#print Quiver.Empty /-
/-- A type synonym for a quiver with no arrows. -/
@[nolint has_nonempty_instance]
def Empty (V) : Type u :=
  V
#align quiver.empty Quiver.Empty
-/

#print Quiver.emptyQuiver /-
instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) :=
  ⟨fun a b => PEmpty⟩
#align quiver.empty_quiver Quiver.emptyQuiver
-/

#print Quiver.empty_arrow /-
@[simp]
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = PEmpty :=
  rfl
#align quiver.empty_arrow Quiver.empty_arrow
-/

#print Quiver.IsThin /-
/-- A quiver is thin if it has no parallel arrows. -/
@[reducible]
def IsThin (V : Type u) [Quiver V] :=
  ∀ a b : V, Subsingleton (a ⟶ b)
#align quiver.is_thin Quiver.IsThin
-/

end Quiver

