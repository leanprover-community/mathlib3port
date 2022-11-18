/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import Mathbin.Data.Opposite

/-!
# Quivers

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

-- mathport name: «expr ⟶ »
infixr:10 " ⟶ " => Quiver.Hom

/- ./././Mathport/Syntax/Translate/Command.lean:347:30: infer kinds are unsupported in Lean 4: #[`obj] [] -/
-- type as \h
/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)
#align prefunctor Prefunctor

namespace Prefunctor

@[ext.1]
theorem ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y), F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G :=
  by
  cases' F with F_obj _
  cases' G with G_obj _
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f
#align prefunctor.ext Prefunctor.ext

/-- The identity morphism between quivers.
-/
@[simps]
def id (V : Type _) [Quiver V] : Prefunctor V V where
  obj := id
  map X Y f := f
#align prefunctor.id Prefunctor.id

instance (V : Type _) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

/-- Composition of morphisms between quivers.
-/
@[simps]
def comp {U : Type _} [Quiver U] {V : Type _} [Quiver V] {W : Type _} [Quiver W] (F : Prefunctor U V)
    (G : Prefunctor V W) : Prefunctor U W where
  obj X := G.obj (F.obj X)
  map X Y f := G.map (F.map f)
#align prefunctor.comp Prefunctor.comp

@[simp]
theorem comp_assoc {U V W Z : Type _} [Quiver U] [Quiver V] [Quiver W] [Quiver Z] (F : Prefunctor U V)
    (G : Prefunctor V W) (H : Prefunctor W Z) : (F.comp G).comp H = F.comp (G.comp H) := by
  apply Prefunctor.ext
  rotate_left
  · rintro X
    rfl
    
  · rintro X Y Z
    rfl
    
#align prefunctor.comp_assoc Prefunctor.comp_assoc

end Prefunctor

namespace Quiver

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => unop b ⟶ unop a⟩
#align quiver.opposite Quiver.opposite

/-- The opposite of an arrow in `V`.
-/
def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X :=
  f
#align quiver.hom.op Quiver.Hom.op

/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X :=
  f
#align quiver.hom.unop Quiver.Hom.unop

/-- A type synonym for a quiver with no arrows. -/
@[nolint has_nonempty_instance]
def Empty (V) : Type u :=
  V
#align quiver.empty Quiver.Empty

instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) :=
  ⟨fun a b => PEmpty⟩
#align quiver.empty_quiver Quiver.emptyQuiver

@[simp]
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = PEmpty :=
  rfl
#align quiver.empty_arrow Quiver.empty_arrow

/-- A quiver is thin if it has no parallel arrows. -/
@[reducible]
def IsThin (V : Type u) [Quiver V] :=
  ∀ a b : V, Subsingleton (a ⟶ b)
#align quiver.is_thin Quiver.IsThin

end Quiver

