/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module combinatorics.quiver.subquiver
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.BoundedOrder
import Mathbin.Combinatorics.Quiver.Basic

/-!
## Wide subquivers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A wide subquiver `H` of a quiver `H` consists of a subset of the edge set `a ⟶ b` for
every pair of vertices `a b : V`. We include 'wide' in the name to emphasize that these
subquivers by definition contain all vertices.
-/


universe v u

#print WideSubquiver /-
/-- A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
    for every pair of vertices `a b`.

    NB: this does not work for `Prop`-valued quivers. It requires `G : quiver.{v+1} V`. -/
def WideSubquiver (V) [Quiver.{v + 1} V] :=
  ∀ a b : V, Set (a ⟶ b)
#align wide_subquiver WideSubquiver
-/

#print WideSubquiver.toType /-
/-- A type synonym for `V`, when thought of as a quiver having only the arrows from
some `wide_subquiver`. -/
@[nolint unused_arguments has_nonempty_instance]
def WideSubquiver.toType (V) [Quiver V] (H : WideSubquiver V) : Type u :=
  V
#align wide_subquiver.to_Type WideSubquiver.toType
-/

#print wideSubquiverHasCoeToSort /-
instance wideSubquiverHasCoeToSort {V} [Quiver V] : CoeSort (WideSubquiver V) (Type u)
    where coe H := WideSubquiver.toType V H
#align wide_subquiver_has_coe_to_sort wideSubquiverHasCoeToSort
-/

#print WideSubquiver.quiver /-
/-- A wide subquiver viewed as a quiver on its own. -/
instance WideSubquiver.quiver {V} [Quiver V] (H : WideSubquiver V) : Quiver H :=
  ⟨fun a b => { f // f ∈ H a b }⟩
#align wide_subquiver.quiver WideSubquiver.quiver
-/

namespace Quiver

instance {V} [Quiver V] : Bot (WideSubquiver V) :=
  ⟨fun a b => ∅⟩

instance {V} [Quiver V] : Top (WideSubquiver V) :=
  ⟨fun a b => Set.univ⟩

instance {V} [Quiver V] : Inhabited (WideSubquiver V) :=
  ⟨⊤⟩

#print Quiver.Total /-
-- TODO Unify with `category_theory.arrow`? (The fields have been named to match.)
/-- `total V` is the type of _all_ arrows of `V`. -/
@[ext, nolint has_nonempty_instance]
structure Total (V : Type u) [Quiver.{v} V] : Sort max (u + 1) v where
  left : V
  right : V
  Hom : left ⟶ right
#align quiver.total Quiver.Total
-/

#print Quiver.wideSubquiverEquivSetTotal /-
/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
def wideSubquiverEquivSetTotal {V} [Quiver V] : WideSubquiver V ≃ Set (Total V)
    where
  toFun H := { e | e.Hom ∈ H e.left e.right }
  invFun S a b := { e | Total.mk a b e ∈ S }
  left_inv H := rfl
  right_inv := by
    intro S
    ext
    cases x
    rfl
#align quiver.wide_subquiver_equiv_set_total Quiver.wideSubquiverEquivSetTotal
-/

#print Quiver.Labelling /-
/-- An `L`-labelling of a quiver assigns to every arrow an element of `L`. -/
def Labelling (V : Type u) [Quiver V] (L : Sort _) :=
  ∀ ⦃a b : V⦄, (a ⟶ b) → L
#align quiver.labelling Quiver.Labelling
-/

instance {V : Type u} [Quiver V] (L) [Inhabited L] : Inhabited (Labelling V L) :=
  ⟨fun a b e => default⟩

end Quiver

