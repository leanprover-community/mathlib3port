/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module combinatorics.quiver.connected_component
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Subquiver
import Mathbin.Combinatorics.Quiver.Path
import Mathbin.Combinatorics.Quiver.Symmetric

/-!
## Weakly connected components

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


For a quiver `V`, we define the type `weakly_connected_component V` as the quotient of `V`
by the relation which identifies `a` with `b` if there is a path from `a` to `b` in `symmetrify V`.
(These zigzags can be seen as a proof-relevant analogue of `eqv_gen`.)

Strongly connected components have not yet been defined.
-/


universe u

namespace Quiver

variable (V : Type _) [Quiver.{u + 1} V]

#print Quiver.zigzagSetoid /-
/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzagSetoid : Setoid V :=
  ⟨fun a b => Nonempty (@Path (Symmetrify V) _ a b), fun a => ⟨Path.nil⟩, fun a b ⟨p⟩ =>
    ⟨p.reverse⟩, fun a b c ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩⟩
#align quiver.zigzag_setoid Quiver.zigzagSetoid
-/

#print Quiver.WeaklyConnectedComponent /-
/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def WeaklyConnectedComponent : Type _ :=
  Quotient (zigzagSetoid V)
#align quiver.weakly_connected_component Quiver.WeaklyConnectedComponent
-/

namespace WeaklyConnectedComponent

variable {V}

#print Quiver.WeaklyConnectedComponent.mk /-
/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → WeaklyConnectedComponent V :=
  Quotient.mk'
#align quiver.weakly_connected_component.mk Quiver.WeaklyConnectedComponent.mk
-/

instance : CoeTC V (WeaklyConnectedComponent V) :=
  ⟨WeaklyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (WeaklyConnectedComponent V) :=
  ⟨show V from default⟩

/- warning: quiver.weakly_connected_component.eq -> Quiver.WeaklyConnectedComponent.eq is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} V] (a : V) (b : V), Iff (Eq.{succ u2} (Quiver.WeaklyConnectedComponent.{u1, u2} V _inst_1) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) V (Quiver.WeaklyConnectedComponent.{u1, u2} V _inst_1) (HasLiftT.mk.{succ u2, succ u2} V (Quiver.WeaklyConnectedComponent.{u1, u2} V _inst_1) (CoeTCₓ.coe.{succ u2, succ u2} V (Quiver.WeaklyConnectedComponent.{u1, u2} V _inst_1) (Quiver.WeaklyConnectedComponent.hasCoeT.{u1, u2} V _inst_1))) a) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) V (Quiver.WeaklyConnectedComponent.{u1, u2} V _inst_1) (HasLiftT.mk.{succ u2, succ u2} V (Quiver.WeaklyConnectedComponent.{u1, u2} V _inst_1) (CoeTCₓ.coe.{succ u2, succ u2} V (Quiver.WeaklyConnectedComponent.{u1, u2} V _inst_1) (Quiver.WeaklyConnectedComponent.hasCoeT.{u1, u2} V _inst_1))) b)) (Nonempty.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) a b))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} V] (a : V) (b : V), Iff (Eq.{succ u1} (Quiver.WeaklyConnectedComponent.{u2, u1} V _inst_1) (Quiver.WeaklyConnectedComponent.mk.{u2, u1} V _inst_1 a) (Quiver.WeaklyConnectedComponent.mk.{u2, u1} V _inst_1 b)) (Nonempty.{max (succ u1) (succ u2)} (Quiver.Path.{succ u2, u1} (Quiver.Symmetrify.{u1} V) (Quiver.symmetrifyQuiver.{u1, u2} V _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align quiver.weakly_connected_component.eq Quiver.WeaklyConnectedComponent.eqₓ'. -/
protected theorem eq (a b : V) :
    (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotient.eq'
#align quiver.weakly_connected_component.eq Quiver.WeaklyConnectedComponent.eq

end WeaklyConnectedComponent

variable {V}

#print Quiver.wideSubquiverSymmetrify /-
-- Without the explicit universe level in `quiver.{v+1}` Lean comes up with
-- `quiver.{max u_2 u_3 + 1}`. This causes problems elsewhere, so we write `quiver.{v+1}`.
/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
def wideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver V := fun a b =>
  { e | Sum.inl e ∈ H a b ∨ Sum.inr e ∈ H b a }
#align quiver.wide_subquiver_symmetrify Quiver.wideSubquiverSymmetrify
-/

end Quiver

