/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module combinatorics.quiver.connected_component
! leanprover-community/mathlib commit a59dad53320b73ef180174aae867addd707ef00e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Subquiver
import Mathbin.Combinatorics.Quiver.Path
import Mathbin.Data.Sum.Basic

/-!
## Weakly connected components

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/836
> Any changes to this file require a corresponding PR to mathlib4.

For a quiver `V`, we build a quiver `symmetrify V` by adding a reversal of every edge.
Informally, a path in `symmetrify V` corresponds to a 'zigzag' in `V`. This lets us
define the type `weakly_connected_component V` as the quotient of `V` by the relation which
identifies `a` with `b` if there is a path from `a` to `b` in `symmetrify V`. (These
zigzags can be seen as a proof-relevant analogue of `eqv_gen`.)

Strongly connected components have not yet been defined.
-/


universe v u

namespace Quiver

#print Quiver.Symmetrify /-
/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_nonempty_instance]
def Symmetrify (V) : Type u :=
  V
#align quiver.symmetrify Quiver.Symmetrify
-/

#print Quiver.symmetrifyQuiver /-
instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V => Sum (a ⟶ b) (b ⟶ a)⟩
#align quiver.symmetrify_quiver Quiver.symmetrifyQuiver
-/

variable (V : Type u) [Quiver.{v + 1} V]

#print Quiver.HasReverse /-
/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class HasReverse where
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)
#align quiver.has_reverse Quiver.HasReverse
-/

#print Quiver.reverse /-
/-- Reverse the direction of an arrow. -/
def reverse {V} [Quiver.{v + 1} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  has_reverse.reverse'
#align quiver.reverse Quiver.reverse
-/

#print Quiver.HasInvolutiveReverse /-
/-- A quiver `has_involutive_reverse` if reversing twice is the identity.`-/
class HasInvolutiveReverse extends HasReverse V where
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f
#align quiver.has_involutive_reverse Quiver.HasInvolutiveReverse
-/

/- warning: quiver.reverse_reverse -> Quiver.reverse_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] [h : Quiver.HasInvolutiveReverse.{u1, u2} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u1, u2} V _inst_2 a b), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V _inst_2 a b) (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 h) b a (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 h) a b f)) f
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] [h : Quiver.HasInvolutiveReverse.{u2, u1} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u2, u1} V _inst_2 a b), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} V _inst_2 a b) (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 h) b a (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 h) a b f)) f
Case conversion may be inaccurate. Consider using '#align quiver.reverse_reverse Quiver.reverse_reverseₓ'. -/
@[simp]
theorem reverse_reverse {V} [Quiver.{v + 1} V] [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f := by apply h.inv'
#align quiver.reverse_reverse Quiver.reverse_reverse

variable {V}

instance : HasReverse (Symmetrify V) :=
  ⟨fun a b e => e.swap⟩

instance :
    HasInvolutiveReverse
      (Symmetrify V) where 
  toHasReverse := ⟨fun a b e => e.swap⟩
  inv' a b e := congr_fun Sum.swap_swap_eq e

#print Quiver.Path.reverse /-
/-- Reverse the direction of a path. -/
@[simp]
def Path.reverse [HasReverse V] {a : V} : ∀ {b}, Path a b → Path b a
  | a, path.nil => Path.nil
  | b, path.cons p e => (reverse e).toPath.comp p.reverse
#align quiver.path.reverse Quiver.Path.reverse
-/

#print Quiver.Path.reverse_toPath /-
@[simp]
theorem Path.reverse_toPath [HasReverse V] {a b : V} (f : a ⟶ b) :
    f.toPath.reverse = (reverse f).toPath :=
  rfl
#align quiver.path.reverse_to_path Quiver.Path.reverse_toPath
-/

#print Quiver.Path.reverse_comp /-
@[simp]
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse := by
  induction q
  · simp
  · simp [q_ih]
#align quiver.path.reverse_comp Quiver.Path.reverse_comp
-/

#print Quiver.Path.reverse_reverse /-
@[simp]
theorem Path.reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by 
  induction p
  · simp
  · simp only [path.reverse, path.reverse_comp, path.reverse_to_path, reverse_reverse, p_ih]
    rfl
#align quiver.path.reverse_reverse Quiver.Path.reverse_reverse
-/

#print Quiver.Symmetrify.of /-
/-- The inclusion of a quiver in its symmetrification -/
def Symmetrify.of : Prefunctor V (Symmetrify
        V) where 
  obj := id
  map X Y f := Sum.inl f
#align quiver.symmetrify.of Quiver.Symmetrify.of
-/

#print Quiver.Symmetrify.lift /-
/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def Symmetrify.lift {V' : Type _} [Quiver V'] [HasReverse V'] (φ : Prefunctor V V') :
    Prefunctor (Symmetrify V) V' where 
  obj := φ.obj
  map X Y f := Sum.rec (fun fwd => φ.map fwd) (fun bwd => reverse (φ.map bwd)) f
#align quiver.symmetrify.lift Quiver.Symmetrify.lift
-/

/- warning: quiver.symmetrify.lift_spec -> Quiver.Symmetrify.lift_spec is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} V] (V' : Type.{u3}) [_inst_2 : Quiver.{succ u4, u3} V'] [_inst_3 : Quiver.HasReverse.{u4, u3} V' _inst_2] (φ : Prefunctor.{succ u1, succ u4, u2, u3} V _inst_1 V' _inst_2), Eq.{max (max (succ u2) (succ u1) (succ u4)) (succ u2) (succ u3)} (Prefunctor.{succ u1, succ u4, u2, u3} V _inst_1 V' _inst_2) (Prefunctor.comp.{u2, succ u1, u2, succ u1, u3, succ u4} V _inst_1 (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 (Quiver.Symmetrify.of.{u1, u2} V _inst_1) (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_1 V' _inst_2 _inst_3 φ)) φ
but is expected to have type
  forall {V : Type.{u4}} [_inst_1 : Quiver.{succ u3, u4} V] (V' : Type.{u2}) [_inst_2 : Quiver.{succ u1, u2} V'] [_inst_3 : Quiver.HasReverse.{u1, u2} V' _inst_2] (φ : Prefunctor.{succ u3, succ u1, u4, u2} V _inst_1 V' _inst_2), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Prefunctor.{succ u3, succ u1, u4, u2} V _inst_1 V' _inst_2) (Prefunctor.comp.{u4, succ u3, u4, succ u3, u2, succ u1} V _inst_1 (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 (Quiver.Symmetrify.of.{u3, u4} V _inst_1) (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_1 V' _inst_2 _inst_3 φ)) φ
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_spec Quiver.Symmetrify.lift_specₓ'. -/
theorem Symmetrify.lift_spec (V' : Type _) [Quiver V'] [HasReverse V'] (φ : Prefunctor V V') :
    Symmetrify.of.comp (Symmetrify.lift φ) = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl
#align quiver.symmetrify.lift_spec Quiver.Symmetrify.lift_spec

/- warning: quiver.symmetrify.lift_reverse -> Quiver.Symmetrify.lift_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} V] (V' : Type.{u3}) [_inst_2 : Quiver.{succ u4, u3} V'] [h : Quiver.HasInvolutiveReverse.{u4, u3} V' _inst_2] (φ : Prefunctor.{succ u1, succ u4, u2, u3} V _inst_1 V' _inst_2) {X : Quiver.Symmetrify.{u2} V} {Y : Quiver.Symmetrify.{u2} V} (f : Quiver.Hom.{succ u1, u2} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) X Y), Eq.{succ u4} (Quiver.Hom.{succ u4, u3} V' _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u3} V' _inst_2 h) φ) Y) (Prefunctor.obj.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u3} V' _inst_2 h) φ) X)) (Prefunctor.map.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u3} V' _inst_2 h) φ) Y X (Quiver.reverse.{u1, u2} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) (Quiver.Symmetrify.hasReverse.{u1, u2} V _inst_1) X Y f)) (Quiver.reverse.{u4, u3} V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u3} V' _inst_2 h) (Prefunctor.obj.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u3} V' _inst_2 h) φ) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u3} V' _inst_2 h) φ) Y) (Prefunctor.map.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u4, u3} V' _inst_2 h) φ) X Y f))
but is expected to have type
  forall {V : Type.{u4}} [_inst_1 : Quiver.{succ u3, u4} V] (V' : Type.{u2}) [_inst_2 : Quiver.{succ u1, u2} V'] [h : Quiver.HasInvolutiveReverse.{u1, u2} V' _inst_2] (φ : Prefunctor.{succ u3, succ u1, u4, u2} V _inst_1 V' _inst_2) {X : Quiver.Symmetrify.{u4} V} {Y : Quiver.Symmetrify.{u4} V} (f : Quiver.Hom.{succ u3, u4} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V' _inst_2 (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_2 h) φ) Y) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_2 h) φ) X)) (Prefunctor.map.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_2 h) φ) Y X (Quiver.reverse.{u3, u4} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) (Quiver.instHasReverseSymmetrifySymmetrifyQuiver.{u3, u4} V _inst_1) X Y f)) (Quiver.reverse.{u1, u2} V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_2 h) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_2 h) φ) X) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_2 h) φ) Y) (Prefunctor.map.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_1 V' _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_2 h) φ) X Y f))
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_reverse Quiver.Symmetrify.lift_reverseₓ'. -/
theorem Symmetrify.lift_reverse (V' : Type _) [Quiver V'] [h : HasInvolutiveReverse V']
    (φ : Prefunctor V V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.reverse ((Symmetrify.lift φ).map f) := by
  dsimp [symmetrify.lift]; cases f
  · simp only
    rfl
  · simp only
    rw [h.inv']
    rfl
#align quiver.symmetrify.lift_reverse Quiver.Symmetrify.lift_reverse

/- warning: quiver.symmetrify.lift_unique -> Quiver.Symmetrify.lift_unique is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} V] (V' : Type.{u3}) [_inst_2 : Quiver.{succ u4, u3} V'] [_inst_3 : Quiver.HasReverse.{u4, u3} V' _inst_2] (φ : Prefunctor.{succ u1, succ u4, u2, u3} V _inst_1 V' _inst_2) (Φ : Prefunctor.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2), (Eq.{max (max (succ u2) (succ u1) (succ u4)) (succ u2) (succ u3)} (Prefunctor.{succ u1, succ u4, u2, u3} V _inst_1 V' _inst_2) (Prefunctor.comp.{u2, succ u1, u2, succ u1, u3, succ u4} V _inst_1 (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 (Quiver.Symmetrify.of.{u1, u2} V _inst_1) Φ) φ) -> (forall {X : V} {Y : V} (f : Quiver.Hom.{succ u1, u2} V (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) X Y), Eq.{succ u4} (Quiver.Hom.{succ u4, u3} V' _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 Φ Y) (Prefunctor.obj.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 Φ X)) (Prefunctor.map.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 Φ Y X (Quiver.reverse.{u1, u2} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) (Quiver.Symmetrify.hasReverse.{u1, u2} V _inst_1) X Y f)) (Quiver.reverse.{u4, u3} V' _inst_2 _inst_3 (Prefunctor.obj.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 Φ X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 Φ Y) (Prefunctor.map.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2 Φ X Y f))) -> (Eq.{max (max (succ u2) (succ u1) (succ u4)) (succ u2) (succ u3)} (Prefunctor.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_1) V' _inst_2) Φ (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_1 V' _inst_2 _inst_3 φ))
but is expected to have type
  forall {V : Type.{u4}} [_inst_1 : Quiver.{succ u3, u4} V] (V' : Type.{u2}) [_inst_2 : Quiver.{succ u1, u2} V'] [_inst_3 : Quiver.HasReverse.{u1, u2} V' _inst_2] (φ : Prefunctor.{succ u3, succ u1, u4, u2} V _inst_1 V' _inst_2) (Φ : Prefunctor.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2), (Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Prefunctor.{succ u3, succ u1, u4, u2} V _inst_1 V' _inst_2) (Prefunctor.comp.{u4, succ u3, u4, succ u3, u2, succ u1} V _inst_1 (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 (Quiver.Symmetrify.of.{u3, u4} V _inst_1) Φ) φ) -> (forall {X : Quiver.Symmetrify.{u4} V} {Y : Quiver.Symmetrify.{u4} V} (f : Quiver.Hom.{succ u3, u4} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V' _inst_2 (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 Φ Y) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 Φ X)) (Prefunctor.map.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 Φ Y X (Quiver.reverse.{u3, u4} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) (Quiver.instHasReverseSymmetrifySymmetrifyQuiver.{u3, u4} V _inst_1) X Y f)) (Quiver.reverse.{u1, u2} V' _inst_2 _inst_3 (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 Φ X) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 Φ Y) (Prefunctor.map.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2 Φ X Y f))) -> (Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Prefunctor.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_1) V' _inst_2) Φ (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_1 V' _inst_2 _inst_3 φ))
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_uniqueₓ'. -/
/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
theorem Symmetrify.lift_unique (V' : Type _) [Quiver V'] [HasReverse V'] (φ : Prefunctor V V')
    (Φ : Prefunctor (Symmetrify V) V') (hΦ : Symmetrify.of.comp Φ = φ)
    (hΦinv : ∀ {X Y : V} (f : X ⟶ Y), Φ.map (reverse f) = reverse (Φ.map f)) :
    Φ = Symmetrify.lift φ := by 
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · dsimp [symmetrify.lift, symmetrify.of]
      convert hΦinv (Sum.inl f)
#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_unique

variable (V)

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

#print Quiver.WeaklyConnectedComponent.eq /-
protected theorem eq (a b : V) :
    (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotient.eq'
#align quiver.weakly_connected_component.eq Quiver.WeaklyConnectedComponent.eq
-/

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

