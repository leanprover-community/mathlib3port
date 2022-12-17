/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module combinatorics.quiver.symmetric
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Combinatorics.Quiver.Path
import Mathbin.Combinatorics.Quiver.Push
import Mathbin.Data.Sum.Basic

/-!
## Symmetric quivers and arrow reversal

This file contains constructions related to symmetric quivers:

* `symmetrify V` adds formal inverses to each arrow of `V`.
* `has_reverse` is the class of quivers where each arrow has an assigned formal inverse.
* `has_involutive_reverse` extends `has_reverse` by requiring that the reverse of the reverse
  is equal to the original arrow.
* `prefunctor.preserve_reverse` is the class of prefunctors mapping reverses to reverses.
* `symmetrify.of`, `symmetrify.lift`, and the associated lemmas witness the universal property
  of `symmetrify`.
-/


universe v u w v'

namespace Quiver

#print Quiver.Symmetrify /-
/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_nonempty_instance]
def Symmetrify (V : Type _) :=
  V
#align quiver.symmetrify Quiver.Symmetrify
-/

#print Quiver.symmetrifyQuiver /-
instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V => Sum (a ⟶ b) (b ⟶ a)⟩
#align quiver.symmetrify_quiver Quiver.symmetrifyQuiver
-/

variable (U V W : Type _) [Quiver.{u + 1} U] [Quiver.{v + 1} V] [Quiver.{w + 1} W]

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

variable {U V W}

/- warning: quiver.reverse_reverse -> Quiver.reverse_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] [h : Quiver.HasInvolutiveReverse.{u1, u2} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u1, u2} V _inst_2 a b), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V _inst_2 a b) (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 h) b a (Quiver.reverse.{u1, u2} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V _inst_2 h) a b f)) f
but is expected to have type
  forall {V : Type.{u1}} [_inst_2 : Quiver.{succ u2, u1} V] [h : Quiver.HasInvolutiveReverse.{u2, u1} V _inst_2] {a : V} {b : V} (f : Quiver.Hom.{succ u2, u1} V _inst_2 a b), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} V _inst_2 a b) (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 h) b a (Quiver.reverse.{u2, u1} V _inst_2 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u1} V _inst_2 h) a b f)) f
Case conversion may be inaccurate. Consider using '#align quiver.reverse_reverse Quiver.reverse_reverseₓ'. -/
@[simp]
theorem reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f :=
  h.inv' f
#align quiver.reverse_reverse Quiver.reverse_reverse

@[simp]
theorem reverse_inj [HasInvolutiveReverse V] {a b : V} (f g : a ⟶ b) :
    reverse f = reverse g ↔ f = g := by 
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr
    assumption
#align quiver.reverse_inj Quiver.reverse_inj

theorem eq_reverse_iff [HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) (g : b ⟶ a) :
    f = reverse g ↔ reverse f = g := by rw [← reverse_inj, reverse_reverse]
#align quiver.eq_reverse_iff Quiver.eq_reverse_iff

section MapReverse

variable [HasReverse U] [HasReverse V] [HasReverse W]

/-- A prefunctor preserving reversal of arrows -/
class Prefunctor.MapReverse (φ : U ⥤q V) where
  map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)
#align prefunctor.map_reverse Prefunctor.MapReverse

@[simp]
theorem Prefunctor.map_reverse' (φ : U ⥤q V) [φ.MapReverse] {u v : U} (e : u ⟶ v) :
    φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e
#align prefunctor.map_reverse' Prefunctor.map_reverse'

instance Prefunctor.mapReverseComp (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q
        ψ).MapReverse where map_reverse' u v e := by
    simp only [Prefunctor.comp_map, Prefunctor.map_reverse']
#align prefunctor.map_reverse_comp Prefunctor.mapReverseComp

instance Prefunctor.mapReverseId : (Prefunctor.id U).MapReverse where map_reverse' u v e := rfl
#align prefunctor.map_reverse_id Prefunctor.mapReverseId

end MapReverse

instance : HasReverse (Symmetrify V) :=
  ⟨fun a b e => e.swap⟩

instance : HasInvolutiveReverse
      (Symmetrify V) where 
  reverse' _ _ e := e.swap
  inv' _ _ e := congr_fun Sum.swap_swap_eq e

@[simp]
theorem symmetrify_reverse {a b : Symmetrify V} (e : a ⟶ b) : reverse e = e.swap :=
  rfl
#align quiver.symmetrify_reverse Quiver.symmetrify_reverse

/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f
#align quiver.hom.to_pos Quiver.Hom.toPos

/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f
#align quiver.hom.to_neg Quiver.Hom.toNeg

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
theorem Path.reverse_reverse [HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by 
  induction p
  · simp
  · simp only [path.reverse, path.reverse_comp, path.reverse_to_path, reverse_reverse, p_ih]
    rfl
#align quiver.path.reverse_reverse Quiver.Path.reverse_reverse
-/

namespace Symmetrify

#print Quiver.Symmetrify.of /-
/-- The inclusion of a quiver in its symmetrification -/
@[simps]
def of : V ⥤q Symmetrify V where 
  obj := id
  map X Y f := Sum.inl f
#align quiver.symmetrify.of Quiver.Symmetrify.of
-/

variable {V' : Type _} [Quiver.{v' + 1} V']

/- warning: quiver.symmetrify.lift -> Quiver.Symmetrify.lift is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u3}} [_inst_2 : Quiver.{succ u1, u3} V] {V' : Type.{u4}} [_inst_4 : Quiver.{succ u2, u4} V'] [_inst_5 : Quiver.HasReverse.{u2, u4} V' _inst_4], (Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) -> (Prefunctor.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4)
but is expected to have type
  forall {V : Type.{u2}} [_inst_2 : Quiver.{succ u1, u2} V] {V' : Type.{u3}} [_inst_4 : Quiver.{succ u4, u3} V'] [_inst_5 : Quiver.HasReverse.{u4, u3} V' _inst_4], (Prefunctor.{succ u1, succ u4, u2, u3} V _inst_2 V' _inst_4) -> (Prefunctor.{succ u1, succ u4, u2, u3} (Quiver.Symmetrify.{u2} V) (Quiver.symmetrifyQuiver.{u2, u1} V _inst_2) V' _inst_4)
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift Quiver.Symmetrify.liftₓ'. -/
/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def lift [HasReverse V'] (φ : V ⥤q V') :
    Symmetrify V ⥤q V' where 
  obj := φ.obj
  map X Y f := Sum.rec (fun fwd => φ.map fwd) (fun bwd => reverse (φ.map bwd)) f
#align quiver.symmetrify.lift Quiver.Symmetrify.lift

/- warning: quiver.symmetrify.lift_spec -> Quiver.Symmetrify.lift_spec is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u3}} [_inst_2 : Quiver.{succ u1, u3} V] {V' : Type.{u4}} [_inst_4 : Quiver.{succ u2, u4} V'] [_inst_5 : Quiver.HasReverse.{u2, u4} V' _inst_4] (φ : Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4), Eq.{max (max (succ u3) (succ u1) (succ u2)) (succ u3) (succ u4)} (Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) (Prefunctor.comp.{u3, succ u1, u3, succ u1, u4, succ u2} V _inst_2 (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.of.{u1, u3} V _inst_2) (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 _inst_5 φ)) φ
but is expected to have type
  forall {V : Type.{u4}} [_inst_2 : Quiver.{succ u3, u4} V] (V' : Type.{u2}) [_inst_4 : Quiver.{succ u1, u2} V'] [_inst_5 : Quiver.HasReverse.{u1, u2} V' _inst_4] (φ : Prefunctor.{succ u3, succ u1, u4, u2} V _inst_2 V' _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Prefunctor.{succ u3, succ u1, u4, u2} V _inst_2 V' _inst_4) (Prefunctor.comp.{u4, succ u3, u4, succ u3, u2, succ u1} V _inst_2 (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.of.{u3, u4} V _inst_2) (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_2 V' _inst_4 _inst_5 φ)) φ
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_spec Quiver.Symmetrify.lift_specₓ'. -/
theorem lift_spec [HasReverse V'] (φ : V ⥤q V') : (of ⋙q lift φ) = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl
#align quiver.symmetrify.lift_spec Quiver.Symmetrify.lift_spec

/- warning: quiver.symmetrify.lift_reverse -> Quiver.Symmetrify.lift_reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u3}} [_inst_2 : Quiver.{succ u1, u3} V] {V' : Type.{u4}} [_inst_4 : Quiver.{succ u2, u4} V'] [h : Quiver.HasInvolutiveReverse.{u2, u4} V' _inst_4] (φ : Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) {X : Quiver.Symmetrify.{u3} V} {Y : Quiver.Symmetrify.{u3} V} (f : Quiver.Hom.{succ u1, u3} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) X Y), Eq.{succ u2} (Quiver.Hom.{succ u2, u4} V' _inst_4 (Prefunctor.obj.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) X)) (Prefunctor.map.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) Y X (Quiver.reverse.{u1, u3} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) (Quiver.Symmetrify.hasReverse.{u1, u3} V _inst_2) X Y f)) (Quiver.reverse.{u2, u4} V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) (Prefunctor.obj.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u2, u4} V' _inst_4 h) φ) X Y f))
but is expected to have type
  forall {V : Type.{u4}} [_inst_2 : Quiver.{succ u3, u4} V] (V' : Type.{u2}) [_inst_4 : Quiver.{succ u1, u2} V'] [h : Quiver.HasInvolutiveReverse.{u1, u2} V' _inst_4] (φ : Prefunctor.{succ u3, succ u1, u4, u2} V _inst_2 V' _inst_4) {X : Quiver.Symmetrify.{u4} V} {Y : Quiver.Symmetrify.{u4} V} (f : Quiver.Hom.{succ u3, u4} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V' _inst_4 (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_4 h) φ) Y) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_4 h) φ) X)) (Prefunctor.map.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_4 h) φ) Y X (Quiver.reverse.{u3, u4} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) (Quiver.instHasReverseSymmetrifySymmetrifyQuiver.{u3, u4} V _inst_2) X Y f)) (Quiver.reverse.{u1, u2} V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_4 h) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_4 h) φ) X) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_4 h) φ) Y) (Prefunctor.map.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_2 V' _inst_4 (Quiver.HasInvolutiveReverse.toHasReverse.{u1, u2} V' _inst_4 h) φ) X Y f))
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_reverse Quiver.Symmetrify.lift_reverseₓ'. -/
theorem lift_reverse [h : HasInvolutiveReverse V'] (φ : V ⥤q V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (lift φ).map (Quiver.reverse f) = Quiver.reverse ((lift φ).map f) := by
  dsimp [lift]; cases f
  · simp only
    rfl
  · simp only [reverse_reverse]
    rfl
#align quiver.symmetrify.lift_reverse Quiver.Symmetrify.lift_reverse

/- warning: quiver.symmetrify.lift_unique -> Quiver.Symmetrify.lift_unique is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u3}} [_inst_2 : Quiver.{succ u1, u3} V] {V' : Type.{u4}} [_inst_4 : Quiver.{succ u2, u4} V'] [_inst_5 : Quiver.HasReverse.{u2, u4} V' _inst_4] (φ : Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) (Φ : Prefunctor.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4), (Eq.{max (max (succ u3) (succ u1) (succ u2)) (succ u3) (succ u4)} (Prefunctor.{succ u1, succ u2, u3, u4} V _inst_2 V' _inst_4) (Prefunctor.comp.{u3, succ u1, u3, succ u1, u4, succ u2} V _inst_2 (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4 (Quiver.Symmetrify.of.{u1, u3} V _inst_2) Φ) φ) -> (forall [hΦrev : Prefunctor.MapReverse.{u2, u1, u3, u4} (Quiver.Symmetrify.{u3} V) V' (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) _inst_4 (Quiver.Symmetrify.hasReverse.{u1, u3} V _inst_2) _inst_5 Φ], Eq.{max (max (succ u3) (succ u1) (succ u2)) (succ u3) (succ u4)} (Prefunctor.{succ u1, succ u2, u3, u4} (Quiver.Symmetrify.{u3} V) (Quiver.symmetrifyQuiver.{u3, u1} V _inst_2) V' _inst_4) Φ (Quiver.Symmetrify.lift.{u1, u2, u3, u4} V _inst_2 V' _inst_4 _inst_5 φ))
but is expected to have type
  forall {V : Type.{u4}} [_inst_2 : Quiver.{succ u3, u4} V] (V' : Type.{u2}) [_inst_4 : Quiver.{succ u1, u2} V'] [_inst_5 : Quiver.HasReverse.{u1, u2} V' _inst_4] (φ : Prefunctor.{succ u3, succ u1, u4, u2} V _inst_2 V' _inst_4) (Φ : Prefunctor.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4), (Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Prefunctor.{succ u3, succ u1, u4, u2} V _inst_2 V' _inst_4) (Prefunctor.comp.{u4, succ u3, u4, succ u3, u2, succ u1} V _inst_2 (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 (Quiver.Symmetrify.of.{u3, u4} V _inst_2) Φ) φ) -> (forall {X : Quiver.Symmetrify.{u4} V} {Y : Quiver.Symmetrify.{u4} V} (f : Quiver.Hom.{succ u3, u4} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) X Y), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} V' _inst_4 (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 Φ Y) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 Φ X)) (Prefunctor.map.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 Φ Y X (Quiver.reverse.{u3, u4} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) (Quiver.instHasReverseSymmetrifySymmetrifyQuiver.{u3, u4} V _inst_2) X Y f)) (Quiver.reverse.{u1, u2} V' _inst_4 _inst_5 (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 Φ X) (Prefunctor.obj.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 Φ Y) (Prefunctor.map.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4 Φ X Y f))) -> (Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Prefunctor.{succ u3, succ u1, u4, u2} (Quiver.Symmetrify.{u4} V) (Quiver.symmetrifyQuiver.{u4, u3} V _inst_2) V' _inst_4) Φ (Quiver.Symmetrify.lift.{u3, u4, u2, u1} V _inst_2 V' _inst_4 _inst_5 φ))
Case conversion may be inaccurate. Consider using '#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_uniqueₓ'. -/
/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
theorem lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
    [hΦrev : Φ.MapReverse] : Φ = lift φ := by 
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · dsimp [lift, of]
      simp only [← Prefunctor.map_reverse', symmetrify_reverse, Sum.swap_inl]
#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_unique

/-- A prefunctor canonically defines a prefunctor of the symmetrifications. -/
@[simps]
def Prefunctor.symmetrify (φ : U ⥤q V) :
    Symmetrify U ⥤q Symmetrify V where 
  obj := φ.obj
  map X Y := Sum.map φ.map φ.map
#align prefunctor.symmetrify Prefunctor.symmetrify

instance Prefunctor.symmetrifyMapReverse (φ : U ⥤q V) : Prefunctor.MapReverse φ.Symmetrify :=
  ⟨fun u v e => by cases e <;> rfl⟩
#align prefunctor.symmetrify_map_reverse Prefunctor.symmetrifyMapReverse

end Symmetrify

namespace Push

variable {V' : Type _} (σ : V → V')

instance [HasReverse V] :
    HasReverse (Push
        σ) where reverse' a b F := by 
    cases F
    constructor
    apply reverse
    exact F_f

instance [HasInvolutiveReverse V] :
    HasInvolutiveReverse
      (Push
        σ) where 
  reverse' a b F := by 
    cases F
    constructor
    apply reverse
    exact F_f
  inv' a b F := by 
    cases F
    dsimp [reverse]
    congr
    apply reverse_reverse

theorem of_reverse [h : HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl
#align quiver.push.of_reverse Quiver.Push.of_reverse

instance ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩
#align quiver.push.of_map_reverse Quiver.Push.ofMapReverse

end Push

/-- A quiver is preconnected iff there exists a path between any pair of
vertices.
Note that if `V` doesn't `has_reverse`, then the definition is stronger than
simply having a preconnected underlying `simple_graph`, since a path in one
direction doesn't induce one in the other.
-/
def IsPreconnected (V) [Quiver.{u + 1} V] :=
  ∀ X Y : V, Nonempty (Path X Y)
#align quiver.is_preconnected Quiver.IsPreconnected

end Quiver

