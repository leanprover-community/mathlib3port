/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Combinatorics.Quiver.Path
import Mathbin.Combinatorics.Quiver.Push
import Mathbin.Data.Sum.Basic

#align_import combinatorics.quiver.symmetric from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
## Symmetric quivers and arrow reversal

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  HasReverse.reverse'
#align quiver.reverse Quiver.reverse
-/

#print Quiver.HasInvolutiveReverse /-
/-- A quiver `has_involutive_reverse` if reversing twice is the identity.`-/
class HasInvolutiveReverse extends HasReverse V where
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f
#align quiver.has_involutive_reverse Quiver.HasInvolutiveReverse
-/

variable {U V W}

#print Quiver.reverse_reverse /-
@[simp]
theorem reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f :=
  h.inv' f
#align quiver.reverse_reverse Quiver.reverse_reverse
-/

#print Quiver.reverse_inj /-
@[simp]
theorem reverse_inj [HasInvolutiveReverse V] {a b : V} (f g : a ⟶ b) :
    reverse f = reverse g ↔ f = g := by
  constructor
  · rintro h; simpa using congr_arg Quiver.reverse h
  · rintro h; congr; assumption
#align quiver.reverse_inj Quiver.reverse_inj
-/

#print Quiver.eq_reverse_iff /-
theorem eq_reverse_iff [HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) (g : b ⟶ a) :
    f = reverse g ↔ reverse f = g := by rw [← reverse_inj, reverse_reverse]
#align quiver.eq_reverse_iff Quiver.eq_reverse_iff
-/

section MapReverse

variable [HasReverse U] [HasReverse V] [HasReverse W]

#print Prefunctor.MapReverse /-
/-- A prefunctor preserving reversal of arrows -/
class Prefunctor.MapReverse (φ : U ⥤q V) where
  map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)
#align prefunctor.map_reverse Prefunctor.MapReverse
-/

#print Prefunctor.map_reverse /-
@[simp]
theorem Prefunctor.map_reverse (φ : U ⥤q V) [φ.MapReverse] {u v : U} (e : u ⟶ v) :
    φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e
#align prefunctor.map_reverse' Prefunctor.map_reverse
-/

#print Prefunctor.mapReverseComp /-
instance Prefunctor.mapReverseComp (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q ψ).MapReverse
    where map_reverse' u v e := by simp only [Prefunctor.comp_map, Prefunctor.map_reverse]
#align prefunctor.map_reverse_comp Prefunctor.mapReverseComp
-/

#print Prefunctor.mapReverseId /-
instance Prefunctor.mapReverseId : (Prefunctor.id U).MapReverse where map_reverse' u v e := rfl
#align prefunctor.map_reverse_id Prefunctor.mapReverseId
-/

end MapReverse

instance : HasReverse (Symmetrify V) :=
  ⟨fun a b e => e.symm⟩

instance : HasInvolutiveReverse (Symmetrify V)
    where
  reverse' _ _ e := e.symm
  inv' _ _ e := congr_fun Sum.swap_swap_eq e

#print Quiver.symmetrify_reverse /-
@[simp]
theorem symmetrify_reverse {a b : Symmetrify V} (e : a ⟶ b) : reverse e = e.symm :=
  rfl
#align quiver.symmetrify_reverse Quiver.symmetrify_reverse
-/

#print Quiver.Hom.toPos /-
/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f
#align quiver.hom.to_pos Quiver.Hom.toPos
-/

#print Quiver.Hom.toNeg /-
/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f
#align quiver.hom.to_neg Quiver.Hom.toNeg
-/

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
    (p.comp q).reverse = q.reverse.comp p.reverse := by induction q; · simp; · simp [q_ih]
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

#print Quiver.Symmetrify.lift /-
/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def lift [HasReverse V'] (φ : V ⥤q V') : Symmetrify V ⥤q V'
    where
  obj := φ.obj
  map X Y f := Sum.rec (fun fwd => φ.map fwd) (fun bwd => reverse (φ.map bwd)) f
#align quiver.symmetrify.lift Quiver.Symmetrify.lift
-/

#print Quiver.Symmetrify.lift_spec /-
theorem lift_spec [HasReverse V'] (φ : V ⥤q V') : of ⋙q lift φ = φ :=
  by
  fapply Prefunctor.ext
  · rintro X; rfl
  · rintro X Y f; rfl
#align quiver.symmetrify.lift_spec Quiver.Symmetrify.lift_spec
-/

#print Quiver.Symmetrify.lift_reverse /-
theorem lift_reverse [h : HasInvolutiveReverse V'] (φ : V ⥤q V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (lift φ).map (Quiver.reverse f) = Quiver.reverse ((lift φ).map f) :=
  by
  dsimp [lift]; cases f
  · simp only; rfl
  · simp only [reverse_reverse]; rfl
#align quiver.symmetrify.lift_reverse Quiver.Symmetrify.lift_reverse
-/

#print Quiver.Symmetrify.lift_unique /-
/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
theorem lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : of ⋙q Φ = φ)
    [hΦrev : Φ.MapReverse] : Φ = lift φ := by
  subst_vars
  fapply Prefunctor.ext
  · rintro X; rfl
  · rintro X Y f
    cases f
    · rfl
    · dsimp [lift, of]
      simp only [← Prefunctor.map_reverse, symmetrify_reverse, Sum.swap_inl]
#align quiver.symmetrify.lift_unique Quiver.Symmetrify.lift_unique
-/

#print Prefunctor.symmetrify /-
/-- A prefunctor canonically defines a prefunctor of the symmetrifications. -/
@[simps]
def Prefunctor.symmetrify (φ : U ⥤q V) : Symmetrify U ⥤q Symmetrify V
    where
  obj := φ.obj
  map X Y := Sum.map φ.map φ.map
#align prefunctor.symmetrify Prefunctor.symmetrify
-/

#print Prefunctor.symmetrify_mapReverse /-
instance Prefunctor.symmetrify_mapReverse (φ : U ⥤q V) : Prefunctor.MapReverse φ.Symmetrify :=
  ⟨fun u v e => by cases e <;> rfl⟩
#align prefunctor.symmetrify_map_reverse Prefunctor.symmetrify_mapReverse
-/

end Symmetrify

namespace Push

variable {V' : Type _} (σ : V → V')

instance [HasReverse V] : HasReverse (Push σ)
    where reverse' a b F := by cases F; constructor; apply reverse; exact F_f

instance [HasInvolutiveReverse V] : HasInvolutiveReverse (Push σ)
    where
  reverse' a b F := by cases F; constructor; apply reverse; exact F_f
  inv' a b F := by cases F; dsimp [reverse]; congr; apply reverse_reverse

#print Quiver.Push.of_reverse /-
theorem of_reverse [h : HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl
#align quiver.push.of_reverse Quiver.Push.of_reverse
-/

#print Quiver.Push.ofMapReverse /-
instance ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩
#align quiver.push.of_map_reverse Quiver.Push.ofMapReverse
-/

end Push

#print Quiver.IsPreconnected /-
/-- A quiver is preconnected iff there exists a path between any pair of
vertices.
Note that if `V` doesn't `has_reverse`, then the definition is stronger than
simply having a preconnected underlying `simple_graph`, since a path in one
direction doesn't induce one in the other.
-/
def IsPreconnected (V) [Quiver.{u + 1} V] :=
  ∀ X Y : V, Nonempty (Path X Y)
#align quiver.is_preconnected Quiver.IsPreconnected
-/

end Quiver

