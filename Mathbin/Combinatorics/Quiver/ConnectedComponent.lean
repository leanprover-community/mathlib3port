/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathbin.Combinatorics.Quiver.Subquiver
import Mathbin.Combinatorics.Quiver.Path

/-!
## Weakly connected components

For a quiver `V`, we build a quiver `symmetrify V` by adding a reversal of every edge.
Informally, a path in `symmetrify V` corresponds to a 'zigzag' in `V`. This lets us
define the type `weakly_connected_component V` as the quotient of `V` by the relation which
identifies `a` with `b` if there is a path from `a` to `b` in `symmetrify V`. (These
zigzags can be seen as a proof-relevant analogue of `eqv_gen`.)

Strongly connected components have not yet been defined.
-/


universe v u

namespace Quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_nonempty_instance]
def Symmetrify (V) : Type u :=
  V

instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V => Sum (a ⟶ b) (b ⟶ a)⟩

variable (V : Type u) [Quiver.{v + 1} V]

/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class HasReverse where
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)

/-- Reverse the direction of an arrow. -/
def reverse {V} [Quiver.{v + 1} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  has_reverse.reverse'

/-- A quiver `has_involutive_reverse` if reversing twice is the identity.`-/
class HasInvolutiveReverse extends HasReverse V where
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f

@[simp]
theorem reverse_reverse {V} [Quiver.{v + 1} V] [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f := by apply h.inv'

variable {V}

instance : HasReverse (Symmetrify V) :=
  ⟨fun a b e => e.swap⟩

instance : HasInvolutiveReverse (Symmetrify V) where
  toHasReverse := ⟨fun a b e => e.swap⟩
  inv' a b e := congr_fun Sum.swap_swap_eq e

/- warning: quiver.path.reverse -> Quiver.Path.reverse is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u}} [_inst_1 : Quiver.{succ v u} V] [_inst_2 : Quiver.HasReverse.{v u} V _inst_1] {a : V} {b : V}, (Quiver.Path.{succ v u} V _inst_1 a b) -> (Quiver.Path.{succ v u} V _inst_1 b a)
but is expected to have type
  forall {V : Type.{u}} [_inst_1 : Quiver.{succ v u} V] [_inst_2 : Quiver.HasReverse.{v u} V _inst_1] {a : V} {b : V}, (Quiver.Path.{succ v u} V _inst_1 a b) -> (Quiver.Path.{succ v u} V _inst_1 b a)
Case conversion may be inaccurate. Consider using '#align quiver.path.reverse Quiver.Path.reverseₓ'. -/
/-- Reverse the direction of a path. -/
@[simp]
def Path.reverse [HasReverse V] {a : V} : ∀ {b}, Path a b → Path b a
  | a, path.nil => Path.nil
  | b, path.cons p e => (reverse e).toPath.comp p.reverse

@[simp]
theorem Path.reverse_to_path [HasReverse V] {a b : V} (f : a ⟶ b) : f.toPath.reverse = (reverse f).toPath :=
  rfl

@[simp]
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse := by
  induction q
  · simp
    
  · simp [q_ih]
    

@[simp]
theorem Path.reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (p : Path a b) : p.reverse.reverse = p := by
  induction p
  · simp
    
  · simp only [path.reverse, path.reverse_comp, path.reverse_to_path, reverse_reverse, p_ih]
    rfl
    

/-- The inclusion of a quiver in its symmetrification -/
def Symmetrify.of : Prefunctor V (Symmetrify V) where
  obj := id
  map X Y f := Sum.inl f

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def Symmetrify.lift {V' : Type _} [Quiver V'] [HasReverse V'] (φ : Prefunctor V V') : Prefunctor (Symmetrify V) V' where
  obj := φ.obj
  map X Y f := Sum.rec (fun fwd => φ.map fwd) (fun bwd => reverse (φ.map bwd)) f

theorem Symmetrify.lift_spec (V' : Type _) [Quiver V'] [HasReverse V'] (φ : Prefunctor V V') :
    Symmetrify.of.comp (Symmetrify.lift φ) = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
    
  · rintro X Y f
    rfl
    

theorem Symmetrify.lift_reverse (V' : Type _) [Quiver V'] [h : HasInvolutiveReverse V'] (φ : Prefunctor V V')
    {X Y : Symmetrify V} (f : X ⟶ Y) :
    (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.reverse ((Symmetrify.lift φ).map f) := by
  dsimp [symmetrify.lift]
  cases f
  · simp only
    rfl
    
  · simp only
    rw [h.inv']
    rfl
    

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
theorem Symmetrify.lift_unique (V' : Type _) [Quiver V'] [HasReverse V'] (φ : Prefunctor V V')
    (Φ : Prefunctor (Symmetrify V) V') (hΦ : Symmetrify.of.comp Φ = φ)
    (hΦinv : ∀ {X Y : V} (f : X ⟶ Y), Φ.map (reverse f) = reverse (Φ.map f)) : Φ = Symmetrify.lift φ := by
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
    
  · rintro X Y f
    cases f
    · rfl
      
    · dsimp [symmetrify.lift, symmetrify.of]
      convert hΦinv (Sum.inl f)
      
    

variable (V)

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzagSetoid : Setoid V :=
  ⟨fun a b => Nonempty (@Path (Symmetrify V) _ a b), fun a => ⟨Path.nil⟩, fun a b ⟨p⟩ => ⟨p.reverse⟩,
    fun a b c ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def WeaklyConnectedComponent : Type _ :=
  Quotient (zigzagSetoid V)

namespace WeaklyConnectedComponent

variable {V}

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → WeaklyConnectedComponent V :=
  Quotient.mk'

instance : CoeTC V (WeaklyConnectedComponent V) :=
  ⟨WeaklyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (WeaklyConnectedComponent V) :=
  ⟨show V from default⟩

protected theorem eq (a b : V) : (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotient.eq'

end WeaklyConnectedComponent

variable {V}

-- Without the explicit universe level in `quiver.{v+1}` Lean comes up with
-- `quiver.{max u_2 u_3 + 1}`. This causes problems elsewhere, so we write `quiver.{v+1}`.
/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
def WideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver V := fun a b =>
  { e | Sum.inl e ∈ H a b ∨ Sum.inr e ∈ H b a }

end Quiver

