/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.add_torsor
! leanprover-community/mathlib commit 3e32bc908f617039c74c06ea9a897e30c30803c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Smul

/-!
# Torsors of additive group actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines torsors of additive group actions.

## Notations

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. It may be appropriate
to refactor in terms of the general definition of group actions, via `to_additive`, when there is a
use for multiplicative torsors (currently mathlib only develops the theory of group actions for
multiplicative group actions).

## Notations

* `v +ᵥ p` is a notation for `has_vadd.vadd`, the left action of an additive monoid;

* `p₁ -ᵥ p₂` is a notation for `has_vsub.vsub`, difference between two points in an additive torsor
  as an element of the corresponding additive group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/


#print AddTorsor /-
/-- An `add_torsor G P` gives a structure to the nonempty type `P`,
acted on by an `add_group G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class AddTorsor (G : outParam (Type _)) (P : Type _) [outParam <| AddGroup G] extends AddAction G P,
    VSub G P where
  [Nonempty : Nonempty P]
  vsub_vadd' : ∀ p1 p2 : P, (p1 -ᵥ p2 : G) +ᵥ p2 = p1
  vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g
#align add_torsor AddTorsor
-/

attribute [instance 100, nolint dangerous_instance] AddTorsor.nonempty

attribute [nolint dangerous_instance] AddTorsor.toHasVsub

#print addGroupIsAddTorsor /-
/-- An `add_group G` is a torsor for itself. -/
@[nolint instance_priority]
instance addGroupIsAddTorsor (G : Type _) [AddGroup G] : AddTorsor G G
    where
  vsub := Sub.sub
  vsub_vadd' := sub_add_cancel
  vadd_vsub' := add_sub_cancel
#align add_group_is_add_torsor addGroupIsAddTorsor
-/

#print vsub_eq_sub /-
/-- Simplify subtraction for a torsor for an `add_group G` over
itself. -/
@[simp]
theorem vsub_eq_sub {G : Type _} [AddGroup G] (g1 g2 : G) : g1 -ᵥ g2 = g1 - g2 :=
  rfl
#align vsub_eq_sub vsub_eq_sub
-/

section General

variable {G : Type _} {P : Type _} [AddGroup G] [T : AddTorsor G P]

#print vsub_vadd /-
/-- Adding the result of subtracting from another point produces that
point. -/
@[simp]
theorem vsub_vadd (p1 p2 : P) : p1 -ᵥ p2 +ᵥ p2 = p1 :=
  AddTorsor.vsub_vadd' p1 p2
#align vsub_vadd vsub_vadd
-/

#print vadd_vsub /-
/-- Adding a group element then subtracting the original point
produces that group element. -/
@[simp]
theorem vadd_vsub (g : G) (p : P) : g +ᵥ p -ᵥ p = g :=
  AddTorsor.vadd_vsub' g p
#align vadd_vsub vadd_vsub
-/

#print vadd_right_cancel /-
/-- If the same point added to two group elements produces equal
results, those group elements are equal. -/
theorem vadd_right_cancel {g1 g2 : G} (p : P) (h : g1 +ᵥ p = g2 +ᵥ p) : g1 = g2 := by
  rw [← vadd_vsub g1, h, vadd_vsub]
#align vadd_right_cancel vadd_right_cancel
-/

#print vadd_right_cancel_iff /-
@[simp]
theorem vadd_right_cancel_iff {g1 g2 : G} (p : P) : g1 +ᵥ p = g2 +ᵥ p ↔ g1 = g2 :=
  ⟨vadd_right_cancel p, fun h => h ▸ rfl⟩
#align vadd_right_cancel_iff vadd_right_cancel_iff
-/

#print vadd_right_injective /-
/-- Adding a group element to the point `p` is an injective
function. -/
theorem vadd_right_injective (p : P) : Function.Injective ((· +ᵥ p) : G → P) := fun g1 g2 =>
  vadd_right_cancel p
#align vadd_right_injective vadd_right_injective
-/

#print vadd_vsub_assoc /-
/-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
group element. -/
theorem vadd_vsub_assoc (g : G) (p1 p2 : P) : g +ᵥ p1 -ᵥ p2 = g + (p1 -ᵥ p2) :=
  by
  apply vadd_right_cancel p2
  rw [vsub_vadd, add_vadd, vsub_vadd]
#align vadd_vsub_assoc vadd_vsub_assoc
-/

#print vsub_self /-
/-- Subtracting a point from itself produces 0. -/
@[simp]
theorem vsub_self (p : P) : p -ᵥ p = (0 : G) := by
  rw [← zero_add (p -ᵥ p), ← vadd_vsub_assoc, vadd_vsub]
#align vsub_self vsub_self
-/

#print eq_of_vsub_eq_zero /-
/-- If subtracting two points produces 0, they are equal. -/
theorem eq_of_vsub_eq_zero {p1 p2 : P} (h : p1 -ᵥ p2 = (0 : G)) : p1 = p2 := by
  rw [← vsub_vadd p1 p2, h, zero_vadd]
#align eq_of_vsub_eq_zero eq_of_vsub_eq_zero
-/

#print vsub_eq_zero_iff_eq /-
/-- Subtracting two points produces 0 if and only if they are
equal. -/
@[simp]
theorem vsub_eq_zero_iff_eq {p1 p2 : P} : p1 -ᵥ p2 = (0 : G) ↔ p1 = p2 :=
  Iff.intro eq_of_vsub_eq_zero fun h => h ▸ vsub_self _
#align vsub_eq_zero_iff_eq vsub_eq_zero_iff_eq
-/

#print vsub_ne_zero /-
theorem vsub_ne_zero {p q : P} : p -ᵥ q ≠ (0 : G) ↔ p ≠ q :=
  not_congr vsub_eq_zero_iff_eq
#align vsub_ne_zero vsub_ne_zero
-/

#print vsub_add_vsub_cancel /-
/-- Cancellation adding the results of two subtractions. -/
@[simp]
theorem vsub_add_vsub_cancel (p1 p2 p3 : P) : p1 -ᵥ p2 + (p2 -ᵥ p3) = p1 -ᵥ p3 :=
  by
  apply vadd_right_cancel p3
  rw [add_vadd, vsub_vadd, vsub_vadd, vsub_vadd]
#align vsub_add_vsub_cancel vsub_add_vsub_cancel
-/

#print neg_vsub_eq_vsub_rev /-
/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
@[simp]
theorem neg_vsub_eq_vsub_rev (p1 p2 : P) : -(p1 -ᵥ p2) = p2 -ᵥ p1 :=
  by
  refine' neg_eq_of_add_eq_zero_right (vadd_right_cancel p1 _)
  rw [vsub_add_vsub_cancel, vsub_self]
#align neg_vsub_eq_vsub_rev neg_vsub_eq_vsub_rev
-/

#print vadd_vsub_eq_sub_vsub /-
theorem vadd_vsub_eq_sub_vsub (g : G) (p q : P) : g +ᵥ p -ᵥ q = g - (q -ᵥ p) := by
  rw [vadd_vsub_assoc, sub_eq_add_neg, neg_vsub_eq_vsub_rev]
#align vadd_vsub_eq_sub_vsub vadd_vsub_eq_sub_vsub
-/

#print vsub_vadd_eq_vsub_sub /-
/-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/
theorem vsub_vadd_eq_vsub_sub (p1 p2 : P) (g : G) : p1 -ᵥ (g +ᵥ p2) = p1 -ᵥ p2 - g := by
  rw [← add_right_inj (p2 -ᵥ p1 : G), vsub_add_vsub_cancel, ← neg_vsub_eq_vsub_rev, vadd_vsub, ←
    add_sub_assoc, ← neg_vsub_eq_vsub_rev, neg_add_self, zero_sub]
#align vsub_vadd_eq_vsub_sub vsub_vadd_eq_vsub_sub
-/

#print vsub_sub_vsub_cancel_right /-
/-- Cancellation subtracting the results of two subtractions. -/
@[simp]
theorem vsub_sub_vsub_cancel_right (p1 p2 p3 : P) : p1 -ᵥ p3 - (p2 -ᵥ p3) = p1 -ᵥ p2 := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd]
#align vsub_sub_vsub_cancel_right vsub_sub_vsub_cancel_right
-/

#print eq_vadd_iff_vsub_eq /-
/-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group
element. -/
theorem eq_vadd_iff_vsub_eq (p1 : P) (g : G) (p2 : P) : p1 = g +ᵥ p2 ↔ p1 -ᵥ p2 = g :=
  ⟨fun h => h.symm ▸ vadd_vsub _ _, fun h => h ▸ (vsub_vadd _ _).symm⟩
#align eq_vadd_iff_vsub_eq eq_vadd_iff_vsub_eq
-/

#print vadd_eq_vadd_iff_neg_add_eq_vsub /-
theorem vadd_eq_vadd_iff_neg_add_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ -v₁ + v₂ = p₁ -ᵥ p₂ := by
  rw [eq_vadd_iff_vsub_eq, vadd_vsub_assoc, ← add_right_inj (-v₁), neg_add_cancel_left, eq_comm]
#align vadd_eq_vadd_iff_neg_add_eq_vsub vadd_eq_vadd_iff_neg_add_eq_vsub
-/

namespace Set

open scoped Pointwise

#print Set.singleton_vsub_self /-
@[simp]
theorem singleton_vsub_self (p : P) : ({p} : Set P) -ᵥ {p} = {(0 : G)} := by
  rw [Set.singleton_vsub_singleton, vsub_self]
#align set.singleton_vsub_self Set.singleton_vsub_self
-/

end Set

#print vadd_vsub_vadd_cancel_right /-
@[simp]
theorem vadd_vsub_vadd_cancel_right (v₁ v₂ : G) (p : P) : v₁ +ᵥ p -ᵥ (v₂ +ᵥ p) = v₁ - v₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, vsub_self, add_zero]
#align vadd_vsub_vadd_cancel_right vadd_vsub_vadd_cancel_right
-/

#print vsub_left_cancel /-
/-- If the same point subtracted from two points produces equal
results, those points are equal. -/
theorem vsub_left_cancel {p1 p2 p : P} (h : p1 -ᵥ p = p2 -ᵥ p) : p1 = p2 := by
  rwa [← sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h 
#align vsub_left_cancel vsub_left_cancel
-/

#print vsub_left_cancel_iff /-
/-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/
@[simp]
theorem vsub_left_cancel_iff {p1 p2 p : P} : p1 -ᵥ p = p2 -ᵥ p ↔ p1 = p2 :=
  ⟨vsub_left_cancel, fun h => h ▸ rfl⟩
#align vsub_left_cancel_iff vsub_left_cancel_iff
-/

#print vsub_left_injective /-
/-- Subtracting the point `p` is an injective function. -/
theorem vsub_left_injective (p : P) : Function.Injective ((· -ᵥ p) : P → G) := fun p2 p3 =>
  vsub_left_cancel
#align vsub_left_injective vsub_left_injective
-/

#print vsub_right_cancel /-
/-- If subtracting two points from the same point produces equal
results, those points are equal. -/
theorem vsub_right_cancel {p1 p2 p : P} (h : p -ᵥ p1 = p -ᵥ p2) : p1 = p2 :=
  by
  refine' vadd_left_cancel (p -ᵥ p2) _
  rw [vsub_vadd, ← h, vsub_vadd]
#align vsub_right_cancel vsub_right_cancel
-/

#print vsub_right_cancel_iff /-
/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[simp]
theorem vsub_right_cancel_iff {p1 p2 p : P} : p -ᵥ p1 = p -ᵥ p2 ↔ p1 = p2 :=
  ⟨vsub_right_cancel, fun h => h ▸ rfl⟩
#align vsub_right_cancel_iff vsub_right_cancel_iff
-/

#print vsub_right_injective /-
/-- Subtracting a point from the point `p` is an injective
function. -/
theorem vsub_right_injective (p : P) : Function.Injective ((· -ᵥ ·) p : P → G) := fun p2 p3 =>
  vsub_right_cancel
#align vsub_right_injective vsub_right_injective
-/

end General

section comm

variable {G : Type _} {P : Type _} [AddCommGroup G] [AddTorsor G P]

#print vsub_sub_vsub_cancel_left /-
/-- Cancellation subtracting the results of two subtractions. -/
@[simp]
theorem vsub_sub_vsub_cancel_left (p1 p2 p3 : P) : p3 -ᵥ p2 - (p3 -ᵥ p1) = p1 -ᵥ p2 := by
  rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm, vsub_add_vsub_cancel]
#align vsub_sub_vsub_cancel_left vsub_sub_vsub_cancel_left
-/

#print vadd_vsub_vadd_cancel_left /-
@[simp]
theorem vadd_vsub_vadd_cancel_left (v : G) (p1 p2 : P) : v +ᵥ p1 -ᵥ (v +ᵥ p2) = p1 -ᵥ p2 := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_cancel']
#align vadd_vsub_vadd_cancel_left vadd_vsub_vadd_cancel_left
-/

#print vsub_vadd_comm /-
theorem vsub_vadd_comm (p1 p2 p3 : P) : (p1 -ᵥ p2 : G) +ᵥ p3 = p3 -ᵥ p2 +ᵥ p1 :=
  by
  rw [← @vsub_eq_zero_iff_eq G, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub]
  simp
#align vsub_vadd_comm vsub_vadd_comm
-/

#print vadd_eq_vadd_iff_sub_eq_vsub /-
theorem vadd_eq_vadd_iff_sub_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂ := by
  rw [vadd_eq_vadd_iff_neg_add_eq_vsub, neg_add_eq_sub]
#align vadd_eq_vadd_iff_sub_eq_vsub vadd_eq_vadd_iff_sub_eq_vsub
-/

#print vsub_sub_vsub_comm /-
theorem vsub_sub_vsub_comm (p₁ p₂ p₃ p₄ : P) : p₁ -ᵥ p₂ - (p₃ -ᵥ p₄) = p₁ -ᵥ p₃ - (p₂ -ᵥ p₄) := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub]
#align vsub_sub_vsub_comm vsub_sub_vsub_comm
-/

end comm

namespace Prod

variable {G : Type _} {P : Type _} {G' : Type _} {P' : Type _} [AddGroup G] [AddGroup G']
  [AddTorsor G P] [AddTorsor G' P']

instance : AddTorsor (G × G') (P × P')
    where
  vadd v p := (v.1 +ᵥ p.1, v.2 +ᵥ p.2)
  zero_vadd p := by simp
  add_vadd := by simp [add_vadd]
  vsub p₁ p₂ := (p₁.1 -ᵥ p₂.1, p₁.2 -ᵥ p₂.2)
  Nonempty := Prod.nonempty
  vsub_vadd' p₁ p₂ := show (p₁.1 -ᵥ p₂.1 +ᵥ p₂.1, _) = p₁ by simp
  vadd_vsub' v p := show (v.1 +ᵥ p.1 -ᵥ p.1, v.2 +ᵥ p.2 -ᵥ p.2) = v by simp

#print Prod.fst_vadd /-
@[simp]
theorem fst_vadd (v : G × G') (p : P × P') : (v +ᵥ p).1 = v.1 +ᵥ p.1 :=
  rfl
#align prod.fst_vadd Prod.fst_vadd
-/

#print Prod.snd_vadd /-
@[simp]
theorem snd_vadd (v : G × G') (p : P × P') : (v +ᵥ p).2 = v.2 +ᵥ p.2 :=
  rfl
#align prod.snd_vadd Prod.snd_vadd
-/

#print Prod.mk_vadd_mk /-
@[simp]
theorem mk_vadd_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') +ᵥ (p, p') = (v +ᵥ p, v' +ᵥ p') :=
  rfl
#align prod.mk_vadd_mk Prod.mk_vadd_mk
-/

#print Prod.fst_vsub /-
@[simp]
theorem fst_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').1 = p₁.1 -ᵥ p₂.1 :=
  rfl
#align prod.fst_vsub Prod.fst_vsub
-/

#print Prod.snd_vsub /-
@[simp]
theorem snd_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').2 = p₁.2 -ᵥ p₂.2 :=
  rfl
#align prod.snd_vsub Prod.snd_vsub
-/

#print Prod.mk_vsub_mk /-
@[simp]
theorem mk_vsub_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') -ᵥ (p₂, p₂') : G × G') = (p₁ -ᵥ p₂, p₁' -ᵥ p₂') :=
  rfl
#align prod.mk_vsub_mk Prod.mk_vsub_mk
-/

end Prod

namespace Pi

universe u v w

variable {I : Type u} {fg : I → Type v} [∀ i, AddGroup (fg i)] {fp : I → Type w}

open AddAction AddTorsor

/-- A product of `add_torsor`s is an `add_torsor`. -/
instance [T : ∀ i, AddTorsor (fg i) (fp i)] : AddTorsor (∀ i, fg i) (∀ i, fp i)
    where
  vadd g p i := g i +ᵥ p i
  zero_vadd p := funext fun i => zero_vadd (fg i) (p i)
  add_vadd g₁ g₂ p := funext fun i => add_vadd (g₁ i) (g₂ i) (p i)
  vsub p₁ p₂ i := p₁ i -ᵥ p₂ i
  Nonempty := ⟨fun i => Classical.choice (T i).Nonempty⟩
  vsub_vadd' p₁ p₂ := funext fun i => vsub_vadd (p₁ i) (p₂ i)
  vadd_vsub' g p := funext fun i => vadd_vsub (g i) (p i)

end Pi

namespace Equiv

variable {G : Type _} {P : Type _} [AddGroup G] [AddTorsor G P]

#print Equiv.vaddConst /-
/-- `v ↦ v +ᵥ p` as an equivalence. -/
def vaddConst (p : P) : G ≃ P where
  toFun v := v +ᵥ p
  invFun p' := p' -ᵥ p
  left_inv v := vadd_vsub _ _
  right_inv p' := vsub_vadd _ _
#align equiv.vadd_const Equiv.vaddConst
-/

#print Equiv.coe_vaddConst /-
@[simp]
theorem coe_vaddConst (p : P) : ⇑(vaddConst p) = fun v => v +ᵥ p :=
  rfl
#align equiv.coe_vadd_const Equiv.coe_vaddConst
-/

#print Equiv.coe_vaddConst_symm /-
@[simp]
theorem coe_vaddConst_symm (p : P) : ⇑(vaddConst p).symm = fun p' => p' -ᵥ p :=
  rfl
#align equiv.coe_vadd_const_symm Equiv.coe_vaddConst_symm
-/

#print Equiv.constVSub /-
/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def constVSub (p : P) : P ≃ G where
  toFun := (· -ᵥ ·) p
  invFun v := -v +ᵥ p
  left_inv p' := by simp
  right_inv v := by simp [vsub_vadd_eq_vsub_sub]
#align equiv.const_vsub Equiv.constVSub
-/

#print Equiv.coe_constVSub /-
@[simp]
theorem coe_constVSub (p : P) : ⇑(constVSub p) = (· -ᵥ ·) p :=
  rfl
#align equiv.coe_const_vsub Equiv.coe_constVSub
-/

#print Equiv.coe_constVSub_symm /-
@[simp]
theorem coe_constVSub_symm (p : P) : ⇑(constVSub p).symm = fun v => -v +ᵥ p :=
  rfl
#align equiv.coe_const_vsub_symm Equiv.coe_constVSub_symm
-/

variable (P)

#print Equiv.constVAdd /-
/-- The permutation given by `p ↦ v +ᵥ p`. -/
def constVAdd (v : G) : Equiv.Perm P where
  toFun := (· +ᵥ ·) v
  invFun := (· +ᵥ ·) (-v)
  left_inv p := by simp [vadd_vadd]
  right_inv p := by simp [vadd_vadd]
#align equiv.const_vadd Equiv.constVAdd
-/

#print Equiv.coe_constVAdd /-
@[simp]
theorem coe_constVAdd (v : G) : ⇑(constVAdd P v) = (· +ᵥ ·) v :=
  rfl
#align equiv.coe_const_vadd Equiv.coe_constVAdd
-/

variable (G)

#print Equiv.constVAdd_zero /-
@[simp]
theorem constVAdd_zero : constVAdd P (0 : G) = 1 :=
  ext <| zero_vadd G
#align equiv.const_vadd_zero Equiv.constVAdd_zero
-/

variable {G}

#print Equiv.constVAdd_add /-
@[simp]
theorem constVAdd_add (v₁ v₂ : G) : constVAdd P (v₁ + v₂) = constVAdd P v₁ * constVAdd P v₂ :=
  ext <| add_vadd v₁ v₂
#align equiv.const_vadd_add Equiv.constVAdd_add
-/

#print Equiv.constVAddHom /-
/-- `equiv.const_vadd` as a homomorphism from `multiplicative G` to `equiv.perm P` -/
def constVAddHom : Multiplicative G →* Equiv.Perm P
    where
  toFun v := constVAdd P v.toAdd
  map_one' := constVAdd_zero G P
  map_mul' := constVAdd_add P
#align equiv.const_vadd_hom Equiv.constVAddHom
-/

variable {P}

open _Root_.Function

#print Equiv.pointReflection /-
/-- Point reflection in `x` as a permutation. -/
def pointReflection (x : P) : Perm P :=
  (constVSub x).trans (vaddConst x)
#align equiv.point_reflection Equiv.pointReflection
-/

#print Equiv.pointReflection_apply /-
theorem pointReflection_apply (x y : P) : pointReflection x y = x -ᵥ y +ᵥ x :=
  rfl
#align equiv.point_reflection_apply Equiv.pointReflection_apply
-/

#print Equiv.pointReflection_symm /-
@[simp]
theorem pointReflection_symm (x : P) : (pointReflection x).symm = pointReflection x :=
  ext <| by simp [point_reflection]
#align equiv.point_reflection_symm Equiv.pointReflection_symm
-/

#print Equiv.pointReflection_self /-
@[simp]
theorem pointReflection_self (x : P) : pointReflection x x = x :=
  vsub_vadd _ _
#align equiv.point_reflection_self Equiv.pointReflection_self
-/

#print Equiv.pointReflection_involutive /-
theorem pointReflection_involutive (x : P) : Involutive (pointReflection x : P → P) := fun y =>
  (Equiv.apply_eq_iff_eq_symm_apply _).2 <| by rw [point_reflection_symm]
#align equiv.point_reflection_involutive Equiv.pointReflection_involutive
-/

#print Equiv.pointReflection_fixed_iff_of_injective_bit0 /-
/-- `x` is the only fixed point of `point_reflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem pointReflection_fixed_iff_of_injective_bit0 {x y : P} (h : Injective (bit0 : G → G)) :
    pointReflection x y = y ↔ y = x := by
  rw [point_reflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
    neg_eq_iff_add_eq_zero, ← bit0, ← bit0_zero, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]
#align equiv.point_reflection_fixed_iff_of_injective_bit0 Equiv.pointReflection_fixed_iff_of_injective_bit0
-/

#print Equiv.injective_pointReflection_left_of_injective_bit0 /-
theorem injective_pointReflection_left_of_injective_bit0 {G P : Type _} [AddCommGroup G]
    [AddTorsor G P] (h : Injective (bit0 : G → G)) (y : P) :
    Injective fun x : P => pointReflection x y :=
  fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [point_reflection_apply, point_reflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero, ← bit0, ← bit0_zero,
    h.eq_iff, vsub_eq_zero_iff_eq] at hy 
#align equiv.injective_point_reflection_left_of_injective_bit0 Equiv.injective_pointReflection_left_of_injective_bit0
-/

end Equiv

#print AddTorsor.subsingleton_iff /-
theorem AddTorsor.subsingleton_iff (G P : Type _) [AddGroup G] [AddTorsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.vaddConst default).subsingleton_congr
#align add_torsor.subsingleton_iff AddTorsor.subsingleton_iff
-/

