/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.basic
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pfunctor.Multivariate.Basic

/-!
# Multivariate quotients of polynomial functors.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive list_shape (a b : Type)
| nil : list_shape
| cons : a -> b -> list_shape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def list (a : Type) := fix list_shape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def multiset (a : Type) := qpf.quot list.perm list a -- not the actual notion
```

And `multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive tree (a : Type)
| node : a -> multiset tree -> tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive tree' (a : Type)
| node : a -> multiset tree' -> tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

 * constructions
   * fix
   * cofix
   * quot
   * comp
   * sigma / pi
   * prj
   * const

each proves that some operations on functors preserves the QPF structure

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open MvFunctor

#print MvQPF /-
/-- Multivariate quotients of polynomial functors.
-/
class MvQPF {n : ℕ} (F : TypeVec.{u} n → Type _) [MvFunctor F] where
  p : MvPFunctor.{u} n
  abs : ∀ {α}, P.Obj α → F α
  repr : ∀ {α}, F α → P.Obj α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α ⟹ β) (p : P.Obj α), abs (f <$$> p) = f <$$> abs p
#align mvqpf MvQPF
-/

namespace MvQPF

variable {n : ℕ} {F : TypeVec.{u} n → Type _} [MvFunctor F] [q : MvQPF F]

include q

open MvFunctor (Liftp Liftr)

/-!
### Show that every mvqpf is a lawful mvfunctor.
-/


/- warning: mvqpf.id_map -> MvQPF.id_map is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1] {α : TypeVec.{u1} n} (x : F α), Eq.{succ u2} (F α) (MvFunctor.map.{u1, u2} n F _inst_1 α α (TypeVec.id.{u1} n α) x) x
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1] {α : TypeVec.{u2} n} (x : F α), Eq.{succ u1} (F α) (MvFunctor.map.{u2, u1} n F _inst_1 α α (TypeVec.id.{u2} n α) x) x
Case conversion may be inaccurate. Consider using '#align mvqpf.id_map MvQPF.id_mapₓ'. -/
protected theorem id_map {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x :=
  by
  rw [← abs_repr x]
  cases' repr x with a f
  rw [← abs_map]
  rfl
#align mvqpf.id_map MvQPF.id_map

/- warning: mvqpf.comp_map -> MvQPF.comp_map is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1] {α : TypeVec.{u1} n} {β : TypeVec.{u1} n} {γ : TypeVec.{u1} n} (f : TypeVec.Arrow.{u1, u1} n α β) (g : TypeVec.Arrow.{u1, u1} n β γ) (x : F α), Eq.{succ u2} (F γ) (MvFunctor.map.{u1, u2} n (fun {α : TypeVec.{u1} n} => F α) _inst_1 α γ (TypeVec.comp.{u1, u1, u1} n α β γ g f) x) (MvFunctor.map.{u1, u2} n F _inst_1 β γ g (MvFunctor.map.{u1, u2} n F _inst_1 α β f x))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1] {α : TypeVec.{u2} n} {β : TypeVec.{u2} n} {γ : TypeVec.{u2} n} (f : TypeVec.Arrow.{u2, u2} n α β) (g : TypeVec.Arrow.{u2, u2} n β γ) (x : F α), Eq.{succ u1} (F γ) (MvFunctor.map.{u2, u1} n F _inst_1 α γ (TypeVec.comp.{u2, u2, u2} n α β γ g f) x) (MvFunctor.map.{u2, u1} n F _inst_1 β γ g (MvFunctor.map.{u2, u1} n F _inst_1 α β f x))
Case conversion may be inaccurate. Consider using '#align mvqpf.comp_map MvQPF.comp_mapₓ'. -/
@[simp]
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
    (g ⊚ f) <$$> x = g <$$> f <$$> x := by
  rw [← abs_repr x]
  cases' repr x with a f
  rw [← abs_map, ← abs_map, ← abs_map]
  rfl
#align mvqpf.comp_map MvQPF.comp_map

#print MvQPF.lawfulMvFunctor /-
instance (priority := 100) lawfulMvFunctor : LawfulMvFunctor F
    where
  id_map := @MvQPF.id_map n F _ _
  comp_map := @comp_map n F _ _
#align mvqpf.is_lawful_mvfunctor MvQPF.lawfulMvFunctor
-/

/- warning: mvqpf.liftp_iff -> MvQPF.liftP_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1] {α : TypeVec.{u1} n} (p : forall {{i : Fin2 n}}, (α i) -> Prop) (x : F α), Iff (MvFunctor.LiftP.{u1, u2} n F _inst_1 (fun (i : Fin2 n) => α i) p x) (Exists.{succ u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => Exists.{succ u1} (TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) (fun (f : TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) => And (Eq.{succ u2} (F α) x (MvQPF.abs.{u1, u2} n F _inst_1 q α (Sigma.mk.{u1, u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) a f))) (forall (i : Fin2 n) (j : MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i), p i (f i j)))))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1] {α : TypeVec.{u2} n} (p : forall {{i : Fin2 n}}, (α i) -> Prop) (x : F α), Iff (MvFunctor.LiftP.{u2, u1} n F _inst_1 (fun (i : Fin2 n) => α i) p x) (Exists.{succ u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => Exists.{succ u2} (TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) (fun (f : TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) => And (Eq.{succ u1} (F α) x (MvQPF.abs.{u2, u1} n F _inst_1 q α (Sigma.mk.{u2, u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) a f))) (forall (i : Fin2 n) (j : MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i), p i (f i j)))))
Case conversion may be inaccurate. Consider using '#align mvqpf.liftp_iff MvQPF.liftP_iffₓ'. -/
-- Lifting predicates and relations
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : F α) :
    LiftP p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
  by
  constructor
  · rintro ⟨y, hy⟩
    cases' h : repr y with a f
    use a, fun i j => (f i j).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i j
    apply (f i j).property
  rintro ⟨a, f, h₀, h₁⟩; dsimp at *
  use abs ⟨a, fun i j => ⟨f i j, h₁ i j⟩⟩
  rw [← abs_map, h₀]; rfl
#align mvqpf.liftp_iff MvQPF.liftP_iff

/- warning: mvqpf.liftr_iff -> MvQPF.liftR_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1] {α : TypeVec.{u1} n} (r : forall {{i : Fin2 n}}, (α i) -> (α i) -> Prop) (x : F α) (y : F α), Iff (MvFunctor.LiftR.{u1, u2} n F _inst_1 (fun (i : Fin2 n) => α i) r x y) (Exists.{succ u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => Exists.{succ u1} (TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) (fun (f₀ : TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) => Exists.{succ u1} (TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) (fun (f₁ : TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) => And (Eq.{succ u2} (F α) x (MvQPF.abs.{u1, u2} n F _inst_1 q α (Sigma.mk.{u1, u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) a f₀))) (And (Eq.{succ u2} (F α) y (MvQPF.abs.{u1, u2} n F _inst_1 q α (Sigma.mk.{u1, u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) a f₁))) (forall (i : Fin2 n) (j : MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i), r i (f₀ i j) (f₁ i j)))))))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1] {α : TypeVec.{u2} n} (r : forall {i : Fin2 n}, (α i) -> (α i) -> Prop) (x : F α) (y : F α), Iff (MvFunctor.LiftR.{u2, u1} n F _inst_1 (fun {i : Fin2 n} => α i) (fun {i._@.Mathlib.Data.QPF.Multivariate.Basic._hyg.634 : Fin2 n} => r i._@.Mathlib.Data.QPF.Multivariate.Basic._hyg.634) x y) (Exists.{succ u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => Exists.{succ u2} (TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) (fun (f₀ : TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) => Exists.{succ u2} (TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) (fun (f₁ : TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) => And (Eq.{succ u1} (F α) x (MvQPF.abs.{u2, u1} n F _inst_1 q α (Sigma.mk.{u2, u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) a f₀))) (And (Eq.{succ u1} (F α) y (MvQPF.abs.{u2, u1} n F _inst_1 q α (Sigma.mk.{u2, u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) a f₁))) (forall (i : Fin2 n) (j : MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i), r i (f₀ i j) (f₁ i j)))))))
Case conversion may be inaccurate. Consider using '#align mvqpf.liftr_iff MvQPF.liftR_iffₓ'. -/
theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : F α) :
    LiftR r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
  by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    cases' h : repr u with a f
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]
      rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]
      rfl
    intro i j
    exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩
  dsimp; constructor
  · rw [xeq, ← abs_map]
    rfl
  rw [yeq, ← abs_map]; rfl
#align mvqpf.liftr_iff MvQPF.liftR_iff

open Set

open MvFunctor

/- warning: mvqpf.mem_supp -> MvQPF.mem_supp is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1] {α : TypeVec.{u1} n} (x : F α) (i : Fin2 n) (u : α i), Iff (Membership.Mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.hasMem.{u1} (α i)) u (MvFunctor.supp.{u1, u2} n F _inst_1 α x i)) (forall (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (f : TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α), (Eq.{succ u2} (F α) (MvQPF.abs.{u1, u2} n F _inst_1 q α (Sigma.mk.{u1, u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) a f)) x) -> (Membership.Mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.hasMem.{u1} (α i)) u (Set.image.{u1, u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i) (α i) (f i) (Set.univ.{u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i)))))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1] {α : TypeVec.{u2} n} (x : F α) (i : Fin2 n) (u : α i), Iff (Membership.mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.instMembershipSet.{u2} (α i)) u (MvFunctor.supp.{u2, u1} n F _inst_1 α x i)) (forall (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (f : TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α), (Eq.{succ u1} (F α) (MvQPF.abs.{u2, u1} n F _inst_1 q α (Sigma.mk.{u2, u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) a f)) x) -> (Membership.mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.instMembershipSet.{u2} (α i)) u (Set.image.{u2, u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i) (α i) (f i) (Set.univ.{u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i)))))
Case conversion may be inaccurate. Consider using '#align mvqpf.mem_supp MvQPF.mem_suppₓ'. -/
theorem mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) :
    u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ :=
  by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : liftp (fun i u => u ∈ f i '' univ) x :=
      by
      rw [liftp_iff]
      refine' ⟨a, f, haf.symm, _⟩
      intro i u
      exact mem_image_of_mem _ (mem_univ _)
    exact h this
  intro h p; rw [liftp_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  rw [← hi]; apply h'
#align mvqpf.mem_supp MvQPF.mem_supp

/- warning: mvqpf.supp_eq -> MvQPF.supp_eq is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1] {α : TypeVec.{u1} n} {i : Fin2 n} (x : F α), Eq.{succ u1} (Set.{u1} (α i)) (MvFunctor.supp.{u1, u2} n F _inst_1 α x i) (setOf.{u1} (α i) (fun (u : α i) => forall (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (f : TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α), (Eq.{succ u2} (F α) (MvQPF.abs.{u1, u2} n F _inst_1 q α (Sigma.mk.{u1, u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) a f)) x) -> (Membership.Mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.hasMem.{u1} (α i)) u (Set.image.{u1, u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i) (α i) (f i) (Set.univ.{u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i))))))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1] {α : TypeVec.{u2} n} {i : Fin2 n} (x : F α), Eq.{succ u2} (Set.{u2} (α i)) (MvFunctor.supp.{u2, u1} n F _inst_1 α x i) (setOf.{u2} (α i) (fun (u : α i) => forall (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (f : TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α), (Eq.{succ u1} (F α) (MvQPF.abs.{u2, u1} n F _inst_1 q α (Sigma.mk.{u2, u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) a f)) x) -> (Membership.mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.instMembershipSet.{u2} (α i)) u (Set.image.{u2, u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i) (α i) (f i) (Set.univ.{u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i))))))
Case conversion may be inaccurate. Consider using '#align mvqpf.supp_eq MvQPF.supp_eqₓ'. -/
theorem supp_eq {α : TypeVec n} {i} (x : F α) :
    supp x i = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ } := by ext <;> apply mem_supp
#align mvqpf.supp_eq MvQPF.supp_eq

/- warning: mvqpf.has_good_supp_iff -> MvQPF.has_good_supp_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1] {α : TypeVec.{u1} n} (x : F α), Iff (forall (p : forall (i : Fin2 n), (α i) -> Prop), Iff (MvFunctor.LiftP.{u1, u2} n F _inst_1 α p x) (forall (i : Fin2 n) (u : α i), (Membership.Mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.hasMem.{u1} (α i)) u (MvFunctor.supp.{u1, u2} n F _inst_1 α x i)) -> (p i u))) (Exists.{succ u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => Exists.{succ u1} (TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) (fun (f : TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) => And (Eq.{succ u2} (F α) (MvQPF.abs.{u1, u2} n F _inst_1 q α (Sigma.mk.{u1, u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) a f)) x) (forall (i : Fin2 n) (a' : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (f' : TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a') α), (Eq.{succ u2} (F α) (MvQPF.abs.{u1, u2} n F _inst_1 q α (Sigma.mk.{u1, u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) a' f')) x) -> (HasSubset.Subset.{u1} (Set.{u1} (α i)) (Set.hasSubset.{u1} (α i)) (Set.image.{u1, u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i) (α i) (f i) (Set.univ.{u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i))) (Set.image.{u1, u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a' i) (α i) (f' i) (Set.univ.{u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a' i))))))))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1] {α : TypeVec.{u2} n} (x : F α), Iff (forall (p : forall (i : Fin2 n), (α i) -> Prop), Iff (MvFunctor.LiftP.{u2, u1} n F _inst_1 α p x) (forall (i : Fin2 n) (u : α i), (Membership.mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.instMembershipSet.{u2} (α i)) u (MvFunctor.supp.{u2, u1} n F _inst_1 α x i)) -> (p i u))) (Exists.{succ u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => Exists.{succ u2} (TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) (fun (f : TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) => And (Eq.{succ u1} (F α) (MvQPF.abs.{u2, u1} n F _inst_1 q α (Sigma.mk.{u2, u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) a f)) x) (forall (i : Fin2 n) (a' : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (f' : TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a') α), (Eq.{succ u1} (F α) (MvQPF.abs.{u2, u1} n F _inst_1 q α (Sigma.mk.{u2, u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) a' f')) x) -> (HasSubset.Subset.{u2} (Set.{u2} (α i)) (Set.instHasSubsetSet.{u2} (α i)) (Set.image.{u2, u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i) (α i) (f i) (Set.univ.{u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i))) (Set.image.{u2, u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a' i) (α i) (f' i) (Set.univ.{u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a' i))))))))
Case conversion may be inaccurate. Consider using '#align mvqpf.has_good_supp_iff MvQPF.has_good_supp_iffₓ'. -/
theorem has_good_supp_iff {α : TypeVec n} (x : F α) :
    (∀ p, LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ i a' f', abs ⟨a', f'⟩ = x → f i '' univ ⊆ f' i '' univ :=
  by
  constructor
  · intro h
    have : liftp (supp x) x := by
      rw [h]
      introv
      exact id
    rw [liftp_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine' ⟨a, f, xeq.symm, _⟩
    intro a' f' h''
    rintro hu u ⟨j, h₂, hfi⟩
    have hh : u ∈ supp x a' := by rw [← hfi] <;> apply h'
    refine' (mem_supp x _ u).mp hh _ _ hu
  rintro ⟨a, f, xeq, h⟩ p; rw [liftp_iff]; constructor
  · rintro ⟨a', f', xeq', h'⟩ i u usuppx
    rcases(mem_supp x _ u).mp (@usuppx) a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    rw [← f'ieq]
    apply h'
  intro h'
  refine' ⟨a, f, xeq.symm, _⟩; intro j y
  apply h'; rw [mem_supp]
  intro a' f' xeq'
  apply h _ a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)
#align mvqpf.has_good_supp_iff MvQPF.has_good_supp_iff

variable (q)

#print MvQPF.IsUniform /-
/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : TypeVec n⦄ (a a' : q.p.A) (f : q.p.B a ⟹ α) (f' : q.p.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ
#align mvqpf.is_uniform MvQPF.IsUniform
-/

#print MvQPF.LiftPPreservation /-
/-- does `abs` preserve `liftp`? -/
def LiftPPreservation : Prop :=
  ∀ ⦃α : TypeVec n⦄ (p : ∀ ⦃i⦄, α i → Prop) (x : q.p.Obj α), LiftP p (abs x) ↔ LiftP p x
#align mvqpf.liftp_preservation MvQPF.LiftPPreservation
-/

#print MvQPF.SuppPreservation /-
/-- does `abs` preserve `supp`? -/
def SuppPreservation : Prop :=
  ∀ ⦃α⦄ (x : q.p.Obj α), supp (abs x) = supp x
#align mvqpf.supp_preservation MvQPF.SuppPreservation
-/

variable (q)

/- warning: mvqpf.supp_eq_of_is_uniform -> MvQPF.supp_eq_of_isUniform is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1], (MvQPF.IsUniform.{u1, u2} n F _inst_1 q) -> (forall {α : TypeVec.{u1} n} (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (f : TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) (i : Fin2 n), Eq.{succ u1} (Set.{u1} (α i)) (MvFunctor.supp.{u1, u2} n F _inst_1 α (MvQPF.abs.{u1, u2} n F _inst_1 q α (Sigma.mk.{u1, u1} (MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q)) => TypeVec.Arrow.{u1, u1} n (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a) α) a f)) i) (Set.image.{u1, u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i) (α i) (f i) (Set.univ.{u1} (MvPFunctor.b.{u1} n (MvQPF.p.{u1, u2} n F _inst_1 q) a i))))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1], (MvQPF.IsUniform.{u2, u1} n F _inst_1 q) -> (forall {α : TypeVec.{u2} n} (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (f : TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) (i : Fin2 n), Eq.{succ u2} (Set.{u2} (α i)) (MvFunctor.supp.{u2, u1} n F _inst_1 α (MvQPF.abs.{u2, u1} n F _inst_1 q α (Sigma.mk.{u2, u2} (MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) (fun (a : MvPFunctor.A.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q)) => TypeVec.Arrow.{u2, u2} n (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a) α) a f)) i) (Set.image.{u2, u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i) (α i) (f i) (Set.univ.{u2} (MvPFunctor.B.{u2} n (MvQPF.P.{u2, u1} n F _inst_1 q) a i))))
Case conversion may be inaccurate. Consider using '#align mvqpf.supp_eq_of_is_uniform MvQPF.supp_eq_of_isUniformₓ'. -/
theorem supp_eq_of_isUniform (h : q.IsUniform) {α : TypeVec n} (a : q.p.A) (f : q.p.B a ⟹ α) :
    ∀ i, supp (abs ⟨a, f⟩) i = f i '' univ := by
  intro ; ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'
#align mvqpf.supp_eq_of_is_uniform MvQPF.supp_eq_of_isUniform

/- warning: mvqpf.liftp_iff_of_is_uniform -> MvQPF.liftP_iff_of_isUniform is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1], (MvQPF.IsUniform.{u1, u2} n F _inst_1 q) -> (forall {α : TypeVec.{u1} n} (x : F α) (p : forall (i : Fin2 n), (α i) -> Prop), Iff (MvFunctor.LiftP.{u1, u2} n F _inst_1 (fun (i : Fin2 n) => α i) p x) (forall (i : Fin2 n) (u : α i), (Membership.Mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.hasMem.{u1} (α i)) u (MvFunctor.supp.{u1, u2} n F _inst_1 α x i)) -> (p i u)))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1], (MvQPF.IsUniform.{u2, u1} n F _inst_1 q) -> (forall {α : TypeVec.{u2} n} (x : F α) (p : forall (i : Fin2 n), (α i) -> Prop), Iff (MvFunctor.LiftP.{u2, u1} n F _inst_1 (fun (i : Fin2 n) => α i) p x) (forall (i : Fin2 n) (u : α i), (Membership.mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.instMembershipSet.{u2} (α i)) u (MvFunctor.supp.{u2, u1} n F _inst_1 α x i)) -> (p i u)))
Case conversion may be inaccurate. Consider using '#align mvqpf.liftp_iff_of_is_uniform MvQPF.liftP_iff_of_isUniformₓ'. -/
theorem liftP_iff_of_isUniform (h : q.IsUniform) {α : TypeVec n} (x : F α) (p : ∀ i, α i → Prop) :
    LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u :=
  by
  rw [liftp_iff, ← abs_repr x]
  cases' repr x with a f; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_is_uniform h, h _ _ _ _ abseq]
    rintro b ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine' ⟨a, f, rfl, fun _ i => h' _ _ _⟩
  rw [supp_eq_of_is_uniform h]
  exact ⟨i, mem_univ i, rfl⟩
#align mvqpf.liftp_iff_of_is_uniform MvQPF.liftP_iff_of_isUniform

/- warning: mvqpf.supp_map -> MvQPF.supp_map is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1], (MvQPF.IsUniform.{u1, u2} n F _inst_1 q) -> (forall {α : TypeVec.{u1} n} {β : TypeVec.{u1} n} (g : TypeVec.Arrow.{u1, u1} n α β) (x : F α) (i : Fin2 n), Eq.{succ u1} (Set.{u1} (β i)) (MvFunctor.supp.{u1, u2} n (fun {α : TypeVec.{u1} n} => F α) _inst_1 β (MvFunctor.map.{u1, u2} n (fun {α : TypeVec.{u1} n} => F α) _inst_1 α β g x) i) (Set.image.{u1, u1} (α i) (β i) (g i) (MvFunctor.supp.{u1, u2} n (fun {α : TypeVec.{u1} n} => F α) _inst_1 α x i)))
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1], (MvQPF.IsUniform.{u2, u1} n F _inst_1 q) -> (forall {α : TypeVec.{u2} n} {β : TypeVec.{u2} n} (g : TypeVec.Arrow.{u2, u2} n α β) (x : F α) (i : Fin2 n), Eq.{succ u2} (Set.{u2} (β i)) (MvFunctor.supp.{u2, u1} n F _inst_1 β (MvFunctor.map.{u2, u1} n F _inst_1 α β g x) i) (Set.image.{u2, u2} (α i) (β i) (g i) (MvFunctor.supp.{u2, u1} n F _inst_1 α x i)))
Case conversion may be inaccurate. Consider using '#align mvqpf.supp_map MvQPF.supp_mapₓ'. -/
theorem supp_map (h : q.IsUniform) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i) :
    supp (g <$$> x) i = g i '' supp x i :=
  by
  rw [← abs_repr x]; cases' repr x with a f; rw [← abs_map, MvPFunctor.map_eq]
  rw [supp_eq_of_is_uniform h, supp_eq_of_is_uniform h, ← image_comp]
  rfl
#align mvqpf.supp_map MvQPF.supp_map

/- warning: mvqpf.supp_preservation_iff_uniform -> MvQPF.suppPreservation_iff_isUniform is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1], Iff (MvQPF.SuppPreservation.{u1, u2} n F _inst_1 q) (MvQPF.IsUniform.{u1, u2} n F _inst_1 q)
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1], Iff (MvQPF.SuppPreservation.{u2, u1} n F _inst_1 q) (MvQPF.IsUniform.{u2, u1} n F _inst_1 q)
Case conversion may be inaccurate. Consider using '#align mvqpf.supp_preservation_iff_uniform MvQPF.suppPreservation_iff_isUniformₓ'. -/
theorem suppPreservation_iff_isUniform : q.SuppPreservation ↔ q.IsUniform :=
  by
  constructor
  · intro h α a a' f f' h' i
    rw [← MvPFunctor.supp_eq, ← MvPFunctor.supp_eq, ← h, h', h]
  · rintro h α ⟨a, f⟩
    ext
    rwa [supp_eq_of_is_uniform, MvPFunctor.supp_eq]
#align mvqpf.supp_preservation_iff_uniform MvQPF.suppPreservation_iff_isUniform

/- warning: mvqpf.supp_preservation_iff_liftp_preservation -> MvQPF.suppPreservation_iff_liftpPreservation is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1], Iff (MvQPF.SuppPreservation.{u1, u2} n F _inst_1 q) (MvQPF.LiftPPreservation.{u1, u2} n F _inst_1 q)
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1], Iff (MvQPF.SuppPreservation.{u2, u1} n F _inst_1 q) (MvQPF.LiftPPreservation.{u2, u1} n F _inst_1 q)
Case conversion may be inaccurate. Consider using '#align mvqpf.supp_preservation_iff_liftp_preservation MvQPF.suppPreservation_iff_liftpPreservationₓ'. -/
theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftPPreservation :=
  by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [supp_preservation_iff_uniform] at h'
    dsimp only [supp_preservation, supp] at h
    simp only [liftp_iff_of_is_uniform, supp_eq_of_is_uniform, MvPFunctor.liftP_iff', h',
      image_univ, mem_range, exists_imp]
    constructor <;> intros <;> subst_vars <;> solve_by_elim
  · rintro α ⟨a, f⟩
    simp only [liftp_preservation] at h
    ext
    simp [supp, h]
#align mvqpf.supp_preservation_iff_liftp_preservation MvQPF.suppPreservation_iff_liftpPreservation

/- warning: mvqpf.liftp_preservation_iff_uniform -> MvQPF.liftpPreservation_iff_uniform is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} n F] [q : MvQPF.{u1, u2} n F _inst_1], Iff (MvQPF.LiftPPreservation.{u1, u2} n F _inst_1 q) (MvQPF.IsUniform.{u1, u2} n F _inst_1 q)
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} n F] [q : MvQPF.{u2, u1} n F _inst_1], Iff (MvQPF.LiftPPreservation.{u2, u1} n F _inst_1 q) (MvQPF.IsUniform.{u2, u1} n F _inst_1 q)
Case conversion may be inaccurate. Consider using '#align mvqpf.liftp_preservation_iff_uniform MvQPF.liftpPreservation_iff_uniformₓ'. -/
theorem liftpPreservation_iff_uniform : q.LiftPPreservation ↔ q.IsUniform := by
  rw [← supp_preservation_iff_liftp_preservation, supp_preservation_iff_uniform]
#align mvqpf.liftp_preservation_iff_uniform MvQPF.liftpPreservation_iff_uniform

end MvQPF

