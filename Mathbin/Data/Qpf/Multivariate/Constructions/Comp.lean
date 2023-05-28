/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.constructions.comp
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pfunctor.Multivariate.Basic
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
# The composition of QPFs is itself a QPF

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/


universe u

namespace MvQPF

open MvFunctor

variable {n m : ℕ} (F : TypeVec.{u} n → Type _) [fF : MvFunctor F] [q : MvQPF F]
  (G : Fin2 n → TypeVec.{u} m → Type u) [fG : ∀ i, MvFunctor <| G i] [q' : ∀ i, MvQPF <| G i]

#print MvQPF.Comp /-
/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/
def Comp (v : TypeVec.{u} m) : Type _ :=
  F fun i : Fin2 n => G i v
#align mvqpf.comp MvQPF.Comp
-/

namespace Comp

open MvFunctor MvPFunctor

variable {F G} {α β : TypeVec.{u} m} (f : α ⟹ β)

instance [I : Inhabited (F fun i : Fin2 n => G i α)] : Inhabited (Comp F G α) :=
  I

#print MvQPF.Comp.mk /-
/-- Constructor for functor composition -/
protected def mk (x : F fun i => G i α) : (Comp F G) α :=
  x
#align mvqpf.comp.mk MvQPF.Comp.mk
-/

#print MvQPF.Comp.get /-
/-- Destructor for functor composition -/
protected def get (x : (Comp F G) α) : F fun i => G i α :=
  x
#align mvqpf.comp.get MvQPF.Comp.get
-/

/- warning: mvqpf.comp.mk_get -> MvQPF.Comp.mk_get is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} {G : (Fin2 n) -> (TypeVec.{u1} m) -> Type.{u1}} {α : TypeVec.{u1} m} (x : MvQPF.Comp.{u1, u2} n m F G α), Eq.{succ u2} (MvQPF.Comp.{u1, u2} n m F G α) (MvQPF.Comp.mk.{u1, u2} n m F G α (MvQPF.Comp.get.{u1, u2} n m F G α x)) x
but is expected to have type
  forall {n : Nat} {m : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} {G : (Fin2 n) -> (TypeVec.{u2} m) -> Type.{u2}} {α : TypeVec.{u2} m} (x : MvQPF.Comp.{u2, u1} n m F G α), Eq.{succ u1} (MvQPF.Comp.{u2, u1} n m F (fun (i : Fin2 n) => G i) α) (MvQPF.Comp.mk.{u2, u1} n m F (fun (i : Fin2 n) => G i) α (MvQPF.Comp.get.{u2, u1} n m F G α x)) x
Case conversion may be inaccurate. Consider using '#align mvqpf.comp.mk_get MvQPF.Comp.mk_getₓ'. -/
@[simp]
protected theorem mk_get (x : (Comp F G) α) : Comp.mk (Comp.get x) = x :=
  rfl
#align mvqpf.comp.mk_get MvQPF.Comp.mk_get

/- warning: mvqpf.comp.get_mk -> MvQPF.Comp.get_mk is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} {G : (Fin2 n) -> (TypeVec.{u1} m) -> Type.{u1}} {α : TypeVec.{u1} m} (x : F (fun (i : Fin2 n) => G i α)), Eq.{succ u2} (F (fun (i : Fin2 n) => G i α)) (MvQPF.Comp.get.{u1, u2} n m F G α (MvQPF.Comp.mk.{u1, u2} n m F G α x)) x
but is expected to have type
  forall {n : Nat} {m : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} {G : (Fin2 n) -> (TypeVec.{u2} m) -> Type.{u2}} {α : TypeVec.{u2} m} (x : F (fun (i : Fin2 n) => G i α)), Eq.{succ u1} (F (fun (i : Fin2 n) => G i α)) (MvQPF.Comp.get.{u2, u1} n m F (fun (i : Fin2 n) => G i) α (MvQPF.Comp.mk.{u2, u1} n m F (fun (i : Fin2 n) => G i) α x)) x
Case conversion may be inaccurate. Consider using '#align mvqpf.comp.get_mk MvQPF.Comp.get_mkₓ'. -/
@[simp]
protected theorem get_mk (x : F fun i => G i α) : Comp.get (Comp.mk x) = x :=
  rfl
#align mvqpf.comp.get_mk MvQPF.Comp.get_mk

include fG

#print MvQPF.Comp.map' /-
/-- map operation defined on a vector of functors -/
protected def map' : (fun i : Fin2 n => G i α) ⟹ fun i : Fin2 n => G i β := fun i => map f
#align mvqpf.comp.map' MvQPF.Comp.map'
-/

include fF

#print MvQPF.Comp.map /-
/-- The composition of functors is itself functorial -/
protected def map : (Comp F G) α → (Comp F G) β :=
  (map fun i => map f : (F fun i => G i α) → F fun i => G i β)
#align mvqpf.comp.map MvQPF.Comp.map
-/

instance : MvFunctor (Comp F G) where map α β := Comp.map

/- warning: mvqpf.comp.map_mk -> MvQPF.Comp.map_mk is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [fF : MvFunctor.{u1, u2} n F] {G : (Fin2 n) -> (TypeVec.{u1} m) -> Type.{u1}} [fG : forall (i : Fin2 n), MvFunctor.{u1, u1} m (G i)] {α : TypeVec.{u1} m} {β : TypeVec.{u1} m} (f : TypeVec.Arrow.{u1, u1} m α β) (x : F (fun (i : Fin2 n) => G i α)), Eq.{succ u2} (MvQPF.Comp.{u1, u2} n m F (fun (i : Fin2 n) {α : TypeVec.{u1} m} => G i α) β) (MvFunctor.map.{u1, u2} m (MvQPF.Comp.{u1, u2} n m F (fun (i : Fin2 n) {α : TypeVec.{u1} m} => G i α)) (MvQPF.Comp.mvfunctor.{u1, u2} n m F fF (fun (i : Fin2 n) {α : TypeVec.{u1} m} => G i α) (fun (i : Fin2 n) => fG i)) α β f (MvQPF.Comp.mk.{u1, u2} n m F (fun (i : Fin2 n) {α : TypeVec.{u1} m} => G i α) α x)) (MvQPF.Comp.mk.{u1, u2} n m F (fun (i : Fin2 n) {α : TypeVec.{u1} m} => G i α) β (MvFunctor.map.{u1, u2} n F fF (fun (i : Fin2 n) => G i α) (fun (i : Fin2 n) => G i β) (fun (i : Fin2 n) (x : G i α) => MvFunctor.map.{u1, u1} m (fun {α : TypeVec.{u1} m} => G i α) (fG i) α β f x) x))
but is expected to have type
  forall {n : Nat} {m : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [fF : MvFunctor.{u2, u1} n F] {G : (Fin2 n) -> (TypeVec.{u2} m) -> Type.{u2}} [fG : forall (i : Fin2 n), MvFunctor.{u2, u2} m (G i)] {α : TypeVec.{u2} m} {β : TypeVec.{u2} m} (f : TypeVec.Arrow.{u2, u2} m α β) (x : F (fun (i : Fin2 n) => G i α)), Eq.{succ u1} (MvQPF.Comp.{u2, u1} n m F (fun (i : Fin2 n) => G i) β) (MvFunctor.map.{u2, u1} m (MvQPF.Comp.{u2, u1} n m F (fun (i : Fin2 n) => G i)) (MvQPF.Comp.instMvFunctorComp.{u2, u1} n m F fF (fun (i : Fin2 n) => G i) (fun (i : Fin2 n) => fG i)) α β f (MvQPF.Comp.mk.{u2, u1} n m F (fun (i : Fin2 n) => G i) α x)) (MvQPF.Comp.mk.{u2, u1} n m F (fun (i : Fin2 n) => G i) β (MvFunctor.map.{u2, u1} n F fF (fun (i : Fin2 n) => G i α) (fun (i : Fin2 n) => G i β) (fun (i : Fin2 n) (x : G i α) => MvFunctor.map.{u2, u2} m (G i) (fG i) α β f x) x))
Case conversion may be inaccurate. Consider using '#align mvqpf.comp.map_mk MvQPF.Comp.map_mkₓ'. -/
theorem map_mk (x : F fun i => G i α) :
    f <$$> Comp.mk x = Comp.mk ((fun i (x : G i α) => f <$$> x) <$$> x) :=
  rfl
#align mvqpf.comp.map_mk MvQPF.Comp.map_mk

/- warning: mvqpf.comp.get_map -> MvQPF.Comp.get_map is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m : Nat} {F : (TypeVec.{u1} n) -> Type.{u2}} [fF : MvFunctor.{u1, u2} n F] {G : (Fin2 n) -> (TypeVec.{u1} m) -> Type.{u1}} [fG : forall (i : Fin2 n), MvFunctor.{u1, u1} m (G i)] {α : TypeVec.{u1} m} {β : TypeVec.{u1} m} (f : TypeVec.Arrow.{u1, u1} m α β) (x : MvQPF.Comp.{u1, u2} n m F G α), Eq.{succ u2} (F (fun (i : Fin2 n) => G i β)) (MvQPF.Comp.get.{u1, u2} n m F G β (MvFunctor.map.{u1, u2} m (MvQPF.Comp.{u1, u2} n m F G) (MvQPF.Comp.mvfunctor.{u1, u2} n m F fF G (fun (i : Fin2 n) => fG i)) α β f x)) (MvFunctor.map.{u1, u2} n F fF (fun (i : Fin2 n) => G i α) (fun (i : Fin2 n) => G i β) (fun (i : Fin2 n) (x : G i α) => MvFunctor.map.{u1, u1} m (fun {α : TypeVec.{u1} m} => G i α) (fG i) α β f x) (MvQPF.Comp.get.{u1, u2} n m F G α x))
but is expected to have type
  forall {n : Nat} {m : Nat} {F : (TypeVec.{u2} n) -> Type.{u1}} [fF : MvFunctor.{u2, u1} n F] {G : (Fin2 n) -> (TypeVec.{u2} m) -> Type.{u2}} [fG : forall (i : Fin2 n), MvFunctor.{u2, u2} m (G i)] {α : TypeVec.{u2} m} {β : TypeVec.{u2} m} (f : TypeVec.Arrow.{u2, u2} m α β) (x : MvQPF.Comp.{u2, u1} n m F G α), Eq.{succ u1} (F (fun (i : Fin2 n) => G i β)) (MvQPF.Comp.get.{u2, u1} n m F G β (MvFunctor.map.{u2, u1} m (MvQPF.Comp.{u2, u1} n m F G) (MvQPF.Comp.instMvFunctorComp.{u2, u1} n m F fF G (fun (i : Fin2 n) => fG i)) α β f x)) (MvFunctor.map.{u2, u1} n F fF (fun (i : Fin2 n) => G i α) (fun (i : Fin2 n) => G i β) (fun (i : Fin2 n) (x : G i α) => MvFunctor.map.{u2, u2} m (G i) (fG i) α β f x) (MvQPF.Comp.get.{u2, u1} n m F (fun (i : Fin2 n) => G i) α x))
Case conversion may be inaccurate. Consider using '#align mvqpf.comp.get_map MvQPF.Comp.get_mapₓ'. -/
theorem get_map (x : Comp F G α) :
    Comp.get (f <$$> x) = (fun i (x : G i α) => f <$$> x) <$$> Comp.get x :=
  rfl
#align mvqpf.comp.get_map MvQPF.Comp.get_map

include q q'

instance : MvQPF (Comp F G)
    where
  p := MvPFunctor.comp (p F) fun i => p <| G i
  abs α := Comp.mk ∘ (map fun i => abs) ∘ abs ∘ MvPFunctor.comp.get
  repr α :=
    MvPFunctor.comp.mk ∘
      repr ∘ (map fun i => (repr : G i α → (fun i : Fin2 n => Obj (p (G i)) α) i)) ∘ Comp.get
  abs_repr := by intros ; simp [(· ∘ ·), MvFunctor.map_map, (· ⊚ ·), abs_repr]
  abs_map := by
    intros ; simp [(· ∘ ·)]; rw [← abs_map]
    simp [MvFunctor.id_map, (· ⊚ ·), map_mk, MvPFunctor.comp.get_map, abs_map, MvFunctor.map_map,
      abs_repr]

end Comp

end MvQPF

