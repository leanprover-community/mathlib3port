/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli

! This file was ported from Lean 3 source module combinatorics.quiver.push
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Basic

/-!

# Pushing a quiver structure along a map

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/868
> Any changes to this file require a corresponding PR to mathlib4.

Given a map `σ : V → W` and a `quiver` instance on `V`, this files defines a `quiver` instance
on `W` by associating to each arrow `v ⟶ v'` in `V` an arrow `σ v ⟶ σ v'` in `W`.

-/


universe v v₁ v₂ u u₁ u₂

variable {V : Type _} [Quiver V] {W : Type _} (σ : V → W)

/- warning: push -> Push is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u_1}} [_inst_1 : Quiver.{u_2, u_1} V] {W : Type.{u_3}}, (V -> W) -> Type.{u_3}
but is expected to have type
  forall {V : Type.{u_1}} {_inst_1 : Type.{u_2}}, (V -> _inst_1) -> Type.{u_2}
Case conversion may be inaccurate. Consider using '#align push Pushₓ'. -/
/-- The `quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unused_arguments]
def Push (σ : V → W) :=
  W
#align push Push

instance [h : Nonempty W] : Nonempty (Push σ) :=
  h

#print PushQuiver /-
/-- The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint has_nonempty_instance]
inductive PushQuiver {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V → W) : W → W → Type max u u₂ v
  | arrow {X Y : V} (f : X ⟶ Y) : PushQuiver (σ X) (σ Y)
#align push_quiver PushQuiver
-/

instance : Quiver (Push σ) :=
  ⟨PushQuiver σ⟩

namespace Push

#print Push.of /-
/-- The prefunctor induced by pushing arrows via `σ` -/
def of : V ⥤q Push σ where 
  obj := σ
  map X Y f := PushQuiver.arrow f
#align push.of Push.of
-/

/- warning: push.of_obj -> Push.of_obj is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {W : Type.{u3}} (σ : V -> W), Eq.{max (succ u1) (succ u3)} (V -> (Push.{u1, u2, u3} V _inst_1 W σ)) (Prefunctor.obj.{u2, succ (max u1 u3 u2), u1, u3} V _inst_1 (Push.{u1, u2, u3} V _inst_1 W σ) (Push.quiver.{u1, u2, u3} V _inst_1 W σ) (Push.of.{u1, u2, u3} V _inst_1 W σ)) σ
but is expected to have type
  forall {V : Type.{u3}} [_inst_1 : Quiver.{u1, u3} V] {W : Type.{u2}} (σ : V -> W), Eq.{max (succ u3) (succ u2)} (V -> (Push.{u3, u2} V W σ)) (Prefunctor.obj.{u1, max (max (succ u3) (succ u1)) (succ u2), u3, u2} V _inst_1 (Push.{u3, u2} V W σ) (instQuiverPush.{u3, u1, u2} V _inst_1 W σ) (Push.of.{u3, u1, u2} V _inst_1 W σ)) σ
Case conversion may be inaccurate. Consider using '#align push.of_obj Push.of_objₓ'. -/
@[simp]
theorem of_obj : (of σ).obj = σ :=
  rfl
#align push.of_obj Push.of_obj

variable {W' : Type _} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))

include φ h

#print Push.lift /-
/-- Given a function `τ : W → W'` and a prefunctor `φ : V ⥤q W'`, one can extend `τ` to be
a prefunctor `W ⥤q W'` if `τ` and `σ` factorize `φ` at the level of objects, where `W` is given
the pushforward quiver structure `push σ`. -/
def lift : Push σ ⥤q W' where 
  obj := τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y f => τ X ⟶ τ Y) fun X Y f => by
      rw [← h X, ← h Y]
      exact φ.map f
#align push.lift Push.lift
-/

/- warning: push.lift_obj -> Push.lift_obj is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {W : Type.{u3}} (σ : V -> W) {W' : Type.{u4}} [_inst_2 : Quiver.{u5, u4} W'] (φ : Prefunctor.{u2, u5, u1, u4} V _inst_1 W' _inst_2) (τ : W -> W') (h : forall (x : V), Eq.{succ u4} W' (Prefunctor.obj.{u2, u5, u1, u4} V _inst_1 W' _inst_2 φ x) (τ (σ x))), Eq.{max (succ u3) (succ u4)} ((Push.{u1, u2, u3} V _inst_1 W σ) -> W') (Prefunctor.obj.{succ (max u1 u3 u2), u5, u3, u4} (Push.{u1, u2, u3} V _inst_1 W σ) (Push.quiver.{u1, u2, u3} V _inst_1 W σ) W' _inst_2 (Push.lift.{u1, u2, u3, u4, u5} V _inst_1 W σ W' _inst_2 φ τ h)) τ
but is expected to have type
  forall {V : Type.{u3}} [_inst_1 : Quiver.{u2, u3} V] {W : Type.{u5}} (σ : V -> W) {W' : Type.{u4}} [_inst_2 : Quiver.{u1, u4} W'] (φ : Prefunctor.{u2, u1, u3, u4} V _inst_1 W' _inst_2) (τ : W -> W') (h : forall (x : V), Eq.{succ u4} W' (Prefunctor.obj.{u2, u1, u3, u4} V _inst_1 W' _inst_2 φ x) (τ (σ x))), Eq.{max (succ u5) (succ u4)} ((Push.{u3, u5} V W σ) -> W') (Prefunctor.obj.{max (max (succ u3) (succ u2)) (succ u5), u1, u5, u4} (Push.{u3, u5} V W σ) (instQuiverPush.{u3, u2, u5} V _inst_1 W σ) W' _inst_2 (Push.lift.{u3, u2, u5, u4, u1} V _inst_1 W σ W' _inst_2 φ τ h)) τ
Case conversion may be inaccurate. Consider using '#align push.lift_obj Push.lift_objₓ'. -/
theorem lift_obj : (lift σ φ τ h).obj = τ :=
  rfl
#align push.lift_obj Push.lift_obj

/- warning: push.lift_comp -> Push.lift_comp is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {W : Type.{u3}} (σ : V -> W) {W' : Type.{u4}} [_inst_2 : Quiver.{u5, u4} W'] (φ : Prefunctor.{u2, u5, u1, u4} V _inst_1 W' _inst_2) (τ : W -> W') (h : forall (x : V), Eq.{succ u4} W' (Prefunctor.obj.{u2, u5, u1, u4} V _inst_1 W' _inst_2 φ x) (τ (σ x))), Eq.{max (imax (succ u1) (succ u1) u2 u5) (succ u1) (succ u4)} (Prefunctor.{u2, u5, u1, u4} V _inst_1 W' _inst_2) (Prefunctor.comp.{u1, u2, u3, succ (max u1 u3 u2), u4, u5} V _inst_1 (Push.{u1, u2, u3} V _inst_1 W σ) (Push.quiver.{u1, u2, u3} V _inst_1 W σ) W' _inst_2 (Push.of.{u1, u2, u3} V _inst_1 W σ) (Push.lift.{u1, u2, u3, u4, u5} V _inst_1 W σ W' _inst_2 φ τ h)) φ
but is expected to have type
  forall {V : Type.{u5}} [_inst_1 : Quiver.{u4, u5} V] {W : Type.{u1}} (σ : V -> W) {W' : Type.{u3}} [_inst_2 : Quiver.{u2, u3} W'] (φ : Prefunctor.{u4, u2, u5, u3} V _inst_1 W' _inst_2) (τ : W -> W') (h : forall (x : V), Eq.{succ u3} W' (Prefunctor.obj.{u4, u2, u5, u3} V _inst_1 W' _inst_2 φ x) (τ (σ x))), Eq.{max (max (max (succ u5) u4) (succ u3)) u2} (Prefunctor.{u4, u2, u5, u3} V _inst_1 W' _inst_2) (Prefunctor.comp.{u5, u4, u1, max (max (succ u5) (succ u4)) (succ u1), u3, u2} V _inst_1 (Push.{u5, u1} V W σ) (instQuiverPush.{u5, u4, u1} V _inst_1 W σ) W' _inst_2 (Push.of.{u5, u4, u1} V _inst_1 W σ) (Push.lift.{u5, u4, u1, u3, u2} V _inst_1 W σ W' _inst_2 φ τ h)) φ
Case conversion may be inaccurate. Consider using '#align push.lift_comp Push.lift_compₓ'. -/
theorem lift_comp : (of σ ⋙q lift σ φ τ h) = φ := by
  fapply Prefunctor.ext
  · rintro
    simp only [Prefunctor.comp_obj]
    symm
    exact h X
  · rintro _ _ f
    simp only [Prefunctor.comp_map]
    apply eq_of_heq
    iterate 2 apply (cast_heq _ _).trans
    symm
    iterate 2 apply (eq_rec_heq _ _).trans
    rfl
#align push.lift_comp Push.lift_comp

/- warning: push.lift_unique -> Push.lift_unique is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {W : Type.{u3}} (σ : V -> W) {W' : Type.{u4}} [_inst_2 : Quiver.{u5, u4} W'] (φ : Prefunctor.{u2, u5, u1, u4} V _inst_1 W' _inst_2) (τ : W -> W') (h : forall (x : V), Eq.{succ u4} W' (Prefunctor.obj.{u2, u5, u1, u4} V _inst_1 W' _inst_2 φ x) (τ (σ x))) (Φ : Prefunctor.{succ (max u1 u3 u2), u5, u3, u4} (Push.{u1, u2, u3} V _inst_1 W σ) (Push.quiver.{u1, u2, u3} V _inst_1 W σ) W' _inst_2), (Eq.{max (succ u3) (succ u4)} ((Push.{u1, u2, u3} V _inst_1 W σ) -> W') (Prefunctor.obj.{succ (max u1 u3 u2), u5, u3, u4} (Push.{u1, u2, u3} V _inst_1 W σ) (Push.quiver.{u1, u2, u3} V _inst_1 W σ) W' _inst_2 Φ) τ) -> (Eq.{max (imax (succ u1) (succ u1) u2 u5) (succ u1) (succ u4)} (Prefunctor.{u2, u5, u1, u4} V _inst_1 W' _inst_2) (Prefunctor.comp.{u1, u2, u3, succ (max u1 u3 u2), u4, u5} V _inst_1 (Push.{u1, u2, u3} V _inst_1 W σ) (Push.quiver.{u1, u2, u3} V _inst_1 W σ) W' _inst_2 (Push.of.{u1, u2, u3} V _inst_1 W σ) Φ) φ) -> (Eq.{max (imax (succ u3) (succ u3) (succ (max u1 u3 u2)) u5) (succ u3) (succ u4)} (Prefunctor.{succ (max u1 u3 u2), u5, u3, u4} (Push.{u1, u2, u3} V _inst_1 W σ) (Push.quiver.{u1, u2, u3} V _inst_1 W σ) W' _inst_2) Φ (Push.lift.{u1, u2, u3, u4, u5} V _inst_1 W σ W' _inst_2 φ τ h))
but is expected to have type
  forall {V : Type.{u5}} [_inst_1 : Quiver.{u4, u5} V] {W : Type.{u3}} (σ : V -> W) {W' : Type.{u1}} [_inst_2 : Quiver.{u2, u1} W'] (φ : Prefunctor.{u4, u2, u5, u1} V _inst_1 W' _inst_2) (τ : W -> W') (h : forall (x : V), Eq.{succ u1} W' (Prefunctor.obj.{u4, u2, u5, u1} V _inst_1 W' _inst_2 φ x) (τ (σ x))) (Φ : Prefunctor.{max (max (succ u5) (succ u4)) (succ u3), u2, u3, u1} (Push.{u5, u3} V W σ) (instQuiverPush.{u5, u4, u3} V _inst_1 W σ) W' _inst_2), (Eq.{max (succ u3) (succ u1)} ((Push.{u5, u3} V W σ) -> W') (Prefunctor.obj.{max (max (succ u5) (succ u4)) (succ u3), u2, u3, u1} (Push.{u5, u3} V W σ) (instQuiverPush.{u5, u4, u3} V _inst_1 W σ) W' _inst_2 Φ) τ) -> (Eq.{max (max (max (succ u5) u4) (succ u1)) u2} (Prefunctor.{u4, u2, u5, u1} V _inst_1 W' _inst_2) (Prefunctor.comp.{u5, u4, u3, max (max (succ u5) (succ u4)) (succ u3), u1, u2} V _inst_1 (Push.{u5, u3} V W σ) (instQuiverPush.{u5, u4, u3} V _inst_1 W σ) W' _inst_2 (Push.of.{u5, u4, u3} V _inst_1 W σ) Φ) φ) -> (Eq.{max (max (max (max (succ u5) (succ u4)) (succ u3)) (succ u1)) u2} (Prefunctor.{max (max (succ u5) (succ u4)) (succ u3), u2, u3, u1} (Push.{u5, u3} V W σ) (instQuiverPush.{u5, u4, u3} V _inst_1 W σ) W' _inst_2) Φ (Push.lift.{u5, u4, u3, u1, u2} V _inst_1 W σ W' _inst_2 φ τ h))
Case conversion may be inaccurate. Consider using '#align push.lift_unique Push.lift_uniqueₓ'. -/
theorem lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by 
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · rintro
    simp_rw [← Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map, cast_eq]
    rfl
#align push.lift_unique Push.lift_unique

end Push

