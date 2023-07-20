/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathbin.Combinatorics.Quiver.Basic

#align_import combinatorics.quiver.push from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!

# Pushing a quiver structure along a map

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a map `σ : V → W` and a `quiver` instance on `V`, this files defines a `quiver` instance
on `W` by associating to each arrow `v ⟶ v'` in `V` an arrow `σ v ⟶ σ v'` in `W`.

-/


universe v v₁ v₂ u u₁ u₂

variable {V : Type _} [Quiver V] {W : Type _} (σ : V → W)

namespace Quiver

#print Quiver.Push /-
/-- The `quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unused_arguments]
def Push (σ : V → W) :=
  W
#align quiver.push Quiver.Push
-/

instance [h : Nonempty W] : Nonempty (Push σ) :=
  h

#print Quiver.PushQuiver /-
/-- The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint has_nonempty_instance]
inductive PushQuiver {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V → W) : W → W → Type max u u₂ v
  | arrow {X Y : V} (f : X ⟶ Y) : push_quiver (σ X) (σ Y)
#align quiver.push_quiver Quiver.PushQuiver
-/

instance : Quiver (Push σ) :=
  ⟨PushQuiver σ⟩

namespace Push

#print Quiver.Push.of /-
/-- The prefunctor induced by pushing arrows via `σ` -/
def of : V ⥤q Push σ where
  obj := σ
  map X Y f := PushQuiver.arrow f
#align quiver.push.of Quiver.Push.of
-/

#print Quiver.Push.of_obj /-
@[simp]
theorem of_obj : (of σ).obj = σ :=
  rfl
#align quiver.push.of_obj Quiver.Push.of_obj
-/

variable {W' : Type _} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))

#print Quiver.Push.lift /-
/-- Given a function `τ : W → W'` and a prefunctor `φ : V ⥤q W'`, one can extend `τ` to be
a prefunctor `W ⥤q W'` if `τ` and `σ` factorize `φ` at the level of objects, where `W` is given
the pushforward quiver structure `push σ`. -/
def lift : Push σ ⥤q W' where
  obj := τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y f => τ X ⟶ τ Y) fun X Y f => by rw [← h X, ← h Y];
      exact φ.map f
#align quiver.push.lift Quiver.Push.lift
-/

#print Quiver.Push.lift_obj /-
theorem lift_obj : (lift σ φ τ h).obj = τ :=
  rfl
#align quiver.push.lift_obj Quiver.Push.lift_obj
-/

#print Quiver.Push.lift_comp /-
theorem lift_comp : of σ ⋙q lift σ φ τ h = φ :=
  by
  fapply Prefunctor.ext
  · rintro; simp only [Prefunctor.comp_obj]; symm; exact h X
  · rintro _ _ f; simp only [Prefunctor.comp_map]
    apply eq_of_hEq
    iterate 2 apply (cast_hEq _ _).trans
    symm
    iterate 2 apply (eq_rec_hEq _ _).trans
    rfl
#align quiver.push.lift_comp Quiver.Push.lift_comp
-/

#print Quiver.Push.lift_unique /-
theorem lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : of σ ⋙q Φ = φ) :
    Φ = lift σ φ τ h := by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · rintro; simp_rw [← Φ₀]
  · rintro _ _ ⟨⟩; subst_vars; simp only [Prefunctor.comp_map, cast_eq]; rfl
#align quiver.push.lift_unique Quiver.Push.lift_unique
-/

end Push

end Quiver

