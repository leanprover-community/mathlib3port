/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Tactic.Basic
import Mathbin.Algebra.Module.Basic

/-!
# Bundle
Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.
We provide a type synonym of `Σ x, E x` as `bundle.total_space E`, to be able to endow it with
a topology which is not the disjoint union topology `sigma.topological_space`. In general, the
constructions of fiber bundles we will make will be of this form.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/


namespace Bundle

variable {B : Type _} (E : B → Type _)

/-- `total_space E` is the total space of the bundle `Σ x, E x`. This type synonym is used to avoid
conflicts with general sigma types.
-/
def TotalSpace :=
  Σx, E x

instance [Inhabited B] [Inhabited (E default)] : Inhabited (TotalSpace E) :=
  ⟨⟨default, default⟩⟩

/-- `bundle.proj E` is the canonical projection `total_space E → B` on the base space. -/
@[simp, reducible]
def proj : TotalSpace E → B :=
  Sigma.fst

/-- Constructor for the total space of a `topological_fiber_bundle_core`. -/
@[simp, reducible]
def totalSpaceMk (E : B → Type _) (b : B) (a : E b) : Bundle.TotalSpace E :=
  ⟨b, a⟩

instance {x : B} : CoeTₓ (E x) (TotalSpace E) :=
  ⟨Sigma.mk x⟩

@[simp]
theorem coe_fst (x : B) (v : E x) : (v : TotalSpace E).fst = x :=
  rfl

theorem to_total_space_coe {x : B} (v : E x) : (v : TotalSpace E) = ⟨x, v⟩ :=
  rfl

/-- `bundle.trivial B F` is the trivial bundle over `B` of fiber `F`. -/
def Trivial (B : Type _) (F : Type _) : B → Type _ :=
  Function.const B F

instance {F : Type _} [Inhabited F] {b : B} : Inhabited (Bundle.Trivial B F b) :=
  ⟨(default : F)⟩

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def Trivial.projSnd (B : Type _) (F : Type _) : TotalSpace (Bundle.Trivial B F) → F :=
  Sigma.snd

section FiberStructures

variable [∀ x, AddCommMonoidₓ (E x)]

@[simp]
theorem coe_snd_map_apply (x : B) (v w : E x) :
    (↑(v + w) : TotalSpace E).snd = (v : TotalSpace E).snd + (w : TotalSpace E).snd :=
  rfl

variable (R : Type _) [Semiringₓ R] [∀ x, Module R (E x)]

@[simp]
theorem coe_snd_map_smul (x : B) (r : R) (v : E x) : (↑(r • v) : TotalSpace E).snd = r • (v : TotalSpace E).snd :=
  rfl

end FiberStructures

section TrivialInstances

attribute [local reducible] Bundle.Trivial

variable {F : Type _} {R : Type _} [Semiringₓ R] (b : B)

instance [AddCommMonoidₓ F] : AddCommMonoidₓ (Bundle.Trivial B F b) :=
  ‹AddCommMonoidₓ F›

instance [AddCommGroupₓ F] : AddCommGroupₓ (Bundle.Trivial B F b) :=
  ‹AddCommGroupₓ F›

instance [AddCommMonoidₓ F] [Module R F] : Module R (Bundle.Trivial B F b) :=
  ‹Module R F›

end TrivialInstances

end Bundle

