/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.RepresentationTheory.Rep
import Mathbin.Algebra.Category.FinVect

/-!
# `fdRep k G` is the category of finite dimensional `k`-linear representations of `G`.

If `V : fdRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `module k V` and `finite_dimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We verify that `fdRep k G` is a rigid monoidal category.

## TODO
* `fdRep k G` has all finite (co)limits.
* `fdRep k G` is abelian.
* `fdRep k G ≌ FinVect (monoid_algebra k G)` (this will require generalising `FinVect` first).
* Upgrade the right rigid structure to a rigid structure.
-/


universe u

open CategoryTheory

open CategoryTheory.Limits

-- ././Mathport/Syntax/Translate/Basic.lean:1203:31: unsupported: @[derive] abbrev
/-- The category of finite dimensional `k`-linear representations of a monoid `G`. -/
--, has_limits, has_colimits
abbrev FdRep (k G : Type u) [Field k] [Monoidₓ G] :=
  Action (FinVect.{u} k) (Mon.of G)

namespace FdRep

variable {k G : Type u} [Field k] [Monoidₓ G]

instance : CoeSort (FdRep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : FdRep k G) : AddCommGroupₓ V := by
  change AddCommGroupₓ ((forget₂ (FdRep k G) (FinVect k)).obj V)
  infer_instance

instance (V : FdRep k G) : Module k V := by
  change Module k ((forget₂ (FdRep k G) (FinVect k)).obj V)
  infer_instance

instance (V : FdRep k G) : FiniteDimensional k V := by
  change FiniteDimensional k ((forget₂ (FdRep k G) (FinVect k)).obj V)
  infer_instance

-- This works well with the new design for representations:
example (V : FdRep k G) : G →* V →ₗ[k] V :=
  V.ρ

/-- Lift an unbundled representation to `Rep`. -/
@[simps ρ]
def of {V : Type u} [AddCommGroupₓ V] [Module k V] [FiniteDimensional k V] (ρ : G →* V →ₗ[k] V) : Rep k G :=
  ⟨FinVect.of k V, ρ⟩

instance : HasForget₂ (FdRep k G) (Rep k G) where
  forget₂ := (forget₂ (FinVect k) (ModuleCat k)).mapAction (Mon.of G)

-- Verify that the monoidal structure is available.
example : MonoidalCategory (FdRep k G) := by
  infer_instance

end FdRep

namespace FdRep

variable {k G : Type u} [Field k] [Groupₓ G]

-- Verify that the rigid structure is available when the monoid is a group.
noncomputable instance : RightRigidCategory (FdRep k G) := by
  change right_rigid_category (Action (FinVect k) (Groupₓₓ.of G))
  infer_instance

end FdRep

