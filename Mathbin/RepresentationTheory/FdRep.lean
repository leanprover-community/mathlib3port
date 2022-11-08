/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.RepresentationTheory.RepCat
import Mathbin.Algebra.Category.FinVectCat.Limits
import Mathbin.CategoryTheory.Preadditive.Schur
import Mathbin.RepresentationTheory.Basic

/-!
# `fdRep k G` is the category of finite dimensional `k`-linear representations of `G`.

If `V : fdRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `module k V` and `finite_dimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We verify that `fdRep k G` is a `k`-linear monoidal category, and right rigid when `G` is a group.

`fdRep k G` has all finite limits.

## TODO
* `fdRep k G ≌ full_subcategory (finite_dimensional k)`
* Upgrade the right rigid structure to a rigid structure (this just needs to be done for `FinVect`).
* `fdRep k G` has all finite colimits.
* `fdRep k G` is abelian.
* `fdRep k G ≌ FinVect (monoid_algebra k G)` (this will require generalising `FinVect` first).

-/


universe u

open CategoryTheory

open CategoryTheory.Limits

/- ./././Mathport/Syntax/Translate/Command.lean:297:31: unsupported: @[derive] abbrev -/
/-- The category of finite dimensional `k`-linear representations of a monoid `G`. -/
abbrev FdRep (k G : Type u) [Field k] [Monoid G] :=
  ActionCat (FinVectCat.{u} k) (MonCat.of G)

namespace FdRep

variable {k G : Type u} [Field k] [Monoid G]

instance : Linear k (FdRep k G) := by infer_instance

instance : CoeSort (FdRep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : FdRep k G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (FdRep k G) (FinVectCat k)).obj V).obj
  infer_instance

instance (V : FdRep k G) : Module k V := by
  change Module k ((forget₂ (FdRep k G) (FinVectCat k)).obj V).obj
  infer_instance

instance (V : FdRep k G) : FiniteDimensional k V := by
  change FiniteDimensional k ((forget₂ (FdRep k G) (FinVectCat k)).obj V).obj
  infer_instance

/-- All hom spaces are finite dimensional. -/
instance (V W : FdRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.ofInjective ((forget₂ (FdRep k G) (FinVectCat k)).mapLinearMap k) (Functor.map_injective _)

/-- The monoid homomorphism corresponding to the action of `G` onto `V : fdRep k G`. -/
def ρ (V : FdRep k G) : G →* V →ₗ[k] V :=
  V.ρ

/-- The underlying `linear_equiv` of an isomorphism of representations. -/
def isoToLinearEquiv {V W : FdRep k G} (i : V ≅ W) : V ≃ₗ[k] W :=
  FinVectCat.isoToLinearEquiv ((ActionCat.forget (FinVectCat k) (MonCat.of G)).mapIso i)

theorem Iso.conj_ρ {V W : FdRep k G} (i : V ≅ W) (g : G) : W.ρ g = (FdRep.isoToLinearEquiv i).conj (V.ρ g) := by
  rw [FdRep.isoToLinearEquiv, ← FinVectCat.Iso.conj_eq_conj, iso.conj_apply]
  rw [iso.eq_inv_comp ((ActionCat.forget (FinVectCat k) (MonCat.of G)).mapIso i)]
  exact (i.hom.comm g).symm

/-- Lift an unbundled representation to `fdRep`. -/
@[simps ρ]
def of {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) : FdRep k G :=
  ⟨FinVectCat.of k V, ρ⟩

instance :
    HasForget₂ (FdRep k G) (RepCat k G) where forget₂ := (forget₂ (FinVectCat k) (ModuleCat k)).mapAction (MonCat.of G)

-- Verify that the monoidal structure is available.
example : MonoidalCategory (FdRep k G) := by infer_instance

example : MonoidalPreadditive (FdRep k G) := by infer_instance

example : MonoidalLinear k (FdRep k G) := by infer_instance

open FiniteDimensional

open Classical

-- Verify that Schur's lemma applies out of the box.
theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FdRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W

end FdRep

namespace FdRep

variable {k G : Type u} [Field k] [Group G]

-- Verify that the rigid structure is available when the monoid is a group.
noncomputable instance : RightRigidCategory (FdRep k G) := by
  change right_rigid_category (ActionCat (FinVectCat k) (GroupCat.of G))
  infer_instance

end FdRep

namespace FdRep

open Representation

variable {k G V W : Type u} [Field k] [Group G]

variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

variable [FiniteDimensional k V] [FiniteDimensional k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Auxiliary definition for `fdRep.dual_tensor_iso_lin_hom`. -/
noncomputable def dualTensorIsoLinHomAux : (FdRep.of ρV.dual ⊗ FdRep.of ρW).V ≅ (FdRep.of (linHom ρV ρW)).V :=
  (dualTensorHomEquiv k V W).toFinVectIso

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- When `V` and `W` are finite dimensional representations of a group `G`, the isomorphism
`dual_tensor_hom_equiv k V W` of vector spaces induces an isomorphism of representations. -/
noncomputable def dualTensorIsoLinHom : FdRep.of ρV.dual ⊗ FdRep.of ρW ≅ FdRep.of (linHom ρV ρW) := by
  apply ActionCat.mkIso (dual_tensor_iso_lin_hom_aux ρV ρW)
  convert dual_tensor_hom_comm ρV ρW

@[simp]
theorem dual_tensor_iso_lin_hom_hom_hom : (dualTensorIsoLinHom ρV ρW).hom.hom = dualTensorHom k V W :=
  rfl

end FdRep

