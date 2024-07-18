/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import RepresentationTheory.Rep
import Algebra.Category.FGModuleCat.Limits
import CategoryTheory.Preadditive.Schur
import RepresentationTheory.Basic

#align_import representation_theory.fdRep from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# `fdRep k G` is the category of finite dimensional `k`-linear representations of `G`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `V : fdRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `module k V` and `finite_dimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We verify that `fdRep k G` is a `k`-linear monoidal category, and rigid when `G` is a group.

`fdRep k G` has all finite limits.

## TODO
* `fdRep k G ≌ full_subcategory (finite_dimensional k)`
* Upgrade the right rigid structure to a rigid structure
  (this just needs to be done for `fgModule`).
* `fdRep k G` has all finite colimits.
* `fdRep k G` is abelian.
* `fdRep k G ≌ fgModule (monoid_algebra k G)`.

-/


universe u

open CategoryTheory

open CategoryTheory.Limits

/- ././././Mathport/Syntax/Translate/Command.lean:342:31: unsupported: @[derive] abbrev -/
#print FDRep /-
/-- The category of finite dimensional `k`-linear representations of a monoid `G`. -/
abbrev FDRep (k G : Type u) [Field k] [Monoid G] :=
  Action (FGModuleCat.{u} k) (MonCat.of G)
#align fdRep FDRep
-/

namespace FDRep

variable {k G : Type u} [Field k] [Monoid G]

instance : Linear k (FDRep k G) := by infer_instance

instance : CoeSort (FDRep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : FDRep k G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance

instance (V : FDRep k G) : Module k V := by
  change Module k ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance

instance (V : FDRep k G) : FiniteDimensional k V := by
  change FiniteDimensional k ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance

/-- All hom spaces are finite dimensional. -/
instance (V W : FDRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.of_injective ((forget₂ (FDRep k G) (FGModuleCat k)).mapLinearMap k)
    (Functor.map_injective _)

#print FDRep.ρ /-
/-- The monoid homomorphism corresponding to the action of `G` onto `V : fdRep k G`. -/
def ρ (V : FDRep k G) : G →* V →ₗ[k] V :=
  V.ρ
#align fdRep.ρ FDRep.ρ
-/

#print FDRep.isoToLinearEquiv /-
/-- The underlying `linear_equiv` of an isomorphism of representations. -/
def isoToLinearEquiv {V W : FDRep k G} (i : V ≅ W) : V ≃ₗ[k] W :=
  FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)
#align fdRep.iso_to_linear_equiv FDRep.isoToLinearEquiv
-/

#print FDRep.Iso.conj_ρ /-
theorem Iso.conj_ρ {V W : FDRep k G} (i : V ≅ W) (g : G) :
    W.ρ g = (FDRep.isoToLinearEquiv i).conj (V.ρ g) :=
  by
  rw [FDRep.isoToLinearEquiv, ← FGModuleCat.Iso.conj_eq_conj, iso.conj_apply]
  rw [iso.eq_inv_comp ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)]
  exact (i.hom.comm g).symm
#align fdRep.iso.conj_ρ FDRep.Iso.conj_ρ
-/

#print FDRep.of /-
/-- Lift an unbundled representation to `fdRep`. -/
@[simps ρ]
def of {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) : FDRep k G :=
  ⟨FGModuleCat.of k V, ρ⟩
#align fdRep.of FDRep.of
-/

instance : HasForget₂ (FDRep k G) (Rep k G)
    where forget₂ := (forget₂ (FGModuleCat k) (ModuleCat k)).mapAction (MonCat.of G)

#print FDRep.forget₂_ρ /-
theorem forget₂_ρ (V : FDRep k G) : ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ = V.ρ := by ext g v;
  rfl
#align fdRep.forget₂_ρ FDRep.forget₂_ρ
-/

-- Verify that the monoidal structure is available.
example : MonoidalCategory (FDRep k G) := by infer_instance

example : MonoidalPreadditive (FDRep k G) := by infer_instance

example : MonoidalLinear k (FDRep k G) := by infer_instance

open FiniteDimensional

open scoped Classical

-- We need to provide this instance explicitely as otherwise `finrank_hom_simple_simple` gives a
-- deterministic timeout.
instance : HasKernels (FDRep k G) := by infer_instance

#print FDRep.finrank_hom_simple_simple /-
-- Verify that Schur's lemma applies out of the box.
theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W
#align fdRep.finrank_hom_simple_simple FDRep.finrank_hom_simple_simple
-/

#print FDRep.forget₂HomLinearEquiv /-
/-- The forgetful functor to `Rep k G` preserves hom-sets and their vector space structure -/
def forget₂HomLinearEquiv (X Y : FDRep k G) :
    ((forget₂ (FDRep k G) (Rep k G)).obj X ⟶ (forget₂ (FDRep k G) (Rep k G)).obj Y) ≃ₗ[k] X ⟶ Y
    where
  toFun f := ⟨f.hom, f.comm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨(forget₂ (FGModuleCat k) (ModuleCat k)).map f.hom, f.comm⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
#align fdRep.forget₂_hom_linear_equiv FDRep.forget₂HomLinearEquiv
-/

end FDRep

namespace FDRep

variable {k G : Type u} [Field k] [Group G]

-- Verify that the right rigid structure is available when the monoid is a group.
noncomputable instance : RightRigidCategory (FDRep k G) := by
  change right_rigid_category (Action (FGModuleCat k) (Grp.of G)); infer_instance

end FDRep

namespace FDRep

-- The variables in this section are slightly weird, living half in `representation` and half in
-- `fdRep`. When we have a better API for general monoidal closed and rigid categories and these
-- structures on `fdRep`, we should remove the dependancy of statements about `fdRep` on
-- `representation.lin_hom` and `representation.dual`. The isomorphism `dual_tensor_iso_lin_hom`
-- below should then just be obtained from general results about rigid categories.
open Representation

variable {k G V : Type u} [Field k] [Group G]

variable [AddCommGroup V] [Module k V]

variable [FiniteDimensional k V]

variable (ρV : Representation k G V) (W : FDRep k G)

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FDRep.dualTensorIsoLinHomAux /-
/-- Auxiliary definition for `fdRep.dual_tensor_iso_lin_hom`. -/
noncomputable def dualTensorIsoLinHomAux :
    (FDRep.of ρV.dual ⊗ W).V ≅ (FDRep.of (linHom ρV W.ρ)).V :=
  (dualTensorHomEquiv k V W).toFGModuleCatIso
#align fdRep.dual_tensor_iso_lin_hom_aux FDRep.dualTensorIsoLinHomAux
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FDRep.dualTensorIsoLinHom /-
/-- When `V` and `W` are finite dimensional representations of a group `G`, the isomorphism
`dual_tensor_hom_equiv k V W` of vector spaces induces an isomorphism of representations. -/
noncomputable def dualTensorIsoLinHom : FDRep.of ρV.dual ⊗ W ≅ FDRep.of (linHom ρV W.ρ) :=
  by
  apply Action.mkIso (dual_tensor_iso_lin_hom_aux ρV W)
  convert dual_tensor_hom_comm ρV W.ρ
#align fdRep.dual_tensor_iso_lin_hom FDRep.dualTensorIsoLinHom
-/

#print FDRep.dualTensorIsoLinHom_hom_hom /-
@[simp]
theorem dualTensorIsoLinHom_hom_hom : (dualTensorIsoLinHom ρV W).hom.hom = dualTensorHom k V W :=
  rfl
#align fdRep.dual_tensor_iso_lin_hom_hom_hom FDRep.dualTensorIsoLinHom_hom_hom
-/

end FDRep

