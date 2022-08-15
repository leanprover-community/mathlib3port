/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.RepresentationTheory.Basic
import Mathbin.RepresentationTheory.Action
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.Algebra.Category.Module.Colimits
import Mathbin.Algebra.Category.Module.Monoidal

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

If `V : Rep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with a `module k V` instance.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We construct the categorical equivalence `Rep k G ≌ Module (monoid_algebra k G)`.
We verify that `Rep k G` is a `k`-linear abelian symmetric monoidal category with all (co)limits.
-/


universe u

open CategoryTheory

open CategoryTheory.Limits

-- ./././Mathport/Syntax/Translate/Basic.lean:1406:31: unsupported: @[derive] abbrev
/-- The category of `k`-linear representations of a monoid `G`. -/
abbrev Rep (k G : Type u) [Ringₓ k] [Monoidₓ G] :=
  Action (ModuleCat.{u} k) (Mon.of G)

instance (k G : Type u) [CommRingₓ k] [Monoidₓ G] : Linear k (Rep k G) := by
  infer_instance

namespace Rep

variable {k G : Type u} [CommRingₓ k] [Monoidₓ G]

instance : CoeSort (Rep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : Rep k G) : AddCommGroupₓ V := by
  change AddCommGroupₓ ((forget₂ (Rep k G) (ModuleCat k)).obj V)
  infer_instance

instance (V : Rep k G) : Module k V := by
  change Module k ((forget₂ (Rep k G) (ModuleCat k)).obj V)
  infer_instance

/-- Specialize the existing `Action.ρ`, changing the type to `representation k G V`.
-/
def ρ (V : Rep k G) : Representation k G V :=
  V.ρ

/-- Lift an unbundled representation to `Rep`. -/
def of {V : Type u} [AddCommGroupₓ V] [Module k V] (ρ : G →* V →ₗ[k] V) : Rep k G :=
  ⟨ModuleCat.of k V, ρ⟩

@[simp]
theorem coe_of {V : Type u} [AddCommGroupₓ V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ : Type u) = V :=
  rfl

@[simp]
theorem of_ρ {V : Type u} [AddCommGroupₓ V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl

-- Verify that limits are calculated correctly.
noncomputable example : PreservesLimits (forget₂ (Rep k G) (ModuleCat.{u} k)) := by
  infer_instance

noncomputable example : PreservesColimits (forget₂ (Rep k G) (ModuleCat.{u} k)) := by
  infer_instance

end Rep

/-!
# The categorical equivalence `Rep k G ≌ Module.{u} (monoid_algebra k G)`.
-/


namespace Rep

variable {k G : Type u} [CommRingₓ k] [Monoidₓ G]

-- Verify that the symmetric monoidal structure is available.
example : SymmetricCategory (Rep k G) := by
  infer_instance

example : MonoidalPreadditive (Rep k G) := by
  infer_instance

example : MonoidalLinear k (Rep k G) := by
  infer_instance

noncomputable section

/-- Auxilliary lemma for `to_Module_monoid_algebra`. -/
theorem to_Module_monoid_algebra_map_aux {k G : Type _} [CommRingₓ k] [Monoidₓ G] (V W : Type _) [AddCommGroupₓ V]
    [AddCommGroupₓ W] [Module k V] [Module k W] (ρ : G →* V →ₗ[k] V) (σ : G →* W →ₗ[k] W) (f : V →ₗ[k] W)
    (w : ∀ g : G, f.comp (ρ g) = (σ g).comp f) (r : MonoidAlgebra k G) (x : V) :
    f ((((MonoidAlgebra.lift k G (V →ₗ[k] V)) ρ) r) x) = (((MonoidAlgebra.lift k G (W →ₗ[k] W)) σ) r) (f x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [← one_smul, ← MonoidAlgebra.lift_single, ← MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
    
  · intro g h gw hw
    simp only [← map_add, ← add_left_injₓ, ← LinearMap.add_apply, ← hw, ← gw]
    
  · intro r g w
    simp only [← AlgHom.map_smul, ← w, ← RingHom.id_apply, ← LinearMap.smul_apply, ← LinearMap.map_smulₛₗ]
    

/-- Auxilliary definition for `to_Module_monoid_algebra`. -/
def toModuleMonoidAlgebraMap {V W : Rep k G} (f : V ⟶ W) :
    ModuleCat.of (MonoidAlgebra k G) V.ρ.AsModule ⟶ ModuleCat.of (MonoidAlgebra k G) W.ρ.AsModule :=
  { f.hom with map_smul' := fun r x => to_Module_monoid_algebra_map_aux V.V W.V V.ρ W.ρ f.hom f.comm r x }

/-- Functorially convert a representation of `G` into a module over `monoid_algebra k G`. -/
def toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat.{u} (MonoidAlgebra k G) where
  obj := fun V => ModuleCat.of _ V.ρ.AsModule
  map := fun V W f => toModuleMonoidAlgebraMap f

/-- Functorially convert a module over `monoid_algebra k G` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat.{u} (MonoidAlgebra k G) ⥤ Rep k G where
  obj := fun M => Rep.of (Representation.ofModule k G M)
  map := fun M N f =>
    { hom := { f with map_smul' := fun r x => f.map_smul (algebraMap k _ r) x },
      comm' := fun g => by
        ext
        apply f.map_smul }

theorem of_Module_monoid_algebra_obj_coe (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M : Type u) = RestrictScalars k (MonoidAlgebra k G) M :=
  rfl

theorem of_Module_monoid_algebra_obj_ρ (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule k G M :=
  rfl

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def counitIsoAddEquiv {M : ModuleCat.{u} (MonoidAlgebra k G)} :
    (of_Module_monoid_algebra ⋙ to_Module_monoid_algebra).obj M ≃+ M := by
  dsimp' [← of_Module_monoid_algebra, ← to_Module_monoid_algebra]
  refine' (Representation.ofModule k G ↥M).asModuleEquiv.trans (RestrictScalars.addEquiv _ _ _)

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def unitIsoAddEquiv {V : Rep k G} : V ≃+ (to_Module_monoid_algebra ⋙ of_Module_monoid_algebra).obj V := by
  dsimp' [← of_Module_monoid_algebra, ← to_Module_monoid_algebra]
  refine' V.ρ.as_module_equiv.symm.trans _
  exact (RestrictScalars.addEquiv _ _ _).symm

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def counitIso (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (of_Module_monoid_algebra ⋙ to_Module_monoid_algebra).obj M ≅ M :=
  LinearEquiv.toModuleIso'
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        dsimp' [← counit_iso_add_equiv]
        simp }

theorem unit_iso_comm (V : Rep k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) =
      ((ofModuleMonoidAlgebra.obj (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) :=
  by
  dsimp' [← unit_iso_add_equiv, ← of_Module_monoid_algebra, ← to_Module_monoid_algebra]
  simp only [← AddEquiv.apply_eq_iff_eq, ← AddEquiv.apply_symm_apply, ← Representation.as_module_equiv_symm_map_rho, ←
    Representation.of_module_as_module_act]

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def unitIso (V : Rep k G) : V ≅ (to_Module_monoid_algebra ⋙ of_Module_monoid_algebra).obj V :=
  Action.mkIso
    (LinearEquiv.toModuleIso'
      { unitIsoAddEquiv with
        map_smul' := fun r x => by
          dsimp' [← unit_iso_add_equiv]
          simp only [← Representation.as_module_equiv_symm_map_smul, ←
            RestrictScalars.add_equiv_symm_map_algebra_map_smul] })
    fun g => by
    ext
    apply unit_iso_comm

/-- The categorical equivalence `Rep k G ≌ Module (monoid_algebra k G)`. -/
def equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat.{u} (MonoidAlgebra k G) where
  Functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso :=
    NatIso.ofComponents (fun V => unitIso V)
      (by
        tidy)
  counitIso :=
    NatIso.ofComponents (fun M => counitIso M)
      (by
        tidy)

-- TODO Verify that the equivalence with `Module (monoid_algebra k G)` is a monoidal functor.
end Rep

