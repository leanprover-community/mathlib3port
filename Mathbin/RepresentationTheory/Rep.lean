/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module representation_theory.Rep
! leanprover-community/mathlib commit 0caf3701139ef2e69c215717665361cda205a90b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RepresentationTheory.Basic
import Mathbin.RepresentationTheory.Action
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.Algebra.Category.Module.Colimits
import Mathbin.Algebra.Category.Module.Monoidal
import Mathbin.Algebra.Category.Module.Adjunctions
import Mathbin.CategoryTheory.Closed.FunctorCategory

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

/- ./././Mathport/Syntax/Translate/Command.lean:323:31: unsupported: @[derive] abbrev -/
/-- The category of `k`-linear representations of a monoid `G`. -/
abbrev Rep (k G : Type u) [Ring k] [Monoid G] :=
  Action (ModuleCat.{u} k) (MonCat.of G)
#align Rep Rep

instance (k G : Type u) [CommRing k] [Monoid G] : Linear k (Rep k G) := by infer_instance

namespace Rep

variable {k G : Type u} [CommRing k]

section

variable [Monoid G]

instance : CoeSort (Rep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : Rep k G) : AddCommGroup V :=
  by
  change AddCommGroup ((forget₂ (Rep k G) (ModuleCat k)).obj V)
  infer_instance

instance (V : Rep k G) : Module k V :=
  by
  change Module k ((forget₂ (Rep k G) (ModuleCat k)).obj V)
  infer_instance

/-- Specialize the existing `Action.ρ`, changing the type to `representation k G V`.
-/
def ρ (V : Rep k G) : Representation k G V :=
  V.ρ
#align Rep.ρ Rep.ρ

/-- Lift an unbundled representation to `Rep`. -/
def of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : Rep k G :=
  ⟨ModuleCat.of k V, ρ⟩
#align Rep.of Rep.of

@[simp]
theorem coe_of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) :
    (of ρ : Type u) = V :=
  rfl
#align Rep.coe_of Rep.coe_of

@[simp]
theorem of_ρ {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl
#align Rep.of_ρ Rep.of_ρ

-- Verify that limits are calculated correctly.
noncomputable example : PreservesLimits (forget₂ (Rep k G) (ModuleCat.{u} k)) := by infer_instance

noncomputable example : PreservesColimits (forget₂ (Rep k G) (ModuleCat.{u} k)) := by infer_instance

section Linearization

variable (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
noncomputable def linearization : MonoidalFunctor (Action (Type u) (MonCat.of G)) (Rep k G) :=
  (ModuleCat.monoidalFree k).mapAction (MonCat.of G)
#align Rep.linearization Rep.linearization

variable {k G}

@[simp]
theorem linearization_obj_ρ (X : Action (Type u) (MonCat.of G)) (g : G) (x : X.V →₀ k) :
    ((linearization k G).1.1.obj X).ρ g x = Finsupp.lmapDomain k k (X.ρ g) x :=
  rfl
#align Rep.linearization_obj_ρ Rep.linearization_obj_ρ

@[simp]
theorem linearization_of (X : Action (Type u) (MonCat.of G)) (g : G) (x : X.V) :
    ((linearization k G).1.1.obj X).ρ g (Finsupp.single x (1 : k)) =
      Finsupp.single (X.ρ g x) (1 : k) :=
  by rw [linearization_obj_ρ, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
#align Rep.linearization_of Rep.linearization_of

variable (X Y : Action (Type u) (MonCat.of G)) (f : X ⟶ Y)

@[simp]
theorem linearization_map_hom :
    ((linearization k G).1.1.map f).hom = Finsupp.lmapDomain k k f.hom :=
  rfl
#align Rep.linearization_map_hom Rep.linearization_map_hom

theorem linearization_map_hom_of (x : X.V) :
    ((linearization k G).1.1.map f).hom (Finsupp.single x (1 : k)) =
      Finsupp.single (f.hom x) (1 : k) :=
  by rw [linearization_map_hom, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
#align Rep.linearization_map_hom_of Rep.linearization_map_hom_of

variable (k G)

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
noncomputable abbrev ofMulAction (H : Type u) [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H
#align Rep.of_mul_action Rep.ofMulAction

/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
noncomputable def linearizationOfMulActionIso (n : ℕ) :
    (linearization k G).1.1.obj (Action.ofMulAction G (Fin n → G)) ≅ ofMulAction k G (Fin n → G) :=
  Iso.refl _
#align Rep.linearization_of_mul_action_iso Rep.linearizationOfMulActionIso

end Linearization

end

section

open Action

variable [Group G] (A B C : Rep k G)

noncomputable instance : MonoidalClosed (Rep k G) :=
  MonoidalClosed.ofEquiv (functorCategoryMonoidalEquivalence _ _)

/-- Explicit description of the 'internal Hom' `iHom(A, B)` of two representations `A, B`:
this is `F⁻¹(iHom(F(A), F(B)))`, where `F` is an equivalence
`Rep k G ≌ (single_obj G ⥤ Module k)`. Just used to prove `Rep.ihom_obj_ρ`. -/
theorem ihom_obj_ρ_def :
    ((ihom A).obj B).ρ =
      (FunctorCategoryEquivalence.inverse.obj
          ((FunctorCategoryEquivalence.functor.obj A).closedIhom.obj
            (FunctorCategoryEquivalence.functor.obj B))).ρ :=
  rfl
#align Rep.ihom_obj_ρ_def Rep.ihom_obj_ρ_def

/-- Given `k`-linear `G`-representations `(A, ρ₁), (B, ρ₂)`, the 'internal Hom' is the
representation on `Homₖ(A, B)` sending `g : G` and `f : A →ₗ[k] B` to `(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simp]
theorem ihom_obj_ρ : ((ihom A).obj B).ρ = A.ρ.linHom B.ρ :=
  by
  refine' MonoidHom.ext fun g => _
  simpa only [ihom_obj_ρ_def, functor_category_equivalence.inverse_obj_ρ_apply,
    functor.closed_ihom_obj_map, ← functor.map_inv, single_obj.inv_as_inv]
#align Rep.ihom_obj_ρ Rep.ihom_obj_ρ

@[simp]
theorem ihom_map_hom {B C : Rep k G} (f : B ⟶ C) :
    ((ihom A).map f).hom = LinearMap.llcomp k A B C f.hom :=
  rfl
#align Rep.ihom_map_hom Rep.ihom_map_hom

/-- Unfolds the unit in the adjunction `A ⊗ - ⊣ iHom(A, -)`; just used to prove
`Rep.ihom_coev_app_hom`. -/
theorem ihom_coev_app_def :
    (ihom.coev A).app B =
      FunctorCategoryEquivalence.unitIso.hom.app B ≫
        FunctorCategoryEquivalence.inverse.map
          ((FunctorCategoryEquivalence.functor.obj A).closedUnit.app _ ≫
            (FunctorCategoryEquivalence.functor.obj A).closedIhom.map
              ((functorCategoryMonoidalEquivalence (ModuleCat.{u} k) (MonCat.of G)).μ A B)) :=
  rfl
#align Rep.ihom_coev_app_def Rep.ihom_coev_app_def

/-- Describes the unit in the adjunction `A ⊗ - ⊣ iHom(A, -)`; given another `k`-linear
`G`-representation `B,` the `k`-linear map underlying the resulting map `B ⟶ iHom(A, A ⊗ B)` is
given by flipping the arguments in the natural `k`-bilinear map `A →ₗ[k] B →ₗ[k] A ⊗ B`. -/
@[simp]
theorem ihom_coev_app_hom : Action.Hom.hom ((ihom.coev A).app B) = (TensorProduct.mk _ _ _).flip :=
  by
  refine' LinearMap.ext fun x => LinearMap.ext fun y => _
  simpa only [ihom_coev_app_def, functor.map_comp, comp_hom,
    functor_category_equivalence.inverse_map_hom, functor.closed_ihom_map_app,
    functor_category_monoidal_equivalence.μ_app]
#align Rep.ihom_coev_app_hom Rep.ihom_coev_app_hom

variable {A B C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given a `k`-linear `G`-representation `A`, the adjunction `A ⊗ - ⊣ iHom(A, -)` defines a
bijection `Hom(A ⊗ B, C) ≃ Hom(B, iHom(A, C))` for all `B, C`. Given `f : A ⊗ B ⟶ C`, this lemma
describes the `k`-linear map underlying `f`'s image under the bijection. It is given by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simp]
theorem monoidalClosed_curry_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.curry f).hom = (TensorProduct.curry f.hom).flip :=
  by
  rw [monoidal_closed.curry_eq, comp_hom, ihom_coev_app_hom]
  rfl
#align Rep.monoidal_closed_curry_hom Rep.monoidalClosed_curry_hom

/-- Given a `k`-linear `G`-representation `A`, the adjunction `A ⊗ - ⊣ iHom(A, -)` defines a
bijection `Hom(A ⊗ B, C) ≃ Hom(B, iHom(A, C))` for all `B, C`. Given `f : B ⟶ iHom(A, C)`, this
lemma describes the `k`-linear map underlying `f`'s image under the bijection. It is given by
flipping the arguments of the `k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then
uncurrying. -/
@[simp]
theorem monoidalClosed_uncurry_hom (f : B ⟶ (ihom A).obj C) :
    (MonoidalClosed.uncurry f).hom = TensorProduct.uncurry _ _ _ _ f.hom.flip :=
  by
  simp only [monoidal_closed.of_equiv_uncurry_def, comp_inv_iso_inv_app,
    monoidal_functor.comm_tensor_left_inv_app, comp_hom,
    functor_category_monoidal_equivalence.inverse_map, functor_category_equivalence.inverse_map_hom,
    functor_category_monoidal_equivalence.μ_iso_inv_app]
  ext
  rfl
#align Rep.monoidal_closed_uncurry_hom Rep.monoidalClosed_uncurry_hom

/-- Describes the counit in the adjunction `A ⊗ - ⊣ iHom(A, -)`; given another `k`-linear
`G`-representation `B,` the `k`-linear map underlying the resulting morphism `A ⊗ iHom(A, B) ⟶ B`
is given by uncurrying the map `A →ₗ[k] (A →ₗ[k] B) →ₗ[k] B` defined by flipping the arguments in
the identity map on `Homₖ(A, B).` -/
@[simp]
theorem ihom_ev_app_hom :
    Action.Hom.hom ((ihom.ev A).app B) = TensorProduct.uncurry _ _ _ _ LinearMap.id.flip :=
  monoidalClosed_uncurry_hom _
#align Rep.ihom_ev_app_hom Rep.ihom_ev_app_hom

end

end Rep

/-!
# The categorical equivalence `Rep k G ≌ Module.{u} (monoid_algebra k G)`.
-/


namespace Rep

variable {k G : Type u} [CommRing k] [Monoid G]

-- Verify that the symmetric monoidal structure is available.
example : SymmetricCategory (Rep k G) := by infer_instance

example : MonoidalPreadditive (Rep k G) := by infer_instance

example : MonoidalLinear k (Rep k G) := by infer_instance

noncomputable section

/-- Auxilliary lemma for `to_Module_monoid_algebra`. -/
theorem to_Module_monoidAlgebra_map_aux {k G : Type _} [CommRing k] [Monoid G] (V W : Type _)
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G →* V →ₗ[k] V)
    (σ : G →* W →ₗ[k] W) (f : V →ₗ[k] W) (w : ∀ g : G, f.comp (ρ g) = (σ g).comp f)
    (r : MonoidAlgebra k G) (x : V) :
    f ((((MonoidAlgebra.lift k G (V →ₗ[k] V)) ρ) r) x) =
      (((MonoidAlgebra.lift k G (W →ₗ[k] W)) σ) r) (f x) :=
  by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw
    simp only [map_add, add_left_inj, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [AlgHom.map_smul, w, RingHom.id_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ]
#align Rep.to_Module_monoid_algebra_map_aux Rep.to_Module_monoidAlgebra_map_aux

/-- Auxilliary definition for `to_Module_monoid_algebra`. -/
def toModuleMonoidAlgebraMap {V W : Rep k G} (f : V ⟶ W) :
    ModuleCat.of (MonoidAlgebra k G) V.ρ.AsModule ⟶ ModuleCat.of (MonoidAlgebra k G) W.ρ.AsModule :=
  { f.hom with
    map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ f.hom f.comm r x }
#align Rep.to_Module_monoid_algebra_map Rep.toModuleMonoidAlgebraMap

/-- Functorially convert a representation of `G` into a module over `monoid_algebra k G`. -/
def toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat.{u} (MonoidAlgebra k G)
    where
  obj V := ModuleCat.of _ V.ρ.AsModule
  map V W f := toModuleMonoidAlgebraMap f
#align Rep.to_Module_monoid_algebra Rep.toModuleMonoidAlgebra

/-- Functorially convert a module over `monoid_algebra k G` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat.{u} (MonoidAlgebra k G) ⥤ Rep k G
    where
  obj M := Rep.of (Representation.ofModule k G M)
  map M N f :=
    { hom := { f with map_smul' := fun r x => f.map_smul (algebraMap k _ r) x }
      comm' := fun g => by
        ext
        apply f.map_smul }
#align Rep.of_Module_monoid_algebra Rep.ofModuleMonoidAlgebra

theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M : Type u) = RestrictScalars k (MonoidAlgebra k G) M :=
  rfl
#align Rep.of_Module_monoid_algebra_obj_coe Rep.ofModuleMonoidAlgebra_obj_coe

theorem ofModuleMonoidAlgebra_obj_ρ (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule k G M :=
  rfl
#align Rep.of_Module_monoid_algebra_obj_ρ Rep.ofModuleMonoidAlgebra_obj_ρ

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def counitIsoAddEquiv {M : ModuleCat.{u} (MonoidAlgebra k G)} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M :=
  by
  dsimp [of_Module_monoid_algebra, to_Module_monoid_algebra]
  refine' (Representation.ofModule k G ↥M).asModuleEquiv.trans (RestrictScalars.addEquiv _ _ _)
#align Rep.counit_iso_add_equiv Rep.counitIsoAddEquiv

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def unitIsoAddEquiv {V : Rep k G} : V ≃+ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  by
  dsimp [of_Module_monoid_algebra, to_Module_monoid_algebra]
  refine' V.ρ.as_module_equiv.symm.trans _
  exact (RestrictScalars.addEquiv _ _ _).symm
#align Rep.unit_iso_add_equiv Rep.unitIsoAddEquiv

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def counitIso (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso'
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        dsimp [counit_iso_add_equiv]
        simp }
#align Rep.counit_iso Rep.counitIso

theorem unit_iso_comm (V : Rep k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) =
      ((ofModuleMonoidAlgebra.obj (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) :=
  by
  dsimp [unit_iso_add_equiv, of_Module_monoid_algebra, to_Module_monoid_algebra]
  simp only [AddEquiv.apply_eq_iff_eq, AddEquiv.apply_symm_apply,
    Representation.asModuleEquiv_symm_map_rho, Representation.ofModule_asModule_act]
#align Rep.unit_iso_comm Rep.unit_iso_comm

/-- Auxilliary definition for `equivalence_Module_monoid_algebra`. -/
def unitIso (V : Rep k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  Action.mkIso
    (LinearEquiv.toModuleIso'
      { unitIsoAddEquiv with
        map_smul' := fun r x => by
          dsimp [unit_iso_add_equiv]
          simp only [Representation.asModuleEquiv_symm_map_smul,
            RestrictScalars.addEquiv_symm_map_algebraMap_smul] })
    fun g => by
    ext
    apply unit_iso_comm
#align Rep.unit_iso Rep.unitIso

/-- The categorical equivalence `Rep k G ≌ Module (monoid_algebra k G)`. -/
def equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat.{u} (MonoidAlgebra k G)
    where
  Functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by tidy)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by tidy)
#align Rep.equivalence_Module_monoid_algebra Rep.equivalenceModuleMonoidAlgebra

-- TODO Verify that the equivalence with `Module (monoid_algebra k G)` is a monoidal functor.
end Rep

