/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston

! This file was ported from Lean 3 source module representation_theory.group_cohomology_resolution
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Projective
import Mathbin.AlgebraicTopology.ExtraDegeneracy
import Mathbin.CategoryTheory.Abelian.Ext
import Mathbin.RepresentationTheory.Rep

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains facts about an important `k[G]`-module structure on `k[Gⁿ]`, where `k` is a
commutative ring and `G` is a group. The module structure arises from the representation
`G →* End(k[Gⁿ])` induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define an isomorphism of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

This allows us to define a `k[G]`-basis on `k[Gⁿ⁺¹]`, by mapping the natural `k[G]`-basis of
`k[G] ⊗ₖ k[Gⁿ]` along the isomorphism.

We then define the standard resolution of `k` as a trivial representation, by
taking the alternating face map complex associated to an appropriate simplicial `k`-linear
`G`-representation. This simplicial object is the `linearization` of the simplicial `G`-set given
by the universal cover of the classifying space of `G`, `EG`. We prove this simplicial `G`-set `EG`
is isomorphic to the Čech nerve of the natural arrow of `G`-sets `G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `group_cohomology.ProjectiveResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`
 * `group_cohomology.resolution.equiv_tensor`
 * `group_cohomology.resolution.of_mul_action_basis`
 * `classifying_space_universal_cover`
 * `group_cohomology.resolution.forget₂_to_Module_homotopy_equiv`
 * `group_cohomology.ProjectiveResolution`

## Implementation notes

We express `k[G]`-module structures on a module `k`-module `V` using the `representation`
definition. We avoid using instances `module (G →₀ k) V` so that we do not run into possible
scalar action diamonds.

We also use the category theory library to bundle the type `k[Gⁿ]` - or more generally `k[H]` when
`H` has `G`-action - and the representation together, as a term of type `Rep k G`, and call it
`Rep.of_mul_action k G H.` This enables us to express the fact that certain maps are
`G`-equivariant by constructing morphisms in the category `Rep k G`, i.e., representations of `G`
over `k`.
-/


noncomputable section

universe u v w

variable {k G : Type u} [CommRing k] {n : ℕ}

open TensorProduct

open CategoryTheory

-- mathport name: «exprGⁿ»
local notation "Gⁿ" => Fin n → G

-- mathport name: «exprGⁿ⁺¹»
local notation "Gⁿ⁺¹" => Fin (n + 1) → G

namespace GroupCohomology.resolution

open Finsupp hiding lift

open Fin (partialProd)

open Representation

section Basis

variable (k G n) [Group G]

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def toTensorAux : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (G →₀ k) ⊗[k] ((Fin n → G) →₀ k) :=
  Finsupp.lift ((G →₀ k) ⊗[k] ((Fin n → G) →₀ k)) k (Fin (n + 1) → G) fun x =>
    single (x 0) 1 ⊗ₜ[k] single (fun i => (x i)⁻¹ * x i.succ) 1
#align group_cohomology.resolution.to_tensor_aux GroupCohomology.Resolution.toTensorAux

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def ofTensorAux : (G →₀ k) ⊗[k] ((Fin n → G) →₀ k) →ₗ[k] (Fin (n + 1) → G) →₀ k :=
  TensorProduct.lift
    (Finsupp.lift _ _ _ fun g => Finsupp.lift _ _ _ fun f => single (g • partialProd f) (1 : k))
#align group_cohomology.resolution.of_tensor_aux GroupCohomology.Resolution.ofTensorAux

variable {k G n}

theorem toTensorAux_single (f : Gⁿ⁺¹) (m : k) :
    toTensorAux k G n (single f m) = single (f 0) m ⊗ₜ single (fun i => (f i)⁻¹ * f i.succ) 1 :=
  by
  simp only [to_tensor_aux, lift_apply, sum_single_index, TensorProduct.smul_tmul']
  · simp
#align group_cohomology.resolution.to_tensor_aux_single GroupCohomology.Resolution.toTensorAux_single

theorem toTensorAux_ofMulAction (g : G) (x : Gⁿ⁺¹) :
    toTensorAux k G n (ofMulAction k G Gⁿ⁺¹ g (single x 1)) =
      TensorProduct.map (ofMulAction k G G g) 1 (toTensorAux k G n (single x 1)) :=
  by simp [of_mul_action_def, to_tensor_aux_single, mul_assoc, inv_mul_cancel_left]
#align group_cohomology.resolution.to_tensor_aux_of_mul_action GroupCohomology.Resolution.toTensorAux_ofMulAction

theorem ofTensorAux_single (g : G) (m : k) (x : Gⁿ →₀ k) :
    ofTensorAux k G n (single g m ⊗ₜ x) =
      Finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (fun f => single (g • partialProd f) m) x :=
  by simp [of_tensor_aux, sum_single_index, smul_sum, mul_comm m]
#align group_cohomology.resolution.of_tensor_aux_single GroupCohomology.Resolution.ofTensorAux_single

theorem ofTensorAux_comm_ofMulAction (g h : G) (x : Gⁿ) :
    ofTensorAux k G n
        (TensorProduct.map (ofMulAction k G G g) (1 : Module.End k (Gⁿ →₀ k))
          (single h (1 : k) ⊗ₜ single x (1 : k))) =
      ofMulAction k G Gⁿ⁺¹ g (ofTensorAux k G n (single h 1 ⊗ₜ single x 1)) :=
  by simp [of_mul_action_def, of_tensor_aux_single, mul_smul]
#align group_cohomology.resolution.of_tensor_aux_comm_of_mul_action GroupCohomology.Resolution.ofTensorAux_comm_ofMulAction

theorem toTensorAux_left_inv (x : Gⁿ⁺¹ →₀ k) : ofTensorAux _ _ _ (toTensorAux _ _ _ x) = x :=
  by
  refine'
    LinearMap.ext_iff.1
      (@Finsupp.lhom_ext _ _ _ k _ _ _ _ _
        (LinearMap.comp (of_tensor_aux _ _ _) (to_tensor_aux _ _ _)) LinearMap.id fun x y => _)
      x
  dsimp
  rw [to_tensor_aux_single x y, of_tensor_aux_single, Finsupp.lift_apply, Finsupp.sum_single_index,
    one_smul, Fin.partialProd_left_inv]
  · rw [zero_smul]
#align group_cohomology.resolution.to_tensor_aux_left_inv GroupCohomology.Resolution.toTensorAux_left_inv

theorem toTensorAux_right_inv (x : (G →₀ k) ⊗[k] (Gⁿ →₀ k)) :
    toTensorAux _ _ _ (ofTensorAux _ _ _ x) = x :=
  by
  refine' TensorProduct.induction_on x (by simp) (fun y z => _) fun z w hz hw => by simp [hz, hw]
  rw [← Finsupp.sum_single y, Finsupp.sum, TensorProduct.sum_tmul]
  simp only [Finset.smul_sum, LinearMap.map_sum]
  refine' Finset.sum_congr rfl fun f hf => _
  simp only [of_tensor_aux_single, Finsupp.lift_apply, Finsupp.smul_single',
    LinearMap.map_finsupp_sum, to_tensor_aux_single, Fin.partialProd_right_inv]
  dsimp
  simp only [Fin.partialProd_zero, mul_one]
  conv_rhs => rw [← Finsupp.sum_single z, Finsupp.sum, TensorProduct.tmul_sum]
  exact
    Finset.sum_congr rfl fun g hg =>
      show _ ⊗ₜ _ = _ by
        rw [← Finsupp.smul_single', TensorProduct.smul_tmul, Finsupp.smul_single_one]
#align group_cohomology.resolution.to_tensor_aux_right_inv GroupCohomology.Resolution.toTensorAux_right_inv

variable (k G n)

/-- A hom of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def toTensor :
    Rep.ofMulAction k G (Fin (n + 1) → G) ⟶
      Rep.of ((Representation.ofMulAction k G G).tprod (1 : G →* Module.End k ((Fin n → G) →₀ k)))
    where
  hom := toTensorAux k G n
  comm' g := by ext <;> exact to_tensor_aux_of_mul_action _ _
#align group_cohomology.resolution.to_tensor GroupCohomology.Resolution.toTensor

/-- A hom of `k`-linear representations of `G` from `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def ofTensor :
    Rep.of ((Representation.ofMulAction k G G).tprod (1 : G →* Module.End k ((Fin n → G) →₀ k))) ⟶
      Rep.ofMulAction k G (Fin (n + 1) → G)
    where
  hom := ofTensorAux k G n
  comm' g := by
    ext
    congr 1
    exact of_tensor_aux_comm_of_mul_action _ _ _
#align group_cohomology.resolution.of_tensor GroupCohomology.Resolution.ofTensor

variable {k G n}

@[simp]
theorem toTensor_single (f : Gⁿ⁺¹) (m : k) :
    (toTensor k G n).hom (single f m) = single (f 0) m ⊗ₜ single (fun i => (f i)⁻¹ * f i.succ) 1 :=
  toTensorAux_single _ _
#align group_cohomology.resolution.to_tensor_single GroupCohomology.Resolution.toTensor_single

@[simp]
theorem ofTensor_single (g : G) (m : k) (x : Gⁿ →₀ k) :
    (ofTensor k G n).hom (single g m ⊗ₜ x) =
      Finsupp.lift (Rep.ofMulAction k G Gⁿ⁺¹) k Gⁿ (fun f => single (g • partialProd f) m) x :=
  ofTensorAux_single _ _ _
#align group_cohomology.resolution.of_tensor_single GroupCohomology.Resolution.ofTensor_single

theorem ofTensor_single' (g : G →₀ k) (x : Gⁿ) (m : k) :
    (ofTensor k G n).hom (g ⊗ₜ single x m) =
      Finsupp.lift _ k G (fun a => single (a • partialProd x) m) g :=
  by simp [of_tensor, of_tensor_aux]
#align group_cohomology.resolution.of_tensor_single' GroupCohomology.Resolution.ofTensor_single'

variable (k G n)

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def equivTensor :
    Rep.ofMulAction k G (Fin (n + 1) → G) ≅
      Rep.of
        ((Representation.ofMulAction k G G).tprod (1 : Representation k G ((Fin n → G) →₀ k))) :=
  Action.mkIso
    (LinearEquiv.toModuleIso
      { toTensorAux k G n with
        invFun := ofTensorAux k G n
        left_inv := toTensorAux_left_inv
        right_inv := fun x => by convert to_tensor_aux_right_inv x })
    (toTensor k G n).comm
#align group_cohomology.resolution.equiv_tensor GroupCohomology.Resolution.equivTensor

@[simp]
theorem equivTensor_def : (equivTensor k G n).hom = toTensor k G n :=
  rfl
#align group_cohomology.resolution.equiv_tensor_def GroupCohomology.Resolution.equivTensor_def

@[simp]
theorem equivTensor_inv_def : (equivTensor k G n).inv = ofTensor k G n :=
  rfl
#align group_cohomology.resolution.equiv_tensor_inv_def GroupCohomology.Resolution.equivTensor_inv_def

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `tensor_product.left_module`, whilst that of the righthand side comes from
`representation.as_module`. Allows us to use `basis.algebra_tensor_product` to get a `k[G]`-basis
of the righthand side. -/
def ofMulActionBasisAux :
    MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k) ≃ₗ[MonoidAlgebra k G]
      (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  { (Rep.equivalenceModuleMonoidAlgebra.1.mapIso (equivTensor k G n).symm).toLinearEquiv with
    map_smul' := fun r x =>
      by
      rw [RingHom.id_apply, LinearEquiv.toFun_eq_coe, ← LinearEquiv.map_smul]
      congr 1
      refine' x.induction_on _ (fun x y => _) fun y z hy hz => _
      · simp only [smul_zero]
      · simp only [TensorProduct.smul_tmul']
        show (r * x) ⊗ₜ y = _
        rw [← of_mul_action_self_smul_eq_mul, smul_tprod_one_as_module]
      · rw [smul_add, hz, hy, smul_add] }
#align group_cohomology.resolution.of_mul_action_basis_aux GroupCohomology.Resolution.ofMulActionBasisAux

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  @Basis.map _ (MonoidAlgebra k G) (MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k)) _ _ _ _ _ _
    (@Algebra.TensorProduct.basis k _ (MonoidAlgebra k G) _ _ ((Fin n → G) →₀ k) _ _ (Fin n → G)
      ⟨LinearEquiv.refl k _⟩)
    (ofMulActionBasisAux k G n)
#align group_cohomology.resolution.of_mul_action_basis GroupCohomology.Resolution.ofMulActionBasis

theorem ofMulActionFree :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  Module.Free.ofBasis (ofMulActionBasis k G n)
#align group_cohomology.resolution.of_mul_action_free GroupCohomology.Resolution.ofMulActionFree

end Basis

end GroupCohomology.resolution

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
def classifyingSpaceUniversalCover [Monoid G] : SimplicialObject (Action (Type u) <| Mon.of G)
    where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map m n f :=
    { hom := fun x => x ∘ f.unop.toOrderHom
      comm' := fun g => rfl }
  map_id' n := rfl
  map_comp' i j k f g := rfl
#align classifying_space_universal_cover classifyingSpaceUniversalCover

namespace classifyingSpaceUniversalCover

open CategoryTheory CategoryTheory.Limits

variable [Monoid G]

/-- When the category is `G`-Set, `cech_nerve_terminal_from` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cechNerveTerminalFromIso :
    cechNerveTerminalFrom (Action.ofMulAction G G) ≅ classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun n => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun m n f =>
    by
    refine' is_limit.hom_ext (Action.ofMulActionLimitCone.{u, 0} _ _).2 fun j => _
    dsimp only [cech_nerve_terminal_from, pi.lift]
    dsimp
    rw [category.assoc, limit.iso_limit_cone_hom_π, limit.lift_π, category.assoc]
    exact (limit.iso_limit_cone_hom_π _ _).symm
#align classifying_space_universal_cover.cech_nerve_terminal_from_iso classifyingSpaceUniversalCover.cechNerveTerminalFromIso

/-- As a simplicial set, `cech_nerve_terminal_from` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ :=
  NatIso.ofComponents (fun n => Types.productIso _) fun m n f =>
    Matrix.ext fun i j => Types.Limit.lift_π_apply _ _ _ _
#align classifying_space_universal_cover.cech_nerve_terminal_from_iso_comp_forget classifyingSpaceUniversalCover.cechNerveTerminalFromIsoCompForget

variable (k G)

open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`. -/
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun i g h => Subsingleton.elim _ _
#align classifying_space_universal_cover.comp_forget_augmented classifyingSpaceUniversalCover.compForgetAugmented

/-- The augmented Čech nerve of the map from `fin 1 → G` to the terminal object in `Type u` has an
extra degeneracy. -/
def extraDegeneracyAugmentedCechNerve :
    ExtraDegeneracy (Arrow.mk <| terminal.from G).augmentedCechNerve :=
  augmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨fun x => (1 : G),
      @Subsingleton.elim _ (@Unique.subsingleton _ (Limits.uniqueToTerminal _)) _ _⟩
#align classifying_space_universal_cover.extra_degeneracy_augmented_cech_nerve classifyingSpaceUniversalCover.extraDegeneracyAugmentedCechNerve

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) :=
  by
  refine'
    extra_degeneracy.of_iso (_ : (arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extra_degeneracy_augmented_cech_nerve G)
  exact
    comma.iso_mk (cech_nerve_terminal_from.iso G ≪≫ cech_nerve_terminal_from_iso_comp_forget G)
      (iso.refl _) (by ext : 2 <;> apply is_terminal.hom_ext terminal_is_terminal)
#align classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented

/-- The free functor `Type u ⥤ Module.{u} k` applied to the universal cover of the classifying
space of `G` as a simplicial set, augmented by the map from `fin 1 → G` to the terminal object
in `Type u`. -/
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free k)).obj (compForgetAugmented G)
#align classifying_space_universal_cover.comp_forget_augmented.to_Module classifyingSpaceUniversalCover.compForgetAugmented.toModule

/-- If we augment the universal cover of the classifying space of `G` as a simplicial set by the
map from `fin 1 → G` to the terminal object in `Type u`, then apply the free functor
`Type u ⥤ Module.{u} k`, the resulting augmented simplicial `k`-module has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmentedToModule :
    ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  ExtraDegeneracy.map (extraDegeneracyCompForgetAugmented G) (ModuleCat.free k)
#align classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented_to_Module classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmentedToModule

end classifyingSpaceUniversalCover

variable (k)

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def GroupCohomology.resolution [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1)
#align group_cohomology.resolution GroupCohomology.resolution

namespace GroupCohomology.resolution

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable (k G) [Monoid G]

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (G : Type u) (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (Fin n → G) →₀ k :=
  Finsupp.lift ((Fin n → G) →₀ k) k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).Sum fun p =>
      Finsupp.single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))
#align group_cohomology.resolution.d GroupCohomology.resolution.d

variable {k G}

@[simp]
theorem d_of {G : Type u} {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (Finsupp.single c 1) =
      Finset.univ.Sum fun p : Fin (n + 1) =>
        Finsupp.single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) :=
  by simp [d]
#align group_cohomology.resolution.d_of GroupCohomology.resolution.d_of

variable (k G)

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def xIso (n : ℕ) : (GroupCohomology.resolution k G).x n ≅ Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _
#align group_cohomology.resolution.X_iso GroupCohomology.resolution.xIso

theorem x_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((GroupCohomology.resolution k G).x n) :=
  Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of (MonoidAlgebra k G) (Representation.ofMulAction k G (Fin (n + 1) → G)).AsModule)
      _ (ofMulActionBasis k G n)
#align group_cohomology.resolution.X_projective GroupCohomology.resolution.x_projective

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) : ((GroupCohomology.resolution k G).d (n + 1) n).hom = d k G (n + 1) :=
  by
  ext (x y)
  dsimp [GroupCohomology.resolution]
  simpa [← @int_cast_smul k, simplicial_object.δ]
#align group_cohomology.resolution.d_eq GroupCohomology.resolution.d_eq

section Exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModule :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
    (GroupCohomology.resolution k G)
#align group_cohomology.resolution.forget₂_to_Module GroupCohomology.resolution.forget₂ToModule

/-- If we apply the free functor `Type u ⥤ Module.{u} k` to the universal cover of the classifying
space of `G` as a simplicial set, then take the alternating face map complex, the result is
isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      GroupCohomology.resolution.forget₂ToModule k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1))
#align group_cohomology.resolution.comp_forget_augmented_iso GroupCohomology.resolution.compForgetAugmentedIso

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂ToModuleHomotopyEquiv :
    HomotopyEquiv (GroupCohomology.resolution.forget₂ToModule k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj
        ((forget₂ (Rep k G) _).obj <| Rep.of Representation.trivial)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (@Finsupp.LinearEquiv.finsuppUnique k k _ _ _ (⊤_ Type u)
              Types.terminalIso.toEquiv.unique).toModuleIso)
#align group_cohomology.resolution.forget₂_to_Module_homotopy_equiv GroupCohomology.resolution.forget₂ToModuleHomotopyEquiv

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.of Representation.trivial
    where
  hom := Finsupp.total _ _ _ fun f => (1 : k)
  comm' g := by
    ext
    show
      Finsupp.total (Fin 1 → G) k k (fun f => (1 : k)) (Finsupp.mapDomain _ (Finsupp.single _ _)) =
        Finsupp.total _ _ _ _ (Finsupp.single _ _)
    simp only [Finsupp.mapDomain_single, Finsupp.total_single]
#align group_cohomology.resolution.ε GroupCohomology.resolution.ε

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂ToModuleHomotopyEquiv_f_0_eq :
    (forget₂ToModuleHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) :=
  by
  show (HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _).f 0 = _
  simp only [HomologicalComplex.comp_f]
  convert category.id_comp _
  · dsimp only [HomotopyEquiv.ofIso, comp_forget_augmented_iso, map_alternating_face_map_complex]
    simp only [iso.symm_hom, eq_to_iso.inv, HomologicalComplex.eqToHom_f, eq_to_hom_refl]
  trans (Finsupp.total _ _ _ fun f => (1 : k)).comp ((ModuleCat.free k).map (terminal.from _))
  · dsimp
    rw [@Finsupp.lmapDomain_total (Fin 1 → G) k k _ _ _ (⊤_ Type u) k _ _ (fun i => (1 : k))
        (fun i => (1 : k))
        (terminal.from
          ((classifyingSpaceUniversalCover G).obj (Opposite.op (SimplexCategory.mk 0))).V)
        LinearMap.id fun i => rfl,
      LinearMap.id_comp]
    rfl
  · congr
    · ext
      dsimp [HomotopyEquiv.ofIso]
      rw [Finsupp.total_single, one_smul, @Unique.eq_default _ types.terminal_iso.to_equiv.unique a,
        Finsupp.single_eq_same]
    · exact @Subsingleton.elim _ (@Unique.subsingleton _ (limits.unique_to_terminal _)) _ _
#align group_cohomology.resolution.forget₂_to_Module_homotopy_equiv_f_0_eq GroupCohomology.resolution.forget₂ToModuleHomotopyEquiv_f_0_eq

theorem d_comp_ε : (GroupCohomology.resolution k G).d 1 0 ≫ ε k G = 0 :=
  by
  ext1
  refine' LinearMap.ext fun x => _
  have : (forget₂_to_Module k G).d 1 0 ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂_to_Module_homotopy_equiv_f_0_eq, ←
        (forget₂_to_Module_homotopy_equiv k G).1.2 1 0 rfl] <;>
      exact comp_zero
  exact LinearMap.ext_iff.1 this _
#align group_cohomology.resolution.d_comp_ε GroupCohomology.resolution.d_comp_ε

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
def εToSingle₀ :
    GroupCohomology.resolution k G ⟶ (ChainComplex.single₀ _).obj (Rep.of Representation.trivial) :=
  ((GroupCohomology.resolution k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩
#align group_cohomology.resolution.ε_to_single₀ GroupCohomology.resolution.εToSingle₀

theorem εToSingle₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (ChainComplex.single₀MapHomologicalComplex _).hom.app _ =
      (forget₂ToModuleHomotopyEquiv k G).hom :=
  by
  refine' ChainComplex.to_single₀_ext _ _ _
  dsimp
  rw [category.comp_id]
  exact (forget₂_to_Module_homotopy_equiv_f_0_eq k G).symm
#align group_cohomology.resolution.ε_to_single₀_comp_eq GroupCohomology.resolution.εToSingle₀_comp_eq

theorem quasiIsoOfForget₂εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) :=
  by
  have h : QuasiIso (forget₂_to_Module_homotopy_equiv k G).hom := HomotopyEquiv.toQuasiIso _
  rw [← ε_to_single₀_comp_eq k G] at h
  haveI := h
  exact quasiIsoOfCompRight _ ((ChainComplex.single₀MapHomologicalComplex _).hom.app _)
#align group_cohomology.resolution.quasi_iso_of_forget₂_ε_to_single₀ GroupCohomology.resolution.quasiIsoOfForget₂εToSingle₀

instance : QuasiIso (εToSingle₀ k G) :=
  (forget₂ _ (ModuleCat.{u} k)).quasiIsoOfMapQuasiIso _ (quasiIsoOfForget₂εToSingle₀ k G)

end Exactness

end GroupCohomology.resolution

open GroupCohomology.resolution

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def GroupCohomology.projectiveResolution :
    ProjectiveResolution (Rep.of (@Representation.trivial k G _ _)) :=
  (εToSingle₀ k G).toSingle₀ProjectiveResolution (x_projective k G)
#align group_cohomology.ProjectiveResolution GroupCohomology.projectiveResolution

instance : EnoughProjectives (Rep k G) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2
    ModuleCat.moduleCat_enoughProjectives.{u}

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `group_cohomology.resolution k G`. -/
def GroupCohomology.extIso (V : Rep k G) (n : ℕ) :
    ((ext k (Rep k G) n).obj (Opposite.op <| Rep.of Representation.trivial)).obj V ≅
      (((((linearYoneda k (Rep k G)).obj V).rightOp.mapHomologicalComplex _).obj
              (GroupCohomology.resolution k G)).homology
          n).unop :=
  by
  let this :=
      (((linear_yoneda k (Rep k G)).obj V).rightOp.leftDerivedObjIso n
            (GroupCohomology.projectiveResolution k G)).unop.symm <;>
    exact this
#align group_cohomology.Ext_iso GroupCohomology.extIso

