/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathbin.Algebra.Homology.QuasiIso
import Mathbin.AlgebraicTopology.ExtraDegeneracy
import Mathbin.CategoryTheory.Abelian.Homology
import Mathbin.RepresentationTheory.RepCat

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

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`
 * `group_cohomology.resolution.equiv_tensor`
 * `group_cohomology.resolution.of_mul_action_basis`
 * `classifying_space_universal_cover`
 * `group_cohomology.resolution`
 * `group_cohomology.resolution.forget₂_to_Module_homotopy_equiv`

## TODO

 * Put these results together and apply the category equivalence `Rep k G ≅ Module k[G]` to define
   the standard resolution of `k` as a projective resolution.

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
  TensorProduct.lift ((Finsupp.lift _ _ _) fun g => Finsupp.lift _ _ _ fun f => single (g • partialProd f) (1 : k))
#align group_cohomology.resolution.of_tensor_aux GroupCohomology.Resolution.ofTensorAux

variable {k G n}

theorem to_tensor_aux_single (f : Gⁿ⁺¹) (m : k) :
    toTensorAux k G n (single f m) = single (f 0) m ⊗ₜ single (fun i => (f i)⁻¹ * f i.succ) 1 := by
  simp only [to_tensor_aux, lift_apply, sum_single_index, TensorProduct.smul_tmul']
  · simp
    
#align group_cohomology.resolution.to_tensor_aux_single GroupCohomology.Resolution.to_tensor_aux_single

theorem to_tensor_aux_of_mul_action (g : G) (x : Gⁿ⁺¹) :
    toTensorAux k G n (ofMulAction k G Gⁿ⁺¹ g (single x 1)) =
      TensorProduct.map (ofMulAction k G G g) 1 (toTensorAux k G n (single x 1)) :=
  by simp [of_mul_action_def, to_tensor_aux_single, mul_assoc, inv_mul_cancel_left]
#align group_cohomology.resolution.to_tensor_aux_of_mul_action GroupCohomology.Resolution.to_tensor_aux_of_mul_action

theorem of_tensor_aux_single (g : G) (m : k) (x : Gⁿ →₀ k) :
    ofTensorAux k G n (single g m ⊗ₜ x) = Finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (fun f => single (g • partialProd f) m) x := by
  simp [of_tensor_aux, sum_single_index, smul_sum, mul_comm m]
#align group_cohomology.resolution.of_tensor_aux_single GroupCohomology.Resolution.of_tensor_aux_single

theorem of_tensor_aux_comm_of_mul_action (g h : G) (x : Gⁿ) :
    ofTensorAux k G n
        (TensorProduct.map (ofMulAction k G G g) (1 : Module.EndCat k (Gⁿ →₀ k))
          (single h (1 : k) ⊗ₜ single x (1 : k))) =
      ofMulAction k G Gⁿ⁺¹ g (ofTensorAux k G n (single h 1 ⊗ₜ single x 1)) :=
  by simp [of_mul_action_def, of_tensor_aux_single, mul_smul]
#align
  group_cohomology.resolution.of_tensor_aux_comm_of_mul_action GroupCohomology.Resolution.of_tensor_aux_comm_of_mul_action

theorem to_tensor_aux_left_inv (x : Gⁿ⁺¹ →₀ k) : ofTensorAux _ _ _ (toTensorAux _ _ _ x) = x := by
  refine'
    LinearMap.ext_iff.1
      (@Finsupp.lhom_ext _ _ _ k _ _ _ _ _ (LinearMap.comp (of_tensor_aux _ _ _) (to_tensor_aux _ _ _)) LinearMap.id
        fun x y => _)
      x
  dsimp
  rw [to_tensor_aux_single x y, of_tensor_aux_single, Finsupp.lift_apply, Finsupp.sum_single_index, one_smul,
    Fin.partial_prod_left_inv]
  · rw [zero_smul]
    
#align group_cohomology.resolution.to_tensor_aux_left_inv GroupCohomology.Resolution.to_tensor_aux_left_inv

theorem to_tensor_aux_right_inv (x : (G →₀ k) ⊗[k] (Gⁿ →₀ k)) : toTensorAux _ _ _ (ofTensorAux _ _ _ x) = x := by
  refine' TensorProduct.induction_on x (by simp) (fun y z => _) fun z w hz hw => by simp [hz, hw]
  rw [← Finsupp.sum_single y, Finsupp.sum, TensorProduct.sum_tmul]
  simp only [Finset.smul_sum, LinearMap.map_sum]
  refine' Finset.sum_congr rfl fun f hf => _
  simp only [of_tensor_aux_single, Finsupp.lift_apply, Finsupp.smul_single', LinearMap.map_finsupp_sum,
    to_tensor_aux_single, Fin.partial_prod_right_inv]
  dsimp
  simp only [Fin.partial_prod_zero, mul_one]
  conv_rhs => rw [← Finsupp.sum_single z, Finsupp.sum, TensorProduct.tmul_sum]
  exact
    Finset.sum_congr rfl fun g hg =>
      show _ ⊗ₜ _ = _ by rw [← Finsupp.smul_single', TensorProduct.smul_tmul, Finsupp.smul_single_one]
#align group_cohomology.resolution.to_tensor_aux_right_inv GroupCohomology.Resolution.to_tensor_aux_right_inv

variable (k G n)

/-- A hom of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def toTensor :
    RepCat.ofMulAction k G (Fin (n + 1) → G) ⟶
      RepCat.of ((Representation.ofMulAction k G G).tprod (1 : G →* Module.EndCat k ((Fin n → G) →₀ k))) where
  Hom := toTensorAux k G n
  comm' g := by ext <;> exact to_tensor_aux_of_mul_action _ _
#align group_cohomology.resolution.to_tensor GroupCohomology.Resolution.toTensor

/-- A hom of `k`-linear representations of `G` from `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def ofTensor :
    RepCat.of ((Representation.ofMulAction k G G).tprod (1 : G →* Module.EndCat k ((Fin n → G) →₀ k))) ⟶
      RepCat.ofMulAction k G (Fin (n + 1) → G) where
  Hom := ofTensorAux k G n
  comm' g := by
    ext
    congr 1
    exact of_tensor_aux_comm_of_mul_action _ _ _
#align group_cohomology.resolution.of_tensor GroupCohomology.Resolution.ofTensor

variable {k G n}

@[simp]
theorem to_tensor_single (f : Gⁿ⁺¹) (m : k) :
    (toTensor k G n).Hom (single f m) = single (f 0) m ⊗ₜ single (fun i => (f i)⁻¹ * f i.succ) 1 :=
  to_tensor_aux_single _ _
#align group_cohomology.resolution.to_tensor_single GroupCohomology.Resolution.to_tensor_single

@[simp]
theorem of_tensor_single (g : G) (m : k) (x : Gⁿ →₀ k) :
    (ofTensor k G n).Hom (single g m ⊗ₜ x) =
      Finsupp.lift (RepCat.ofMulAction k G Gⁿ⁺¹) k Gⁿ (fun f => single (g • partialProd f) m) x :=
  of_tensor_aux_single _ _ _
#align group_cohomology.resolution.of_tensor_single GroupCohomology.Resolution.of_tensor_single

theorem of_tensor_single' (g : G →₀ k) (x : Gⁿ) (m : k) :
    (ofTensor k G n).Hom (g ⊗ₜ single x m) = Finsupp.lift _ k G (fun a => single (a • partialProd x) m) g := by
  simp [of_tensor, of_tensor_aux]
#align group_cohomology.resolution.of_tensor_single' GroupCohomology.Resolution.of_tensor_single'

variable (k G n)

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def equivTensor :
    RepCat.ofMulAction k G (Fin (n + 1) → G) ≅
      RepCat.of ((Representation.ofMulAction k G G).tprod (1 : Representation k G ((Fin n → G) →₀ k))) :=
  ActionCat.mkIso
    (LinearEquiv.toModuleIso
      { toTensorAux k G n with invFun := ofTensorAux k G n, left_inv := to_tensor_aux_left_inv,
        right_inv := fun x => by convert to_tensor_aux_right_inv x })
    (toTensor k G n).comm
#align group_cohomology.resolution.equiv_tensor GroupCohomology.Resolution.equivTensor

@[simp]
theorem equiv_tensor_def : (equivTensor k G n).Hom = toTensor k G n :=
  rfl
#align group_cohomology.resolution.equiv_tensor_def GroupCohomology.Resolution.equiv_tensor_def

@[simp]
theorem equiv_tensor_inv_def : (equivTensor k G n).inv = ofTensor k G n :=
  rfl
#align group_cohomology.resolution.equiv_tensor_inv_def GroupCohomology.Resolution.equiv_tensor_inv_def

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `tensor_product.left_module`, whilst that of the righthand side comes from
`representation.as_module`. Allows us to use `basis.algebra_tensor_product` to get a `k[G]`-basis
of the righthand side. -/
def ofMulActionBasisAux :
    MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k) ≃ₗ[MonoidAlgebra k G] (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  { (RepCat.equivalenceModuleMonoidAlgebra.1.mapIso (equivTensor k G n).symm).toLinearEquiv with
    map_smul' := fun r x => by
      rw [RingHom.id_apply, LinearEquiv.to_fun_eq_coe, ← LinearEquiv.map_smul]
      congr 1
      refine' x.induction_on _ (fun x y => _) fun y z hy hz => _
      · simp only [smul_zero]
        
      · simp only [TensorProduct.smul_tmul']
        show (r * x) ⊗ₜ y = _
        rw [← of_mul_action_self_smul_eq_mul, smul_tprod_one_as_module]
        
      · rw [smul_add, hz, hy, smul_add]
         }
#align group_cohomology.resolution.of_mul_action_basis_aux GroupCohomology.Resolution.ofMulActionBasisAux

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionBasis : Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  @Basis.map _ (MonoidAlgebra k G) (MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k)) _ _ _ _ _ _
    (@Algebra.TensorProduct.basis k _ (MonoidAlgebra k G) _ _ ((Fin n → G) →₀ k) _ _ (Fin n → G) ⟨LinearEquiv.refl k _⟩)
    (ofMulActionBasisAux k G n)
#align group_cohomology.resolution.of_mul_action_basis GroupCohomology.Resolution.ofMulActionBasis

theorem ofMulActionFree : Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  Module.Free.ofBasis (ofMulActionBasis k G n)
#align group_cohomology.resolution.of_mul_action_free GroupCohomology.Resolution.ofMulActionFree

end Basis

end GroupCohomology.resolution

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
def classifyingSpaceUniversalCover [Monoid G] : SimplicialObject (ActionCat (Type u) <| MonCat.of G) where
  obj n := ActionCat.ofMulAction G (Fin (n.unop.len + 1) → G)
  map m n f := { Hom := fun x => x ∘ f.unop.toOrderHom, comm' := fun g => rfl }
  map_id' n := rfl
  map_comp' i j k f g := rfl
#align classifying_space_universal_cover classifyingSpaceUniversalCover

namespace classifyingSpaceUniversalCover

open CategoryTheory CategoryTheory.Limits

variable [Monoid G]

/-- When the category is `G`-Set, `cech_nerve_terminal_from` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cechNerveTerminalFromIso : cechNerveTerminalFrom (ActionCat.ofMulAction G G) ≅ classifyingSpaceUniversalCover G :=
  (NatIso.ofComponents fun n => limit.isoLimitCone (ActionCat.ofMulActionLimitCone _ _)) fun m n f => by
    refine' is_limit.hom_ext (ActionCat.ofMulActionLimitCone.{u, 0} _ _).2 fun j => _
    dsimp only [cech_nerve_terminal_from, pi.lift]
    dsimp
    rw [category.assoc, limit.iso_limit_cone_hom_π, limit.lift_π, category.assoc]
    exact (limit.iso_limit_cone_hom_π _ _).symm
#align
  classifying_space_universal_cover.cech_nerve_terminal_from_iso classifyingSpaceUniversalCover.cechNerveTerminalFromIso

/-- As a simplicial set, `cech_nerve_terminal_from` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
def cechNerveTerminalFromIsoCompForget : cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ :=
  (NatIso.ofComponents fun n => Types.productIso _) fun m n f => Matrix.ext fun i j => Types.Limit.lift_π_apply _ _ _ _
#align
  classifying_space_universal_cover.cech_nerve_terminal_from_iso_comp_forget classifyingSpaceUniversalCover.cechNerveTerminalFromIsoCompForget

variable (k G)

open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`. -/
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  (SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _) (terminal.from _)) fun i g h =>
    Subsingleton.elim _ _
#align classifying_space_universal_cover.comp_forget_augmented classifyingSpaceUniversalCover.compForgetAugmented

/-- The augmented Čech nerve of the map from `fin 1 → G` to the terminal object in `Type u` has an
extra degeneracy. -/
def extraDegeneracyAugmentedCechNerve : ExtraDegeneracy (arrow.mk <| terminal.from G).augmentedCechNerve :=
  augmentedCechNerve.extraDegeneracy (arrow.mk <| terminal.from G)
    ⟨fun x => (1 : G), @Subsingleton.elim _ (@Unique.subsingleton _ (Limits.uniqueToTerminal _)) _ _⟩
#align
  classifying_space_universal_cover.extra_degeneracy_augmented_cech_nerve classifyingSpaceUniversalCover.extraDegeneracyAugmentedCechNerve

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) := by
  refine'
    extra_degeneracy.of_iso (_ : (arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extra_degeneracy_augmented_cech_nerve G)
  exact
    comma.iso_mk (cech_nerve_terminal_from.iso G ≪≫ cech_nerve_terminal_from_iso_comp_forget G) (iso.refl _)
      (by ext : 2 <;> apply is_terminal.hom_ext terminal_is_terminal)
#align
  classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented

/-- The free functor `Type u ⥤ Module.{u} k` applied to the universal cover of the classifying
space of `G` as a simplicial set, augmented by the map from `fin 1 → G` to the terminal object
in `Type u`. -/
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free k)).obj (compForgetAugmented G)
#align
  classifying_space_universal_cover.comp_forget_augmented.to_Module classifyingSpaceUniversalCover.compForgetAugmented.toModule

/-- If we augment the universal cover of the classifying space of `G` as a simplicial set by the
map from `fin 1 → G` to the terminal object in `Type u`, then apply the free functor
`Type u ⥤ Module.{u} k`, the resulting augmented simplicial `k`-module has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmentedToModule : ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  ExtraDegeneracy.map (extraDegeneracyCompForgetAugmented G) (ModuleCat.free k)
#align
  classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented_to_Module classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmentedToModule

end classifyingSpaceUniversalCover

variable (k) [Monoid G]

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def GroupCohomology.resolution :=
  (AlgebraicTopology.alternatingFaceMapComplex (RepCat k G)).obj
    (classifyingSpaceUniversalCover G ⋙ (RepCat.linearization k G).1.1)
#align group_cohomology.resolution GroupCohomology.resolution

namespace GroupCohomology.resolution

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable (k G)

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (G : Type u) (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (Fin n → G) →₀ k :=
  Finsupp.lift ((Fin n → G) →₀ k) k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).Sum fun p => Finsupp.single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))
#align group_cohomology.resolution.d GroupCohomology.resolution.d

variable {k G}

@[simp]
theorem d_of {G : Type u} {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (Finsupp.single c 1) =
      Finset.univ.Sum fun p : Fin (n + 1) => Finsupp.single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) :=
  by simp [d]
#align group_cohomology.resolution.d_of GroupCohomology.resolution.d_of

variable (k G)

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def xIso (n : ℕ) : (GroupCohomology.resolution k G).x n ≅ RepCat.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _
#align group_cohomology.resolution.X_iso GroupCohomology.resolution.xIso

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) : ((GroupCohomology.resolution k G).d (n + 1) n).Hom = d k G (n + 1) := by
  ext (x y)
  dsimp [GroupCohomology.resolution]
  simpa [← @int_cast_smul k, simplicial_object.δ]
#align group_cohomology.resolution.d_eq GroupCohomology.resolution.d_eq

section Exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModule :=
  ((forget₂ (RepCat k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj (GroupCohomology.resolution k G)
#align group_cohomology.resolution.forget₂_to_Module GroupCohomology.resolution.forget₂ToModule

/-- If we apply the free functor `Type u ⥤ Module.{u} k` to the universal cover of the classifying
space of `G` as a simplicial set, then take the alternating face map complex, the result is
isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      GroupCohomology.resolution.forget₂ToModule k G :=
  eqToIso
    (Functor.congr_obj (map_alternating_face_map_complex (forget₂ (RepCat k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ (RepCat.linearization k G).1.1))
#align group_cohomology.resolution.comp_forget_augmented_iso GroupCohomology.resolution.compForgetAugmentedIso

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂ToModuleHomotopyEquiv :
    HomotopyEquiv (GroupCohomology.resolution.forget₂ToModule k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj ((forget₂ (RepCat k G) _).obj <| RepCat.of Representation.trivial)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (@Finsupp.LinearEquiv.finsuppUnique k k _ _ _ (⊤_ Type u) Types.terminalIso.toEquiv.unique).toModuleIso)
#align
  group_cohomology.resolution.forget₂_to_Module_homotopy_equiv GroupCohomology.resolution.forget₂ToModuleHomotopyEquiv

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def ε : RepCat.ofMulAction k G (Fin 1 → G) ⟶ RepCat.of Representation.trivial where
  Hom := Finsupp.total _ _ _ fun f => (1 : k)
  comm' g := by
    ext
    show
      Finsupp.total (Fin 1 → G) k k (fun f => (1 : k)) (Finsupp.mapDomain _ (Finsupp.single _ _)) =
        Finsupp.total _ _ _ _ (Finsupp.single _ _)
    simp only [Finsupp.map_domain_single, Finsupp.total_single]
#align group_cohomology.resolution.ε GroupCohomology.resolution.ε

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂_to_Module_homotopy_equiv_f_0_eq :
    (forget₂ToModuleHomotopyEquiv k G).1.f 0 = (forget₂ (RepCat k G) _).map (ε k G) := by
  show (HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _).f 0 = _
  simp only [HomologicalComplex.comp_f]
  convert category.id_comp _
  · dsimp only [HomotopyEquiv.ofIso, comp_forget_augmented_iso, map_alternating_face_map_complex]
    simp only [iso.symm_hom, eq_to_iso.inv, HomologicalComplex.eq_to_hom_f, eq_to_hom_refl]
    
  trans (Finsupp.total _ _ _ fun f => (1 : k)).comp ((ModuleCat.free k).map (terminal.from _))
  · dsimp
    rw [@Finsupp.lmap_domain_total (Fin 1 → G) k k _ _ _ (⊤_ Type u) k _ _ (fun i => (1 : k)) (fun i => (1 : k))
        (terminal.from ((classifyingSpaceUniversalCover G).obj (Opposite.op (SimplexCategory.mk 0))).V) LinearMap.id
        fun i => rfl,
      LinearMap.id_comp]
    rfl
    
  · congr
    · ext
      dsimp [HomotopyEquiv.ofIso]
      rw [Finsupp.total_single, one_smul, @Unique.eq_default _ types.terminal_iso.to_equiv.unique a,
        Finsupp.single_eq_same]
      
    · exact @Subsingleton.elim _ (@Unique.subsingleton _ (limits.unique_to_terminal _)) _ _
      
    
#align
  group_cohomology.resolution.forget₂_to_Module_homotopy_equiv_f_0_eq GroupCohomology.resolution.forget₂_to_Module_homotopy_equiv_f_0_eq

theorem d_comp_ε : (GroupCohomology.resolution k G).d 1 0 ≫ ε k G = 0 := by
  ext1
  refine' LinearMap.ext fun x => _
  have : (forget₂_to_Module k G).d 1 0 ≫ (forget₂ (RepCat k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂_to_Module_homotopy_equiv_f_0_eq, ← (forget₂_to_Module_homotopy_equiv k G).1.2 1 0 rfl] <;>
      exact comp_zero
  exact LinearMap.ext_iff.1 this _
#align group_cohomology.resolution.d_comp_ε GroupCohomology.resolution.d_comp_ε

theorem forget₂_to_Module_exact_succ (n : ℕ) :
    Exact ((GroupCohomology.resolution.forget₂ToModule k G).d (n + 2) (n + 1))
      ((GroupCohomology.resolution.forget₂ToModule k G).d (n + 1) n) :=
  (Preadditive.exact_iff_homology_zero _ _).2
    ⟨(GroupCohomology.resolution.forget₂ToModule k G).d_comp_d _ _ _,
      ⟨(ChainComplex.homologySuccIso _ _).symm.trans
          ((homologyObjIsoOfHomotopyEquiv (forget₂ToModuleHomotopyEquiv k G) _).trans homologyZeroZero)⟩⟩
#align group_cohomology.resolution.forget₂_to_Module_exact_succ GroupCohomology.resolution.forget₂_to_Module_exact_succ

theorem exact_at_succ (n : ℕ) :
    Exact ((GroupCohomology.resolution k G).d (n + 2) (n + 1)) ((GroupCohomology.resolution k G).d (n + 1) n) :=
  (forget₂ (RepCat k G) (ModuleCat.{u} k)).exact_of_exact_map (forget₂_to_Module_exact_succ _ _ _)
#align group_cohomology.resolution.exact_at_succ GroupCohomology.resolution.exact_at_succ

theorem forget_to_Module_exact₀ :
    Exact ((GroupCohomology.resolution.forget₂ToModule k G).d 1 0) ((forget₂ToModuleHomotopyEquiv k G).1.f 0) := by
  rw [preadditive.exact_iff_homology_zero]
  have h : (forget₂_to_Module k G).d 1 0 ≫ (forget₂_to_Module_homotopy_equiv k G).Hom.f 0 = 0 := by
    rw [← (forget₂_to_Module_homotopy_equiv k G).1.2 1 0 rfl]
    simp only [ChainComplex.single₀_obj_X_d, comp_zero]
  refine' ⟨h, Nonempty.intro (homologyIsoKernelDesc _ _ _ ≪≫ _)⟩
  · suffices is_split_mono (cokernel.desc _ _ h) by
      haveI := this
      apply kernel.of_mono
    refine'
      is_split_mono.mk'
        ⟨(forget₂_to_Module_homotopy_equiv k G).2.f 0 ≫ cokernel.π ((forget₂_to_Module k G).d 1 0),
          coequalizer.hom_ext _⟩
    rw [cokernel.π_desc_assoc, ← category.assoc, ← HomologicalComplex.comp_f,
      (forget₂_to_Module_homotopy_equiv k G).homotopyHomInvId.comm 0]
    simp
    
#align group_cohomology.resolution.forget_to_Module_exact₀ GroupCohomology.resolution.forget_to_Module_exact₀

theorem exact₀ : Exact ((GroupCohomology.resolution k G).d 1 0) (ε k G) :=
  (forget₂ (RepCat k G) (ModuleCat.{u} k)).exact_of_exact_map
    (by rw [← forget₂_to_Module_homotopy_equiv_f_0_eq] <;> exact forget_to_Module_exact₀ _ _)
#align group_cohomology.resolution.exact₀ GroupCohomology.resolution.exact₀

end Exactness

end GroupCohomology.resolution

