/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathbin.RepresentationTheory.Rep
import Mathbin.RepresentationTheory.Basic

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains facts about an important `k[G]`-module structure on `k[Gⁿ]`, where `k` is a
commutative ring and `G` is a group. The module structure arises from the representation
`G →* End(k[Gⁿ])` induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define an isomorphism of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

This allows us to define a `k[G]`-basis on `k[Gⁿ⁺¹]`, by mapping the natural `k[G]`-basis of
`k[G] ⊗ₖ k[Gⁿ]` along the isomorphism.

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`
 * `group_cohomology.resolution.equiv_tensor`
 * `group_cohomology.resolution.of_mul_action_basis`

## TODO

 * Use the freeness of `k[Gⁿ⁺¹]` to build a projective resolution of the (trivial) `k[G]`-module
   `k`, and so develop group cohomology.

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

universe u

variable {k G : Type u} [CommRingₓ k] {n : ℕ}

open TensorProduct

-- mathport name: «exprGⁿ»
local notation "Gⁿ" => Finₓ n → G

-- mathport name: «exprGⁿ⁺¹»
local notation "Gⁿ⁺¹" => Finₓ (n + 1) → G

namespace GroupCohomology.Resolution

open Finsupp hiding lift

open Finₓ (partialProd)

open Representation

variable (k G n) [Groupₓ G]

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def toTensorAux : ((Finₓ (n + 1) → G) →₀ k) →ₗ[k] (G →₀ k) ⊗[k] ((Finₓ n → G) →₀ k) :=
  Finsupp.lift ((G →₀ k) ⊗[k] ((Finₓ n → G) →₀ k)) k (Finₓ (n + 1) → G) fun x =>
    single (x 0) 1 ⊗ₜ[k] single (fun i => (x i)⁻¹ * x i.succ) 1

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def ofTensorAux : (G →₀ k) ⊗[k] ((Finₓ n → G) →₀ k) →ₗ[k] (Finₓ (n + 1) → G) →₀ k :=
  TensorProduct.lift ((Finsupp.lift _ _ _) fun g => Finsupp.lift _ _ _ fun f => single (g • partialProd f) (1 : k))

variable {k G n}

theorem to_tensor_aux_single (f : Gⁿ⁺¹) (m : k) :
    toTensorAux k G n (single f m) = single (f 0) m ⊗ₜ single (fun i => (f i)⁻¹ * f i.succ) 1 := by
  simp only [to_tensor_aux, lift_apply, sum_single_index, TensorProduct.smul_tmul']
  · simp
    

theorem to_tensor_aux_of_mul_action (g : G) (x : Gⁿ⁺¹) :
    toTensorAux k G n (ofMulAction k G Gⁿ⁺¹ g (single x 1)) =
      TensorProduct.map (ofMulAction k G G g) 1 (toTensorAux k G n (single x 1)) :=
  by
  simp [of_mul_action_def, to_tensor_aux_single, mul_assoc, inv_mul_cancel_leftₓ]

theorem of_tensor_aux_single (g : G) (m : k) (x : Gⁿ →₀ k) :
    ofTensorAux k G n (single g m ⊗ₜ x) = Finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (fun f => single (g • partialProd f) m) x := by
  simp [of_tensor_aux, sum_single_index, smul_sum, mul_comm m]

theorem of_tensor_aux_comm_of_mul_action (g h : G) (x : Gⁿ) :
    ofTensorAux k G n
        (TensorProduct.map (ofMulAction k G G g) (1 : Module.End k (Gⁿ →₀ k)) (single h (1 : k) ⊗ₜ single x (1 : k))) =
      ofMulAction k G Gⁿ⁺¹ g (ofTensorAux k G n (single h 1 ⊗ₜ single x 1)) :=
  by
  simp [of_mul_action_def, of_tensor_aux_single, mul_smul]

theorem to_tensor_aux_left_inv (x : Gⁿ⁺¹ →₀ k) : ofTensorAux _ _ _ (toTensorAux _ _ _ x) = x := by
  refine'
    LinearMap.ext_iff.1
      (@Finsupp.lhom_ext _ _ _ k _ _ _ _ _ (LinearMap.comp (of_tensor_aux _ _ _) (to_tensor_aux _ _ _)) LinearMap.id
        fun x y => _)
      x
  dsimp'
  rw [to_tensor_aux_single x y, of_tensor_aux_single, Finsupp.lift_apply, Finsupp.sum_single_index, one_smul,
    Finₓ.partial_prod_left_inv]
  · rw [zero_smul]
    

theorem to_tensor_aux_right_inv (x : (G →₀ k) ⊗[k] (Gⁿ →₀ k)) : toTensorAux _ _ _ (ofTensorAux _ _ _ x) = x := by
  refine'
    TensorProduct.induction_on x
      (by
        simp )
      (fun y z => _) fun z w hz hw => by
      simp [hz, hw]
  rw [← Finsupp.sum_single y, Finsupp.sum, TensorProduct.sum_tmul]
  simp only [Finset.smul_sum, LinearMap.map_sum]
  refine' Finset.sum_congr rfl fun f hf => _
  simp only [of_tensor_aux_single, Finsupp.lift_apply, Finsupp.smul_single', LinearMap.map_finsupp_sum,
    to_tensor_aux_single, Finₓ.partial_prod_right_inv]
  dsimp'
  simp only [Finₓ.partial_prod_zero, mul_oneₓ]
  conv_rhs => rw [← Finsupp.sum_single z, Finsupp.sum, TensorProduct.tmul_sum]
  exact
    Finset.sum_congr rfl fun g hg =>
      show _ ⊗ₜ _ = _ by
        rw [← Finsupp.smul_single', TensorProduct.smul_tmul, Finsupp.smul_single_one]

variable (k G n)

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
abbrev _root_.Rep.of_mul_action (G : Type u) [Monoidₓ G] (H : Type u) [MulAction G H] : Rep k G :=
  Rep.of <| Representation.ofMulAction k G H

/-- A hom of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def toTensor :
    Rep.ofMulAction k G (Finₓ (n + 1) → G) ⟶
      Rep.of ((Representation.ofMulAction k G G).tprod (1 : G →* Module.End k ((Finₓ n → G) →₀ k))) where
  hom := toTensorAux k G n
  comm' := fun g => by
    ext <;> exact to_tensor_aux_of_mul_action _ _

/-- A hom of `k`-linear representations of `G` from `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def ofTensor :
    Rep.of ((Representation.ofMulAction k G G).tprod (1 : G →* Module.End k ((Finₓ n → G) →₀ k))) ⟶
      Rep.ofMulAction k G (Finₓ (n + 1) → G) where
  hom := ofTensorAux k G n
  comm' := fun g => by
    ext
    congr 1
    exact of_tensor_aux_comm_of_mul_action _ _ _

variable {k G n}

@[simp]
theorem to_tensor_single (f : Gⁿ⁺¹) (m : k) :
    (toTensor k G n).hom (single f m) = single (f 0) m ⊗ₜ single (fun i => (f i)⁻¹ * f i.succ) 1 :=
  to_tensor_aux_single _ _

@[simp]
theorem of_tensor_single (g : G) (m : k) (x : Gⁿ →₀ k) :
    (ofTensor k G n).hom (single g m ⊗ₜ x) =
      Finsupp.lift (Rep.ofMulAction k G Gⁿ⁺¹) k Gⁿ (fun f => single (g • partialProd f) m) x :=
  of_tensor_aux_single _ _ _

theorem of_tensor_single' (g : G →₀ k) (x : Gⁿ) (m : k) :
    (ofTensor k G n).hom (g ⊗ₜ single x m) = Finsupp.lift _ k G (fun a => single (a • partialProd x) m) g := by
  simp [of_tensor, of_tensor_aux]

variable (k G n)

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def equivTensor :
    Rep.ofMulAction k G (Finₓ (n + 1) → G) ≅
      Rep.of ((Representation.ofMulAction k G G).tprod (1 : Representation k G ((Finₓ n → G) →₀ k))) :=
  Action.mkIso
    (LinearEquiv.toModuleIso
      { toTensorAux k G n with invFun := ofTensorAux k G n, left_inv := to_tensor_aux_left_inv,
        right_inv := fun x => by
          convert to_tensor_aux_right_inv x })
    (toTensor k G n).comm

-- not quite sure which simp lemmas to make here
@[simp]
theorem equiv_tensor_def : (equivTensor k G n).hom = toTensor k G n :=
  rfl

@[simp]
theorem equiv_tensor_inv_def : (equivTensor k G n).inv = ofTensor k G n :=
  rfl

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `tensor_product.left_module`, whilst that of the righthand side comes from
`representation.as_module`. Allows us to use `basis.algebra_tensor_product` to get a `k[G]`-basis
of the righthand side. -/
def ofMulActionBasisAux :
    MonoidAlgebra k G ⊗[k] ((Finₓ n → G) →₀ k) ≃ₗ[MonoidAlgebra k G] (ofMulAction k G (Finₓ (n + 1) → G)).AsModule :=
  { (Rep.equivalenceModuleMonoidAlgebra.1.mapIso (equivTensor k G n).symm).toLinearEquiv with
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

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionBasis : Basis (Finₓ n → G) (MonoidAlgebra k G) (ofMulAction k G (Finₓ (n + 1) → G)).AsModule :=
  @Basis.map _ (MonoidAlgebra k G) (MonoidAlgebra k G ⊗[k] ((Finₓ n → G) →₀ k)) _ _ _ _ _ _
    (@Algebra.TensorProduct.basis k _ (MonoidAlgebra k G) _ _ ((Finₓ n → G) →₀ k) _ _ (Finₓ n → G)
      ⟨LinearEquiv.refl k _⟩)
    (ofMulActionBasisAux k G n)

theorem of_mul_action_free : Module.Free (MonoidAlgebra k G) (ofMulAction k G (Finₓ (n + 1) → G)).AsModule :=
  Module.Free.of_basis (ofMulActionBasis k G n)

end GroupCohomology.Resolution

