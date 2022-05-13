/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.MonoidAlgebra.Basic
import Mathbin.LinearAlgebra.Trace
import Mathbin.LinearAlgebra.Dual
import Mathbin.LinearAlgebra.FreeModule.Basic

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * representation.representation
  * representation.character
  * representation.tprod
  * representation.lin_hom
  * represensation.dual

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`.
-/


open MonoidAlgebra (lift of)

open LinearMap

section

variable (k G V : Type _) [CommSemiringₓ k] [Monoidₓ G] [AddCommMonoidₓ V] [Module k V]

/-- A representation of `G` on the `k`-module `V` is an homomorphism `G →* (V →ₗ[k] V)`.
-/
abbrev Representation :=
  G →* V →ₗ[k] V

end

namespace Representation

section trivialₓ

variable {k G V : Type _} [CommSemiringₓ k] [Monoidₓ G] [AddCommMonoidₓ V] [Module k V]

/-- The trivial representation of `G` on the one-dimensional module `k`.
-/
def trivial : Representation k G k :=
  1

@[simp]
theorem trivial_def (g : G) (v : k) : trivial g v = v :=
  rfl

end trivialₓ

section MonoidAlgebra

variable {k G V : Type _} [CommSemiringₓ k] [Monoidₓ G] [AddCommMonoidₓ V] [Module k V]

variable (ρ : Representation k G V)

/-- A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `monoid_algebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def asAlgebraHom : MonoidAlgebra k G →ₐ[k] Module.End k V :=
  (lift k G _) ρ

theorem as_algebra_hom_def : asAlgebraHom ρ = (lift k G _) ρ :=
  rfl

@[simp]
theorem as_algebra_hom_single (g : G) : asAlgebraHom ρ (Finsupp.single g 1) = ρ g := by
  simp only [as_algebra_hom_def, MonoidAlgebra.lift_single, one_smul]

theorem as_algebra_hom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [MonoidAlgebra.of_apply, as_algebra_hom_single]

/-- A `k`-linear representation of `G` on `V` can be thought of as
a module over `monoid_algebra k G`.
-/
noncomputable def asModule : Module (MonoidAlgebra k G) V :=
  Module.compHom V (asAlgebraHom ρ).toRingHom

end MonoidAlgebra

section Groupₓ

variable {k G V : Type _} [CommSemiringₓ k] [Groupₓ G] [AddCommMonoidₓ V] [Module k V]

variable (ρ : Representation k G V)

/-- When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def asGroupHom : G →* Units (V →ₗ[k] V) :=
  MonoidHom.toHomUnits ρ

theorem as_group_hom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g := by
  simp only [as_group_hom, MonoidHom.coe_to_hom_units]

end Groupₓ

section Character

variable {k G V : Type _} [CommRingₓ k] [Groupₓ G] [AddCommGroupₓ V] [Module k V]

variable (ρ : Representation k G V)

/-- The character associated to a representation of `G`, which as a map `G → k`
sends each element to the trace of the corresponding linear map.
-/
@[simp]
noncomputable def character (g : G) : k :=
  trace k V (ρ g)

theorem char_mul_comm (g : G) (h : G) : character ρ (h * g) = character ρ (g * h) := by
  simp only [trace_mul_comm, character, map_mul]

/-- The character of a representation is constant on conjugacy classes. -/
theorem char_conj (g : G) (h : G) : (character ρ) (h * g * h⁻¹) = (character ρ) g := by
  simp only [character, ← as_group_hom_apply, map_mul, map_inv, trace_conj]

variable [Nontrivial k] [Module.Free k V] [Module.Finite k V]

/-- The evaluation of the character at the identity is the dimension of the representation. -/
theorem char_one : character ρ 1 = FiniteDimensional.finrank k V := by
  simp only [character, map_one, trace_one]

end Character

section TensorProduct

variable {k G V W : Type _} [CommSemiringₓ k] [Monoidₓ G]

variable [AddCommMonoidₓ V] [Module k V] [AddCommMonoidₓ W] [Module k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

open TensorProduct

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
def tprod : Representation k G (V ⊗[k] W) where
  toFun := fun g => TensorProduct.map (ρV g) (ρW g)
  map_one' := by
    simp only [map_one, TensorProduct.map_one]
  map_mul' := fun g h => by
    simp only [map_mul, TensorProduct.map_mul]

-- mathport name: «expr ⊗ »
notation ρV " ⊗ " ρW => tprod ρV ρW

@[simp]
theorem tprod_apply (g : G) : (ρV ⊗ ρW) g = TensorProduct.map (ρV g) (ρW g) :=
  rfl

end TensorProduct

section LinearHom

variable {k G V W : Type _} [CommSemiringₓ k] [Groupₓ G]

variable [AddCommMonoidₓ V] [Module k V] [AddCommMonoidₓ W] [Module k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def linHom : Representation k G (V →ₗ[k] W) where
  toFun := fun g =>
    { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹,
      map_add' := fun f₁ f₂ => by
        simp_rw [add_comp, comp_add],
      map_smul' := fun r f => by
        simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' :=
    LinearMap.ext fun x => by
      simp_rw [coe_mk, inv_one, map_one, one_apply, one_eq_id, comp_id, id_comp]
  map_mul' := fun g h =>
    LinearMap.ext fun x => by
      simp_rw [coe_mul, coe_mk, Function.comp_applyₓ, mul_inv_rev, map_mul, mul_eq_comp, comp_assoc]

@[simp]
theorem lin_hom_apply (g : G) (f : V →ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹ :=
  rfl

/-- The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : module.dual k V`.
-/
def dual : Representation k G (Module.Dual k V) where
  toFun := fun g =>
    { toFun := fun f => f ∘ₗ ρV g⁻¹,
      map_add' := fun f₁ f₂ => by
        simp only [add_comp],
      map_smul' := fun r f => by
        ext
        simp only [coe_comp, Function.comp_app, smul_apply, RingHom.id_apply] }
  map_one' := by
    ext
    simp only [coe_comp, Function.comp_app, map_one, inv_one, coe_mk, one_apply]
  map_mul' := fun g h => by
    ext
    simp only [coe_comp, Function.comp_app, mul_inv_rev, map_mul, coe_mk, mul_apply]

@[simp]
theorem dual_apply (g : G) (f : Module.Dual k V) : (dual ρV) g f = f ∘ₗ ρV g⁻¹ :=
  rfl

end LinearHom

end Representation

