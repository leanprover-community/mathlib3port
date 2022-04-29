/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.Nilpotent

/-!
# Cartan subalgebras

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `lie_subalgebra.normalizer`
  * `lie_subalgebra.le_normalizer_of_ideal`
  * `lie_subalgebra.is_cartan_subalgebra`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/


universe u v w w₁ w₂

variable {R : Type u} {L : Type v}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] (H : LieSubalgebra R L)

namespace LieSubalgebra

/-- The normalizer of a Lie subalgebra `H` is the set of elements of the Lie algebra whose bracket
with any element of `H` lies in `H`. It is the Lie algebra equivalent of the group-theoretic
normalizer (see `subgroup.normalizer`) and is an idealizer in the sense of abstract algebra. -/
def normalizer : LieSubalgebra R L where
  Carrier := { x : L | ∀ y : L, y ∈ H → ⁅x,y⁆ ∈ H }
  zero_mem' := fun y hy => by
    rw [zero_lie y]
    exact H.zero_mem
  add_mem' := fun z₁ z₂ h₁ h₂ y hy => by
    rw [add_lie]
    exact H.add_mem (h₁ y hy) (h₂ y hy)
  smul_mem' := fun t y hy z hz => by
    rw [smul_lie]
    exact H.smul_mem t (hy z hz)
  lie_mem' := fun z₁ z₂ h₁ h₂ y hy => by
    rw [lie_lie]
    exact H.sub_mem (h₁ _ (h₂ y hy)) (h₂ _ (h₁ y hy))

theorem mem_normalizer_iff (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅x,y⁆ ∈ H :=
  Iff.rfl

theorem mem_normalizer_iff' (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅y,x⁆ ∈ H :=
  forall₂_congrₓ fun y hy => by
    rw [← lie_skew, neg_mem_iff]

theorem le_normalizer : H ≤ H.normalizer := fun x hx => show ∀ y : L, y ∈ H → ⁅x,y⁆ ∈ H from fun y => H.lie_mem hx

variable {H}

theorem lie_mem_sup_of_mem_normalizer {x y z : L} (hx : x ∈ H.normalizer) (hy : y ∈ (R∙x)⊔↑H) (hz : z ∈ (R∙x)⊔↑H) :
    ⁅y,z⁆ ∈ (R∙x)⊔↑H := by
  rw [Submodule.mem_sup] at hy hz
  obtain ⟨u₁, hu₁, v, hv : v ∈ H, rfl⟩ := hy
  obtain ⟨u₂, hu₂, w, hw : w ∈ H, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := submodule.mem_span_singleton.mp hu₁
  obtain ⟨s, rfl⟩ := submodule.mem_span_singleton.mp hu₂
  apply Submodule.mem_sup_right
  simp only [LieSubalgebra.mem_coe_submodule, smul_lie, add_lie, zero_addₓ, lie_add, smul_zero, lie_smul, lie_self]
  refine' H.add_mem (H.smul_mem s _) (H.add_mem (H.smul_mem t _) (H.lie_mem hv hw))
  exacts[(H.mem_normalizer_iff' x).mp hx v hv, (H.mem_normalizer_iff x).mp hx w hw]

/-- A Lie subalgebra is an ideal of its normalizer. -/
theorem ideal_in_normalizer : ∀ {x y : L}, x ∈ H.normalizer → y ∈ H → ⁅x,y⁆ ∈ H := fun x y h => h y

/-- A Lie subalgebra `H` is an ideal of any Lie subalgebra `K` containing `H` and contained in the
normalizer of `H`. -/
theorem exists_nested_lie_ideal_of_le_normalizer {K : LieSubalgebra R L} (h₁ : H ≤ K) (h₂ : K ≤ H.normalizer) :
    ∃ I : LieIdeal R K, (I : LieSubalgebra R K) = ofLe h₁ := by
  rw [exists_nested_lie_ideal_coe_eq_iff]
  exact fun x y hx hy => ideal_in_normalizer (h₂ hx) hy

/-- The normalizer of a Lie subalgebra `H` is the maximal Lie subalgebra in which `H` is a Lie
ideal. -/
theorem le_normalizer_of_ideal {N : LieSubalgebra R L} (h : ∀ x y : L, x ∈ N → y ∈ H → ⁅x,y⁆ ∈ H) : N ≤ H.normalizer :=
  fun x hx y => h x y hx

variable (H)

theorem normalizer_eq_self_iff : H.normalizer = H ↔ (LieModule.maxTrivSubmodule R H <| L ⧸ H.toLieSubmodule) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  refine' ⟨fun h => _, fun h => le_antisymmₓ (fun x hx => _) H.le_normalizer⟩
  · rintro ⟨x⟩ hx
    suffices x ∈ H by
      simpa
    rw [← h, H.mem_normalizer_iff']
    intro y hy
    replace hx : ⁅_,LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
    
  · let y := LieSubmodule.Quotient.mk' H.to_lie_submodule x
    have hy : y ∈ LieModule.maxTrivSubmodule R H (L ⧸ H.to_lie_submodule) := by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero, coe_bracket_of_module, Submodule.coe_mk,
        mem_to_lie_submodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa using h y hy
    

/-- A Cartan subalgebra is a nilpotent, self-normalizing subalgebra. -/
class IsCartanSubalgebra : Prop where
  nilpotent : LieAlgebra.IsNilpotent R H
  self_normalizing : H.normalizer = H

end LieSubalgebra

@[simp]
theorem LieIdeal.normalizer_eq_top {R : Type u} {L : Type v} [CommRingₓ R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) : (I : LieSubalgebra R L).normalizer = ⊤ := by
  ext x
  simpa only [LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_trueₓ] using fun y hy => I.lie_mem hy

open LieIdeal

/-- A nilpotent Lie algebra is its own Cartan subalgebra. -/
instance LieAlgebra.top_is_cartan_subalgebra_of_nilpotent [LieAlgebra.IsNilpotent R L] :
    LieSubalgebra.IsCartanSubalgebra (⊤ : LieSubalgebra R L) where
  nilpotent := inferInstance
  self_normalizing := by
    rw [← top_coe_lie_subalgebra, normalizer_eq_top, top_coe_lie_subalgebra]

