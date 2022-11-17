/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Topology.Algebra.Module.CharacterSpace
import Mathbin.Analysis.NormedSpace.WeakDual
import Mathbin.Analysis.NormedSpace.Spectrum

/-!
# Normed algebras

This file contains basic facts about normed algebras.

## Main results

* We show that the character space of a normed algebra is compact using the Banach-Alaoglu theorem.

## TODO

* Show compactness for topological vector spaces; this requires the TVS version of Banach-Alaoglu.

## Tags

normed algebra, character space, continuous functional calculus

-/


variable {𝕜 : Type _} {A : Type _}

namespace WeakDual

namespace CharacterSpace

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

theorem norm_le_norm_one (φ : characterSpace 𝕜 A) : ∥toNormedDual (φ : WeakDual 𝕜 A)∥ ≤ ∥(1 : A)∥ :=
  ContinuousLinearMap.op_norm_le_bound _ (norm_nonneg (1 : A)) $ fun a =>
    mul_comm ∥a∥ ∥(1 : A)∥ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ a)
#align weak_dual.character_space.norm_le_norm_one WeakDual.characterSpace.norm_le_norm_one

instance [ProperSpace 𝕜] : CompactSpace (characterSpace 𝕜 A) := by
  rw [← is_compact_iff_compact_space]
  have h : character_space 𝕜 A ⊆ to_normed_dual ⁻¹' Metric.closedBall 0 ∥(1 : A)∥ := by
    intro φ hφ
    rw [Set.mem_preimage, mem_closed_ball_zero_iff]
    exact (norm_le_norm_one ⟨φ, ⟨hφ.1, hφ.2⟩⟩ : _)
  exact is_compact_of_is_closed_subset (is_compact_closed_ball 𝕜 0 _) character_space.is_closed h

end CharacterSpace

end WeakDual

