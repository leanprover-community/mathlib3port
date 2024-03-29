/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Analysis.Complex.UpperHalfPlane.Basic
import Analysis.Convex.Contractible
import Analysis.Convex.Normed
import Analysis.Convex.Complex
import Analysis.Complex.ReImTopology
import Topology.Homotopy.Contractible

#align_import analysis.complex.upper_half_plane.topology from "leanprover-community/mathlib"@"9240e8be927a0955b9a82c6c85ef499ee3a626b8"

/-!
# Topology on the upper half plane

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we introduce a `topological_space` structure on the upper half plane and provide
various instances.
-/


noncomputable section

open Set Filter Function TopologicalSpace Complex

open scoped Filter Topology UpperHalfPlane

namespace UpperHalfPlane

instance : TopologicalSpace ℍ :=
  Subtype.topologicalSpace

#print UpperHalfPlane.openEmbedding_coe /-
theorem openEmbedding_coe : OpenEmbedding (coe : ℍ → ℂ) :=
  IsOpen.openEmbedding_subtype_val <| isOpen_lt continuous_const Complex.continuous_im
#align upper_half_plane.open_embedding_coe UpperHalfPlane.openEmbedding_coe
-/

#print UpperHalfPlane.embedding_coe /-
theorem embedding_coe : Embedding (coe : ℍ → ℂ) :=
  embedding_subtype_val
#align upper_half_plane.embedding_coe UpperHalfPlane.embedding_coe
-/

#print UpperHalfPlane.continuous_coe /-
theorem continuous_coe : Continuous (coe : ℍ → ℂ) :=
  embedding_coe.Continuous
#align upper_half_plane.continuous_coe UpperHalfPlane.continuous_coe
-/

#print UpperHalfPlane.continuous_re /-
theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe
#align upper_half_plane.continuous_re UpperHalfPlane.continuous_re
-/

#print UpperHalfPlane.continuous_im /-
theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe
#align upper_half_plane.continuous_im UpperHalfPlane.continuous_im
-/

instance : SecondCountableTopology ℍ :=
  TopologicalSpace.Subtype.secondCountableTopology _ _

instance : T3Space ℍ :=
  Subtype.t3Space

instance : NormalSpace ℍ :=
  NormalSpace.of_regularSpace_secondCountableTopology ℍ

instance : ContractibleSpace ℍ :=
  (convex_halfspace_im_gt 0).ContractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

instance : LocPathConnectedSpace ℍ :=
  locPathConnected_of_isOpen <| isOpen_lt continuous_const Complex.continuous_im

instance : NoncompactSpace ℍ := by
  refine' ⟨fun h => _⟩
  have : IsCompact (Complex.im ⁻¹' Ioi 0) := isCompact_iff_isCompact_univ.2 h
  replace := this.is_closed.closure_eq
  rw [closure_preimage_im, closure_Ioi, Set.ext_iff] at this
  exact absurd ((this 0).1 left_mem_Ici) (lt_irrefl _)

instance : LocallyCompactSpace ℍ :=
  openEmbedding_coe.LocallyCompactSpace

end UpperHalfPlane

