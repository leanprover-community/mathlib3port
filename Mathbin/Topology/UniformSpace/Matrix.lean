/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Heather Macbeth
-/
import Mathbin.Topology.UniformSpace.Pi
import Mathbin.Data.Matrix.Basic

#align_import topology.uniform_space.matrix from "leanprover-community/mathlib"@"d64d67d000b974f0d86a2be7918cf800be6271c8"

/-!
# Uniform space structure on matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open scoped uniformity Topology

variable (m n 𝕜 : Type _) [UniformSpace 𝕜]

namespace Matrix

instance : UniformSpace (Matrix m n 𝕜) :=
  (by infer_instance : UniformSpace (m → n → 𝕜))

#print Matrix.uniformity /-
theorem uniformity :
    𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a.1 i j, a.2 i j) :=
  by
  erw [Pi.uniformity, Pi.uniformity]
  simp_rw [Filter.comap_iInf, Filter.comap_comap]
  rfl
#align matrix.uniformity Matrix.uniformity
-/

#print Matrix.uniformContinuous /-
theorem uniformContinuous {β : Type _} [UniformSpace β] {f : β → Matrix m n 𝕜} :
    UniformContinuous f ↔ ∀ i j, UniformContinuous fun x => f x i j := by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_iInf, Filter.tendsto_comap_iff]
#align matrix.uniform_continuous Matrix.uniformContinuous
-/

instance [CompleteSpace 𝕜] : CompleteSpace (Matrix m n 𝕜) :=
  (by infer_instance : CompleteSpace (m → n → 𝕜))

instance [SeparatedSpace 𝕜] : SeparatedSpace (Matrix m n 𝕜) :=
  (by infer_instance : SeparatedSpace (m → n → 𝕜))

end Matrix

