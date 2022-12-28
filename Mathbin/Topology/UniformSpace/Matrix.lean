/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Heather Macbeth

! This file was ported from Lean 3 source module topology.uniform_space.matrix
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.Pi
import Mathbin.Data.Matrix.Basic

/-!
# Uniform space structure on matrices
-/


open uniformity TopologicalSpace

variable (m n 𝕜 : Type _) [UniformSpace 𝕜]

namespace Matrix

instance : UniformSpace (Matrix m n 𝕜) :=
  (by infer_instance : UniformSpace (m → n → 𝕜))

theorem uniformity :
    𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a.1 i j, a.2 i j) :=
  by
  erw [PiCat.uniformity, PiCat.uniformity]
  simp_rw [Filter.comap_infi, Filter.comap_comap]
  rfl
#align matrix.uniformity Matrix.uniformity

theorem uniform_continuous {β : Type _} [UniformSpace β] {f : β → Matrix m n 𝕜} :
    UniformContinuous f ↔ ∀ i j, UniformContinuous fun x => f x i j := by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_infi, Filter.tendsto_comap_iff]
#align matrix.uniform_continuous Matrix.uniform_continuous

instance [CompleteSpace 𝕜] : CompleteSpace (Matrix m n 𝕜) :=
  (by infer_instance : CompleteSpace (m → n → 𝕜))

instance [SeparatedSpace 𝕜] : SeparatedSpace (Matrix m n 𝕜) :=
  (by infer_instance : SeparatedSpace (m → n → 𝕜))

end Matrix

