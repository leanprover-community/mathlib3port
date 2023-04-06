/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Heather Macbeth

! This file was ported from Lean 3 source module topology.uniform_space.matrix
! leanprover-community/mathlib commit d64d67d000b974f0d86a2be7918cf800be6271c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.Pi
import Mathbin.Data.Matrix.Basic

/-!
# Uniform space structure on matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open uniformity Topology

variable (m n 𝕜 : Type _) [UniformSpace 𝕜]

namespace Matrix

instance : UniformSpace (Matrix m n 𝕜) :=
  (by infer_instance : UniformSpace (m → n → 𝕜))

/- warning: matrix.uniformity -> Matrix.uniformity is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u1}) (n : Type.{u2}) (𝕜 : Type.{u3}) [_inst_1 : UniformSpace.{u3} 𝕜], Eq.{succ (max u1 u2 u3)} (Filter.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))) (uniformity.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.uniformSpace.{u1, u2, u3} m n 𝕜 _inst_1)) (infᵢ.{max u1 u2 u3, succ u1} (Filter.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))) (ConditionallyCompleteLattice.toHasInf.{max u1 u2 u3} (Filter.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2 u3} (Filter.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))) (Filter.completeLattice.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))))) m (fun (i : m) => infᵢ.{max u1 u2 u3, succ u2} (Filter.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))) (ConditionallyCompleteLattice.toHasInf.{max u1 u2 u3} (Filter.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2 u3} (Filter.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))) (Filter.completeLattice.{max u1 u2 u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜))))) n (fun (j : n) => Filter.comap.{max u1 u2 u3, u3} (Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜)) (Prod.{u3, u3} 𝕜 𝕜) (fun (a : Prod.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜)) => Prod.mk.{u3, u3} 𝕜 𝕜 (Prod.fst.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜) a i j) (Prod.snd.{max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n 𝕜) (Matrix.{u1, u2, u3} m n 𝕜) a i j)) (uniformity.{u3} 𝕜 _inst_1))))
but is expected to have type
  forall (m : Type.{u3}) (n : Type.{u2}) (𝕜 : Type.{u1}) [_inst_1 : UniformSpace.{u1} 𝕜], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Filter.{max (max u1 u2) u3} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))) (uniformity.{max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.instUniformSpaceMatrix.{u3, u2, u1} m n 𝕜 _inst_1)) (infᵢ.{max (max u3 u2) u1, succ u3} (Filter.{max (max u3 u2) u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))) (ConditionallyCompleteLattice.toInfSet.{max (max u3 u2) u1} (Filter.{max (max u3 u2) u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))) (CompleteLattice.toConditionallyCompleteLattice.{max (max u3 u2) u1} (Filter.{max (max u3 u2) u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))) (Filter.instCompleteLatticeFilter.{max (max u3 u2) u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))))) m (fun (i : m) => infᵢ.{max (max u3 u2) u1, succ u2} (Filter.{max (max u3 u2) u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))) (ConditionallyCompleteLattice.toInfSet.{max (max u3 u2) u1} (Filter.{max (max u3 u2) u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))) (CompleteLattice.toConditionallyCompleteLattice.{max (max u3 u2) u1} (Filter.{max (max u3 u2) u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))) (Filter.instCompleteLatticeFilter.{max (max u3 u2) u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜))))) n (fun (j : n) => Filter.comap.{max (max u3 u2) u1, u1} (Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜)) (Prod.{u1, u1} 𝕜 𝕜) (fun (a : Prod.{max (max u1 u2) u3, max (max u1 u2) u3} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜)) => Prod.mk.{u1, u1} 𝕜 𝕜 (Prod.fst.{max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜) a i j) (Prod.snd.{max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n 𝕜) (Matrix.{u3, u2, u1} m n 𝕜) a i j)) (uniformity.{u1} 𝕜 _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.uniformity Matrix.uniformityₓ'. -/
theorem uniformity :
    𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a.1 i j, a.2 i j) :=
  by
  erw [Pi.uniformity, Pi.uniformity]
  simp_rw [Filter.comap_infᵢ, Filter.comap_comap]
  rfl
#align matrix.uniformity Matrix.uniformity

/- warning: matrix.uniform_continuous -> Matrix.uniformContinuous is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u1}) (n : Type.{u2}) (𝕜 : Type.{u3}) [_inst_1 : UniformSpace.{u3} 𝕜] {β : Type.{u4}} [_inst_2 : UniformSpace.{u4} β] {f : β -> (Matrix.{u1, u2, u3} m n 𝕜)}, Iff (UniformContinuous.{u4, max u1 u2 u3} β (Matrix.{u1, u2, u3} m n 𝕜) _inst_2 (Matrix.uniformSpace.{u1, u2, u3} m n 𝕜 _inst_1) f) (forall (i : m) (j : n), UniformContinuous.{u4, u3} β 𝕜 _inst_2 _inst_1 (fun (x : β) => f x i j))
but is expected to have type
  forall (m : Type.{u3}) (n : Type.{u2}) (𝕜 : Type.{u1}) [_inst_1 : UniformSpace.{u1} 𝕜] {β : Type.{u4}} [_inst_2 : UniformSpace.{u4} β] {f : β -> (Matrix.{u3, u2, u1} m n 𝕜)}, Iff (UniformContinuous.{u4, max (max u3 u2) u1} β (Matrix.{u3, u2, u1} m n 𝕜) _inst_2 (Matrix.instUniformSpaceMatrix.{u3, u2, u1} m n 𝕜 _inst_1) f) (forall (i : m) (j : n), UniformContinuous.{u4, u1} β 𝕜 _inst_2 _inst_1 (fun (x : β) => f x i j))
Case conversion may be inaccurate. Consider using '#align matrix.uniform_continuous Matrix.uniformContinuousₓ'. -/
theorem uniformContinuous {β : Type _} [UniformSpace β] {f : β → Matrix m n 𝕜} :
    UniformContinuous f ↔ ∀ i j, UniformContinuous fun x => f x i j := by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_infᵢ, Filter.tendsto_comap_iff]
#align matrix.uniform_continuous Matrix.uniformContinuous

instance [CompleteSpace 𝕜] : CompleteSpace (Matrix m n 𝕜) :=
  (by infer_instance : CompleteSpace (m → n → 𝕜))

instance [SeparatedSpace 𝕜] : SeparatedSpace (Matrix m n 𝕜) :=
  (by infer_instance : SeparatedSpace (m → n → 𝕜))

end Matrix

