/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.pi
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.Cauchy
import Mathbin.Topology.UniformSpace.Separation

/-!
# Indexed product of uniform spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


noncomputable section

open uniformity Topology

section

open Filter UniformSpace

universe u

variable {ι : Type _} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)]

include U

#print Pi.uniformSpace /-
instance Pi.uniformSpace : UniformSpace (∀ i, α i) :=
  UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (fun a : ∀ i, α i => a i) (U i)).toCore
      Pi.topologicalSpace <|
    Eq.symm toTopologicalSpace_infᵢ
#align Pi.uniform_space Pi.uniformSpace
-/

/- warning: Pi.uniformity -> Pi.uniformity is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} (α : ι -> Type.{u1}) [U : forall (i : ι), UniformSpace.{u1} (α i)], Eq.{succ (max u2 u1)} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))) (uniformity.{max u2 u1} (forall (i : ι), α i) (Pi.uniformSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => U i))) (infᵢ.{max u2 u1, succ u2} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))) (ConditionallyCompleteLattice.toHasInf.{max u2 u1} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))) (Filter.completeLattice.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))))) ι (fun (i : ι) => Filter.comap.{max u2 u1, u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i)) (Prod.{u1, u1} (α i) (α i)) (fun (a : Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i)) => Prod.mk.{u1, u1} (α i) (α i) (Prod.fst.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i) a i) (Prod.snd.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i) a i)) (uniformity.{u1} (α i) (U i))))
but is expected to have type
  forall {ι : Type.{u1}} (α : ι -> Type.{u2}) [U : forall (i : ι), UniformSpace.{u2} (α i)], Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))) (uniformity.{max u2 u1} (forall (i : ι), α i) (Pi.uniformSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => U i))) (infᵢ.{max u2 u1, succ u1} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))) (Filter.instCompleteLatticeFilter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i))))) ι (fun (i : ι) => Filter.comap.{max u2 u1, u2} (Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i)) (Prod.{u2, u2} (α i) (α i)) (fun (a : Prod.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i)) => Prod.mk.{u2, u2} (α i) (α i) (Prod.fst.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i) a i) (Prod.snd.{max u2 u1, max u2 u1} (forall (i : ι), α i) (forall (i : ι), α i) a i)) (uniformity.{u2} (α i) (U i))))
Case conversion may be inaccurate. Consider using '#align Pi.uniformity Pi.uniformityₓ'. -/
theorem Pi.uniformity : 𝓤 (∀ i, α i) = ⨅ i : ι, (Filter.comap fun a => (a.1 i, a.2 i)) <| 𝓤 (α i) :=
  infᵢ_uniformity
#align Pi.uniformity Pi.uniformity

variable {α}

/- warning: uniform_continuous_pi -> uniformContinuous_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [U : forall (i : ι), UniformSpace.{u1} (α i)] {β : Type.{u3}} [_inst_1 : UniformSpace.{u3} β] {f : β -> (forall (i : ι), α i)}, Iff (UniformContinuous.{u3, max u2 u1} β (forall (i : ι), α i) _inst_1 (Pi.uniformSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => U i)) f) (forall (i : ι), UniformContinuous.{u3, u1} β (α i) _inst_1 (U i) (fun (x : β) => f x i))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u3}} [U : forall (i : ι), UniformSpace.{u3} (α i)] {β : Type.{u2}} [_inst_1 : UniformSpace.{u2} β] {f : β -> (forall (i : ι), α i)}, Iff (UniformContinuous.{u2, max u3 u1} β (forall (i : ι), α i) _inst_1 (Pi.uniformSpace.{u3, u1} ι (fun (i : ι) => α i) (fun (i : ι) => U i)) f) (forall (i : ι), UniformContinuous.{u2, u3} β (α i) _inst_1 (U i) (fun (x : β) => f x i))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_pi uniformContinuous_piₓ'. -/
theorem uniformContinuous_pi {β : Type _} [UniformSpace β] {f : β → ∀ i, α i} :
    UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i := by
  simp only [UniformContinuous, Pi.uniformity, tendsto_infi, tendsto_comap_iff]
#align uniform_continuous_pi uniformContinuous_pi

variable (α)

/- warning: Pi.uniform_continuous_proj -> Pi.uniformContinuous_proj is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} (α : ι -> Type.{u1}) [U : forall (i : ι), UniformSpace.{u1} (α i)] (i : ι), UniformContinuous.{max u2 u1, u1} (forall (i : ι), α i) (α i) (Pi.uniformSpace.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => U i)) (U i) (fun (a : forall (i : ι), α i) => a i)
but is expected to have type
  forall {ι : Type.{u1}} (α : ι -> Type.{u2}) [U : forall (i : ι), UniformSpace.{u2} (α i)] (i : ι), UniformContinuous.{max u2 u1, u2} (forall (i : ι), α i) (α i) (Pi.uniformSpace.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => U i)) (U i) (fun (a : forall (i : ι), α i) => a i)
Case conversion may be inaccurate. Consider using '#align Pi.uniform_continuous_proj Pi.uniformContinuous_projₓ'. -/
theorem Pi.uniformContinuous_proj (i : ι) : UniformContinuous fun a : ∀ i : ι, α i => a i :=
  uniformContinuous_pi.1 uniformContinuous_id i
#align Pi.uniform_continuous_proj Pi.uniformContinuous_proj

#print Pi.complete /-
instance Pi.complete [∀ i, CompleteSpace (α i)] : CompleteSpace (∀ i, α i) :=
  ⟨by
    intro f hf
    haveI := hf.1
    have : ∀ i, ∃ x : α i, Filter.map (fun a : ∀ i, α i => a i) f ≤ 𝓝 x :=
      by
      intro i
      have key : Cauchy (map (fun a : ∀ i : ι, α i => a i) f) :=
        hf.map (Pi.uniformContinuous_proj α i)
      exact cauchy_iff_exists_le_nhds.1 key
    choose x hx using this
    use x
    rwa [nhds_pi, le_pi]⟩
#align Pi.complete Pi.complete
-/

#print Pi.separated /-
instance Pi.separated [∀ i, SeparatedSpace (α i)] : SeparatedSpace (∀ i, α i) :=
  separated_def.2 fun x y H => by
    ext i
    apply eq_of_separated_of_uniform_continuous (Pi.uniformContinuous_proj α i)
    apply H
#align Pi.separated Pi.separated
-/

end

