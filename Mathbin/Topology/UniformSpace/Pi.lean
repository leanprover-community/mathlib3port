/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Topology.UniformSpace.Cauchy
import Topology.UniformSpace.Separation

#align_import topology.uniform_space.pi from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# Indexed product of uniform spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


noncomputable section

open scoped uniformity Topology

section

open Filter UniformSpace

universe u

variable {ι : Type _} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)]

#print Pi.uniformSpace /-
instance Pi.uniformSpace : UniformSpace (∀ i, α i) :=
  UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (fun a : ∀ i, α i => a i) (U i)).toCore
      Pi.topologicalSpace <|
    Eq.symm UniformSpace.toTopologicalSpace_iInf
#align Pi.uniform_space Pi.uniformSpace
-/

#print Pi.uniformity /-
theorem Pi.uniformity : 𝓤 (∀ i, α i) = ⨅ i : ι, (Filter.comap fun a => (a.1 i, a.2 i)) <| 𝓤 (α i) :=
  iInf_uniformity
#align Pi.uniformity Pi.uniformity
-/

variable {α}

#print uniformContinuous_pi /-
theorem uniformContinuous_pi {β : Type _} [UniformSpace β] {f : β → ∀ i, α i} :
    UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i := by
  simp only [UniformContinuous, Pi.uniformity, tendsto_infi, tendsto_comap_iff]
#align uniform_continuous_pi uniformContinuous_pi
-/

variable (α)

#print Pi.uniformContinuous_proj /-
theorem Pi.uniformContinuous_proj (i : ι) : UniformContinuous fun a : ∀ i : ι, α i => a i :=
  uniformContinuous_pi.1 uniformContinuous_id i
#align Pi.uniform_continuous_proj Pi.uniformContinuous_proj
-/

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

/- warning: Pi.separated clashes with pi.t0_space -> Pi.instT0Space
Case conversion may be inaccurate. Consider using '#align Pi.separated Pi.instT0Spaceₓ'. -/
#print Pi.instT0Space /-
instance Pi.instT0Space [∀ i, T0Space (α i)] : T0Space (∀ i, α i) :=
  t0Space_iff_uniformity.2 fun x y H => by
    ext i
    apply eq_of_separated_of_uniform_continuous (Pi.uniformContinuous_proj α i)
    apply H
#align Pi.separated Pi.instT0Space
-/

end

