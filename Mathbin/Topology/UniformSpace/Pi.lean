/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.pi
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.Cauchy
import Mathbin.Topology.UniformSpace.Separation

/-!
# Indexed product of uniform spaces
-/


noncomputable section

open uniformity TopologicalSpace

section

open Filter UniformSpace

universe u

variable {ι : Type _} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)]

include U

instance PiCat.uniformSpace : UniformSpace (∀ i, α i) :=
  UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (fun a : ∀ i, α i => a i) (U i)).toCore
      PiCat.topologicalSpace <|
    Eq.symm to_topological_space_infi
#align Pi.uniform_space PiCat.uniformSpace

theorem PiCat.uniformity :
    𝓤 (∀ i, α i) = ⨅ i : ι, (Filter.comap fun a => (a.1 i, a.2 i)) <| 𝓤 (α i) :=
  infi_uniformity
#align Pi.uniformity PiCat.uniformity

variable {α}

theorem uniform_continuous_pi {β : Type _} [UniformSpace β] {f : β → ∀ i, α i} :
    UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i := by
  simp only [UniformContinuous, PiCat.uniformity, tendsto_infi, tendsto_comap_iff]
#align uniform_continuous_pi uniform_continuous_pi

variable (α)

theorem PiCat.uniform_continuous_proj (i : ι) : UniformContinuous fun a : ∀ i : ι, α i => a i :=
  uniform_continuous_pi.1 uniform_continuous_id i
#align Pi.uniform_continuous_proj PiCat.uniform_continuous_proj

instance PiCat.complete [∀ i, CompleteSpace (α i)] : CompleteSpace (∀ i, α i) :=
  ⟨by
    intro f hf
    haveI := hf.1
    have : ∀ i, ∃ x : α i, Filter.map (fun a : ∀ i, α i => a i) f ≤ 𝓝 x :=
      by
      intro i
      have key : Cauchy (map (fun a : ∀ i : ι, α i => a i) f) :=
        hf.map (PiCat.uniform_continuous_proj α i)
      exact cauchy_iff_exists_le_nhds.1 key
    choose x hx using this
    use x
    rwa [nhds_pi, le_pi]⟩
#align Pi.complete PiCat.complete

instance PiCat.separated [∀ i, SeparatedSpace (α i)] : SeparatedSpace (∀ i, α i) :=
  separated_def.2 fun x y H => by
    ext i
    apply eq_of_separated_of_uniform_continuous (PiCat.uniform_continuous_proj α i)
    apply H
#align Pi.separated PiCat.separated

end

