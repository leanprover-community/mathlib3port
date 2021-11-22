import Mathbin.Topology.UniformSpace.Cauchy 
import Mathbin.Topology.UniformSpace.Separation 
import Mathbin.Topology.DenseEmbedding

/-!
# Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/


open Filter

open_locale TopologicalSpace Filter

variable{α : Type _}

theorem IsComplete.is_closed [UniformSpace α] [SeparatedSpace α] {s : Set α} (h : IsComplete s) : IsClosed s :=
  is_closed_iff_cluster_pt.2$
    fun a ha =>
      by 
        let f := 𝓝[s] a 
        have  : Cauchy f := cauchy_nhds.mono' ha inf_le_left 
        rcases h f this inf_le_right with ⟨y, ys, fy⟩
        rwa [(tendsto_nhds_unique' ha inf_le_left fy : a = y)]

namespace DenseInducing

open Filter

variable[TopologicalSpace α]{β : Type _}[TopologicalSpace β]

variable{γ : Type _}[UniformSpace γ][CompleteSpace γ][SeparatedSpace γ]

theorem continuous_extend_of_cauchy {e : α → β} {f : α → γ} (de : DenseInducing e)
  (h : ∀ b : β, Cauchy (map f (comap e$ 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend$ fun b => CompleteSpace.complete (h b)

end DenseInducing

