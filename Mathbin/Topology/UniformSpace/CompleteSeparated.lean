import Mathbin.Topology.UniformSpace.Cauchy 
import Mathbin.Topology.UniformSpace.Separation 
import Mathbin.Topology.DenseEmbedding

/-!
# Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/


open Filter

open_locale TopologicalSpace Filter

variable {α : Type _}

-- error in Topology.UniformSpace.CompleteSeparated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_complete.is_closed [uniform_space α] [separated_space α] {s : set α} (h : is_complete s) : is_closed s :=
«expr $ »(is_closed_iff_cluster_pt.2, λ a ha, begin
   let [ident f] [] [":=", expr «expr𝓝[ ] »(s, a)],
   have [] [":", expr cauchy f] [":=", expr cauchy_nhds.mono' ha inf_le_left],
   rcases [expr h f this inf_le_right, "with", "⟨", ident y, ",", ident ys, ",", ident fy, "⟩"],
   rwa [expr (tendsto_nhds_unique' ha inf_le_left fy : «expr = »(a, y))] []
 end)

namespace DenseInducing

open Filter

variable [TopologicalSpace α] {β : Type _} [TopologicalSpace β]

variable {γ : Type _} [UniformSpace γ] [CompleteSpace γ] [SeparatedSpace γ]

theorem continuous_extend_of_cauchy {e : α → β} {f : α → γ} (de : DenseInducing e)
  (h : ∀ b : β, Cauchy (map f (comap e$ 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend$ fun b => CompleteSpace.complete (h b)

end DenseInducing

