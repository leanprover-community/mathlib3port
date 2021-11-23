import Mathbin.Topology.Algebra.FilterBasis 
import Mathbin.Topology.Algebra.UniformGroup

/-!
# Uniform properties of neighborhood bases in topological algebra

This files contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/


open_locale uniformity Filter

open Filter

namespace AddGroupFilterBasis

variable{G : Type _}[AddCommGroupₓ G](B : AddGroupFilterBasis G)

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
protected def UniformSpace : UniformSpace G :=
  @TopologicalAddGroup.toUniformSpace G _ B.topology B.is_topological_add_group

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
protected theorem UniformAddGroup : @UniformAddGroup G B.uniform_space _ :=
  @topological_add_group_is_uniform G _ B.topology B.is_topological_add_group

-- error in Topology.Algebra.UniformFilterBasis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cauchy_iff
{F : filter G} : «expr ↔ »(@cauchy G B.uniform_space F, «expr ∧ »(F.ne_bot, ∀
  U «expr ∈ » B, «expr∃ , »((M «expr ∈ » F), ∀ x y «expr ∈ » M, «expr ∈ »(«expr - »(y, x), U)))) :=
begin
  letI [] [] [":=", expr B.uniform_space],
  haveI [] [] [":=", expr B.uniform_add_group],
  suffices [] [":", expr «expr ↔ »(«expr ≤ »(«expr ×ᶠ »(F, F), expr𝓤() G), ∀
    U «expr ∈ » B, «expr∃ , »((M «expr ∈ » F), ∀ x y «expr ∈ » M, «expr ∈ »(«expr - »(y, x), U)))],
  by split; rintros ["⟨", ident h', ",", ident h, "⟩"]; refine [expr ⟨h', _⟩]; [rwa ["<-", expr this] [], rwa [expr this] []],
  rw ["[", expr uniformity_eq_comap_nhds_zero G, ",", "<-", expr map_le_iff_le_comap, "]"] [],
  change [expr «expr ↔ »(tendsto _ _ _, _)] [] [],
  simp [] [] [] ["[", expr (basis_sets F).prod_self.tendsto_iff B.nhds_zero_has_basis, "]"] [] []
end

end AddGroupFilterBasis

