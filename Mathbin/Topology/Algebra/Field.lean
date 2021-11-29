import Mathbin.Topology.Algebra.Ring 
import Mathbin.Topology.Algebra.GroupWithZero

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/


namespace TopologicalRing

open TopologicalSpace Function

variable(R : Type _)[Ringₓ R]

variable[TopologicalSpace R]

/-- The induced topology on units of a topological ring.
This is not a global instance since other topologies could be relevant. Instead there is a class
`induced_units` asserting that something equivalent to this construction holds. -/
def topological_space_units : TopologicalSpace (Units R) :=
  induced (coeₓ : Units R → R) ‹_›

/-- Asserts the topology on units is the induced topology.

 Note: this is not always the correct topology.
 Another good candidate is the subspace topology of $R \times R$,
 with the units embedded via $u \mapsto (u, u^{-1})$.
 These topologies are not (propositionally) equal in general. -/
class induced_units[t : TopologicalSpace$ Units R] : Prop where 
  top_eq : t = induced (coeₓ : Units R → R) ‹_›

variable[TopologicalSpace$ Units R]

theorem units_topology_eq [induced_units R] : ‹TopologicalSpace (Units R)› = induced (coeₓ : Units R → R) ‹_› :=
  induced_units.top_eq

theorem induced_units.continuous_coe [induced_units R] : Continuous (coeₓ : Units R → R) :=
  (units_topology_eq R).symm ▸ continuous_induced_dom

theorem units_embedding [induced_units R] : Embedding (coeₓ : Units R → R) :=
  { induced := units_topology_eq R, inj := fun x y h => Units.ext h }

-- error in Topology.Algebra.Field: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance top_monoid_units [topological_ring R] [induced_units R] : has_continuous_mul (units R) :=
⟨begin
   let [ident mulR] [] [":=", expr λ p : «expr × »(R, R), «expr * »(p.1, p.2)],
   let [ident mulRx] [] [":=", expr λ p : «expr × »(units R, units R), «expr * »(p.1, p.2)],
   have [ident key] [":", expr «expr = »(«expr ∘ »(coe, mulRx), «expr ∘ »(mulR, λ p, (p.1.val, p.2.val)))] [],
   from [expr rfl],
   rw ["[", expr continuous_iff_le_induced, ",", expr units_topology_eq R, ",", expr prod_induced_induced, ",", expr induced_compose, ",", expr key, ",", "<-", expr induced_compose, "]"] [],
   apply [expr induced_mono],
   rw ["<-", expr continuous_iff_le_induced] [],
   exact [expr continuous_mul]
 end⟩

end TopologicalRing

variable(K : Type _)[DivisionRing K][TopologicalSpace K]

-- error in Topology.Algebra.Field: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class topological_division_ringextends topological_ring K : exprProp() :=
  (continuous_inv : ∀ x : K, «expr ≠ »(x, 0) → continuous_at (λ x : K, «expr ⁻¹»(x) : K → K) x)

namespace TopologicalDivisionRing

open Filter Set

/-!
In this section, we show that units of a topological division ring endowed with the
induced topology form a topological group. These are not global instances because
one could want another topology on units. To turn on this feature, use:

```lean
local attribute [instance]
topological_ring.topological_space_units topological_division_ring.units_top_group
```
-/


attribute [local instance] TopologicalRing.topologicalSpaceUnits

instance (priority := 100)induced_units : TopologicalRing.InducedUnits K :=
  ⟨rfl⟩

variable[TopologicalDivisionRing K]

-- error in Topology.Algebra.Field: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem units_top_group : topological_group (units K) :=
{ continuous_inv := begin
    have [] [":", expr «expr = »(«expr ∘ »((coe : units K → K), (λ
       x, «expr ⁻¹»(x) : units K → units K)), «expr ∘ »((λ x, «expr ⁻¹»(x) : K → K), (coe : units K → K)))] [],
    from [expr funext units.coe_inv'],
    rw [expr continuous_iff_continuous_at] [],
    intros [ident x],
    rw ["[", expr continuous_at, ",", expr nhds_induced, ",", expr nhds_induced, ",", expr tendsto_iff_comap, ",", expr comap_comm this, "]"] [],
    apply [expr comap_mono],
    rw ["[", "<-", expr tendsto_iff_comap, ",", expr units.coe_inv', "]"] [],
    exact [expr topological_division_ring.continuous_inv (x : K) x.ne_zero]
  end,
  ..topological_ring.top_monoid_units K }

attribute [local instance] units_top_group

-- error in Topology.Algebra.Field: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_units_inv : continuous (λ x : units K, («expr↑ »(«expr ⁻¹»(x)) : K)) :=
(topological_ring.induced_units.continuous_coe K).comp topological_group.continuous_inv

end TopologicalDivisionRing

section affineHomeomorph

/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/


variable{𝕜 : Type _}[Field 𝕜][TopologicalSpace 𝕜][TopologicalRing 𝕜]

/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affineHomeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 :=
  { toFun := fun x => (a*x)+b, invFun := fun y => (y - b) / a,
    left_inv :=
      fun x =>
        by 
          simp only [add_sub_cancel]
          exact mul_div_cancel_left x h,
    right_inv :=
      fun y =>
        by 
          simp [mul_div_cancel' _ h] }

end affineHomeomorph

