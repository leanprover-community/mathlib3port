import Mathbin.LinearAlgebra.AffineSpace.AffineMap 
import Mathbin.Topology.Algebra.Group 
import Mathbin.Topology.Algebra.MulAction

/-!
# Topological properties of affine spaces and maps

For now, this contains only a few facts regarding the continuity of affine maps in the special
case when the point space and vector space are the same.

TODO: Deal with the case where the point spaces are different from the vector spaces. Note that
we do have some results in this direction under the assumption that the topologies are induced by
(semi)norms.
-/


namespace AffineMap

variable{R E F : Type _}

variable[AddCommGroupₓ E][TopologicalSpace E]

variable[AddCommGroupₓ F][TopologicalSpace F][TopologicalAddGroup F]

section Ringₓ

variable[Ringₓ R][Module R E][Module R F]

-- error in Topology.Algebra.Affine: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An affine map is continuous iff its underlying linear map is continuous. See also
`affine_map.continuous_linear_iff`. -/
theorem continuous_iff {f : «expr →ᵃ[ ] »(E, R, F)} : «expr ↔ »(continuous f, continuous f.linear) :=
begin
  split,
  { intro [ident hc],
    rw [expr decomp' f] [],
    have [] [] [":=", expr hc.sub continuous_const],
    exact [expr this] },
  { intro [ident hc],
    rw [expr decomp f] [],
    have [] [] [":=", expr hc.add continuous_const],
    exact [expr this] }
end

/-- The line map is continuous. -/
@[continuity]
theorem line_map_continuous [TopologicalSpace R] [HasContinuousSmul R F] {p v : F} :
  Continuous («expr⇑ » (line_map p v : R →ᵃ[R] F)) :=
  continuous_iff.mpr$ (continuous_id.smul continuous_const).add$ @continuous_const _ _ _ _ (0 : F)

end Ringₓ

section CommRingₓ

variable[CommRingₓ R][Module R F][TopologicalSpace R][HasContinuousSmul R F]

@[continuity]
theorem homothety_continuous (x : F) (t : R) : Continuous$ homothety x t :=
  by 
    suffices  : «expr⇑ » (homothety x t) = fun y => (t • (y - x))+x
    ·
      rw [this]
      continuity 
    ext y 
    simp [homothety_apply]

end CommRingₓ

section Field

variable[Field R][Module R F][TopologicalSpace R][HasContinuousSmul R F]

theorem homothety_is_open_map (x : F) (t : R) (ht : t ≠ 0) : IsOpenMap$ homothety x t :=
  by 
    apply IsOpenMap.of_inverse (homothety_continuous x (t⁻¹)) <;>
      intro e <;> simp [←AffineMap.comp_apply, ←homothety_mul, ht]

end Field

end AffineMap

