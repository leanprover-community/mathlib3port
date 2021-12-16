import Mathbin.Topology.Algebra.Nonarchimedean.Bases 
import Mathbin.Topology.Algebra.UniformFilterBasis 
import Mathbin.RingTheory.Valuation.Basic

/-!
# The topology on a valued ring

In this file, we define the non archimedean topology induced by a valuation on a ring.
The main definition is a `valued` type class which equips a ring with a valuation taking
values in a group with zero (living in the same universe). Other instances are then deduced from
this.
-/


open_locale Classical TopologicalSpace

open Set Valuation

noncomputable section 

universe u

/-- A valued ring is a ring that comes equipped with a distinguished valuation.-/
class Valued (R : Type u) [Ringₓ R] where 
  Γ₀ : Type u
  [grp : LinearOrderedCommGroupWithZero Γ₀]
  V : Valuation R Γ₀

attribute [instance] Valued.grp

namespace Valued

variable {R : Type _} [Ringₓ R] [Valued R]

/-- The basis of open subgroups for the topology on a valued ring.-/
theorem subgroups_basis : RingSubgroupsBasis fun γ : Units (Γ₀ R) => Valued.v.ltAddSubgroup γ :=
  { inter :=
      by 
        rintro γ₀ γ₁ 
        use min γ₀ γ₁ 
        simp [Valuation.ltAddSubgroup] <;> tauto,
    mul :=
      by 
        rintro γ 
        cases' exists_square_le γ with γ₀ h 
        use γ₀ 
        rintro - ⟨r, s, r_in, s_in, rfl⟩
        calc v (r*s) = v r*v s := Valuation.map_mul _ _ _ _ < γ₀*γ₀ := mul_lt_mul₀ r_in s_in _ ≤ γ :=
          by 
            exactModCast h,
    leftMul :=
      by 
        rintro x γ 
        rcases GroupWithZeroₓ.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
        ·
          use 1
          rintro y (y_in : v y < 1)
          change v (x*y) < _ 
          rw [Valuation.map_mul, Hx, zero_mul]
          exact Units.zero_lt γ
        ·
          simp only [image_subset_iff, set_of_subset_set_of, preimage_set_of_eq, Valuation.map_mul]
          use γx⁻¹*γ 
          rintro y (vy_lt : v y < ↑γx⁻¹*γ)
          change v (x*y) < γ 
          rw [Valuation.map_mul, Hx, mul_commₓ]
          rw [Units.coe_mul, mul_commₓ] at vy_lt 
          simpa using mul_inv_lt_of_lt_mul₀ vy_lt,
    rightMul :=
      by 
        rintro x γ 
        rcases GroupWithZeroₓ.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
        ·
          use 1
          rintro y (y_in : v y < 1)
          change v (y*x) < _ 
          rw [Valuation.map_mul, Hx, mul_zero]
          exact Units.zero_lt γ
        ·
          use γx⁻¹*γ 
          rintro y (vy_lt : v y < ↑γx⁻¹*γ)
          change v (y*x) < γ 
          rw [Valuation.map_mul, Hx]
          rw [Units.coe_mul, mul_commₓ] at vy_lt 
          simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

instance (priority := 100) : TopologicalSpace R :=
  subgroups_basis.topology

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  mem_nhds
  { s : Set R } { x : R } : s ∈ 𝓝 x ↔ ∃ γ : Units Valued.Γ₀ R , { y | v y - x < γ } ⊆ s
  := by simpa [ subgroups_basis.has_basis_nhds x . mem_iff ]

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  mem_nhds_zero
  { s : Set R } : s ∈ 𝓝 ( 0 : R ) ↔ ∃ γ : Units Γ₀ R , { x | v x < ( γ : Γ₀ R ) } ⊆ s
  := by simp [ Valued.mem_nhds , sub_zero ]

theorem loc_const {x : R} (h : v x ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x :=
  by 
    rw [Valued.mem_nhds]
    rcases units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩
    use γ 
    rw [hx]
    intro y y_in 
    exact Valuation.map_eq_of_sub_lt _ y_in

/-- The uniform structure on a valued ring.-/
instance (priority := 100) UniformSpace : UniformSpace R :=
  TopologicalAddGroup.toUniformSpace R

/-- A valued ring is a uniform additive group.-/
instance (priority := 100) UniformAddGroup : UniformAddGroup R :=
  topological_add_group_is_uniform

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (M «expr ∈ » F)
theorem cauchy_iff {F : Filter R} :
  Cauchy F ↔ F.ne_bot ∧ ∀ γ : Units (Γ₀ R), ∃ (M : _)(_ : M ∈ F), ∀ x y, x ∈ M → y ∈ M → v (y - x) < γ :=
  by 
    rw [AddGroupFilterBasis.cauchy_iff]
    apply and_congr Iff.rfl 
    simpRw [subgroups_basis.mem_add_group_filter_basis_iff]
    constructor
    ·
      intro h γ 
      exact h _ (subgroups_basis.mem_add_group_filter_basis _)
    ·
      rintro h - ⟨γ, rfl⟩
      exact h γ

end Valued

