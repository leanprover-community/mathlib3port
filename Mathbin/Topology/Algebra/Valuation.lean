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

noncomputable theory

universe u

/-- A valued ring is a ring that comes equipped with a distinguished valuation.-/
class Valued(R : Type u)[Ringₓ R] where 
  Γ₀ : Type u
  [grp : LinearOrderedCommGroupWithZero Γ₀]
  V : Valuation R Γ₀

attribute [instance] Valued.grp

namespace Valued

variable{R : Type _}[Ringₓ R][Valued R]

-- error in Topology.Algebra.Valuation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The basis of open subgroups for the topology on a valued ring.-/
theorem subgroups_basis : ring_subgroups_basis (λ γ : units (Γ₀ R), valued.v.lt_add_subgroup γ) :=
{ inter := begin
    rintros [ident γ₀, ident γ₁],
    use [expr min γ₀ γ₁],
    simp [] [] [] ["[", expr valuation.lt_add_subgroup, "]"] [] []; tauto []
  end,
  mul := begin
    rintros [ident γ],
    cases [expr exists_square_le γ] ["with", ident γ₀, ident h],
    use [expr γ₀],
    rintro ["-", "⟨", ident r, ",", ident s, ",", ident r_in, ",", ident s_in, ",", ident rfl, "⟩"],
    calc
      «expr = »(v «expr * »(r, s), «expr * »(v r, v s)) : valuation.map_mul _ _ _
      «expr < »(..., «expr * »(γ₀, γ₀)) : mul_lt_mul₀ r_in s_in
      «expr ≤ »(..., γ) : by exact_mod_cast [expr h]
  end,
  left_mul := begin
    rintros [ident x, ident γ],
    rcases [expr group_with_zero.eq_zero_or_unit (v x), "with", ident Hx, "|", "⟨", ident γx, ",", ident Hx, "⟩"],
    { use [expr 1],
      rintros [ident y, "(", ident y_in, ":", expr «expr < »(v y, 1), ")"],
      change [expr «expr < »(v «expr * »(x, y), _)] [] [],
      rw ["[", expr valuation.map_mul, ",", expr Hx, ",", expr zero_mul, "]"] [],
      exact [expr units.zero_lt γ] },
    { simp [] [] ["only"] ["[", expr image_subset_iff, ",", expr set_of_subset_set_of, ",", expr preimage_set_of_eq, ",", expr valuation.map_mul, "]"] [] [],
      use [expr «expr * »(«expr ⁻¹»(γx), γ)],
      rintros [ident y, "(", ident vy_lt, ":", expr «expr < »(v y, «expr↑ »(«expr * »(«expr ⁻¹»(γx), γ))), ")"],
      change [expr «expr < »(v «expr * »(x, y), γ)] [] [],
      rw ["[", expr valuation.map_mul, ",", expr Hx, ",", expr mul_comm, "]"] [],
      rw ["[", expr units.coe_mul, ",", expr mul_comm, "]"] ["at", ident vy_lt],
      simpa [] [] [] [] [] ["using", expr mul_inv_lt_of_lt_mul₀ vy_lt] }
  end,
  right_mul := begin
    rintros [ident x, ident γ],
    rcases [expr group_with_zero.eq_zero_or_unit (v x), "with", ident Hx, "|", "⟨", ident γx, ",", ident Hx, "⟩"],
    { use [expr 1],
      rintros [ident y, "(", ident y_in, ":", expr «expr < »(v y, 1), ")"],
      change [expr «expr < »(v «expr * »(y, x), _)] [] [],
      rw ["[", expr valuation.map_mul, ",", expr Hx, ",", expr mul_zero, "]"] [],
      exact [expr units.zero_lt γ] },
    { use [expr «expr * »(«expr ⁻¹»(γx), γ)],
      rintros [ident y, "(", ident vy_lt, ":", expr «expr < »(v y, «expr↑ »(«expr * »(«expr ⁻¹»(γx), γ))), ")"],
      change [expr «expr < »(v «expr * »(y, x), γ)] [] [],
      rw ["[", expr valuation.map_mul, ",", expr Hx, "]"] [],
      rw ["[", expr units.coe_mul, ",", expr mul_comm, "]"] ["at", ident vy_lt],
      simpa [] [] [] [] [] ["using", expr mul_inv_lt_of_lt_mul₀ vy_lt] }
  end }

instance (priority := 100) : TopologicalSpace R :=
  subgroups_basis.topology

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : Units (Valued.Γ₀ R), { y | v (y - x) < γ } ⊆ s :=
  by 
    simpa [(subgroups_basis.has_basis_nhds x).mem_iff]

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔ ∃ γ : Units (Γ₀ R), { x | v x < (γ : Γ₀ R) } ⊆ s :=
  by 
    simp [Valued.mem_nhds, sub_zero]

theorem loc_const {x : R} (h : v x ≠ 0) : { y:R | v y = v x } ∈ 𝓝 x :=
  by 
    rw [Valued.mem_nhds]
    rcases units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩
    use γ 
    rw [hx]
    intro y y_in 
    exact Valuation.map_eq_of_sub_lt _ y_in

/-- The uniform structure on a valued ring.-/
instance (priority := 100)UniformSpace : UniformSpace R :=
  TopologicalAddGroup.toUniformSpace R

/-- A valued ring is a uniform additive group.-/
instance (priority := 100)UniformAddGroup : UniformAddGroup R :=
  topological_add_group_is_uniform

theorem cauchy_iff {F : Filter R} :
  Cauchy F ↔ F.ne_bot ∧ ∀ (γ : Units (Γ₀ R)), ∃ (M : _)(_ : M ∈ F), ∀ x y, x ∈ M → y ∈ M → v (y - x) < γ :=
  by 
    rw [AddGroupFilterBasis.cauchy_iff]
    apply and_congr Iff.rfl 
    simpRw [subgroups_basis.mem_add_group_filter_basis_iff]
    split 
    ·
      intro h γ 
      exact h _ (subgroups_basis.mem_add_group_filter_basis _)
    ·
      rintro h - ⟨γ, rfl⟩
      exact h γ

end Valued

