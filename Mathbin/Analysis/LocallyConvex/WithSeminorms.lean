/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker

! This file was ported from Lean 3 source module analysis.locally_convex.with_seminorms
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Seminorm
import Mathbin.Analysis.LocallyConvex.Bounded
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Topology.Algebra.Module.LocallyConvex

/-!
# Topology induced by a family of seminorms

## Main definitions

* `seminorm_family.basis_sets`: The set of open seminorm balls for a family of seminorms.
* `seminorm_family.module_filter_basis`: A module filter basis formed by the open balls.
* `seminorm.is_bounded`: A linear map `f : E →ₗ[𝕜] F` is bounded iff every seminorm in `F` can be
bounded by a finite number of seminorms in `E`.

## Main statements

* `with_seminorms.to_locally_convex_space`: A space equipped with a family of seminorms is locally
convex.
* `with_seminorms.first_countable`: A space is first countable if it's topology is induced by a
countable family of seminorms.

## Continuity of semilinear maps

If `E` and `F` are topological vector space with the topology induced by a family of seminorms, then
we have a direct method to prove that a linear map is continuous:
* `seminorm.continuous_from_bounded`: A bounded linear map `f : E →ₗ[𝕜] F` is continuous.

If the topology of a space `E` is induced by a family of seminorms, then we can characterize von
Neumann boundedness in terms of that seminorm family. Together with
`linear_map.continuous_of_locally_bounded` this gives general criterion for continuity.

* `with_seminorms.is_vonN_bounded_iff_finset_seminorm_bounded`
* `with_seminorms.is_vonN_bounded_iff_seminorm_bounded`
* `with_seminorms.image_is_vonN_bounded_iff_finset_seminorm_bounded`
* `with_seminorms.image_is_vonN_bounded_iff_seminorm_bounded`

## Tags

seminorm, locally convex
-/


open NormedField Set Seminorm TopologicalSpace

open BigOperators Nnreal Pointwise TopologicalSpace

variable {𝕜 𝕜₂ E F G ι ι' : Type _}

section FilterBasis

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable (𝕜 E ι)

/-- An abbreviation for indexed families of seminorms. This is mainly to allow for dot-notation. -/
abbrev SeminormFamily :=
  ι → Seminorm 𝕜 E
#align seminorm_family SeminormFamily

variable {𝕜 E ι}

namespace SeminormFamily

/-- The sets of a filter basis for the neighborhood filter of 0. -/
def basisSets (p : SeminormFamily 𝕜 E ι) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (hr : 0 < r), singleton <| ball (s.sup p) (0 : E) r
#align seminorm_family.basis_sets SeminormFamily.basisSets

variable (p : SeminormFamily 𝕜 E ι)

theorem basis_sets_iff {U : Set E} :
    U ∈ p.basis_sets ↔ ∃ (i : Finset ι)(r : _)(hr : 0 < r), U = ball (i.sup p) 0 r := by
  simp only [basis_sets, mem_Union, mem_singleton_iff]
#align seminorm_family.basis_sets_iff SeminormFamily.basis_sets_iff

theorem basis_sets_mem (i : Finset ι) {r : ℝ} (hr : 0 < r) : (i.sup p).ball 0 r ∈ p.basis_sets :=
  (basis_sets_iff _).mpr ⟨i, _, hr, rfl⟩
#align seminorm_family.basis_sets_mem SeminormFamily.basis_sets_mem

theorem basis_sets_singleton_mem (i : ι) {r : ℝ} (hr : 0 < r) : (p i).ball 0 r ∈ p.basis_sets :=
  (basis_sets_iff _).mpr ⟨{i}, _, hr, by rw [Finset.sup_singleton]⟩
#align seminorm_family.basis_sets_singleton_mem SeminormFamily.basis_sets_singleton_mem

theorem basis_sets_nonempty [Nonempty ι] : p.basis_sets.Nonempty :=
  by
  let i := Classical.arbitrary ι
  refine' set.nonempty_def.mpr ⟨(p i).ball 0 1, _⟩
  exact p.basis_sets_singleton_mem i zero_lt_one
#align seminorm_family.basis_sets_nonempty SeminormFamily.basis_sets_nonempty

theorem basis_sets_intersect (U V : Set E) (hU : U ∈ p.basis_sets) (hV : V ∈ p.basis_sets) :
    ∃ (z : Set E)(H : z ∈ p.basis_sets), z ⊆ U ∩ V := by
  classical
    rcases p.basis_sets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
    rcases p.basis_sets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
    use ((s ∪ t).sup p).ball 0 (min r₁ r₂)
    refine' ⟨p.basis_sets_mem (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), _⟩
    rw [hU, hV, ball_finset_sup_eq_Inter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩),
      ball_finset_sup_eq_Inter _ _ _ hr₁, ball_finset_sup_eq_Inter _ _ _ hr₂]
    exact
      Set.subset_inter
        (Set.interᵢ₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_left _ _ hi, ball_mono <| min_le_left _ _⟩)
        (Set.interᵢ₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_right _ _ hi, ball_mono <| min_le_right _ _⟩)
#align seminorm_family.basis_sets_intersect SeminormFamily.basis_sets_intersect

theorem basis_sets_zero (U) (hU : U ∈ p.basis_sets) : (0 : E) ∈ U :=
  by
  rcases p.basis_sets_iff.mp hU with ⟨ι', r, hr, hU⟩
  rw [hU, mem_ball_zero, map_zero]
  exact hr
#align seminorm_family.basis_sets_zero SeminormFamily.basis_sets_zero

theorem basis_sets_add (U) (hU : U ∈ p.basis_sets) :
    ∃ (V : Set E)(H : V ∈ p.basis_sets), V + V ⊆ U :=
  by
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine' ⟨p.basis_sets_mem s (div_pos hr zero_lt_two), _⟩
  refine' Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) _
  rw [hU, add_zero, add_halves']
#align seminorm_family.basis_sets_add SeminormFamily.basis_sets_add

theorem basis_sets_neg (U) (hU' : U ∈ p.basis_sets) :
    ∃ (V : Set E)(H : V ∈ p.basis_sets), V ⊆ (fun x : E => -x) ⁻¹' U :=
  by
  rcases p.basis_sets_iff.mp hU' with ⟨s, r, hr, hU⟩
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩
#align seminorm_family.basis_sets_neg SeminormFamily.basis_sets_neg

/-- The `add_group_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
protected def addGroupFilterBasis [Nonempty ι] : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm p.basis_sets p.basis_sets_nonempty p.basis_sets_intersect
    p.basis_sets_zero p.basis_sets_add p.basis_sets_neg
#align seminorm_family.add_group_filter_basis SeminormFamily.addGroupFilterBasis

theorem basis_sets_smul_right (v : E) (U : Set E) (hU : U ∈ p.basis_sets) :
    ∀ᶠ x : 𝕜 in 𝓝 0, x • v ∈ U :=
  by
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU, Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, map_smul_eq_mul]
  by_cases h : 0 < (s.sup p) v
  · simp_rw [(lt_div_iff h).symm]
    rw [← _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
  simp_rw [le_antisymm (not_lt.mp h) (map_nonneg _ v), mul_zero, hr]
  exact IsOpen.mem_nhds is_open_univ (mem_univ 0)
#align seminorm_family.basis_sets_smul_right SeminormFamily.basis_sets_smul_right

variable [Nonempty ι]

theorem basis_sets_smul (U) (hU : U ∈ p.basis_sets) :
    ∃ (V : Set 𝕜)(H : V ∈ 𝓝 (0 : 𝕜))(W : Set E)(H : W ∈ p.AddGroupFilterBasis.sets), V • W ⊆ U :=
  by
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  refine' ⟨Metric.ball 0 r.sqrt, Metric.ball_mem_nhds 0 (real.sqrt_pos.mpr hr), _⟩
  refine' ⟨(s.sup p).ball 0 r.sqrt, p.basis_sets_mem s (real.sqrt_pos.mpr hr), _⟩
  refine' Set.Subset.trans (ball_smul_ball (s.sup p) r.sqrt r.sqrt) _
  rw [hU, Real.mul_self_sqrt (le_of_lt hr)]
#align seminorm_family.basis_sets_smul SeminormFamily.basis_sets_smul

theorem basis_sets_smul_left (x : 𝕜) (U : Set E) (hU : U ∈ p.basis_sets) :
    ∃ (V : Set E)(H : V ∈ p.AddGroupFilterBasis.sets), V ⊆ (fun y : E => x • y) ⁻¹' U :=
  by
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]
  by_cases h : x ≠ 0
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / ‖x‖)
    exact ⟨p.basis_sets_mem s (div_pos hr (norm_pos_iff.mpr h)), subset.rfl⟩
  refine' ⟨(s.sup p).ball 0 r, p.basis_sets_mem s hr, _⟩
  simp only [not_ne_iff.mp h, subset_def, mem_ball_zero, hr, mem_univ, map_zero, imp_true_iff,
    preimage_const_of_mem, zero_smul]
#align seminorm_family.basis_sets_smul_left SeminormFamily.basis_sets_smul_left

/-- The `module_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
protected def moduleFilterBasis : ModuleFilterBasis 𝕜 E
    where
  toAddGroupFilterBasis := p.AddGroupFilterBasis
  smul' := p.basis_sets_smul
  smul_left' := p.basis_sets_smul_left
  smul_right' := p.basis_sets_smul_right
#align seminorm_family.module_filter_basis SeminormFamily.moduleFilterBasis

theorem filter_eq_infi (p : SeminormFamily 𝕜 E ι) :
    p.ModuleFilterBasis.toFilterBasis.filter = ⨅ i, (𝓝 0).comap (p i) :=
  by
  refine' le_antisymm (le_infᵢ fun i => _) _
  · rw [p.module_filter_basis.to_filter_basis.has_basis.le_basis_iff
        (metric.nhds_basis_ball.comap _)]
    intro ε hε
    refine' ⟨(p i).ball 0 ε, _, _⟩
    · rw [← (Finset.sup_singleton : _ = p i)]
      exact p.basis_sets_mem {i} hε
    · rw [id, (p i).ball_zero_eq_preimage_ball]
  · rw [p.module_filter_basis.to_filter_basis.has_basis.ge_iff]
    rintro U (hU : U ∈ p.basis_sets)
    rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, rfl⟩
    rw [id, Seminorm.ball_finset_sup_eq_Inter _ _ _ hr, s.Inter_mem_sets]
    exact fun i hi =>
      Filter.mem_infi_of_mem i
        ⟨Metric.ball 0 r, Metric.ball_mem_nhds 0 hr,
          Eq.subset (p i).ball_zero_eq_preimage_ball.symm⟩
#align seminorm_family.filter_eq_infi SeminormFamily.filter_eq_infi

end SeminormFamily

end FilterBasis

section Bounded

namespace Seminorm

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

-- Todo: This should be phrased entirely in terms of the von Neumann bornology.
/-- The proposition that a linear map is bounded between spaces with families of seminorms. -/
def IsBounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜₂ F) (f : E →ₛₗ[σ₁₂] F) : Prop :=
  ∀ i, ∃ s : Finset ι, ∃ C : ℝ≥0, C ≠ 0 ∧ (q i).comp f ≤ C • s.sup p
#align seminorm.is_bounded Seminorm.IsBounded

theorem is_bounded_const (ι' : Type _) [Nonempty ι'] {p : ι → Seminorm 𝕜 E} {q : Seminorm 𝕜₂ F}
    (f : E →ₛₗ[σ₁₂] F) :
    IsBounded p (fun _ : ι' => q) f ↔ ∃ (s : Finset ι)(C : ℝ≥0), C ≠ 0 ∧ q.comp f ≤ C • s.sup p :=
  by simp only [is_bounded, forall_const]
#align seminorm.is_bounded_const Seminorm.is_bounded_const

theorem const_is_bounded (ι : Type _) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F}
    (f : E →ₛₗ[σ₁₂] F) :
    IsBounded (fun _ : ι => p) q f ↔ ∀ i, ∃ C : ℝ≥0, C ≠ 0 ∧ (q i).comp f ≤ C • p :=
  by
  constructor <;> intro h i
  · rcases h i with ⟨s, C, hC, h⟩
    exact ⟨C, hC, le_trans h (smul_le_smul (Finset.sup_le fun _ _ => le_rfl) le_rfl)⟩
  use {Classical.arbitrary ι}
  simp only [h, Finset.sup_singleton]
#align seminorm.const_is_bounded Seminorm.const_is_bounded

theorem is_bounded_sup {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F} {f : E →ₛₗ[σ₁₂] F}
    (hf : IsBounded p q f) (s' : Finset ι') :
    ∃ (C : ℝ≥0)(s : Finset ι), 0 < C ∧ (s'.sup q).comp f ≤ C • s.sup p := by
  classical
    obtain rfl | hs' := s'.eq_empty_or_nonempty
    · exact ⟨1, ∅, zero_lt_one, by simp [Seminorm.bot_eq_zero]⟩
    choose fₛ fC hf using hf
    use s'.card • s'.sup fC, Finset.bUnion s' fₛ
    constructor
    · refine' nsmul_pos _ (ne_of_gt (Finset.Nonempty.card_pos hs'))
      cases' Finset.Nonempty.bex hs' with j hj
      exact lt_of_lt_of_le (zero_lt_iff.mpr (And.left (hf j))) (Finset.le_sup hj)
    have hs : ∀ i : ι', i ∈ s' → (q i).comp f ≤ s'.sup fC • (Finset.bUnion s' fₛ).sup p :=
      by
      intro i hi
      refine' le_trans (And.right (hf i)) (smul_le_smul _ (Finset.le_sup hi))
      exact Finset.sup_mono (Finset.subset_bUnion_of_mem fₛ hi)
    refine' le_trans (comp_mono f (finset_sup_le_sum q s')) _
    simp_rw [← pullback_apply, AddMonoidHom.map_sum, pullback_apply]
    refine' le_trans (Finset.sum_le_sum hs) _
    rw [Finset.sum_const, smul_assoc]
    exact le_rfl
#align seminorm.is_bounded_sup Seminorm.is_bounded_sup

end Seminorm

end Bounded

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι]

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
structure WithSeminorms (p : SeminormFamily 𝕜 E ι) [t : TopologicalSpace E] : Prop where
  topology_eq_with_seminorms : t = p.ModuleFilterBasis.topology
#align with_seminorms WithSeminorms

theorem WithSeminorms.with_seminorms_eq {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) : t = p.ModuleFilterBasis.topology :=
  hp.1
#align with_seminorms.with_seminorms_eq WithSeminorms.with_seminorms_eq

variable [TopologicalSpace E]

variable {p : SeminormFamily 𝕜 E ι}

theorem WithSeminorms.topological_add_group (hp : WithSeminorms p) : TopologicalAddGroup E :=
  by
  rw [hp.with_seminorms_eq]
  exact AddGroupFilterBasis.is_topological_add_group _
#align with_seminorms.topological_add_group WithSeminorms.topological_add_group

theorem WithSeminorms.has_basis (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basis_sets) id :=
  by
  rw [congr_fun (congr_arg (@nhds E) hp.1) 0]
  exact AddGroupFilterBasis.nhds_zero_has_basis _
#align with_seminorms.has_basis WithSeminorms.has_basis

theorem WithSeminorms.has_basis_zero_ball (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun sr : Finset ι × ℝ => 0 < sr.2) fun sr => (sr.1.sup p).ball 0 sr.2 :=
  by
  refine' ⟨fun V => _⟩
  simp only [hp.has_basis.mem_iff, SeminormFamily.basis_sets_iff, Prod.exists]
  constructor
  · rintro ⟨-, ⟨s, r, hr, rfl⟩, hV⟩
    exact ⟨s, r, hr, hV⟩
  · rintro ⟨s, r, hr, hV⟩
    exact ⟨_, ⟨s, r, hr, rfl⟩, hV⟩
#align with_seminorms.has_basis_zero_ball WithSeminorms.has_basis_zero_ball

theorem WithSeminorms.has_basis_ball (hp : WithSeminorms p) {x : E} :
    (𝓝 (x : E)).HasBasis (fun sr : Finset ι × ℝ => 0 < sr.2) fun sr => (sr.1.sup p).ball x sr.2 :=
  by
  haveI : TopologicalAddGroup E := hp.topological_add_group
  rw [← map_add_left_nhds_zero]
  convert hp.has_basis_zero_ball.map ((· + ·) x)
  ext sr : 1
  have : (sr.fst.sup p).ball (x +ᵥ 0) sr.snd = x +ᵥ (sr.fst.sup p).ball 0 sr.snd :=
    Eq.symm (Seminorm.vadd_ball (sr.fst.sup p))
  rwa [vadd_eq_add, add_zero] at this
#align with_seminorms.has_basis_ball WithSeminorms.has_basis_ball

/-- The `x`-neighbourhoods of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around `x`.-/
theorem WithSeminorms.mem_nhds_iff (hp : WithSeminorms p) (x : E) (U : Set E) :
    U ∈ nhds x ↔ ∃ s : Finset ι, ∃ r > 0, (s.sup p).ball x r ⊆ U := by
  rw [hp.has_basis_ball.mem_iff, Prod.exists]
#align with_seminorms.mem_nhds_iff WithSeminorms.mem_nhds_iff

/-- The open sets of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around all of their points.-/
theorem WithSeminorms.is_open_iff_mem_balls (hp : WithSeminorms p) (U : Set E) :
    IsOpen U ↔ ∀ x ∈ U, ∃ s : Finset ι, ∃ r > 0, (s.sup p).ball x r ⊆ U := by
  simp_rw [← WithSeminorms.mem_nhds_iff hp _ U, is_open_iff_mem_nhds]
#align with_seminorms.is_open_iff_mem_balls WithSeminorms.is_open_iff_mem_balls

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ≠ » 0) -/
/- Note that through the following lemmas, one also immediately has that separating families
of seminorms induce T₂ and T₃ topologies by `topological_add_group.t2_space`
and `topological_add_group.t3_space` -/
/-- A separating family of seminorms induces a T₁ topology. -/
theorem WithSeminorms.t1_of_separating (hp : WithSeminorms p)
    (h : ∀ (x) (_ : x ≠ 0), ∃ i, p i x ≠ 0) : T1Space E :=
  by
  haveI := hp.topological_add_group
  refine' TopologicalAddGroup.t1_space _ _
  rw [← is_open_compl_iff, hp.is_open_iff_mem_balls]
  rintro x (hx : x ≠ 0)
  cases' h x hx with i pi_nonzero
  refine' ⟨{i}, p i x, by positivity, subset_compl_singleton_iff.mpr _⟩
  rw [Finset.sup_singleton, mem_ball, zero_sub, map_neg_eq_map, not_lt]
#align with_seminorms.t1_of_separating WithSeminorms.t1_of_separating

/-- A family of seminorms inducing a T₁ topology is separating. -/
theorem WithSeminorms.separating_of_t1 [T1Space E] (hp : WithSeminorms p) (x : E) (hx : x ≠ 0) :
    ∃ i, p i x ≠ 0 := by
  have := ((t1_space_tfae E).out 0 9).mp inferInstance
  by_contra' h
  refine' hx (this _)
  rw [hp.has_basis_zero_ball.specializes_iff]
  rintro ⟨s, r⟩ (hr : 0 < r)
  simp only [ball_finset_sup_eq_Inter _ _ _ hr, mem_Inter₂, mem_ball_zero, h, hr, forall_true_iff]
#align with_seminorms.separating_of_t1 WithSeminorms.separating_of_t1

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ≠ » 0) -/
/-- A family of seminorms is separating iff it induces a T₁ topology. -/
theorem WithSeminorms.separating_iff_t1 (hp : WithSeminorms p) :
    (∀ (x) (_ : x ≠ 0), ∃ i, p i x ≠ 0) ↔ T1Space E :=
  by
  refine' ⟨WithSeminorms.t1_of_separating hp, _⟩
  intro
  exact WithSeminorms.separating_of_t1 hp
#align with_seminorms.separating_iff_t1 WithSeminorms.separating_iff_t1

end Topology

section TopologicalAddGroup

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [t : TopologicalSpace E] [TopologicalAddGroup E]

variable [Nonempty ι]

include t

theorem SeminormFamily.withSeminormsOfNhds (p : SeminormFamily 𝕜 E ι)
    (h : 𝓝 (0 : E) = p.ModuleFilterBasis.toFilterBasis.filter) : WithSeminorms p :=
  by
  refine'
    ⟨TopologicalAddGroup.ext inferInstance p.add_group_filter_basis.is_topological_add_group _⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h
#align seminorm_family.with_seminorms_of_nhds SeminormFamily.withSeminormsOfNhds

theorem SeminormFamily.withSeminormsOfHasBasis (p : SeminormFamily 𝕜 E ι)
    (h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basis_sets) id) : WithSeminorms p :=
  p.withSeminormsOfNhds <|
    Filter.HasBasis.eq_of_same_basis h p.AddGroupFilterBasis.toFilterBasis.HasBasis
#align seminorm_family.with_seminorms_of_has_basis SeminormFamily.withSeminormsOfHasBasis

theorem SeminormFamily.with_seminorms_iff_nhds_eq_infi (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔ (𝓝 0 : Filter E) = ⨅ i, (𝓝 0).comap (p i) :=
  by
  rw [← p.filter_eq_infi]
  refine' ⟨fun h => _, p.with_seminorms_of_nhds⟩
  rw [h.topology_eq_with_seminorms]
  exact AddGroupFilterBasis.nhds_zero_eq _
#align
  seminorm_family.with_seminorms_iff_nhds_eq_infi SeminormFamily.with_seminorms_iff_nhds_eq_infi

theorem WithSeminorms.continuous_seminorm [Module ℝ E] [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E]
    [HasContinuousConstSmul ℝ E] {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (i : ι) :
    Continuous (p i) := by
  refine' Seminorm.continuous _
  rw [p.with_seminorms_iff_nhds_eq_infi.mp hp, ball_zero_eq_preimage_ball]
  exact Filter.mem_infi_of_mem i (Filter.preimage_mem_comap <| Metric.ball_mem_nhds _ one_pos)
#align with_seminorms.continuous_seminorm WithSeminorms.continuous_seminorm

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr = »(_, «expr⨅ , »((i), _))]] -/
/-- The topology induced by a family of seminorms is exactly the infimum of the ones induced by
each seminorm individually. We express this as a characterization of `with_seminorms p`. -/
theorem SeminormFamily.with_seminorms_iff_topological_space_eq_infi (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔
      t =
        ⨅ i, (p i).toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace :=
  by
  rw [p.with_seminorms_iff_nhds_eq_infi,
    TopologicalAddGroup.ext_iff inferInstance (topological_add_group_infi fun i => inferInstance),
    nhds_infi]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr = »(_, «expr⨅ , »((i), _))]]"
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup
  all_goals infer_instance
#align
  seminorm_family.with_seminorms_iff_topological_space_eq_infi SeminormFamily.with_seminorms_iff_topological_space_eq_infi

omit t

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr = »(_, «expr⨅ , »((i), _))]] -/
/-- The uniform structure induced by a family of seminorms is exactly the infimum of the ones
induced by each seminorm individually. We express this as a characterization of
`with_seminorms p`. -/
theorem SeminormFamily.with_seminorms_iff_uniform_space_eq_infi [u : UniformSpace E]
    [UniformAddGroup E] (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔ u = ⨅ i, (p i).toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace :=
  by
  rw [p.with_seminorms_iff_nhds_eq_infi,
    UniformAddGroup.ext_iff inferInstance (uniform_add_group_infi fun i => inferInstance),
    to_topological_space_infi, nhds_infi]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr = »(_, «expr⨅ , »((i), _))]]"
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup
  all_goals infer_instance
#align
  seminorm_family.with_seminorms_iff_uniform_space_eq_infi SeminormFamily.with_seminorms_iff_uniform_space_eq_infi

end TopologicalAddGroup

section NormedSpace

/-- The topology of a `normed_space 𝕜 E` is induced by the seminorm `norm_seminorm 𝕜 E`. -/
theorem normWithSeminorms (𝕜 E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    WithSeminorms fun _ : Fin 1 => normSeminorm 𝕜 E :=
  by
  let p : SeminormFamily 𝕜 E (Fin 1) := fun _ => normSeminorm 𝕜 E
  refine'
    ⟨seminormed_add_comm_group.to_topological_add_group.ext
        p.add_group_filter_basis.is_topological_add_group _⟩
  refine' Filter.HasBasis.eq_of_same_basis Metric.nhds_basis_ball _
  rw [← ball_norm_seminorm 𝕜 E]
  refine'
    Filter.HasBasis.to_has_basis p.add_group_filter_basis.nhds_zero_has_basis _ fun r hr =>
      ⟨(normSeminorm 𝕜 E).ball 0 r, p.basis_sets_singleton_mem 0 hr, rfl.subset⟩
  rintro U (hU : U ∈ p.basis_sets)
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  use r, hr
  rw [hU, id.def]
  by_cases h : s.nonempty
  · rw [Finset.sup_const h]
  rw [finset.not_nonempty_iff_eq_empty.mp h, Finset.sup_empty, ball_bot _ hr]
  exact Set.subset_univ _
#align norm_with_seminorms normWithSeminorms

end NormedSpace

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι]

variable {p : SeminormFamily 𝕜 E ι}

variable [TopologicalSpace E]

theorem WithSeminorms.is_vonN_bounded_iff_finset_seminorm_bounded {s : Set E}
    (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ I : Finset ι, ∃ (r : _)(hr : 0 < r), ∀ x ∈ s, I.sup p x < r :=
  by
  rw [hp.has_basis.is_vonN_bounded_basis_iff]
  constructor
  · intro h I
    simp only [id.def] at h
    specialize h ((I.sup p).ball 0 1) (p.basis_sets_mem I zero_lt_one)
    rcases h with ⟨r, hr, h⟩
    cases' NormedField.exists_lt_norm 𝕜 r with a ha
    specialize h a (le_of_lt ha)
    rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hr.trans ha), mul_one] at h
    refine' ⟨‖a‖, lt_trans hr ha, _⟩
    intro x hx
    specialize h hx
    exact (Finset.sup I p).mem_ball_zero.mp h
  intro h s' hs'
  rcases p.basis_sets_iff.mp hs' with ⟨I, r, hr, hs'⟩
  rw [id.def, hs']
  rcases h I with ⟨r', hr', h'⟩
  simp_rw [← (I.sup p).mem_ball_zero] at h'
  refine' Absorbs.mono_right _ h'
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr
#align
  with_seminorms.is_vonN_bounded_iff_finset_seminorm_bounded WithSeminorms.is_vonN_bounded_iff_finset_seminorm_bounded

theorem WithSeminorms.image_is_vonN_bounded_iff_finset_seminorm_bounded (f : G → E) {s : Set G}
    (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔
      ∀ I : Finset ι, ∃ (r : _)(hr : 0 < r), ∀ x ∈ s, I.sup p (f x) < r :=
  by simp_rw [hp.is_vonN_bounded_iff_finset_seminorm_bounded, Set.ball_image_iff]
#align
  with_seminorms.image_is_vonN_bounded_iff_finset_seminorm_bounded WithSeminorms.image_is_vonN_bounded_iff_finset_seminorm_bounded

theorem WithSeminorms.is_vonN_bounded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ i : ι, ∃ (r : _)(hr : 0 < r), ∀ x ∈ s, p i x < r :=
  by
  rw [hp.is_vonN_bounded_iff_finset_seminorm_bounded]
  constructor
  · intro hI i
    convert hI {i}
    rw [Finset.sup_singleton]
  intro hi I
  by_cases hI : I.nonempty
  · choose r hr h using hi
    have h' : 0 < I.sup' hI r := by
      rcases hI.bex with ⟨i, hi⟩
      exact lt_of_lt_of_le (hr i) (Finset.le_sup' r hi)
    refine' ⟨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => _⟩
    refine' lt_of_lt_of_le (h i x hx) _
    simp only [Finset.le_sup'_iff, exists_prop]
    exact ⟨i, hi, (Eq.refl _).le⟩
  simp only [finset.not_nonempty_iff_eq_empty.mp hI, Finset.sup_empty, coe_bot, Pi.zero_apply,
    exists_prop]
  exact ⟨1, zero_lt_one, fun _ _ => zero_lt_one⟩
#align
  with_seminorms.is_vonN_bounded_iff_seminorm_bounded WithSeminorms.is_vonN_bounded_iff_seminorm_bounded

theorem WithSeminorms.image_is_vonN_bounded_iff_seminorm_bounded (f : G → E) {s : Set G}
    (hp : WithSeminorms p) :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔ ∀ i : ι, ∃ (r : _)(hr : 0 < r), ∀ x ∈ s, p i (f x) < r :=
  by simp_rw [hp.is_vonN_bounded_iff_seminorm_bounded, Set.ball_image_iff]
#align
  with_seminorms.image_is_vonN_bounded_iff_seminorm_bounded WithSeminorms.image_is_vonN_bounded_iff_seminorm_bounded

end NontriviallyNormedField

section ContinuousBounded

namespace Seminorm

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

variable [Nonempty ι] [Nonempty ι']

theorem continuous_of_continuous_comp {q : SeminormFamily 𝕜₂ F ι'} [TopologicalSpace E]
    [TopologicalAddGroup E] [TopologicalSpace F] [TopologicalAddGroup F] (hq : WithSeminorms q)
    (f : E →ₛₗ[σ₁₂] F) (hf : ∀ i, Continuous ((q i).comp f)) : Continuous f :=
  by
  refine' continuous_of_continuous_at_zero f _
  simp_rw [ContinuousAt, f.map_zero, q.with_seminorms_iff_nhds_eq_infi.mp hq, Filter.tendsto_infi,
    Filter.tendsto_comap_iff]
  intro i
  convert (hf i).ContinuousAt
  exact (map_zero _).symm
#align seminorm.continuous_of_continuous_comp Seminorm.continuous_of_continuous_comp

theorem continuous_iff_continuous_comp [NormedAlgebra ℝ 𝕜₂] [Module ℝ F] [IsScalarTower ℝ 𝕜₂ F]
    {q : SeminormFamily 𝕜₂ F ι'} [TopologicalSpace E] [TopologicalAddGroup E] [TopologicalSpace F]
    [TopologicalAddGroup F] [HasContinuousConstSmul ℝ F] (hq : WithSeminorms q) (f : E →ₛₗ[σ₁₂] F) :
    Continuous f ↔ ∀ i, Continuous ((q i).comp f) :=
  ⟨fun h i => Continuous.comp (hq.continuous_seminorm i) h, continuous_of_continuous_comp hq f⟩
#align seminorm.continuous_iff_continuous_comp Seminorm.continuous_iff_continuous_comp

theorem continuous_from_bounded {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜₂ F ι'}
    [TopologicalSpace E] [TopologicalAddGroup E] (hp : WithSeminorms p) [TopologicalSpace F]
    [TopologicalAddGroup F] (hq : WithSeminorms q) (f : E →ₛₗ[σ₁₂] F)
    (hf : Seminorm.IsBounded p q f) : Continuous f :=
  by
  refine' continuous_of_continuous_comp hq _ fun i => Seminorm.continuous_of_continuous_at_zero _
  rw [Metric.continuous_at_iff', map_zero]
  intro r hr
  rcases hf i with ⟨s₁, C, hC, hf⟩
  have hC' : 0 < C := hC.bot_lt
  rw [hp.has_basis.eventually_iff]
  refine' ⟨(s₁.sup p).ball 0 (r / C), p.basis_sets_mem _ (by positivity), _⟩
  simp_rw [← Metric.mem_ball, ← mem_preimage, ← ball_zero_eq_preimage_ball]
  refine' subset.trans _ (ball_antitone hf)
  rw [ball_smul (s₁.sup p) hC']
  rfl
#align seminorm.continuous_from_bounded Seminorm.continuous_from_bounded

theorem cont_with_seminorms_normed_space (F) [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]
    [UniformSpace E] [UniformAddGroup E] {p : ι → Seminorm 𝕜 E} (hp : WithSeminorms p)
    (f : E →ₛₗ[σ₁₂] F)
    (hf : ∃ (s : Finset ι)(C : ℝ≥0), C ≠ 0 ∧ (normSeminorm 𝕜₂ F).comp f ≤ C • s.sup p) :
    Continuous f := by
  rw [← Seminorm.is_bounded_const (Fin 1)] at hf
  exact continuous_from_bounded hp (normWithSeminorms 𝕜₂ F) f hf
#align seminorm.cont_with_seminorms_normed_space Seminorm.cont_with_seminorms_normed_space

theorem cont_normed_space_to_with_seminorms (E) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [UniformSpace F] [UniformAddGroup F] {q : ι → Seminorm 𝕜₂ F} (hq : WithSeminorms q)
    (f : E →ₛₗ[σ₁₂] F) (hf : ∀ i : ι, ∃ C : ℝ≥0, C ≠ 0 ∧ (q i).comp f ≤ C • normSeminorm 𝕜 E) :
    Continuous f := by
  rw [← Seminorm.const_is_bounded (Fin 1)] at hf
  exact continuous_from_bounded (normWithSeminorms 𝕜 E) hq f hf
#align seminorm.cont_normed_space_to_with_seminorms Seminorm.cont_normed_space_to_with_seminorms

end Seminorm

end ContinuousBounded

section LocallyConvexSpace

open LocallyConvexSpace

variable [Nonempty ι] [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]

theorem WithSeminorms.toLocallyConvexSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    LocallyConvexSpace ℝ E :=
  by
  apply of_basis_zero ℝ E id fun s => s ∈ p.basis_sets
  · rw [hp.1, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.has_basis _
  · intro s hs
    change s ∈ Set.unionᵢ _ at hs
    simp_rw [Set.mem_unionᵢ, Set.mem_singleton_iff] at hs
    rcases hs with ⟨I, r, hr, rfl⟩
    exact convex_ball _ _ _
#align with_seminorms.to_locally_convex_space WithSeminorms.toLocallyConvexSpace

end LocallyConvexSpace

section NormedSpace

variable (𝕜) [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SeminormedAddCommGroup E]

/-- Not an instance since `𝕜` can't be inferred. See `normed_space.to_locally_convex_space` for a
slightly weaker instance version. -/
theorem NormedSpace.toLocallyConvexSpace' [NormedSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    LocallyConvexSpace ℝ E :=
  (normWithSeminorms 𝕜 E).toLocallyConvexSpace
#align normed_space.to_locally_convex_space' NormedSpace.toLocallyConvexSpace'

/-- See `normed_space.to_locally_convex_space'` for a slightly stronger version which is not an
instance. -/
instance NormedSpace.toLocallyConvexSpace [NormedSpace ℝ E] : LocallyConvexSpace ℝ E :=
  NormedSpace.toLocallyConvexSpace' ℝ
#align normed_space.to_locally_convex_space NormedSpace.toLocallyConvexSpace

end NormedSpace

section TopologicalConstructions

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- The family of seminorms obtained by composing each seminorm by a linear map. -/
def SeminormFamily.comp (q : SeminormFamily 𝕜₂ F ι) (f : E →ₛₗ[σ₁₂] F) : SeminormFamily 𝕜 E ι :=
  fun i => (q i).comp f
#align seminorm_family.comp SeminormFamily.comp

theorem SeminormFamily.comp_apply (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E →ₛₗ[σ₁₂] F) :
    q.comp f i = (q i).comp f :=
  rfl
#align seminorm_family.comp_apply SeminormFamily.comp_apply

theorem SeminormFamily.finset_sup_comp (q : SeminormFamily 𝕜₂ F ι) (s : Finset ι)
    (f : E →ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup (q.comp f) :=
  by
  ext x
  rw [Seminorm.comp_apply, Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  rfl
#align seminorm_family.finset_sup_comp SeminormFamily.finset_sup_comp

variable [TopologicalSpace F] [TopologicalAddGroup F]

theorem LinearMap.withSeminormsInduced [hι : Nonempty ι] {q : SeminormFamily 𝕜₂ F ι}
    (hq : WithSeminorms q) (f : E →ₛₗ[σ₁₂] F) :
    @WithSeminorms 𝕜 E ι _ _ _ _ (q.comp f) (induced f inferInstance) :=
  by
  letI : TopologicalSpace E := induced f inferInstance
  letI : TopologicalAddGroup E := topological_add_group_induced f
  rw [(q.comp f).with_seminorms_iff_nhds_eq_infi, nhds_induced, map_zero,
    q.with_seminorms_iff_nhds_eq_infi.mp hq, Filter.comap_infi]
  refine' infᵢ_congr fun i => _
  exact Filter.comap_comap
#align linear_map.with_seminorms_induced LinearMap.withSeminormsInduced

theorem Inducing.withSeminorms [hι : Nonempty ι] {q : SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q)
    [TopologicalSpace E] {f : E →ₛₗ[σ₁₂] F} (hf : Inducing f) : WithSeminorms (q.comp f) :=
  by
  rw [hf.induced]
  exact f.with_seminorms_induced hq
#align inducing.with_seminorms Inducing.withSeminorms

end TopologicalConstructions

section TopologicalProperties

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nonempty ι] [Countable ι]

variable {p : SeminormFamily 𝕜 E ι}

variable [UniformSpace E] [UniformAddGroup E]

/-- If the topology of a space is induced by a countable family of seminorms, then the topology
is first countable. -/
theorem WithSeminorms.first_countable (hp : WithSeminorms p) :
    TopologicalSpace.FirstCountableTopology E :=
  by
  have : (𝓝 (0 : E)).IsCountablyGenerated :=
    by
    rw [p.with_seminorms_iff_nhds_eq_infi.mp hp]
    exact Filter.Infi.is_countably_generated _
  haveI : (uniformity E).IsCountablyGenerated := UniformAddGroup.uniformity_countably_generated
  exact UniformSpace.first_countable_topology E
#align with_seminorms.first_countable WithSeminorms.first_countable

end TopologicalProperties

