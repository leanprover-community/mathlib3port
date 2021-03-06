/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
import Mathbin.Analysis.Seminorm
import Mathbin.Analysis.LocallyConvex.Bounded

/-!
# Topology induced by a family of seminorms

## Main definitions

* `seminorm_family.basis_sets`: The set of open seminorm balls for a family of seminorms.
* `seminorm_family.module_filter_basis`: A module filter basis formed by the open balls.
* `seminorm.is_bounded`: A linear map `f : E ââ[ð] F` is bounded iff every seminorm in `F` can be
bounded by a finite number of seminorms in `E`.

## Main statements

* `continuous_from_bounded`: A bounded linear map `f : E ââ[ð] F` is continuous.
* `seminorm_family.to_locally_convex_space`: A space equipped with a family of seminorms is locally
convex.

## TODO

Show that for any locally convex space there exist seminorms that induce the topology.

## Tags

seminorm, locally convex
-/


open NormedField Set Seminorm TopologicalSpace

open BigOperators Nnreal Pointwise TopologicalSpace

variable {ð E F G Î¹ Î¹' : Type _}

section FilterBasis

variable [NormedField ð] [AddCommGroupâ E] [Module ð E]

variable (ð E Î¹)

/-- An abbreviation for indexed families of seminorms. This is mainly to allow for dot-notation. -/
abbrev SeminormFamily :=
  Î¹ â Seminorm ð E

variable {ð E Î¹}

namespace SeminormFamily

/-- The sets of a filter basis for the neighborhood filter of 0. -/
def BasisSets (p : SeminormFamily ð E Î¹) : Set (Set E) :=
  â (s : Finset Î¹) (r) (hr : 0 < r), singleton <| Ball (s.sup p) (0 : E) r

variable (p : SeminormFamily ð E Î¹)

theorem basis_sets_iff {U : Set E} : U â p.basis_sets â â (i : Finset Î¹)(r : _)(hr : 0 < r), U = Ball (i.sup p) 0 r :=
  by
  simp only [â basis_sets, â mem_Union, â mem_singleton_iff]

theorem basis_sets_mem (i : Finset Î¹) {r : â} (hr : 0 < r) : (i.sup p).ball 0 r â p.basis_sets :=
  (basis_sets_iff _).mpr â¨i, _, hr, rflâ©

theorem basis_sets_singleton_mem (i : Î¹) {r : â} (hr : 0 < r) : (p i).ball 0 r â p.basis_sets :=
  (basis_sets_iff _).mpr
    â¨{i}, _, hr, by
      rw [Finset.sup_singleton]â©

theorem basis_sets_nonempty [Nonempty Î¹] : p.basis_sets.Nonempty := by
  let i := Classical.arbitrary Î¹
  refine' set.nonempty_def.mpr â¨(p i).ball 0 1, _â©
  exact p.basis_sets_singleton_mem i zero_lt_one

theorem basis_sets_intersect (U V : Set E) (hU : U â p.basis_sets) (hV : V â p.basis_sets) :
    â (z : Set E)(H : z â p.basis_sets), z â U â© V := by
  classical
  rcases p.basis_sets_iff.mp hU with â¨s, râ, hrâ, hUâ©
  rcases p.basis_sets_iff.mp hV with â¨t, râ, hrâ, hVâ©
  use ((s âª t).sup p).ball 0 (min râ râ)
  refine' â¨p.basis_sets_mem (s âª t) (lt_min_iff.mpr â¨hrâ, hrââ©), _â©
  rw [hU, hV, ball_finset_sup_eq_Inter _ _ _ (lt_min_iff.mpr â¨hrâ, hrââ©), ball_finset_sup_eq_Inter _ _ _ hrâ,
    ball_finset_sup_eq_Inter _ _ _ hrâ]
  exact
    Set.subset_inter (Set.Interâ_mono' fun i hi => â¨i, Finset.subset_union_left _ _ hi, ball_mono <| min_le_leftâ _ _â©)
      (Set.Interâ_mono' fun i hi => â¨i, Finset.subset_union_right _ _ hi, ball_mono <| min_le_rightâ _ _â©)

theorem basis_sets_zero (U) (hU : U â p.basis_sets) : (0 : E) â U := by
  rcases p.basis_sets_iff.mp hU with â¨Î¹', r, hr, hUâ©
  rw [hU, mem_ball_zero, map_zero]
  exact hr

theorem basis_sets_add (U) (hU : U â p.basis_sets) : â (V : Set E)(H : V â p.basis_sets), V + V â U := by
  rcases p.basis_sets_iff.mp hU with â¨s, r, hr, hUâ©
  use (s.sup p).ball 0 (r / 2)
  refine' â¨p.basis_sets_mem s (div_pos hr zero_lt_two), _â©
  refine' Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) _
  rw [hU, add_zeroâ, add_halves']

theorem basis_sets_neg (U) (hU' : U â p.basis_sets) :
    â (V : Set E)(H : V â p.basis_sets), V â (fun x : E => -x) â»Â¹' U := by
  rcases p.basis_sets_iff.mp hU' with â¨s, r, hr, hUâ©
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero]
  exact â¨U, hU', Eq.subset hUâ©

/-- The `add_group_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
protected def addGroupFilterBasis [Nonempty Î¹] : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm p.basis_sets p.basis_sets_nonempty p.basis_sets_intersect p.basis_sets_zero p.basis_sets_add
    p.basis_sets_neg

theorem basis_sets_smul_right (v : E) (U : Set E) (hU : U â p.basis_sets) : âá¶  x : ð in ð 0, x â¢ v â U := by
  rcases p.basis_sets_iff.mp hU with â¨s, r, hr, hUâ©
  rw [hU, Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, (s.sup p).smul]
  by_cases' h : 0 < (s.sup p) v
  Â· simp_rw [(lt_div_iff h).symm]
    rw [â _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
    
  simp_rw [le_antisymmâ (not_lt.mp h) ((s.sup p).Nonneg v), mul_zero, hr]
  exact IsOpen.mem_nhds is_open_univ (mem_univ 0)

variable [Nonempty Î¹]

theorem basis_sets_smul (U) (hU : U â p.basis_sets) :
    â (V : Set ð)(H : V â ð (0 : ð))(W : Set E)(H : W â p.AddGroupFilterBasis.Sets), V â¢ W â U := by
  rcases p.basis_sets_iff.mp hU with â¨s, r, hr, hUâ©
  refine' â¨Metric.Ball 0 r.sqrt, Metric.ball_mem_nhds 0 (real.sqrt_pos.mpr hr), _â©
  refine' â¨(s.sup p).ball 0 r.sqrt, p.basis_sets_mem s (real.sqrt_pos.mpr hr), _â©
  refine' Set.Subset.trans (ball_smul_ball (s.sup p) r.sqrt r.sqrt) _
  rw [hU, Real.mul_self_sqrt (le_of_ltâ hr)]

theorem basis_sets_smul_left (x : ð) (U : Set E) (hU : U â p.basis_sets) :
    â (V : Set E)(H : V â p.AddGroupFilterBasis.Sets), V â (fun y : E => x â¢ y) â»Â¹' U := by
  rcases p.basis_sets_iff.mp hU with â¨s, r, hr, hUâ©
  rw [hU]
  by_cases' h : x â  0
  Â· rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / â¥xâ¥)
    exact â¨p.basis_sets_mem s (div_pos hr (norm_pos_iff.mpr h)), subset.rflâ©
    
  refine' â¨(s.sup p).ball 0 r, p.basis_sets_mem s hr, _â©
  simp only [â not_ne_iff.mp h, â subset_def, â mem_ball_zero, â hr, â mem_univ, â map_zero, â implies_true_iff, â
    preimage_const_of_mem, â zero_smul]

/-- The `module_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
protected def moduleFilterBasis : ModuleFilterBasis ð E where
  toAddGroupFilterBasis := p.AddGroupFilterBasis
  smul' := p.basis_sets_smul
  smul_left' := p.basis_sets_smul_left
  smul_right' := p.basis_sets_smul_right

theorem filter_eq_infi (p : SeminormFamily ð E Î¹) : p.ModuleFilterBasis.toFilterBasis.filter = â¨ i, (ð 0).comap (p i) :=
  by
  refine' le_antisymmâ (le_infi fun i => _) _
  Â· rw [p.module_filter_basis.to_filter_basis.has_basis.le_basis_iff (metric.nhds_basis_ball.comap _)]
    intro Îµ hÎµ
    refine' â¨(p i).ball 0 Îµ, _, _â©
    Â· rw [â (Finset.sup_singleton : _ = p i)]
      exact p.basis_sets_mem {i} hÎµ
      
    Â· rw [id, (p i).ball_zero_eq_preimage_ball]
      
    
  Â· rw [p.module_filter_basis.to_filter_basis.has_basis.ge_iff]
    rintro U (hU : U â p.basis_sets)
    rcases p.basis_sets_iff.mp hU with â¨s, r, hr, rflâ©
    rw [id, Seminorm.ball_finset_sup_eq_Inter _ _ _ hr, s.Inter_mem_sets]
    exact fun i hi =>
      Filter.mem_infi_of_mem i
        â¨Metric.Ball 0 r, Metric.ball_mem_nhds 0 hr, Eq.subset (p i).ball_zero_eq_preimage_ball.symmâ©
    

end SeminormFamily

end FilterBasis

section Bounded

namespace Seminorm

variable [NormedField ð] [AddCommGroupâ E] [Module ð E] [AddCommGroupâ F] [Module ð F]

/-- The proposition that a linear map is bounded between spaces with families of seminorms. -/
-- Todo: This should be phrased entirely in terms of the von Neumann bornology.
def IsBounded (p : Î¹ â Seminorm ð E) (q : Î¹' â Seminorm ð F) (f : E ââ[ð] F) : Prop :=
  â i, â s : Finset Î¹, â C : ââ¥0 , C â  0 â§ (q i).comp f â¤ C â¢ s.sup p

theorem is_bounded_const (Î¹' : Type _) [Nonempty Î¹'] {p : Î¹ â Seminorm ð E} {q : Seminorm ð F} (f : E ââ[ð] F) :
    IsBounded p (fun _ : Î¹' => q) f â â (s : Finset Î¹)(C : ââ¥0 ), C â  0 â§ q.comp f â¤ C â¢ s.sup p := by
  simp only [â is_bounded, â forall_const]

theorem const_is_bounded (Î¹ : Type _) [Nonempty Î¹] {p : Seminorm ð E} {q : Î¹' â Seminorm ð F} (f : E ââ[ð] F) :
    IsBounded (fun _ : Î¹ => p) q f â â i, â C : ââ¥0 , C â  0 â§ (q i).comp f â¤ C â¢ p := by
  constructor <;> intro h i
  Â· rcases h i with â¨s, C, hC, hâ©
    exact â¨C, hC, le_transâ h (smul_le_smul (Finset.sup_le fun _ _ => le_rfl) le_rfl)â©
    
  use {Classical.arbitrary Î¹}
  simp only [â h, â Finset.sup_singleton]

theorem is_bounded_sup {p : Î¹ â Seminorm ð E} {q : Î¹' â Seminorm ð F} {f : E ââ[ð] F} (hf : IsBounded p q f)
    (s' : Finset Î¹') : â (C : ââ¥0 )(s : Finset Î¹), 0 < C â§ (s'.sup q).comp f â¤ C â¢ s.sup p := by
  classical
  by_cases' hs' : Â¬s'.nonempty
  Â· refine' â¨1, â, zero_lt_one, _â©
    rw [finset.not_nonempty_iff_eq_empty.mp hs', Finset.sup_empty, Seminorm.bot_eq_zero, zero_comp]
    exact Seminorm.nonneg _
    
  rw [not_not] at hs'
  choose fâ fC hf using hf
  use s'.card â¢ s'.sup fC, Finset.bUnion s' fâ
  constructor
  Â· refine' nsmul_pos _ (ne_of_gtâ (Finset.Nonempty.card_pos hs'))
    cases' Finset.Nonempty.bex hs' with j hj
    exact lt_of_lt_of_leâ (zero_lt_iff.mpr (And.elim_left (hf j))) (Finset.le_sup hj)
    
  have hs : â i : Î¹', i â s' â (q i).comp f â¤ s'.sup fC â¢ (Finset.bUnion s' fâ).sup p := by
    intro i hi
    refine' le_transâ (And.elim_right (hf i)) (smul_le_smul _ (Finset.le_sup hi))
    exact Finset.sup_mono (Finset.subset_bUnion_of_mem fâ hi)
  refine' le_transâ (comp_mono f (finset_sup_le_sum q s')) _
  simp_rw [â pullback_apply, AddMonoidHom.map_sum, pullback_apply]
  refine' le_transâ (Finset.sum_le_sum hs) _
  rw [Finset.sum_const, smul_assoc]
  exact le_rfl

end Seminorm

end Bounded

section Topology

variable [NormedField ð] [AddCommGroupâ E] [Module ð E] [Nonempty Î¹]

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
class WithSeminorms (p : SeminormFamily ð E Î¹) [t : TopologicalSpace E] : Prop where
  topology_eq_with_seminorms : t = p.ModuleFilterBasis.topology

theorem SeminormFamily.with_seminorms_eq (p : SeminormFamily ð E Î¹) [t : TopologicalSpace E] [WithSeminorms p] :
    t = p.ModuleFilterBasis.topology :=
  WithSeminorms.topology_eq_with_seminorms

variable [TopologicalSpace E]

variable (p : SeminormFamily ð E Î¹) [WithSeminorms p]

theorem SeminormFamily.has_basis : (ð (0 : E)).HasBasis (fun s : Set E => s â p.basis_sets) id := by
  rw [congr_fun (congr_arg (@nhds E) p.with_seminorms_eq) 0]
  exact AddGroupFilterBasis.nhds_zero_has_basis _

end Topology

section TopologicalAddGroup

variable [NormedField ð] [AddCommGroupâ E] [Module ð E]

variable [TopologicalSpace E] [TopologicalAddGroup E]

variable [Nonempty Î¹]

theorem SeminormFamily.with_seminorms_of_nhds (p : SeminormFamily ð E Î¹)
    (h : ð (0 : E) = p.ModuleFilterBasis.toFilterBasis.filter) : WithSeminorms p := by
  refine'
    â¨TopologicalAddGroup.ext
        (by
          infer_instance)
        p.add_group_filter_basis.is_topological_add_group _â©
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h

theorem SeminormFamily.with_seminorms_of_has_basis (p : SeminormFamily ð E Î¹)
    (h : (ð (0 : E)).HasBasis (fun s : Set E => s â p.basis_sets) id) : WithSeminorms p :=
  p.with_seminorms_of_nhds <| Filter.HasBasis.eq_of_same_basis h p.AddGroupFilterBasis.toFilterBasis.HasBasis

theorem SeminormFamily.with_seminorms_iff_nhds_eq_infi (p : SeminormFamily ð E Î¹) :
    WithSeminorms p â (ð 0 : Filter E) = â¨ i, (ð 0).comap (p i) := by
  rw [â p.filter_eq_infi]
  refine' â¨fun h => _, p.with_seminorms_of_nhdsâ©
  rw [h.topology_eq_with_seminorms]
  exact AddGroupFilterBasis.nhds_zero_eq _

end TopologicalAddGroup

section NormedSpace

/-- The topology of a `normed_space ð E` is induced by the seminorm `norm_seminorm ð E`. -/
instance norm_with_seminorms (ð E) [NormedField ð] [SemiNormedGroup E] [NormedSpace ð E] :
    WithSeminorms fun _ : Finâ 1 => normSeminorm ð E := by
  let p : SeminormFamily ð E (Finâ 1) := fun _ => normSeminorm ð E
  refine' â¨TopologicalAddGroup.ext normed_top_group p.add_group_filter_basis.is_topological_add_group _â©
  refine' Filter.HasBasis.eq_of_same_basis Metric.nhds_basis_ball _
  rw [â ball_norm_seminorm ð E]
  refine'
    Filter.HasBasis.to_has_basis p.add_group_filter_basis.nhds_zero_has_basis _ fun r hr =>
      â¨(normSeminorm ð E).ball 0 r, p.basis_sets_singleton_mem 0 hr, rfl.subsetâ©
  rintro U (hU : U â p.basis_sets)
  rcases p.basis_sets_iff.mp hU with â¨s, r, hr, hUâ©
  use r, hr
  rw [hU, id.def]
  by_cases' h : s.nonempty
  Â· rw [Finset.sup_const h]
    
  rw [finset.not_nonempty_iff_eq_empty.mp h, Finset.sup_empty, ball_bot _ hr]
  exact Set.subset_univ _

end NormedSpace

section NondiscreteNormedField

variable [NondiscreteNormedField ð] [AddCommGroupâ E] [Module ð E] [Nonempty Î¹]

variable (p : SeminormFamily ð E Î¹)

variable [TopologicalSpace E] [WithSeminorms p]

theorem Bornology.is_vonN_bounded_iff_finset_seminorm_bounded {s : Set E} :
    Bornology.IsVonNBounded ð s â â I : Finset Î¹, â (r : _)(hr : 0 < r), â, â x â s, â, I.sup p x < r := by
  rw [p.has_basis.is_vonN_bounded_basis_iff]
  constructor
  Â· intro h I
    simp only [â id.def] at h
    specialize h ((I.sup p).ball 0 1) (p.basis_sets_mem I zero_lt_one)
    rcases h with â¨r, hr, hâ©
    cases' NormedField.exists_lt_norm ð r with a ha
    specialize h a (le_of_ltâ ha)
    rw [Seminorm.smul_ball_zero (lt_transâ hr ha), mul_oneâ] at h
    refine' â¨â¥aâ¥, lt_transâ hr ha, _â©
    intro x hx
    specialize h hx
    exact (Finset.sup I p).mem_ball_zero.mp h
    
  intro h s' hs'
  rcases p.basis_sets_iff.mp hs' with â¨I, r, hr, hs'â©
  rw [id.def, hs']
  rcases h I with â¨r', hr', h'â©
  simp_rw [â (I.sup p).mem_ball_zero] at h'
  refine' Absorbs.mono_right _ h'
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr

theorem Bornology.is_vonN_bounded_iff_seminorm_bounded {s : Set E} :
    Bornology.IsVonNBounded ð s â â i : Î¹, â (r : _)(hr : 0 < r), â, â x â s, â, p i x < r := by
  rw [Bornology.is_vonN_bounded_iff_finset_seminorm_bounded p]
  constructor
  Â· intro hI i
    convert hI {i}
    rw [Finset.sup_singleton]
    
  intro hi I
  by_cases' hI : I.nonempty
  Â· choose r hr h using hi
    have h' : 0 < I.sup' hI r := by
      rcases hI.bex with â¨i, hiâ©
      exact lt_of_lt_of_leâ (hr i) (Finset.le_sup' r hi)
    refine' â¨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => _â©
    refine' lt_of_lt_of_leâ (h i x hx) _
    simp only [â Finset.le_sup'_iff, â exists_prop]
    exact â¨i, hi, (Eq.refl _).leâ©
    
  simp only [â finset.not_nonempty_iff_eq_empty.mp hI, â Finset.sup_empty, â coe_bot, â Pi.zero_apply, â exists_prop]
  exact â¨1, zero_lt_one, fun _ _ => zero_lt_oneâ©

end NondiscreteNormedField

section ContinuousBounded

namespace Seminorm

variable [NormedField ð] [AddCommGroupâ E] [Module ð E] [AddCommGroupâ F] [Module ð F]

variable [Nonempty Î¹] [Nonempty Î¹']

theorem continuous_from_bounded (p : SeminormFamily ð E Î¹) (q : SeminormFamily ð F Î¹') [UniformSpace E]
    [UniformAddGroup E] [WithSeminorms p] [UniformSpace F] [UniformAddGroup F] [WithSeminorms q] (f : E ââ[ð] F)
    (hf : Seminorm.IsBounded p q f) : Continuous f := by
  refine' continuous_of_continuous_at_zero f _
  rw [continuous_at_def, f.map_zero, p.with_seminorms_eq]
  intro U hU
  rw [q.with_seminorms_eq, AddGroupFilterBasis.nhds_zero_eq, FilterBasis.mem_filter_iff] at hU
  rcases hU with â¨V, hV : V â q.basis_sets, hUâ©
  rcases q.basis_sets_iff.mp hV with â¨sâ, r, hr, hVâ©
  rw [hV] at hU
  rw [p.add_group_filter_basis.nhds_zero_eq, FilterBasis.mem_filter_iff]
  rcases Seminorm.is_bounded_sup hf sâ with â¨C, sâ, hC, hfâ©
  refine' â¨(sâ.sup p).ball 0 (r / C), p.basis_sets_mem _ (div_pos hr (nnreal.coe_pos.mpr hC)), _â©
  refine' subset.trans _ (preimage_mono hU)
  simp_rw [â LinearMap.map_zero f, â ball_comp]
  refine' subset.trans _ (ball_antitone hf)
  rw [ball_smul (sâ.sup p) hC]

theorem cont_with_seminorms_normed_space (F) [SemiNormedGroup F] [NormedSpace ð F] [UniformSpace E] [UniformAddGroup E]
    (p : Î¹ â Seminorm ð E) [WithSeminorms p] (f : E ââ[ð] F)
    (hf : â (s : Finset Î¹)(C : ââ¥0 ), C â  0 â§ (normSeminorm ð F).comp f â¤ C â¢ s.sup p) : Continuous f := by
  rw [â Seminorm.is_bounded_const (Finâ 1)] at hf
  exact continuous_from_bounded p (fun _ : Finâ 1 => normSeminorm ð F) f hf

theorem cont_normed_space_to_with_seminorms (E) [SemiNormedGroup E] [NormedSpace ð E] [UniformSpace F]
    [UniformAddGroup F] (q : Î¹ â Seminorm ð F) [WithSeminorms q] (f : E ââ[ð] F)
    (hf : â i : Î¹, â C : ââ¥0 , C â  0 â§ (q i).comp f â¤ C â¢ normSeminorm ð E) : Continuous f := by
  rw [â Seminorm.const_is_bounded (Finâ 1)] at hf
  exact continuous_from_bounded (fun _ : Finâ 1 => normSeminorm ð E) q f hf

end Seminorm

end ContinuousBounded

section LocallyConvexSpace

open LocallyConvexSpace

variable [Nonempty Î¹] [NormedField ð] [NormedSpace â ð] [AddCommGroupâ E] [Module ð E] [Module â E]
  [IsScalarTower â ð E] [TopologicalSpace E] [TopologicalAddGroup E]

theorem SeminormFamily.to_locally_convex_space (p : SeminormFamily ð E Î¹) [WithSeminorms p] : LocallyConvexSpace â E :=
  by
  apply of_basis_zero â E id fun s => s â p.basis_sets
  Â· rw [p.with_seminorms_eq, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.has_basis _
    
  Â· intro s hs
    change s â Set.Union _ at hs
    simp_rw [Set.mem_Union, Set.mem_singleton_iff] at hs
    rcases hs with â¨I, r, hr, rflâ©
    exact convex_ball _ _ _
    

end LocallyConvexSpace

section NormedSpace

variable (ð) [NormedField ð] [NormedSpace â ð] [SemiNormedGroup E]

/-- Not an instance since `ð` can't be inferred. See `normed_space.to_locally_convex_space` for a
slightly weaker instance version. -/
theorem NormedSpace.to_locally_convex_space' [NormedSpace ð E] [Module â E] [IsScalarTower â ð E] :
    LocallyConvexSpace â E :=
  SeminormFamily.to_locally_convex_space fun _ : Finâ 1 => normSeminorm ð E

/-- See `normed_space.to_locally_convex_space'` for a slightly stronger version which is not an
instance. -/
instance NormedSpace.to_locally_convex_space [NormedSpace â E] : LocallyConvexSpace â E :=
  NormedSpace.to_locally_convex_space' â

end NormedSpace

section TopologicalConstructions

variable [NormedField ð] [AddCommGroupâ F] [Module ð F] [AddCommGroupâ E] [Module ð E]

/-- The family of seminorms obtained by composing each seminorm by a linear map. -/
def SeminormFamily.comp (q : SeminormFamily ð F Î¹) (f : E ââ[ð] F) : SeminormFamily ð E Î¹ := fun i => (q i).comp f

theorem SeminormFamily.comp_apply (q : SeminormFamily ð F Î¹) (i : Î¹) (f : E ââ[ð] F) : q.comp f i = (q i).comp f :=
  rfl

theorem SeminormFamily.finset_sup_comp (q : SeminormFamily ð F Î¹) (s : Finset Î¹) (f : E ââ[ð] F) :
    (s.sup q).comp f = s.sup (q.comp f) := by
  ext x
  rw [Seminorm.comp_apply, Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  rfl

variable [TopologicalSpace F] [TopologicalAddGroup F]

theorem LinearMap.with_seminorms_induced [hÎ¹ : Nonempty Î¹] {q : SeminormFamily ð F Î¹} [hq : WithSeminorms q]
    (f : E ââ[ð] F) : @WithSeminorms ð E Î¹ _ _ _ _ (q.comp f) (induced f inferInstance) := by
  let this : TopologicalSpace E := induced f inferInstance
  let this : TopologicalAddGroup E := topological_add_group_induced f
  rw [(q.comp f).with_seminorms_iff_nhds_eq_infi, nhds_induced, map_zero, q.with_seminorms_iff_nhds_eq_infi.mp hq,
    Filter.comap_infi]
  refine' infi_congr fun i => _
  exact Filter.comap_comap

theorem Inducing.with_seminorms [hÎ¹ : Nonempty Î¹] {q : SeminormFamily ð F Î¹} [hq : WithSeminorms q] [TopologicalSpace E]
    {f : E ââ[ð] F} (hf : Inducing f) : WithSeminorms (q.comp f) := by
  rw [hf.induced]
  exact f.with_seminorms_induced

end TopologicalConstructions

