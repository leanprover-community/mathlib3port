/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module analysis.convex.gauge
! leanprover-community/mathlib commit 373b03b5b9d0486534edbe94747f23cb3712f93d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Analysis.NormedSpace.Pointwise
import Mathbin.Analysis.Seminorm
import Mathbin.Data.IsROrC.Basic
import Mathbin.Tactic.Congrm

/-!
# The Minkowksi functional

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the Minkowski functional, aka gauge.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a real vector space,
* `gauge`: Aka Minkowksi functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gauge_seminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

Minkowski functional, gauge
-/


open NormedField Set

open scoped Pointwise Topology NNReal

noncomputable section

variable {𝕜 E F : Type _}

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E]

#print gauge /-
/-- The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : Set E) (x : E) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ x ∈ r • s}
#align gauge gauge
-/

variable {s t : Set E} {a : ℝ} {x : E}

#print gauge_def /-
theorem gauge_def : gauge s x = sInf ({r ∈ Set.Ioi 0 | x ∈ r • s}) :=
  rfl
#align gauge_def gauge_def
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr Inf (λ r, _)]] -/
#print gauge_def' /-
/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
theorem gauge_def' : gauge s x = sInf ({r ∈ Set.Ioi 0 | r⁻¹ • x ∈ s}) :=
  by
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr Inf (λ r, _)]]"
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _
#align gauge_def' gauge_def'
-/

private theorem gauge_set_bdd_below : BddBelow {r : ℝ | 0 < r ∧ x ∈ r • s} :=
  ⟨0, fun r hr => hr.1.le⟩

#print Absorbent.gauge_set_nonempty /-
/-- If the given subset is `absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
theorem Absorbent.gauge_set_nonempty (absorbs : Absorbent ℝ s) :
    {r : ℝ | 0 < r ∧ x ∈ r • s}.Nonempty :=
  let ⟨r, hr₁, hr₂⟩ := Absorbs x
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).ge⟩
#align absorbent.gauge_set_nonempty Absorbent.gauge_set_nonempty
-/

#print gauge_mono /-
theorem gauge_mono (hs : Absorbent ℝ s) (h : s ⊆ t) : gauge t ≤ gauge s := fun x =>
  csInf_le_csInf gauge_set_bddBelow hs.gauge_set_nonempty fun r hr => ⟨hr.1, smul_set_mono h hr.2⟩
#align gauge_mono gauge_mono
-/

#print exists_lt_of_gauge_lt /-
theorem exists_lt_of_gauge_lt (absorbs : Absorbent ℝ s) (h : gauge s x < a) :
    ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s :=
  by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_csInf_lt absorbs.gauge_set_nonempty h
  exact ⟨b, hb, hba, hx⟩
#align exists_lt_of_gauge_lt exists_lt_of_gauge_lt
-/

#print gauge_zero /-
/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp]
theorem gauge_zero : gauge s 0 = 0 := by
  rw [gauge_def']
  by_cases (0 : E) ∈ s
  · simp only [smul_zero, sep_true, h, csInf_Ioi]
  · simp only [smul_zero, sep_false, h, Real.sInf_empty]
#align gauge_zero gauge_zero
-/

#print gauge_zero' /-
@[simp]
theorem gauge_zero' : gauge (0 : Set E) = 0 := by
  ext
  rw [gauge_def']
  obtain rfl | hx := eq_or_ne x 0
  · simp only [csInf_Ioi, mem_zero, Pi.zero_apply, eq_self_iff_true, sep_true, smul_zero]
  · simp only [mem_zero, Pi.zero_apply, inv_eq_zero, smul_eq_zero]
    convert Real.sInf_empty
    exact eq_empty_iff_forall_not_mem.2 fun r hr => hr.2.elim (ne_of_gt hr.1) hx
#align gauge_zero' gauge_zero'
-/

#print gauge_empty /-
@[simp]
theorem gauge_empty : gauge (∅ : Set E) = 0 := by ext;
  simp only [gauge_def', Real.sInf_empty, mem_empty_iff_false, Pi.zero_apply, sep_false]
#align gauge_empty gauge_empty
-/

#print gauge_of_subset_zero /-
theorem gauge_of_subset_zero (h : s ⊆ 0) : gauge s = 0 := by
  obtain rfl | rfl := subset_singleton_iff_eq.1 h; exacts [gauge_empty, gauge_zero']
#align gauge_of_subset_zero gauge_of_subset_zero
-/

#print gauge_nonneg /-
/-- The gauge is always nonnegative. -/
theorem gauge_nonneg (x : E) : 0 ≤ gauge s x :=
  Real.sInf_nonneg _ fun x hx => hx.1.le
#align gauge_nonneg gauge_nonneg
-/

#print gauge_neg /-
theorem gauge_neg (symmetric : ∀ x ∈ s, -x ∈ s) (x : E) : gauge s (-x) = gauge s x :=
  by
  have : ∀ x, -x ∈ s ↔ x ∈ s := fun x => ⟨fun h => by simpa using Symmetric _ h, Symmetric x⟩
  simp_rw [gauge_def', smul_neg, this]
#align gauge_neg gauge_neg
-/

#print gauge_neg_set_neg /-
theorem gauge_neg_set_neg (x : E) : gauge (-s) (-x) = gauge s x := by
  simp_rw [gauge_def', smul_neg, neg_mem_neg]
#align gauge_neg_set_neg gauge_neg_set_neg
-/

#print gauge_neg_set_eq_gauge_neg /-
theorem gauge_neg_set_eq_gauge_neg (x : E) : gauge (-s) x = gauge s (-x) := by
  rw [← gauge_neg_set_neg, neg_neg]
#align gauge_neg_set_eq_gauge_neg gauge_neg_set_eq_gauge_neg
-/

#print gauge_le_of_mem /-
theorem gauge_le_of_mem (ha : 0 ≤ a) (hx : x ∈ a • s) : gauge s x ≤ a :=
  by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [mem_singleton_iff.1 (zero_smul_set_subset _ hx), gauge_zero]
  · exact csInf_le gauge_set_bdd_below ⟨ha', hx⟩
#align gauge_le_of_mem gauge_le_of_mem
-/

#print gauge_le_eq /-
theorem gauge_le_eq (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : Absorbent ℝ s) (ha : 0 ≤ a) :
    {x | gauge s x ≤ a} = ⋂ (r : ℝ) (H : a < r), r • s :=
  by
  ext
  simp_rw [Set.mem_iInter, Set.mem_setOf_eq]
  refine' ⟨fun h r hr => _, fun h => le_of_forall_pos_lt_add fun ε hε => _⟩
  · have hr' := ha.trans_lt hr
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr)
    suffices (r⁻¹ * δ) • δ⁻¹ • x ∈ s by rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this 
    rw [mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne'] at hδ 
    refine' hs₁.smul_mem_of_zero_mem hs₀ hδ ⟨by positivity, _⟩
    rw [inv_mul_le_iff hr', mul_one]
    exact hδr.le
  · have hε' := (lt_add_iff_pos_right a).2 (half_pos hε)
    exact
      (gauge_le_of_mem (ha.trans hε'.le) <| h _ hε').trans_lt (add_lt_add_left (half_lt_self hε) _)
#align gauge_le_eq gauge_le_eq
-/

#print gauge_lt_eq' /-
theorem gauge_lt_eq' (absorbs : Absorbent ℝ s) (a : ℝ) :
    {x | gauge s x < a} = ⋃ (r : ℝ) (H : 0 < r) (H : r < a), r • s :=
  by
  ext
  simp_rw [mem_set_of_eq, mem_Union, exists_prop]
  exact
    ⟨exists_lt_of_gauge_lt Absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩
#align gauge_lt_eq' gauge_lt_eq'
-/

#print gauge_lt_eq /-
theorem gauge_lt_eq (absorbs : Absorbent ℝ s) (a : ℝ) :
    {x | gauge s x < a} = ⋃ r ∈ Set.Ioo 0 (a : ℝ), r • s :=
  by
  ext
  simp_rw [mem_set_of_eq, mem_Union, exists_prop, mem_Ioo, and_assoc']
  exact
    ⟨exists_lt_of_gauge_lt Absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩
#align gauge_lt_eq gauge_lt_eq
-/

#print gauge_lt_one_subset_self /-
theorem gauge_lt_one_subset_self (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
    {x | gauge s x < 1} ⊆ s := by
  rw [gauge_lt_eq Absorbs]
  refine' Set.iUnion₂_subset fun r hr _ => _
  rintro ⟨y, hy, rfl⟩
  exact hs.smul_mem_of_zero_mem h₀ hy (Ioo_subset_Icc_self hr)
#align gauge_lt_one_subset_self gauge_lt_one_subset_self
-/

#print gauge_le_one_of_mem /-
theorem gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
  gauge_le_of_mem zero_le_one <| by rwa [one_smul]
#align gauge_le_one_of_mem gauge_le_one_of_mem
-/

#print self_subset_gauge_le_one /-
theorem self_subset_gauge_le_one : s ⊆ {x | gauge s x ≤ 1} := fun x => gauge_le_one_of_mem
#align self_subset_gauge_le_one self_subset_gauge_le_one
-/

#print Convex.gauge_le /-
theorem Convex.gauge_le (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) (a : ℝ) :
    Convex ℝ {x | gauge s x ≤ a} := by
  by_cases ha : 0 ≤ a
  · rw [gauge_le_eq hs h₀ Absorbs ha]
    exact convex_iInter fun i => convex_iInter fun hi => hs.smul _
  · convert convex_empty
    exact eq_empty_iff_forall_not_mem.2 fun x hx => ha <| (gauge_nonneg _).trans hx
#align convex.gauge_le Convex.gauge_le
-/

#print Balanced.starConvex /-
theorem Balanced.starConvex (hs : Balanced ℝ s) : StarConvex ℝ 0 s :=
  starConvex_zero_iff.2 fun x hx a ha₀ ha₁ =>
    hs _ (by rwa [Real.norm_of_nonneg ha₀]) (smul_mem_smul_set hx)
#align balanced.star_convex Balanced.starConvex
-/

#print le_gauge_of_not_mem /-
theorem le_gauge_of_not_mem (hs₀ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ a • s) :
    a ≤ gauge s x := by
  rw [starConvex_zero_iff] at hs₀ 
  obtain ⟨r, hr, h⟩ := hs₂
  refine' le_csInf ⟨r, hr, singleton_subset_iff.1 <| h _ (Real.norm_of_nonneg hr.le).ge⟩ _
  rintro b ⟨hb, x, hx', rfl⟩
  refine' not_lt.1 fun hba => hx _
  have ha := hb.trans hba
  refine' ⟨(a⁻¹ * b) • x, hs₀ hx' (by positivity) _, _⟩
  · rw [← div_eq_inv_mul]
    exact div_le_one_of_le hba.le ha.le
  · rw [← mul_smul, mul_inv_cancel_left₀ ha.ne']
#align le_gauge_of_not_mem le_gauge_of_not_mem
-/

#print one_le_gauge_of_not_mem /-
theorem one_le_gauge_of_not_mem (hs₁ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ s) :
    1 ≤ gauge s x :=
  le_gauge_of_not_mem hs₁ hs₂ <| by rwa [one_smul]
#align one_le_gauge_of_not_mem one_le_gauge_of_not_mem
-/

section LinearOrderedField

variable {α : Type _} [LinearOrderedField α] [MulActionWithZero α ℝ] [OrderedSMul α ℝ]

#print gauge_smul_of_nonneg /-
theorem gauge_smul_of_nonneg [MulActionWithZero α E] [IsScalarTower α ℝ (Set E)] {s : Set E} {a : α}
    (ha : 0 ≤ a) (x : E) : gauge s (a • x) = a • gauge s x :=
  by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul, gauge_zero, zero_smul]
  rw [gauge_def', gauge_def', ← Real.sInf_smul_of_nonneg ha]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, hx⟩
    simp_rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx 
    have := smul_pos (inv_pos.2 ha') hr
    refine' ⟨a⁻¹ • r, ⟨this, _⟩, smul_inv_smul₀ ha'.ne' _⟩
    rwa [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc,
      mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha'.ne'), inv_inv]
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx 
    have := smul_pos ha' hr
    refine' ⟨this, _⟩
    rw [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc]
    exact smul_mem_smul_set hx
#align gauge_smul_of_nonneg gauge_smul_of_nonneg
-/

#print gauge_smul_left_of_nonneg /-
theorem gauge_smul_left_of_nonneg [MulActionWithZero α E] [SMulCommClass α ℝ ℝ]
    [IsScalarTower α ℝ ℝ] [IsScalarTower α ℝ E] {s : Set E} {a : α} (ha : 0 ≤ a) :
    gauge (a • s) = a⁻¹ • gauge s :=
  by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_set_subset _)]
  ext
  rw [gauge_def', Pi.smul_apply, gauge_def', ← Real.sInf_smul_of_nonneg (inv_nonneg.2 ha)]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, y, hy, h⟩
    simp_rw [mem_Ioi] at hr ⊢
    refine' ⟨a • r, ⟨smul_pos ha' hr, _⟩, inv_smul_smul₀ ha'.ne' _⟩
    rwa [smul_inv₀, smul_assoc, ← h, inv_smul_smul₀ ha'.ne']
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr ⊢
    have := smul_pos ha' hr
    refine' ⟨smul_pos (inv_pos.2 ha') hr, r⁻¹ • x, hx, _⟩
    rw [smul_inv₀, smul_assoc, inv_inv]
#align gauge_smul_left_of_nonneg gauge_smul_left_of_nonneg
-/

#print gauge_smul_left /-
theorem gauge_smul_left [Module α E] [SMulCommClass α ℝ ℝ] [IsScalarTower α ℝ ℝ]
    [IsScalarTower α ℝ E] {s : Set E} (symmetric : ∀ x ∈ s, -x ∈ s) (a : α) :
    gauge (a • s) = |a|⁻¹ • gauge s :=
  by
  rw [← gauge_smul_left_of_nonneg (abs_nonneg a)]
  obtain h | h := abs_choice a
  · rw [h]
  · rw [h, Set.neg_smul_set, ← Set.smul_set_neg]
    congr
    ext y
    refine' ⟨Symmetric _, fun hy => _⟩
    rw [← neg_neg y]
    exact Symmetric _ hy
  · infer_instance
#align gauge_smul_left gauge_smul_left
-/

end LinearOrderedField

section IsROrC

variable [IsROrC 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

#print gauge_norm_smul /-
theorem gauge_norm_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (‖r‖ • x) = gauge s (r • x) :=
  by
  unfold gauge
  congr with θ
  rw [@IsROrC.real_smul_eq_coe_smul 𝕜]
  refine' and_congr_right fun hθ => (hs.smul _).mem_smul_iff _
  rw [IsROrC.norm_ofReal, abs_norm]
#align gauge_norm_smul gauge_norm_smul
-/

#print gauge_smul /-
/-- If `s` is balanced, then the Minkowski functional is ℂ-homogeneous. -/
theorem gauge_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (r • x) = ‖r‖ * gauge s x := by
  rw [← smul_eq_mul, ← gauge_smul_of_nonneg (norm_nonneg r), gauge_norm_smul hs]; infer_instance
#align gauge_smul gauge_smul
-/

end IsROrC

section TopologicalSpace

variable [TopologicalSpace E] [ContinuousSMul ℝ E]

#print interior_subset_gauge_lt_one /-
theorem interior_subset_gauge_lt_one (s : Set E) : interior s ⊆ {x | gauge s x < 1} :=
  by
  intro x hx
  let f : ℝ → E := fun t => t • x
  have hf : Continuous f := by continuity
  let s' := f ⁻¹' interior s
  have hs' : IsOpen s' := hf.is_open_preimage _ isOpen_interior
  have one_mem : (1 : ℝ) ∈ s' := by simpa only [s', f, Set.mem_preimage, one_smul]
  obtain ⟨ε, hε₀, hε⟩ := (Metric.nhds_basis_closedBall.1 _).1 (isOpen_iff_mem_nhds.1 hs' 1 one_mem)
  rw [Real.closedBall_eq_Icc] at hε 
  have hε₁ : 0 < 1 + ε := hε₀.trans (lt_one_add ε)
  have : (1 + ε)⁻¹ < 1 := by
    rw [inv_lt_one_iff]
    right
    linarith
  refine' (gauge_le_of_mem (inv_nonneg.2 hε₁.le) _).trans_lt this
  rw [mem_inv_smul_set_iff₀ hε₁.ne']
  exact
    interior_subset
      (hε ⟨(sub_le_self _ hε₀.le).trans ((le_add_iff_nonneg_right _).2 hε₀.le), le_rfl⟩)
#align interior_subset_gauge_lt_one interior_subset_gauge_lt_one
-/

#print gauge_lt_one_eq_self_of_open /-
theorem gauge_lt_one_eq_self_of_open (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : IsOpen s) :
    {x | gauge s x < 1} = s :=
  by
  refine' (gauge_lt_one_subset_self hs₁ ‹_› <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀).antisymm _
  convert interior_subset_gauge_lt_one s
  exact hs₂.interior_eq.symm
#align gauge_lt_one_eq_self_of_open gauge_lt_one_eq_self_of_open
-/

theorem gauge_lt_one_of_mem_of_open (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : IsOpen s) {x : E}
    (hx : x ∈ s) : gauge s x < 1 := by rwa [← gauge_lt_one_eq_self_of_open hs₁ hs₀ hs₂] at hx 
#align gauge_lt_one_of_mem_of_open gauge_lt_one_of_mem_of_openₓ

theorem gauge_lt_of_mem_smul (x : E) (ε : ℝ) (hε : 0 < ε) (hs₀ : (0 : E) ∈ s) (hs₁ : Convex ℝ s)
    (hs₂ : IsOpen s) (hx : x ∈ ε • s) : gauge s x < ε :=
  by
  have : ε⁻¹ • x ∈ s := by rwa [← mem_smul_set_iff_inv_smul_mem₀ hε.ne']
  have h_gauge_lt := gauge_lt_one_of_mem_of_open hs₁ hs₀ hs₂ this
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff hε, mul_one] at
    h_gauge_lt 
  infer_instance
#align gauge_lt_of_mem_smul gauge_lt_of_mem_smulₓ

end TopologicalSpace

#print gauge_add_le /-
theorem gauge_add_le (hs : Convex ℝ s) (absorbs : Absorbent ℝ s) (x y : E) :
    gauge s (x + y) ≤ gauge s x + gauge s y :=
  by
  refine' le_of_forall_pos_lt_add fun ε hε => _
  obtain ⟨a, ha, ha', hx⟩ :=
    exists_lt_of_gauge_lt Absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', hy⟩ :=
    exists_lt_of_gauge_lt Absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne'] at hx 
  rw [mem_smul_set_iff_inv_smul_mem₀ hb.ne'] at hy 
  suffices gauge s (x + y) ≤ a + b by linarith
  have hab : 0 < a + b := add_pos ha hb
  apply gauge_le_of_mem hab.le
  have := convex_iff_div.1 hs hx hy ha.le hb.le hab
  rwa [smul_smul, smul_smul, ← mul_div_right_comm, ← mul_div_right_comm, mul_inv_cancel ha.ne',
    mul_inv_cancel hb.ne', ← smul_add, one_div, ← mem_smul_set_iff_inv_smul_mem₀ hab.ne'] at this 
#align gauge_add_le gauge_add_le
-/

section IsROrC

variable [IsROrC 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

#print gaugeSeminorm /-
/-- `gauge s` as a seminorm when `s` is  balanced, convex and absorbent. -/
@[simps]
def gaugeSeminorm (hs₀ : Balanced 𝕜 s) (hs₁ : Convex ℝ s) (hs₂ : Absorbent ℝ s) : Seminorm 𝕜 E :=
  Seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)
#align gauge_seminorm gaugeSeminorm
-/

variable {hs₀ : Balanced 𝕜 s} {hs₁ : Convex ℝ s} {hs₂ : Absorbent ℝ s} [TopologicalSpace E]
  [ContinuousSMul ℝ E]

#print gaugeSeminorm_lt_one_of_open /-
theorem gaugeSeminorm_lt_one_of_open (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    gaugeSeminorm hs₀ hs₁ hs₂ x < 1 :=
  gauge_lt_one_of_mem_of_open hs₁ hs₂.zero_mem hs hx
#align gauge_seminorm_lt_one_of_open gaugeSeminorm_lt_one_of_open
-/

#print gaugeSeminorm_ball_one /-
theorem gaugeSeminorm_ball_one (hs : IsOpen s) : (gaugeSeminorm hs₀ hs₁ hs₂).ball 0 1 = s :=
  by
  rw [Seminorm.ball_zero_eq]
  exact gauge_lt_one_eq_self_of_open hs₁ hs₂.zero_mem hs
#align gauge_seminorm_ball_one gaugeSeminorm_ball_one
-/

end IsROrC

#print Seminorm.gauge_ball /-
/-- Any seminorm arises as the gauge of its unit ball. -/
@[simp]
protected theorem Seminorm.gauge_ball (p : Seminorm ℝ E) : gauge (p.ball 0 1) = p :=
  by
  ext
  obtain hp | hp := {r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1}.eq_empty_or_nonempty
  · rw [gauge, hp, Real.sInf_empty]
    by_contra
    have hpx : 0 < p x := (map_nonneg _ _).lt_of_ne h
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    refine' hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, _, smul_inv_smul₀ hpx₂.ne' _⟩
    rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂),
      inv_mul_lt_iff hpx₂, mul_one]
    exact lt_mul_of_one_lt_left hpx one_lt_two
  refine' IsGLB.csInf_eq ⟨fun r => _, fun r hr => le_of_forall_pos_le_add fun ε hε => _⟩ hp
  · rintro ⟨hr, y, hy, rfl⟩
    rw [p.mem_ball_zero] at hy 
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le hy.le
  · have hpε : 0 < p x + ε := by positivity
    refine' hr ⟨hpε, (p x + ε)⁻¹ • x, _, smul_inv_smul₀ hpε.ne' _⟩
    rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpε),
      inv_mul_lt_iff hpε, mul_one]
    exact lt_add_of_pos_right _ hε
#align seminorm.gauge_ball Seminorm.gauge_ball
-/

#print Seminorm.gaugeSeminorm_ball /-
theorem Seminorm.gaugeSeminorm_ball (p : Seminorm ℝ E) :
    gaugeSeminorm (p.balanced_ball_zero 1) (p.convex_ball 0 1) (p.absorbent_ball_zero zero_lt_one) =
      p :=
  FunLike.coe_injective p.gauge_ball
#align seminorm.gauge_seminorm_ball Seminorm.gaugeSeminorm_ball
-/

end AddCommGroup

section Norm

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {r : ℝ} {x : E}

#print gauge_unit_ball /-
theorem gauge_unit_ball (x : E) : gauge (Metric.ball (0 : E) 1) x = ‖x‖ := by
  rw [← ball_normSeminorm ℝ, Seminorm.gauge_ball, coe_normSeminorm]
#align gauge_unit_ball gauge_unit_ball
-/

#print gauge_ball /-
theorem gauge_ball (hr : 0 < r) (x : E) : gauge (Metric.ball (0 : E) r) x = ‖x‖ / r :=
  by
  rw [← smul_unitBall_of_pos hr, gauge_smul_left, Pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul]
  simp_rw [mem_ball_zero_iff, norm_neg]
  exact fun _ => id
#align gauge_ball gauge_ball
-/

#print mul_gauge_le_norm /-
theorem mul_gauge_le_norm (hs : Metric.ball (0 : E) r ⊆ s) : r * gauge s x ≤ ‖x‖ :=
  by
  obtain hr | hr := le_or_lt r 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr <| gauge_nonneg _).trans (norm_nonneg _)
  rw [mul_comm, ← le_div_iff hr, ← gauge_ball hr]
  exact gauge_mono (absorbent_ball_zero hr) hs x
#align mul_gauge_le_norm mul_gauge_le_norm
-/

#print Convex.lipschitzWith_gauge /-
theorem Convex.lipschitzWith_gauge {r : ℝ≥0} (hc : Convex ℝ s) (hr : 0 < r)
    (hs : Metric.ball (0 : E) r ⊆ s) : LipschitzWith r⁻¹ (gauge s) :=
  have : Absorbent ℝ (Metric.ball (0 : E) r) := absorbent_ball_zero hr
  LipschitzWith.of_le_add_mul _ fun x y =>
    calc
      gauge s x = gauge s (y + (x - y)) := by simp
      _ ≤ gauge s y + gauge s (x - y) := (gauge_add_le hc (this.Subset hs) _ _)
      _ ≤ gauge s y + ‖x - y‖ / r :=
        (add_le_add_left ((gauge_mono this hs (x - y)).trans_eq (gauge_ball hr _)) _)
      _ = gauge s y + r⁻¹ * dist x y := by rw [dist_eq_norm, div_eq_inv_mul]
#align convex.lipschitz_with_gauge Convex.lipschitzWith_gauge
-/

#print Convex.uniformContinuous_gauge /-
theorem Convex.uniformContinuous_gauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 (0 : E)) :
    UniformContinuous (gauge s) :=
  by
  obtain ⟨r, hr₀, hr⟩ := Metric.mem_nhds_iff.1 h₀
  lift r to ℝ≥0 using le_of_lt hr₀
  exact (hc.lipschitz_with_gauge hr₀ hr).UniformContinuous
#align convex.uniform_continuous_gauge Convex.uniformContinuous_gauge
-/

end Norm

