/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth

! This file was ported from Lean 3 source module measure_theory.function.simple_func_dense
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.SimpleFunc

/-!
# Density of simple functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

## Main definitions

* `measure_theory.simple_func.nearest_pt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `simple_func` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `measure_theory.simple_func.approx_on (f : β → α) (hf : measurable f) (s : set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [separable_space s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.

## Main results

* `tendsto_approx_on` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `measure_theory.simple_func.approx_on f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/


open Set Function Filter TopologicalSpace ENNReal Emetric Finset

open Classical Topology ENNReal MeasureTheory BigOperators

variable {α β ι E F 𝕜 : Type _}

noncomputable section

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/


variable [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]

#print MeasureTheory.SimpleFunc.nearestPtInd /-
/-- `nearest_pt_ind e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearest_pt_ind e N x` returns the least of their indexes. -/
noncomputable def nearestPtInd (e : ℕ → α) : ℕ → α →ₛ ℕ
  | 0 => const α 0
  | N + 1 =>
    piecewise (⋂ k ≤ N, { x | edist (e (N + 1)) x < edist (e k) x })
      (MeasurableSet.iInter fun k =>
        MeasurableSet.iInter fun hk =>
          measurableSet_lt measurable_edist_right measurable_edist_right)
      (const α <| N + 1) (nearest_pt_ind N)
#align measure_theory.simple_func.nearest_pt_ind MeasureTheory.SimpleFunc.nearestPtInd
-/

#print MeasureTheory.SimpleFunc.nearestPt /-
/-- `nearest_pt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
one point are at the same distance from `x`, then `nearest_pt e N x` returns the point with the
least possible index. -/
noncomputable def nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ α :=
  (nearestPtInd e N).map e
#align measure_theory.simple_func.nearest_pt MeasureTheory.SimpleFunc.nearestPt
-/

#print MeasureTheory.SimpleFunc.nearestPtInd_zero /-
@[simp]
theorem nearestPtInd_zero (e : ℕ → α) : nearestPtInd e 0 = const α 0 :=
  rfl
#align measure_theory.simple_func.nearest_pt_ind_zero MeasureTheory.SimpleFunc.nearestPtInd_zero
-/

#print MeasureTheory.SimpleFunc.nearestPt_zero /-
@[simp]
theorem nearestPt_zero (e : ℕ → α) : nearestPt e 0 = const α (e 0) :=
  rfl
#align measure_theory.simple_func.nearest_pt_zero MeasureTheory.SimpleFunc.nearestPt_zero
-/

/- warning: measure_theory.simple_func.nearest_pt_ind_succ -> MeasureTheory.SimpleFunc.nearestPtInd_succ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.nearest_pt_ind_succ MeasureTheory.SimpleFunc.nearestPtInd_succₓ'. -/
theorem nearestPtInd_succ (e : ℕ → α) (N : ℕ) (x : α) :
    nearestPtInd e (N + 1) x =
      if ∀ k ≤ N, edist (e (N + 1)) x < edist (e k) x then N + 1 else nearestPtInd e N x :=
  by simp only [nearest_pt_ind, coe_piecewise, Set.piecewise]; congr ; simp
#align measure_theory.simple_func.nearest_pt_ind_succ MeasureTheory.SimpleFunc.nearestPtInd_succ

#print MeasureTheory.SimpleFunc.nearestPtInd_le /-
theorem nearestPtInd_le (e : ℕ → α) (N : ℕ) (x : α) : nearestPtInd e N x ≤ N :=
  by
  induction' N with N ihN; · simp
  simp only [nearest_pt_ind_succ]
  split_ifs
  exacts[le_rfl, ihN.trans N.le_succ]
#align measure_theory.simple_func.nearest_pt_ind_le MeasureTheory.SimpleFunc.nearestPtInd_le
-/

/- warning: measure_theory.simple_func.edist_nearest_pt_le -> MeasureTheory.SimpleFunc.edist_nearestPt_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u1} α] [_inst_3 : OpensMeasurableSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_2)) _inst_1] (e : Nat -> α) (x : α) {k : Nat} {N : Nat}, (LE.le.{0} Nat Nat.hasLe k N) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_2) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, u1} α _inst_1 α) (fun (_x : MeasureTheory.SimpleFunc.{u1, u1} α _inst_1 α) => α -> α) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u1} α α _inst_1) (MeasureTheory.SimpleFunc.nearestPt.{u1} α _inst_1 _inst_2 _inst_3 e N) x) x) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_2) (e k) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u1} α] [_inst_3 : OpensMeasurableSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_2)) _inst_1] (e : Nat -> α) (x : α) {k : Nat} {N : Nat}, (LE.le.{0} Nat instLENat k N) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_2) (MeasureTheory.SimpleFunc.toFun.{u1, u1} α _inst_1 α (MeasureTheory.SimpleFunc.nearestPt.{u1} α _inst_1 _inst_2 _inst_3 e N) x) x) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_2) (e k) x))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.edist_nearest_pt_le MeasureTheory.SimpleFunc.edist_nearestPt_leₓ'. -/
theorem edist_nearestPt_le (e : ℕ → α) (x : α) {k N : ℕ} (hk : k ≤ N) :
    edist (nearestPt e N x) x ≤ edist (e k) x :=
  by
  induction' N with N ihN generalizing k
  · simp [nonpos_iff_eq_zero.1 hk, le_refl]
  · simp only [nearest_pt, nearest_pt_ind_succ, map_apply]
    split_ifs
    · rcases hk.eq_or_lt with (rfl | hk)
      exacts[le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
    · push_neg  at h
      rcases h with ⟨l, hlN, hxl⟩
      rcases hk.eq_or_lt with (rfl | hk)
      exacts[(ihN hlN).trans hxl, ihN (Nat.lt_succ_iff.1 hk)]
#align measure_theory.simple_func.edist_nearest_pt_le MeasureTheory.SimpleFunc.edist_nearestPt_le

#print MeasureTheory.SimpleFunc.tendsto_nearestPt /-
theorem tendsto_nearestPt {e : ℕ → α} {x : α} (hx : x ∈ closure (range e)) :
    Tendsto (fun N => nearestPt e N x) atTop (𝓝 x) :=
  by
  refine' (at_top_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => _
  rcases EMetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  rw [edist_comm] at hN
  exact ⟨N, trivial, fun n hn => (edist_nearest_pt_le e x hn).trans_lt hN⟩
#align measure_theory.simple_func.tendsto_nearest_pt MeasureTheory.SimpleFunc.tendsto_nearestPt
-/

variable [MeasurableSpace β] {f : β → α}

#print MeasureTheory.SimpleFunc.approxOn /-
/-- Approximate a measurable function by a sequence of simple functions `F n` such that
`F n x ∈ s`. -/
noncomputable def approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) : β →ₛ α :=
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  comp (nearest_pt (fun k => Nat.casesOn k y₀ (coe ∘ dense_seq s) : ℕ → α) n) f hf
#align measure_theory.simple_func.approx_on MeasureTheory.SimpleFunc.approxOn
-/

#print MeasureTheory.SimpleFunc.approxOn_zero /-
@[simp]
theorem approxOn_zero {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) : approxOn f hf s y₀ h₀ 0 x = y₀ :=
  rfl
#align measure_theory.simple_func.approx_on_zero MeasureTheory.SimpleFunc.approxOn_zero
-/

#print MeasureTheory.SimpleFunc.approxOn_mem /-
theorem approxOn_mem {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) (x : β) : approxOn f hf s y₀ h₀ n x ∈ s :=
  by
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  suffices ∀ n, (Nat.casesOn n y₀ (coe ∘ dense_seq s) : α) ∈ s by apply this
  rintro (_ | n)
  exacts[h₀, Subtype.mem _]
#align measure_theory.simple_func.approx_on_mem MeasureTheory.SimpleFunc.approxOn_mem
-/

#print MeasureTheory.SimpleFunc.approxOn_comp /-
@[simp]
theorem approxOn_comp {γ : Type _} [MeasurableSpace γ] {f : β → α} (hf : Measurable f) {g : γ → β}
    (hg : Measurable g) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) :
    approxOn (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approxOn f hf s y₀ h₀ n).comp g hg :=
  rfl
#align measure_theory.simple_func.approx_on_comp MeasureTheory.SimpleFunc.approxOn_comp
-/

#print MeasureTheory.SimpleFunc.tendsto_approxOn /-
theorem tendsto_approxOn {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] {x : β} (hx : f x ∈ closure s) :
    Tendsto (fun n => approxOn f hf s y₀ h₀ n x) atTop (𝓝 <| f x) :=
  by
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  rw [← @Subtype.range_coe _ s, ← image_univ, ← (dense_range_dense_seq s).closure_eq] at hx
  simp only [approx_on, coe_comp]
  refine' tendsto_nearest_pt (closure_minimal _ isClosed_closure hx)
  simp only [Nat.range_casesOn, closure_union, range_comp coe]
  exact
    subset.trans (image_closure_subset_closure_image continuous_subtype_val)
      (subset_union_right _ _)
#align measure_theory.simple_func.tendsto_approx_on MeasureTheory.SimpleFunc.tendsto_approxOn
-/

/- warning: measure_theory.simple_func.edist_approx_on_mono -> MeasureTheory.SimpleFunc.edist_approxOn_mono is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.edist_approx_on_mono MeasureTheory.SimpleFunc.edist_approxOn_monoₓ'. -/
theorem edist_approxOn_mono {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) {m n : ℕ} (h : m ≤ n) :
    edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist (approxOn f hf s y₀ h₀ m x) (f x) :=
  by
  dsimp only [approx_on, coe_comp, (· ∘ ·)]
  exact edist_nearest_pt_le _ _ ((nearest_pt_ind_le _ _ _).trans h)
#align measure_theory.simple_func.edist_approx_on_mono MeasureTheory.SimpleFunc.edist_approxOn_mono

/- warning: measure_theory.simple_func.edist_approx_on_le -> MeasureTheory.SimpleFunc.edist_approxOn_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.edist_approx_on_le MeasureTheory.SimpleFunc.edist_approxOn_leₓ'. -/
theorem edist_approxOn_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) : edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
  edist_approxOn_mono hf h₀ x (zero_le n)
#align measure_theory.simple_func.edist_approx_on_le MeasureTheory.SimpleFunc.edist_approxOn_le

/- warning: measure_theory.simple_func.edist_approx_on_y0_le -> MeasureTheory.SimpleFunc.edist_approxOn_y0_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.edist_approx_on_y0_le MeasureTheory.SimpleFunc.edist_approxOn_y0_leₓ'. -/
theorem edist_approxOn_y0_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) :
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
  calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤
        edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ ≤ edist y₀ (f x) + edist y₀ (f x) := add_le_add_left (edist_approxOn_le hf h₀ x n) _
    
#align measure_theory.simple_func.edist_approx_on_y0_le MeasureTheory.SimpleFunc.edist_approxOn_y0_le

end SimpleFunc

end MeasureTheory

