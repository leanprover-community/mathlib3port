/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Topology.MetricSpace.Baire
import Mathbin.Topology.Algebra.Module.Basic

/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

Herein we prove the Banach-Steinhaus theorem: any collection of bounded linear maps
from a Banach space into a normed space which is pointwise bounded is uniformly bounded.

## TODO

For now, we only prove the standard version by appeal to the Baire category theorem.
Much more general versions exist (in particular, for maps from barrelled spaces to locally
convex spaces), but these are not yet in `mathlib`.
-/


open Set

variable {E F ð ðâ : Type _} [SemiNormedGroup E] [SemiNormedGroup F] [NondiscreteNormedField ð]
  [NondiscreteNormedField ðâ] [NormedSpace ð E] [NormedSpace ðâ F] {Ïââ : ð â+* ðâ} [RingHomIsometric Ïââ]

/-- This is the standard Banach-Steinhaus theorem, or Uniform Boundedness Principle.
If a family of continuous linear maps from a Banach space into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded. -/
theorem banach_steinhaus {Î¹ : Type _} [CompleteSpace E] {g : Î¹ â E âSL[Ïââ] F} (h : â x, â C, â i, â¥g i xâ¥ â¤ C) :
    â C', â i, â¥g iâ¥ â¤ C' := by
  -- sequence of subsets consisting of those `x : E` with norms `â¥g i xâ¥` bounded by `n`
  let e : â â Set E := fun n => â i : Î¹, { x : E | â¥g i xâ¥ â¤ n }
  -- each of these sets is closed
  have hc : â n : â, IsClosed (e n) := fun i =>
    is_closed_Inter fun i => is_closed_le (Continuous.norm (g i).cont) continuous_const
  -- the union is the entire space; this is where we use `h`
  have hU : (â n : â, e n) = univ := by
    refine' eq_univ_of_forall fun x => _
    cases' h x with C hC
    obtain â¨m, hmâ© := exists_nat_ge C
    exact â¨e m, mem_range_self m, mem_Inter.mpr fun i => le_transâ (hC i) hmâ©
  -- apply the Baire category theorem to conclude that for some `m : â`, `e m` contains some `x`
  rcases nonempty_interior_of_Union_of_closed hc hU with â¨m, x, hxâ©
  rcases metric.is_open_iff.mp is_open_interior x hx with â¨Îµ, Îµ_pos, hÎµâ©
  obtain â¨k, hkâ© := NormedField.exists_one_lt_norm ð
  -- show all elements in the ball have norm bounded by `m` after applying any `g i`
  have real_norm_le : â z : E, z â Metric.Ball x Îµ â â i : Î¹, â¥g i zâ¥ â¤ m := by
    intro z hz i
    replace hz := mem_Inter.mp (interior_Inter_subset _ (hÎµ hz)) i
    apply interior_subset hz
  have Îµk_pos : 0 < Îµ / â¥kâ¥ := div_pos Îµ_pos (zero_lt_one.trans hk)
  refine' â¨(m + m : â) / (Îµ / â¥kâ¥), fun i => ContinuousLinearMap.op_norm_le_of_shell Îµ_pos _ hk _â©
  Â· exact div_nonneg (Nat.cast_nonneg _) Îµk_pos.le
    
  intro y le_y y_lt
  calc â¥g i yâ¥ = â¥g i (y + x) - g i xâ¥ := by
      rw [ContinuousLinearMap.map_add, add_sub_cancel]_ â¤ â¥g i (y + x)â¥ + â¥g i xâ¥ := norm_sub_le _ _ _ â¤ m + m :=
      add_le_add
        (real_norm_le (y + x)
          (by
            rwa [add_commâ, add_mem_ball_iff_norm])
          i)
        (real_norm_le x (Metric.mem_ball_self Îµ_pos) i)_ = (m + m : â) :=
      (m.cast_add m).symm _ â¤ (m + m : â) * (â¥yâ¥ / (Îµ / â¥kâ¥)) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _)
        ((one_le_div <| div_pos Îµ_pos (zero_lt_one.trans hk)).2 le_y)_ = (m + m : â) / (Îµ / â¥kâ¥) * â¥yâ¥ :=
      (mul_comm_div _ _ _).symm

open Ennreal

open Ennreal

/-- This version of Banach-Steinhaus is stated in terms of suprema of `ââ¥â¬â¥â : ââ¥0â`
for convenience. -/
theorem banach_steinhaus_supr_nnnorm {Î¹ : Type _} [CompleteSpace E] {g : Î¹ â E âSL[Ïââ] F}
    (h : â x, (â¨ i, ââ¥g i xâ¥â) < â) : (â¨ i, ââ¥g iâ¥â) < â := by
  have h' : â x : E, â C : â, â i : Î¹, â¥g i xâ¥ â¤ C := by
    intro x
    rcases lt_iff_exists_coe.mp (h x) with â¨p, hpâ, _â©
    refine' â¨p, fun i => _â©
    exact_mod_cast
      calc
        (â¥g i xâ¥â : ââ¥0â) â¤ â¨ j, â¥g j xâ¥â := le_supr _ i
        _ = p := hpâ
        
  cases' banach_steinhaus h' with C' hC'
  refine' (supr_le fun i => _).trans_lt (@coe_lt_top C'.to_nnreal)
  rw [â norm_to_nnreal]
  exact coe_mono (Real.to_nnreal_le_to_nnreal <| hC' i)

open TopologicalSpace

open Filter

/-- Given a *sequence* of continuous linear maps which converges pointwise and for which the
domain is complete, the Banach-Steinhaus theorem is used to guarantee that the limit map
is a *continuous* linear map as well. -/
def continuousLinearMapOfTendsto [CompleteSpace E] [T2Space F] (g : â â E âSL[Ïââ] F) {f : E â F}
    (h : Tendsto (fun n x => g n x) atTop (ð f)) : E âSL[Ïââ] F where
  toFun := f
  map_add' := (linearMapOfTendsto _ _ h).map_add'
  map_smul' := (linearMapOfTendsto _ _ h).map_smul'
  cont := by
    -- show that the maps are pointwise bounded and apply `banach_steinhaus`
    have h_point_bdd : â x : E, â C : â, â n : â, â¥g n xâ¥ â¤ C := by
      intro x
      rcases cauchy_seq_bdd (tendsto_pi_nhds.mp h x).CauchySeq with â¨C, C_pos, hCâ©
      refine' â¨C + â¥g 0 xâ¥, fun n => _â©
      simp_rw [dist_eq_norm] at hC
      calc â¥g n xâ¥ â¤ â¥g 0 xâ¥ + â¥g n x - g 0 xâ¥ := norm_le_insert' _ _ _ â¤ C + â¥g 0 xâ¥ := by
          linarith [hC n 0]
    cases' banach_steinhaus h_point_bdd with C' hC'
    /- show the uniform bound from `banach_steinhaus` is a norm bound of the limit map
             by allowing "an `Îµ` of room." -/
    refine'
      AddMonoidHomClass.continuous_of_bound (linearMapOfTendsto _ _ h) C' fun x =>
        le_of_forall_pos_lt_add fun Îµ Îµ_pos => _
    cases' metric.tendsto_at_top.mp (tendsto_pi_nhds.mp h x) Îµ Îµ_pos with n hn
    have lt_Îµ : â¥g n x - f xâ¥ < Îµ := by
      rw [â dist_eq_norm]
      exact hn n (le_reflâ n)
    calc â¥f xâ¥ â¤ â¥g n xâ¥ + â¥g n x - f xâ¥ := norm_le_insert _ _ _ < â¥g nâ¥ * â¥xâ¥ + Îµ := by
        linarith [lt_Îµ, (g n).le_op_norm x]_ â¤ C' * â¥xâ¥ + Îµ := by
        nlinarith [hC' n, norm_nonneg x]

