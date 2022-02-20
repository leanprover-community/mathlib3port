/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.BoxIntegral.Box.Basic
import Mathbin.Analysis.SpecificLimits

/-!
# Induction on subboxes

In this file we prove the following induction principle for `box_integral.box`, see
`box_integral.box.subbox_induction_on`. Let `p` be a predicate on `box_integral.box ι`, let `I` be a
box. Suppose that the following two properties hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it is true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true.

## Tags

rectangular box, induction
-/


open Set Finset Function Filter Metric

open_locale Classical TopologicalSpace Filter Ennreal

noncomputable section

namespace BoxIntegral

namespace Box

variable {ι : Type _} {I J : Box ι}

/-- For a box `I`, the hyperplanes passing through its center split `I` into `2 ^ card ι` boxes.
`box_integral.box.split_center_box I s` is one of these boxes. See also
`box_integral.partition.split_center` for the corresponding `box_integral.partition`. -/
def splitCenterBox (I : Box ι) (s : Set ι) : Box ι where
  lower := s.piecewise (fun i => (I.lower i + I.upper i) / 2) I.lower
  upper := s.piecewise I.upper fun i => (I.lower i + I.upper i) / 2
  lower_lt_upper := fun i => by
    dunfold Set.piecewise
    split_ifs <;> simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper]

theorem mem_split_center_box {s : Set ι} {y : ι → ℝ} :
    y ∈ I.splitCenterBox s ↔ y ∈ I ∧ ∀ i, (I.lower i + I.upper i) / 2 < y i ↔ i ∈ s := by
  simp only [split_center_box, mem_def, ← forall_and_distrib]
  refine' forall_congrₓ fun i => _
  dunfold Set.piecewise
  split_ifs with hs <;> simp only [hs, iff_trueₓ, iff_falseₓ, not_ltₓ]
  exacts[⟨fun H => ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩, fun H => ⟨H.2, H.1.2⟩⟩,
    ⟨fun H => ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩, fun H => ⟨H.1.1, H.2⟩⟩]

theorem split_center_box_le (I : Box ι) (s : Set ι) : I.splitCenterBox s ≤ I := fun x hx =>
  (mem_split_center_box.1 hx).1

theorem disjoint_split_center_box (I : Box ι) {s t : Set ι} (h : s ≠ t) :
    Disjoint (I.splitCenterBox s : Set (ι → ℝ)) (I.splitCenterBox t) := by
  rintro y ⟨hs, ht⟩
  apply h
  ext i
  rw [mem_coe, mem_split_center_box] at hs ht
  rw [← hs.2, ← ht.2]

theorem injective_split_center_box (I : Box ι) : Injective I.splitCenterBox := fun s t H =>
  by_contra fun Hne => (I.disjoint_split_center_box Hne).Ne (nonempty_coe _).ne_empty (H ▸ rfl)

@[simp]
theorem exists_mem_split_center_box {I : Box ι} {x : ι → ℝ} : (∃ s, x ∈ I.splitCenterBox s) ↔ x ∈ I :=
  ⟨fun ⟨s, hs⟩ => I.split_center_box_le s hs, fun hx =>
    ⟨{ i | (I.lower i + I.upper i) / 2 < x i }, mem_split_center_box.2 ⟨hx, fun i => Iff.rfl⟩⟩⟩

/-- `box_integral.box.split_center_box` bundled as a `function.embedding`. -/
@[simps]
def splitCenterBoxEmb (I : Box ι) : Set ι ↪ Box ι :=
  ⟨splitCenterBox I, injective_split_center_box I⟩

@[simp]
theorem Union_coe_split_center_box (I : Box ι) : (⋃ s, (I.splitCenterBox s : Set (ι → ℝ))) = I := by
  ext x
  simp

@[simp]
theorem upper_sub_lower_split_center_box (I : Box ι) (s : Set ι) (i : ι) :
    (I.splitCenterBox s).upper i - (I.splitCenterBox s).lower i = (I.upper i - I.lower i) / 2 := by
  by_cases' hs : i ∈ s <;> field_simp [split_center_box, hs, mul_two, two_mul]

/-- Let `p` be a predicate on `box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* `H_ind` : Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split
  it into `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.

* `H_nhds` : For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within
  `I.Icc` such that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I`
  with a coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `box_integral.box.subbox_induction_on` for a version using
`box_integral.prepartition.split_center` instead of `box_integral.box.split_center_box`.

The proof still works if we assume `H_ind` only for subboxes `J ≤ I` that are homothetic to `I` with
a coefficient of the form `2⁻ᵐ` but we do not need this generalization yet. -/
@[elab_as_eliminator]
theorem subbox_induction_on' {p : Box ι → Prop} (I : Box ι) (H_ind : ∀, ∀ J ≤ I, ∀, (∀ s, p (splitCenterBox J s)) → p J)
    (H_nhds :
      ∀,
        ∀ z ∈ I.Icc,
          ∀,
            ∃ U ∈ 𝓝[I.Icc] z,
              ∀,
                ∀ J ≤ I,
                  ∀ m : ℕ,
                    z ∈ J.Icc → J.Icc ⊆ U → (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) → p J) :
    p I := by
  by_contra hpI
  -- First we use `H_ind` to construct a decreasing sequence of boxes such that `∀ m, ¬p (J m)`.
  replace H_ind := fun J hJ => not_imp_not.2 (H_ind J hJ)
  simp only [exists_imp_distrib, not_forall] at H_ind
  choose! s hs using H_ind
  set J : ℕ → box ι := fun m => ((fun J => split_center_box J (s J))^[m]) I
  have J_succ : ∀ m, J (m + 1) = split_center_box (J m) (s <| J m) := fun m => iterate_succ_apply' _ _ _
  -- Now we prove some properties of `J`
  have hJmono : Antitone J :=
    antitone_nat_of_succ_le fun n => by
      simpa [J_succ] using split_center_box_le _ _
  have hJle : ∀ m, J m ≤ I := fun m => hJmono (zero_le m)
  have hJp : ∀ m, ¬p (J m) := fun m =>
    Nat.recOn m hpI fun m => by
      simpa only [J_succ] using hs (J m) (hJle m)
  have hJsub : ∀ m i, (J m).upper i - (J m).lower i = (I.upper i - I.lower i) / 2 ^ m := by
    intro m i
    induction' m with m ihm
    · simp [J]
      
    simp only [pow_succ'ₓ, J_succ, upper_sub_lower_split_center_box, ihm, div_div_eq_div_mul]
  have h0 : J 0 = I := rfl
  -- Now we clear unneeded assumptions
  clear_value J
  clear hpI hs J_succ s
  -- Let `z` be the unique common point of all `(J m).Icc`. Then `H_nhds` proves `p (J m)` for
  -- sufficiently large `m`. This contradicts `hJp`.
  set z : ι → ℝ := ⨆ m, (J m).lower
  have hzJ : ∀ m, z ∈ (J m).Icc :=
    mem_Inter.1
      (csupr_mem_Inter_Icc_of_antitone_Icc ((@box.Icc ι).Monotone.comp_antitone hJmono) fun m => (J m).lower_le_upper)
  have hJl_mem : ∀ m, (J m).lower ∈ I.Icc := fun m => le_iff_Icc.1 (hJle m) (J m).lower_mem_Icc
  have hJu_mem : ∀ m, (J m).upper ∈ I.Icc := fun m => le_iff_Icc.1 (hJle m) (J m).upper_mem_Icc
  have hJlz : tendsto (fun m => (J m).lower) at_top (𝓝 z) :=
    tendsto_at_top_csupr (antitone_lower.comp hJmono) ⟨I.upper, fun x ⟨m, hm⟩ => hm ▸ (hJl_mem m).2⟩
  have hJuz : tendsto (fun m => (J m).upper) at_top (𝓝 z) := by
    suffices tendsto (fun m => (J m).upper - (J m).lower) at_top (𝓝 0) by
      simpa using hJlz.add this
    refine' tendsto_pi_nhds.2 fun i => _
    simpa [hJsub] using tendsto_const_nhds.div_at_top (tendsto_pow_at_top_at_top_of_one_lt (@one_lt_two ℝ _ _))
  replace hJlz : tendsto (fun m => (J m).lower) at_top (𝓝[Icc I.lower I.upper] z)
  exact tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ hJlz (eventually_of_forall hJl_mem)
  replace hJuz : tendsto (fun m => (J m).upper) at_top (𝓝[Icc I.lower I.upper] z)
  exact tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ hJuz (eventually_of_forall hJu_mem)
  rcases H_nhds z (h0 ▸ hzJ 0) with ⟨U, hUz, hU⟩
  rcases(tendsto_lift'.1 (hJlz.Icc hJuz) U hUz).exists with ⟨m, hUm⟩
  exact hJp m (hU (J m) (hJle m) m (hzJ m) hUm (hJsub m))

end Box

end BoxIntegral

