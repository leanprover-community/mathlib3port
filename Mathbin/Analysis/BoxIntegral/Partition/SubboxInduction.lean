import Mathbin.Analysis.BoxIntegral.Box.SubboxInduction 
import Mathbin.Analysis.BoxIntegral.Partition.Tagged

/-!
# Induction on subboxes

In this file we prove (see
`box_integral.tagged_partition.exists_is_Henstock_is_subordinate_homothetic`) that for every box `I`
in `ℝⁿ` and a function `r : ℝⁿ → ℝ` positive on `I` there exists a tagged partition `π` of `I` such
that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ n`.

Later we will use this lemma to prove that the Henstock filter is nontrivial, hence the Henstock
integral is well-defined.

## Tags

partition, tagged partition, Henstock integral
-/


namespace BoxIntegral

open Set Metric

open_locale Classical TopologicalSpace

noncomputable theory

variable{ι : Type _}[Fintype ι]{I J : box ι}

namespace Prepartition

/-- Split a box in `ℝⁿ` into `2 ^ n` boxes by hyperplanes passing through its center. -/
def split_center (I : box ι) : prepartition I :=
  { boxes := Finset.univ.map (box.split_center_box_emb I),
    le_of_mem' :=
      by 
        simp [I.split_center_box_le],
    PairwiseDisjoint :=
      by 
        rw [Finset.coe_map, Finset.coe_univ, image_univ]
        rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne 
        exact I.disjoint_split_center_box (mt (congr_argₓ _) Hne) }

@[simp]
theorem mem_split_center : J ∈ split_center I ↔ ∃ s, I.split_center_box s = J :=
  by 
    simp [split_center]

theorem is_partition_split_center (I : box ι) : is_partition (split_center I) :=
  fun x hx =>
    by 
      simp [hx]

theorem upper_sub_lower_of_mem_split_center (h : J ∈ split_center I) (i : ι) :
  J.upper i - J.lower i = (I.upper i - I.lower i) / 2 :=
  let ⟨s, hs⟩ := mem_split_center.1 h 
  hs ▸ I.upper_sub_lower_split_center_box s i

end Prepartition

namespace Box

open Prepartition TaggedPrepartition

/-- Let `p` be a predicate on `box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `box_integral.box.subbox_induction_on'` for a version using
`box_integral.box.split_center_box` instead of `box_integral.prepartition.split_center`. -/
@[elab_as_eliminator]
theorem subbox_induction_on {p : box ι → Prop} (I : box ι)
  (H_ind : ∀ J (_ : J ≤ I), (∀ J' (_ : J' ∈ split_center J), p J') → p J)
  (H_nhds :
    ∀ z (_ : z ∈ I.Icc),
      ∃ (U : _)(_ : U ∈ 𝓝[I.Icc] z),
        ∀ J (_ : J ≤ I) (m : ℕ),
          z ∈ J.Icc → J.Icc ⊆ U → (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) → p J) :
  p I :=
  by 
    refine' subbox_induction_on' I (fun J hle hs => H_ind J hle$ fun J' h' => _) H_nhds 
    rcases mem_split_center.1 h' with ⟨s, rfl⟩
    exact hs s

-- error in Analysis.BoxIntegral.Partition.SubboxInduction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a box `I` in `ℝⁿ` and a function `r : ℝⁿ → (0, ∞)`, there exists a tagged partition `π` of
`I` such that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ m`.

This lemma implies that the Henstock filter is nontrivial, hence the Henstock integral is
well-defined. -/
theorem exists_tagged_partition_is_Henstock_is_subordinate_homothetic
(I : box ι)
(r : (ι → exprℝ()) → Ioi (0 : exprℝ())) : «expr∃ , »((π : tagged_prepartition I), «expr ∧ »(π.is_partition, «expr ∧ »(π.is_Henstock, «expr ∧ »(π.is_subordinate r, «expr ∧ »(∀
     J «expr ∈ » π, «expr∃ , »((m : exprℕ()), ∀
      i, «expr = »(«expr - »((J : _).upper i, J.lower i), «expr / »(«expr - »(I.upper i, I.lower i), «expr ^ »(2, m)))), «expr = »(π.distortion, I.distortion)))))) :=
begin
  refine [expr subbox_induction_on I (λ J hle hJ, _) (λ z hz, _)],
  { choose ["!"] [ident πi] [ident hP, ident hHen, ident hr, ident Hn, ident Hd] ["using", expr hJ],
    choose ["!"] [ident n] [ident hn] ["using", expr Hn],
    have [ident hP] [":", expr ((split_center J).bUnion_tagged πi).is_partition] [],
    from [expr (is_partition_split_center _).bUnion_tagged hP],
    have [ident hsub] [":", expr ∀
     J' «expr ∈ » (split_center J).bUnion_tagged πi, «expr∃ , »((n : exprℕ()), ∀
      i, «expr = »(«expr - »((J' : _).upper i, J'.lower i), «expr / »(«expr - »(J.upper i, J.lower i), «expr ^ »(2, n))))] [],
    { intros [ident J', ident hJ'],
      rcases [expr (split_center J).mem_bUnion_tagged.1 hJ', "with", "⟨", ident J₁, ",", ident h₁, ",", ident h₂, "⟩"],
      refine [expr ⟨«expr + »(n J₁ J', 1), λ i, _⟩],
      simp [] [] ["only"] ["[", expr hn J₁ h₁ J' h₂, ",", expr upper_sub_lower_of_mem_split_center h₁, ",", expr pow_succ, ",", expr div_div_eq_div_mul, "]"] [] [] },
    refine [expr ⟨_, hP, is_Henstock_bUnion_tagged.2 hHen, is_subordinate_bUnion_tagged.2 hr, hsub, _⟩],
    refine [expr tagged_prepartition.distortion_of_const _ hP.nonempty_boxes (λ J' h', _)],
    rcases [expr hsub J' h', "with", "⟨", ident n, ",", ident hn, "⟩"],
    exact [expr box.distortion_eq_of_sub_eq_div hn] },
  { refine [expr ⟨«expr ∩ »(I.Icc, closed_ball z (r z)), inter_mem_nhds_within _ (closed_ball_mem_nhds _ (r z).coe_prop), _⟩],
    intros [ident J, ident Hle, ident n, ident Hmem, ident HIcc, ident Hsub],
    rw [expr set.subset_inter_iff] ["at", ident HIcc],
    refine [expr ⟨single _ _ le_rfl _ Hmem, is_partition_single _, is_Henstock_single _, (is_subordinate_single _ _).2 HIcc.2, _, distortion_single _ _⟩],
    simp [] [] ["only"] ["[", expr tagged_prepartition.mem_single, ",", expr forall_eq, "]"] [] [],
    refine [expr ⟨0, λ i, _⟩],
    simp [] [] [] [] [] [] }
end

end Box

namespace Prepartition

open TaggedPrepartition Finset Function

-- error in Analysis.BoxIntegral.Partition.SubboxInduction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a box `I` in `ℝⁿ`, a function `r : ℝⁿ → (0, ∞)`, and a prepartition `π` of `I`, there
exists a tagged prepartition `π'` of `I` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
theorem exists_tagged_le_is_Henstock_is_subordinate_Union_eq
{I : box ι}
(r : (ι → exprℝ()) → Ioi (0 : exprℝ()))
(π : prepartition I) : «expr∃ , »((π' : tagged_prepartition I), «expr ∧ »(«expr ≤ »(π'.to_prepartition, π), «expr ∧ »(π'.is_Henstock, «expr ∧ »(π'.is_subordinate r, «expr ∧ »(«expr = »(π'.distortion, π.distortion), «expr = »(π'.Union, π.Union)))))) :=
begin
  have [] [] [":=", expr λ J, box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic J r],
  choose ["!"] [ident πi] [ident πip, ident πiH, ident πir, ident hsub, ident πid] [],
  clear [ident hsub],
  refine [expr ⟨π.bUnion_tagged πi, bUnion_le _ _, is_Henstock_bUnion_tagged.2 (λ
     J _, πiH J), is_subordinate_bUnion_tagged.2 (λ J _, πir J), _, π.Union_bUnion_partition (λ J _, πip J)⟩],
  rw ["[", expr distortion_bUnion_tagged, "]"] [],
  exact [expr sup_congr rfl (λ J _, πid J)]
end

/-- Given a prepartition `π` of a box `I` and a function `r : ℝⁿ → (0, ∞)`, `π.to_subordinate r`
is a tagged partition `π'` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
def to_subordinate (π : prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : tagged_prepartition I :=
  (π.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r).some

theorem to_subordinate_to_prepartition_le (π : prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
  (π.to_subordinate r).toPrepartition ≤ π :=
  (π.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r).some_spec.1

theorem is_Henstock_to_subordinate (π : prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : (π.to_subordinate r).IsHenstock :=
  (π.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r).some_spec.2.1

theorem is_subordinate_to_subordinate (π : prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
  (π.to_subordinate r).IsSubordinate r :=
  (π.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r).some_spec.2.2.1

@[simp]
theorem distortion_to_subordinate (π : prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
  (π.to_subordinate r).distortion = π.distortion :=
  (π.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r).some_spec.2.2.2.1

@[simp]
theorem Union_to_subordinate (π : prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : (π.to_subordinate r).Union = π.Union :=
  (π.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r).some_spec.2.2.2.2

end Prepartition

namespace TaggedPrepartition

/-- Given a tagged prepartition `π₁`, a prepartition `π₂` that covers exactly `I \ π₁.Union`, and
a function `r : ℝⁿ → (0, ∞)`, returns the union of `π₁` and `π₂.to_subordinate r`. This partition
`π` has the following properties:

* `π` is a partition, i.e. it covers the whole `I`;
* `π₁.boxes ⊆ π.boxes`;
* `π.tag J = π₁.tag J` whenever `J ∈ π₁`;
* `π` is Henstock outside of `π₁`: `π.tag J ∈ J.Icc` whenever `J ∈ π`, `J ∉ π₁`;
* `π` is subordinate to `r` outside of `π₁`;
* the distortion of `π` is equal to the maximum of the distortions of `π₁` and `π₂`.
-/
def union_compl_to_subordinate (π₁ : tagged_prepartition I) (π₂ : prepartition I) (hU : π₂.Union = I \ π₁.Union)
  (r : (ι → ℝ) → Ioi (0 : ℝ)) : tagged_prepartition I :=
  π₁.disj_union (π₂.to_subordinate r) (((π₂.Union_to_subordinate r).trans hU).symm ▸ disjoint_diff)

theorem is_partition_union_compl_to_subordinate (π₁ : tagged_prepartition I) (π₂ : prepartition I)
  (hU : π₂.Union = I \ π₁.Union) (r : (ι → ℝ) → Ioi (0 : ℝ)) : is_partition (π₁.union_compl_to_subordinate π₂ hU r) :=
  prepartition.is_partition_disj_union_of_eq_diff ((π₂.Union_to_subordinate r).trans hU)

@[simp]
theorem union_compl_to_subordinate_boxes (π₁ : tagged_prepartition I) (π₂ : prepartition I)
  (hU : π₂.Union = I \ π₁.Union) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
  (π₁.union_compl_to_subordinate π₂ hU r).boxes = π₁.boxes ∪ (π₂.to_subordinate r).boxes :=
  rfl

@[simp]
theorem Union_union_compl_to_subordinate_boxes (π₁ : tagged_prepartition I) (π₂ : prepartition I)
  (hU : π₂.Union = I \ π₁.Union) (r : (ι → ℝ) → Ioi (0 : ℝ)) : (π₁.union_compl_to_subordinate π₂ hU r).Union = I :=
  (is_partition_union_compl_to_subordinate _ _ _ _).Union_eq

@[simp]
theorem distortion_union_compl_to_subordinate (π₁ : tagged_prepartition I) (π₂ : prepartition I)
  (hU : π₂.Union = I \ π₁.Union) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
  (π₁.union_compl_to_subordinate π₂ hU r).distortion = max π₁.distortion π₂.distortion :=
  by 
    simp [union_compl_to_subordinate]

end TaggedPrepartition

end BoxIntegral

