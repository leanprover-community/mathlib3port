import Mathbin.Analysis.BoxIntegral.Partition.Basic

/-!
# Tagged partitions

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
‵π`. For simplicity we require that the function `box_integral.tagged_prepartition.tag` is defined
on all boxes `J : box ι` but use its values only on boxes of the partition. Given `π :
box_integral.tagged_partition I`, we require that each `box_integral.tagged_partition π J` belongs
to `box_integral.box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is called
a *Henstock* partition. We do not include this assumption into the definition of a tagged
(pre)partition because McShane integral is defined as a limit along tagged partitions without this
requirement.

### Tags

rectangular box, box partition
-/


noncomputable section 

open_locale Classical Ennreal Nnreal

open Set Function

namespace BoxIntegral

variable {ι : Type _}

/-- A tagged prepartition is a prepartition enriched with a tagged point for each box of the
prepartition. For simiplicity we require that `tag` is defined for all boxes in `ι → ℝ` but
we will use onle the values of `tag` on the boxes of the partition. -/
structure tagged_prepartition (I : box ι) extends prepartition I where 
  Tag : box ι → ι → ℝ 
  tag_mem_Icc : ∀ J, tag J ∈ I.Icc

namespace TaggedPrepartition

variable {I J J₁ J₂ : box ι} (π : tagged_prepartition I) {x : ι → ℝ}

instance : HasMem (box ι) (tagged_prepartition I) :=
  ⟨fun J π => J ∈ π.boxes⟩

@[simp]
theorem mem_to_prepartition {π : tagged_prepartition I} : J ∈ π.to_prepartition ↔ J ∈ π :=
  Iff.rfl

@[simp]
theorem mem_mk (π : prepartition I) f h : J ∈ mk π f h ↔ J ∈ π :=
  Iff.rfl

/-- Union of all boxes of a tagged prepartition. -/
def Union : Set (ι → ℝ) :=
  π.to_prepartition.Union

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
theorem Union_def : π.Union = ⋃ (J : _)(_ : J ∈ π), ↑J :=
  rfl

@[simp]
theorem Union_mk (π : prepartition I) f h : (mk π f h).Union = π.Union :=
  rfl

@[simp]
theorem Union_to_prepartition : π.to_prepartition.Union = π.Union :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
@[simp]
theorem mem_Union : x ∈ π.Union ↔ ∃ (J : _)(_ : J ∈ π), x ∈ J :=
  Set.mem_bUnion_iff

theorem subset_Union (h : J ∈ π) : ↑J ⊆ π.Union :=
  subset_bUnion_of_mem h

theorem Union_subset : π.Union ⊆ I :=
  bUnion_subset π.le_of_mem'

/-- A tagged prepartition is a partition if it covers the whole box. -/
def is_partition :=
  π.to_prepartition.is_partition

theorem is_partition_iff_Union_eq : is_partition π ↔ π.Union = I :=
  prepartition.is_partition_iff_Union_eq

/-- The tagged partition made of boxes of `π` that satisfy predicate `p`. -/
@[simps (config := { fullyApplied := ff })]
def Filter (p : box ι → Prop) : tagged_prepartition I :=
  ⟨π.1.filter p, π.2, π.3⟩

@[simp]
theorem mem_filter {p : box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J :=
  Finset.mem_filter

@[simp]
theorem Union_filter_not (π : tagged_prepartition I) (p : box ι → Prop) :
  (π.filter fun J => ¬p J).Union = π.Union \ (π.filter p).Union :=
  π.to_prepartition.Union_filter_not p

end TaggedPrepartition

namespace Prepartition

variable {I J : box ι}

/-- Given a partition `π` of `I : box_integral.box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
def bUnion_tagged (π : prepartition I) (πi : ∀ J, tagged_prepartition J) : tagged_prepartition I :=
  { toPrepartition := π.bUnion fun J => (πi J).toPrepartition,
    Tag := fun J => (πi (π.bUnion_index (fun J => (πi J).toPrepartition) J)).Tag J,
    tag_mem_Icc := fun J => box.le_iff_Icc.1 (π.bUnion_index_le _ _) ((πi _).tag_mem_Icc _) }

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J' «expr ∈ » π)
@[simp]
theorem mem_bUnion_tagged (π : prepartition I) {πi : ∀ J, tagged_prepartition J} :
  J ∈ π.bUnion_tagged πi ↔ ∃ (J' : _)(_ : J' ∈ π), J ∈ πi J' :=
  π.mem_bUnion

theorem tag_bUnion_tagged (π : prepartition I) {πi : ∀ J, tagged_prepartition J} (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J) :
  (π.bUnion_tagged πi).Tag J' = (πi J).Tag J' :=
  by 
    have  : J' ∈ π.bUnion_tagged πi 
    exact π.mem_bUnion.2 ⟨J, hJ, hJ'⟩
    obtain rfl := π.bUnion_index_of_mem hJ hJ' 
    rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
@[simp]
theorem Union_bUnion_tagged (π : prepartition I) (πi : ∀ J, tagged_prepartition J) :
  (π.bUnion_tagged πi).Union = ⋃ (J : _)(_ : J ∈ π), (πi J).Union :=
  Union_bUnion _ _

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π.bUnion_tagged πi)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J' «expr ∈ » πi J)
theorem forall_bUnion_tagged (p : (ι → ℝ) → box ι → Prop) (π : prepartition I) (πi : ∀ J, tagged_prepartition J) :
  (∀ J _ : J ∈ π.bUnion_tagged πi, p ((π.bUnion_tagged πi).Tag J) J) ↔
    ∀ J _ : J ∈ π J' _ : J' ∈ πi J, p ((πi J).Tag J') J' :=
  by 
    simp only [bex_imp_distrib, mem_bUnion_tagged]
    refine' ⟨fun H J hJ J' hJ' => _, fun H J' J hJ hJ' => _⟩
    ·
      rw [←π.tag_bUnion_tagged hJ hJ']
      exact H J' J hJ hJ'
    ·
      rw [π.tag_bUnion_tagged hJ hJ']
      exact H J hJ J' hJ'

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
theorem is_partition.bUnion_tagged {π : prepartition I} (h : is_partition π) {πi : ∀ J, tagged_prepartition J}
  (hi : ∀ J _ : J ∈ π, (πi J).IsPartition) : (π.bUnion_tagged πi).IsPartition :=
  h.bUnion hi

end Prepartition

namespace TaggedPrepartition

variable {I J : box ι} {π π₁ π₂ : tagged_prepartition I} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps (config := { fullyApplied := ff }) Tag]
def bUnion_prepartition (π : tagged_prepartition I) (πi : ∀ J, prepartition J) : tagged_prepartition I :=
  { toPrepartition := π.to_prepartition.bUnion πi, Tag := fun J => π.tag (π.to_prepartition.bUnion_index πi J),
    tag_mem_Icc := fun J => π.tag_mem_Icc _ }

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
theorem is_partition.bUnion_prepartition {π : tagged_prepartition I} (h : is_partition π) {πi : ∀ J, prepartition J}
  (hi : ∀ J _ : J ∈ π, (πi J).IsPartition) : (π.bUnion_prepartition πi).IsPartition :=
  h.bUnion hi

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `to_partition = π₁.to_partition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def inf_prepartition (π : tagged_prepartition I) (π' : prepartition I) : tagged_prepartition I :=
  π.bUnion_prepartition$ fun J => π'.restrict J

@[simp]
theorem inf_prepartition_to_prepartition (π : tagged_prepartition I) (π' : prepartition I) :
  (π.inf_prepartition π').toPrepartition = π.to_prepartition⊓π' :=
  rfl

theorem mem_inf_prepartition_comm :
  J ∈ π₁.inf_prepartition π₂.to_prepartition ↔ J ∈ π₂.inf_prepartition π₁.to_prepartition :=
  by 
    simp only [←mem_to_prepartition, inf_prepartition_to_prepartition, inf_comm]

theorem is_partition.inf_prepartition (h₁ : π₁.is_partition) {π₂ : prepartition I} (h₂ : π₂.is_partition) :
  (π₁.inf_prepartition π₂).IsPartition :=
  h₁.inf h₂

open Metric

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def is_Henstock (π : tagged_prepartition I) : Prop :=
  ∀ J _ : J ∈ π, π.tag J ∈ J.Icc

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
@[simp]
theorem is_Henstock_bUnion_tagged {π : prepartition I} {πi : ∀ J, tagged_prepartition J} :
  is_Henstock (π.bUnion_tagged πi) ↔ ∀ J _ : J ∈ π, (πi J).IsHenstock :=
  π.forall_bUnion_tagged (fun x J => x ∈ J.Icc) πi

/-- In a Henstock prepartition, there are at most `2 ^ fintype.card ι` boxes with a given tag. -/
theorem is_Henstock.card_filter_tag_eq_le [Fintype ι] (h : π.is_Henstock) (x : ι → ℝ) :
  (π.boxes.filter fun J => π.tag J = x).card ≤ 2 ^ Fintype.card ι :=
  calc (π.boxes.filter fun J => π.tag J = x).card ≤ (π.boxes.filter fun J : box ι => x ∈ J.Icc).card :=
    by 
      refine' Finset.card_le_of_subset fun J hJ => _ 
      rw [Finset.mem_filter] at hJ⊢
      rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ ≤ 2 ^ Fintype.card ι := π.to_prepartition.card_filter_mem_Icc_le x
    

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included in
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def is_subordinate [Fintype ι] (π : tagged_prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  ∀ J _ : J ∈ π, (J : _).Icc ⊆ closed_ball (π.tag J) (r$ π.tag J)

variable {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
@[simp]
theorem is_subordinate_bUnion_tagged [Fintype ι] {π : prepartition I} {πi : ∀ J, tagged_prepartition J} :
  is_subordinate (π.bUnion_tagged πi) r ↔ ∀ J _ : J ∈ π, (πi J).IsSubordinate r :=
  π.forall_bUnion_tagged (fun x J => J.Icc ⊆ closed_ball x (r x)) πi

theorem is_subordinate.bUnion_prepartition [Fintype ι] (h : is_subordinate π r) (πi : ∀ J, prepartition J) :
  is_subordinate (π.bUnion_prepartition πi) r :=
  fun J hJ =>
    subset.trans (box.le_iff_Icc.1$ π.to_prepartition.le_bUnion_index hJ)$ h _$ π.to_prepartition.bUnion_index_mem hJ

theorem is_subordinate.inf_prepartition [Fintype ι] (h : is_subordinate π r) (π' : prepartition I) :
  is_subordinate (π.inf_prepartition π') r :=
  h.bUnion_prepartition _

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
theorem is_subordinate.mono' [Fintype ι] {π : tagged_prepartition I} (hr₁ : π.is_subordinate r₁)
  (h : ∀ J _ : J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) : π.is_subordinate r₂ :=
  fun J hJ x hx => closed_ball_subset_closed_ball (h _ hJ) (hr₁ _ hJ hx)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » I.Icc)
theorem is_subordinate.mono [Fintype ι] {π : tagged_prepartition I} (hr₁ : π.is_subordinate r₁)
  (h : ∀ x _ : x ∈ I.Icc, r₁ x ≤ r₂ x) : π.is_subordinate r₂ :=
  hr₁.mono'$ fun J _ => h _$ π.tag_mem_Icc J

theorem is_subordinate.diam_le [Fintype ι] {π : tagged_prepartition I} (h : π.is_subordinate r) (hJ : J ∈ π.boxes) :
  diam J.Icc ≤ 2*r (π.tag J) :=
  calc diam J.Icc ≤ diam (closed_ball (π.tag J) (r$ π.tag J)) := diam_mono (h J hJ) bounded_closed_ball 
    _ ≤ 2*r (π.tag J) := diam_closed_ball (le_of_ltₓ (r _).2)
    

/-- Tagged prepartition with single box and prescribed tag. -/
@[simps (config := { fullyApplied := ff })]
def single (I J : box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ I.Icc) : tagged_prepartition I :=
  ⟨prepartition.single I J hJ, fun J => x, fun J => h⟩

@[simp]
theorem mem_single {J'} (hJ : J ≤ I) (h : x ∈ I.Icc) : J' ∈ single I J hJ x h ↔ J' = J :=
  Finset.mem_singleton

instance (I : box ι) : Inhabited (tagged_prepartition I) :=
  ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩

theorem is_partition_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) : (single I J hJ x h).IsPartition ↔ J = I :=
  prepartition.is_partition_single_iff hJ

theorem is_partition_single (h : x ∈ I.Icc) : (single I I le_rfl x h).IsPartition :=
  prepartition.is_partition_top I

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J' «expr ∈ » single I J hJ x h)
theorem forall_mem_single (p : (ι → ℝ) → box ι → Prop) (hJ : J ≤ I) (h : x ∈ I.Icc) :
  (∀ J' _ : J' ∈ single I J hJ x h, p ((single I J hJ x h).Tag J') J') ↔ p x J :=
  by 
    simp 

@[simp]
theorem is_Henstock_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) : is_Henstock (single I J hJ x h) ↔ x ∈ J.Icc :=
  forall_mem_single (fun x J => x ∈ J.Icc) hJ h

@[simp]
theorem is_Henstock_single (h : x ∈ I.Icc) : is_Henstock (single I I le_rfl x h) :=
  (is_Henstock_single_iff (le_reflₓ I) h).2 h

@[simp]
theorem is_subordinate_single [Fintype ι] (hJ : J ≤ I) (h : x ∈ I.Icc) :
  is_subordinate (single I J hJ x h) r ↔ J.Icc ⊆ closed_ball x (r x) :=
  forall_mem_single (fun x J => J.Icc ⊆ closed_ball x (r x)) hJ h

@[simp]
theorem Union_single (hJ : J ≤ I) (h : x ∈ I.Icc) : (single I J hJ x h).Union = J :=
  prepartition.Union_single hJ

/-- Union of two tagged prepartitions with disjoint unions of boxes. -/
def disj_union (π₁ π₂ : tagged_prepartition I) (h : Disjoint π₁.Union π₂.Union) : tagged_prepartition I :=
  { toPrepartition := π₁.to_prepartition.disj_union π₂.to_prepartition h, Tag := π₁.boxes.piecewise π₁.tag π₂.tag,
    tag_mem_Icc :=
      fun J =>
        by 
          dunfold Finset.piecewise 
          splitIfs 
          exacts[π₁.tag_mem_Icc J, π₂.tag_mem_Icc J] }

@[simp]
theorem disj_union_boxes (h : Disjoint π₁.Union π₂.Union) : (π₁.disj_union π₂ h).boxes = π₁.boxes ∪ π₂.boxes :=
  rfl

@[simp]
theorem mem_disj_union (h : Disjoint π₁.Union π₂.Union) : J ∈ π₁.disj_union π₂ h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
  Finset.mem_union

@[simp]
theorem Union_disj_union (h : Disjoint π₁.Union π₂.Union) : (π₁.disj_union π₂ h).Union = π₁.Union ∪ π₂.Union :=
  prepartition.Union_disj_union _

theorem disj_union_tag_of_mem_left (h : Disjoint π₁.Union π₂.Union) (hJ : J ∈ π₁) :
  (π₁.disj_union π₂ h).Tag J = π₁.tag J :=
  dif_pos hJ

theorem disj_union_tag_of_mem_right (h : Disjoint π₁.Union π₂.Union) (hJ : J ∈ π₂) :
  (π₁.disj_union π₂ h).Tag J = π₂.tag J :=
  dif_neg$ fun h₁ => h ⟨π₁.subset_Union h₁ J.upper_mem, π₂.subset_Union hJ J.upper_mem⟩

theorem is_subordinate.disj_union [Fintype ι] (h₁ : is_subordinate π₁ r) (h₂ : is_subordinate π₂ r)
  (h : Disjoint π₁.Union π₂.Union) : is_subordinate (π₁.disj_union π₂ h) r :=
  by 
    refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
    ·
      rw [disj_union_tag_of_mem_left _ hJ]
      exact h₁ _ hJ
    ·
      rw [disj_union_tag_of_mem_right _ hJ]
      exact h₂ _ hJ

theorem is_Henstock.disj_union (h₁ : is_Henstock π₁) (h₂ : is_Henstock π₂) (h : Disjoint π₁.Union π₂.Union) :
  is_Henstock (π₁.disj_union π₂ h) :=
  by 
    refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
    ·
      rw [disj_union_tag_of_mem_left _ hJ]
      exact h₁ _ hJ
    ·
      rw [disj_union_tag_of_mem_right _ hJ]
      exact h₂ _ hJ

/-- If `I ≤ J`, then every tagged prepartition of `I` is a tagged prepartition of `J`. -/
def embed_box (I J : box ι) (h : I ≤ J) : tagged_prepartition I ↪ tagged_prepartition J :=
  { toFun :=
      fun π =>
        { π with le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h,
          tag_mem_Icc := fun J => box.le_iff_Icc.1 h (π.tag_mem_Icc J) },
    inj' :=
      by 
        rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H 
        simpa using H }

section Distortion

variable [Fintype ι] (π)

open Finset

/-- The distortion of a tagged prepartition is the maximum of distortions of its boxes. -/
def distortion :  ℝ≥0  :=
  π.to_prepartition.distortion

theorem distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
  le_sup h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
theorem distortion_le_iff {c :  ℝ≥0 } : π.distortion ≤ c ↔ ∀ J _ : J ∈ π, box.distortion J ≤ c :=
  sup_le_iff

@[simp]
theorem _root_.box_integral.prepartition.distortion_bUnion_tagged (π : prepartition I)
  (πi : ∀ J, tagged_prepartition J) : (π.bUnion_tagged πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bUnion _ _

@[simp]
theorem distortion_bUnion_prepartition (π : tagged_prepartition I) (πi : ∀ J, prepartition J) :
  (π.bUnion_prepartition πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bUnion _ _

@[simp]
theorem distortion_disj_union (h : Disjoint π₁.Union π₂.Union) :
  (π₁.disj_union π₂ h).distortion = max π₁.distortion π₂.distortion :=
  sup_union

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (J «expr ∈ » π)
theorem distortion_of_const {c} (h₁ : π.boxes.nonempty) (h₂ : ∀ J _ : J ∈ π, box.distortion J = c) : π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]
theorem distortion_single (hJ : J ≤ I) (h : x ∈ I.Icc) : distortion (single I J hJ x h) = J.distortion :=
  sup_singleton

theorem distortion_filter_le (p : box ι → Prop) : (π.filter p).distortion ≤ π.distortion :=
  sup_mono (filter_subset _ _)

end Distortion

end TaggedPrepartition

end BoxIntegral

