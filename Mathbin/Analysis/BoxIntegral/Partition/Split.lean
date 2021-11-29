import Mathbin.Analysis.BoxIntegral.Partition.Basic

/-!
# Split a box along one or more hyperplanes

## Main definitions

A hyperplane `{x : ι → ℝ | x i = a}` splits a rectangular box `I : box_integral.box ι` into two
smaller boxes. If `a ∉ Ioo (I.lower i, I.upper i)`, then one of these boxes is empty, so it is not a
box in the sense of `box_integral.box`.

We introduce the following definitions.

* `box_integral.box.split_lower I i a` and `box_integral.box.split_upper I i a` are these boxes (as
  `with_bot (box_integral.box ι)`);
* `box_integral.prepartition.split I i a` is the partition of `I` made of these two boxes (or of one
   box `I` if one of these boxes is empty);
* `box_integral.prepartition.split_many I s`, where `s : finset (ι × ℝ)` is a finite set of
  hyperplanes `{x : ι → ℝ | x i = a}` encoded as pairs `(i, a)`, is the partition of `I` made by
  cutting it along all the hyperplanes in `s`.

## Main results

The main result `box_integral.prepartition.exists_Union_eq_diff` says that any prepartition `π` of
`I` admits a prepartition `π'` of `I` that covers exactly `I \ π.Union`. One of these prepartitions
is available as `box_integral.prepartition.compl`.

## Tags

rectangular box, partition, hyperplane
-/


noncomputable theory

open_locale Classical BigOperators Filter

open Function Set Filter

namespace BoxIntegral

variable {ι M : Type _} {n : ℕ}

namespace Box

variable {I : box ι} {i : ι} {x : ℝ} {y : ι → ℝ}

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_lower I i x` is the box `I ∩ {y | y i ≤ x}`
(if it is nonempty). As usual, we represent a box that may be empty as
`with_bot (box_integral.box ι)`. -/
def split_lower (I : box ι) (i : ι) (x : ℝ) : WithBot (box ι) :=
  mk' I.lower (update I.upper i (min x (I.upper i)))

@[simp]
theorem coe_split_lower : (split_lower I i x : Set (ι → ℝ)) = I ∩ { y | y i ≤ x } :=
  by 
    rw [split_lower, coe_mk']
    ext y 
    simp only [mem_univ_pi, mem_Ioc, mem_inter_eq, mem_coe, mem_set_of_eq, forall_and_distrib, ←Pi.le_def,
      le_update_iff, le_min_iff, and_assoc, and_forall_ne i, mem_def]
    rw [and_comm (y i ≤ x), Pi.le_def]

theorem split_lower_le : I.split_lower i x ≤ I :=
  with_bot_coe_subset_iff.1$
    by 
      simp 

@[simp]
theorem split_lower_eq_bot {i x} : I.split_lower i x = ⊥ ↔ x ≤ I.lower i :=
  by 
    rw [split_lower, mk'_eq_bot, exists_update_iff I.upper fun j y => y ≤ I.lower j]
    simp [(I.lower_lt_upper _).not_le]

@[simp]
theorem split_lower_eq_self : I.split_lower i x = I ↔ I.upper i ≤ x :=
  by 
    simp [split_lower, update_eq_iff]

theorem split_lower_def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
  (h' : ∀ j, I.lower j < update I.upper i x j :=
    (forall_update_iff I.upper fun j y => I.lower j < y).2 ⟨h.1, fun j hne => I.lower_lt_upper _⟩) :
  I.split_lower i x = (⟨I.lower, update I.upper i x, h'⟩ : box ι) :=
  by 
    simp only [split_lower, mk'_eq_coe, min_eq_leftₓ h.2.le]
    use rfl 
    congr

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_upper I i x` is the box `I ∩ {y | x < y i}`
(if it is nonempty). As usual, we represent a box that may be empty as
`with_bot (box_integral.box ι)`. -/
def split_upper (I : box ι) (i : ι) (x : ℝ) : WithBot (box ι) :=
  mk' (update I.lower i (max x (I.lower i))) I.upper

@[simp]
theorem coe_split_upper : (split_upper I i x : Set (ι → ℝ)) = I ∩ { y | x < y i } :=
  by 
    rw [split_upper, coe_mk']
    ext y 
    simp only [mem_univ_pi, mem_Ioc, mem_inter_eq, mem_coe, mem_set_of_eq, forall_and_distrib,
      forall_update_iff I.lower fun j z => z < y j, max_lt_iff, and_assoc (x < y i), and_forall_ne i, mem_def]
    exact and_comm _ _

theorem split_upper_le : I.split_upper i x ≤ I :=
  with_bot_coe_subset_iff.1$
    by 
      simp 

@[simp]
theorem split_upper_eq_bot {i x} : I.split_upper i x = ⊥ ↔ I.upper i ≤ x :=
  by 
    rw [split_upper, mk'_eq_bot, exists_update_iff I.lower fun j y => I.upper j ≤ y]
    simp [(I.lower_lt_upper _).not_le]

@[simp]
theorem split_upper_eq_self : I.split_upper i x = I ↔ x ≤ I.lower i :=
  by 
    simp [split_upper, update_eq_iff]

theorem split_upper_def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
  (h' : ∀ j, update I.lower i x j < I.upper j :=
    (forall_update_iff I.lower fun j y => y < I.upper j).2 ⟨h.2, fun j hne => I.lower_lt_upper _⟩) :
  I.split_upper i x = (⟨update I.lower i x, I.upper, h'⟩ : box ι) :=
  by 
    simp only [split_upper, mk'_eq_coe, max_eq_leftₓ h.1.le]
    refine' ⟨_, rfl⟩
    congr

theorem disjoint_split_lower_split_upper (I : box ι) (i : ι) (x : ℝ) :
  Disjoint (I.split_lower i x) (I.split_upper i x) :=
  by 
    rw [←disjoint_with_bot_coe, coe_split_lower, coe_split_upper]
    refine' (Disjoint.inf_left' _ _).inf_right' _ 
    exact fun y hy : y i ≤ x ∧ x < y i => not_lt_of_le hy.1 hy.2

theorem split_lower_ne_split_upper (I : box ι) (i : ι) (x : ℝ) : I.split_lower i x ≠ I.split_upper i x :=
  by 
    cases le_or_ltₓ x (I.lower i)
    ·
      rw [split_upper_eq_self.2 h, split_lower_eq_bot.2 h]
      exact WithBot.bot_ne_coe _
    ·
      refine' (disjoint_split_lower_split_upper I i x).Ne _ 
      rwa [Ne.def, split_lower_eq_bot, not_leₓ]

end Box

namespace Prepartition

variable {I J : box ι} {i : ι} {x : ℝ}

/-- The partition of `I : box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x i < y}`.
One of these boxes can be empty, then this partition is just the single-box partition `⊤`. -/
def split (I : box ι) (i : ι) (x : ℝ) : prepartition I :=
  of_with_bot {I.split_lower i x, I.split_upper i x}
    (by 
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro J (rfl | rfl)
      exacts[box.split_lower_le, box.split_upper_le])
    (by 
      simp only [Finset.coe_insert, Finset.coe_singleton, true_andₓ, Set.mem_singleton_iff,
        pairwise_insert_of_symmetric symmetric_disjoint, pairwise_singleton]
      rintro J rfl -
      exact I.disjoint_split_lower_split_upper i x)

@[simp]
theorem mem_split_iff : J ∈ split I i x ↔ «expr↑ » J = I.split_lower i x ∨ «expr↑ » J = I.split_upper i x :=
  by 
    simp [split]

theorem mem_split_iff' :
  J ∈ split I i x ↔ (J : Set (ι → ℝ)) = I ∩ { y | y i ≤ x } ∨ (J : Set (ι → ℝ)) = I ∩ { y | x < y i } :=
  by 
    simp [mem_split_iff, ←box.with_bot_coe_inj]

@[simp]
theorem Union_split (I : box ι) (i : ι) (x : ℝ) : (split I i x).Union = I :=
  by 
    simp [split, ←inter_union_distrib_left, ←set_of_or, le_or_ltₓ]

theorem is_partition_split (I : box ι) (i : ι) (x : ℝ) : is_partition (split I i x) :=
  is_partition_iff_Union_eq.2$ Union_split I i x

theorem sum_split_boxes {M : Type _} [AddCommMonoidₓ M] (I : box ι) (i : ι) (x : ℝ) (f : box ι → M) :
  (∑J in (split I i x).boxes, f J) = (I.split_lower i x).elim 0 f+(I.split_upper i x).elim 0 f :=
  by 
    rw [split, sum_of_with_bot, Finset.sum_pair (I.split_lower_ne_split_upper i x)]

/-- If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not split `I`. -/
theorem split_of_not_mem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = ⊤ :=
  by 
    refine' ((is_partition_top I).eq_of_boxes_subset fun J hJ => _).symm 
    rcases mem_top.1 hJ with rfl 
    clear hJ 
    rw [mem_boxes, mem_split_iff]
    rw [mem_Ioo, not_and_distrib, not_ltₓ, not_ltₓ] at h 
    cases h <;> [right, left]
    ·
      rwa [eq_comm, box.split_upper_eq_self]
    ·
      rwa [eq_comm, box.split_lower_eq_self]

theorem coe_eq_of_mem_split_of_mem_le {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J) (h₃ : y i ≤ x) :
  (J : Set (ι → ℝ)) = I ∩ { y | y i ≤ x } :=
  (mem_split_iff'.1 h₁).resolve_right$
    fun H =>
      by 
        rw [←box.mem_coe, H] at h₂ 
        exact h₃.not_lt h₂.2

theorem coe_eq_of_mem_split_of_lt_mem {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J) (h₃ : x < y i) :
  (J : Set (ι → ℝ)) = I ∩ { y | x < y i } :=
  (mem_split_iff'.1 h₁).resolve_left$
    fun H =>
      by 
        rw [←box.mem_coe, H] at h₂ 
        exact h₃.not_le h₂.2

-- error in Analysis.BoxIntegral.Partition.Split: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem restrict_split (h : «expr ≤ »(I, J)) (i : ι) (x : exprℝ()) : «expr = »((split J i x).restrict I, split I i x) :=
begin
  refine [expr ((is_partition_split J i x).restrict h).eq_of_boxes_subset _],
  simp [] [] ["only"] ["[", expr finset.subset_iff, ",", expr mem_boxes, ",", expr mem_restrict', ",", expr exists_prop, ",", expr mem_split_iff', "]"] [] [],
  have [] [":", expr ∀ s, «expr ⊆ »((«expr ∩ »(I, s) : set (ι → exprℝ())), J)] [],
  from [expr λ s, (inter_subset_left _ _).trans h],
  rintro [ident J₁, "⟨", ident J₂, ",", "(", ident H₂, "|", ident H₂, ")", ",", ident H₁, "⟩"]; [left, right]; simp [] [] [] ["[", expr H₁, ",", expr H₂, ",", expr inter_left_comm «expr↑ »(I), ",", expr this, "]"] [] []
end

theorem inf_split (π : prepartition I) (i : ι) (x : ℝ) : π⊓split I i x = π.bUnion fun J => split J i x :=
  bUnion_congr_of_le rfl$ fun J hJ => restrict_split hJ i x

/-- Split a box along many hyperplanes `{y | y i = x}`; each hyperplane is given by the pair
`(i x)`. -/
def split_many (I : box ι) (s : Finset (ι × ℝ)) : prepartition I :=
  s.inf fun p => split I p.1 p.2

@[simp]
theorem split_many_empty (I : box ι) : split_many I ∅ = ⊤ :=
  Finset.inf_empty

@[simp]
theorem split_many_insert (I : box ι) (s : Finset (ι × ℝ)) (p : ι × ℝ) :
  split_many I (insert p s) = split_many I s⊓split I p.1 p.2 :=
  by 
    rw [split_many, Finset.inf_insert, inf_comm, split_many]

theorem split_many_le_split (I : box ι) {s : Finset (ι × ℝ)} {p : ι × ℝ} (hp : p ∈ s) :
  split_many I s ≤ split I p.1 p.2 :=
  Finset.inf_le hp

theorem is_partition_split_many (I : box ι) (s : Finset (ι × ℝ)) : is_partition (split_many I s) :=
  Finset.induction_on s
      (by 
        simp only [split_many_empty, is_partition_top])$
    fun a s ha hs =>
      by 
        simpa only [split_many_insert, inf_split] using hs.bUnion fun J hJ => is_partition_split _ _ _

@[simp]
theorem Union_split_many (I : box ι) (s : Finset (ι × ℝ)) : (split_many I s).Union = I :=
  (is_partition_split_many I s).Union_eq

theorem inf_split_many {I : box ι} (π : prepartition I) (s : Finset (ι × ℝ)) :
  π⊓split_many I s = π.bUnion fun J => split_many J s :=
  by 
    induction' s using Finset.induction_on with p s hp ihp
    ·
      simp 
    ·
      simpRw [split_many_insert, ←inf_assoc, ihp, inf_split, bUnion_assoc]

-- error in Analysis.BoxIntegral.Partition.Split: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Let `s : finset (ι × ℝ)` be a set of hyperplanes `{x : ι → ℝ | x i = r}` in `ι → ℝ` encoded as
pairs `(i, r)`. Suppose that this set contains all faces of a box `J`. The hyperplanes of `s` split
a box `I` into subboxes. Let `Js` be one of them. If `J` and `Js` have nonempty intersection, then
`Js` is a subbox of `J`.  -/
theorem not_disjoint_imp_le_of_subset_of_mem_split_many
{I J Js : box ι}
{s : finset «expr × »(ι, exprℝ())}
(H : ∀ i, «expr ⊆ »({(i, J.lower i), (i, J.upper i)}, s))
(HJs : «expr ∈ »(Js, split_many I s))
(Hn : «expr¬ »(disjoint (J : with_bot (box ι)) Js)) : «expr ≤ »(Js, J) :=
begin
  simp [] [] ["only"] ["[", expr finset.insert_subset, ",", expr finset.singleton_subset_iff, "]"] [] ["at", ident H],
  rcases [expr box.not_disjoint_coe_iff_nonempty_inter.mp Hn, "with", "⟨", ident x, ",", ident hx, ",", ident hxs, "⟩"],
  refine [expr λ y hy i, ⟨_, _⟩],
  { rcases [expr split_many_le_split I (H i).1 HJs, "with", "⟨", ident Jl, ",", ident Hmem, ":", expr «expr ∈ »(Jl, split I i (J.lower i)), ",", ident Hle, "⟩"],
    have [] [] [":=", expr Hle hxs],
    rw ["[", "<-", expr box.coe_subset_coe, ",", expr coe_eq_of_mem_split_of_lt_mem Hmem this (hx i).1, "]"] ["at", ident Hle],
    exact [expr (Hle hy).2] },
  { rcases [expr split_many_le_split I (H i).2 HJs, "with", "⟨", ident Jl, ",", ident Hmem, ":", expr «expr ∈ »(Jl, split I i (J.upper i)), ",", ident Hle, "⟩"],
    have [] [] [":=", expr Hle hxs],
    rw ["[", "<-", expr box.coe_subset_coe, ",", expr coe_eq_of_mem_split_of_mem_le Hmem this (hx i).2, "]"] ["at", ident Hle],
    exact [expr (Hle hy).2] }
end

section Fintype

variable [Fintype ι]

/-- Let `s` be a finite set of boxes in `ℝⁿ = ι → ℝ`. Then there exists a finite set `t₀` of
hyperplanes (namely, the set of all hyperfaces of boxes in `s`) such that for any `t ⊇ t₀`
and any box `I` in `ℝⁿ` the following holds. The hyperplanes from `t` split `I` into subboxes.
Let `J'` be one of them, and let `J` be one of the boxes in `s`. If these boxes have a nonempty
intersection, then `J' ≤ J`. -/
theorem eventually_not_disjoint_imp_le_of_mem_split_many (s : Finset (box ι)) :
  ∀ᶠt : Finset (ι × ℝ) in at_top,
    ∀ I : box ι J _ : J ∈ s J' _ : J' ∈ split_many I t, ¬Disjoint (J : WithBot (box ι)) J' → J' ≤ J :=
  by 
    refine'
      eventually_at_top.2
        ⟨s.bUnion fun J => finset.univ.bUnion fun i => {(i, J.lower i), (i, J.upper i)},
          fun t ht I J hJ J' hJ' => not_disjoint_imp_le_of_subset_of_mem_split_many (fun i => _) hJ'⟩
    exact fun p hp => ht (Finset.mem_bUnion.2 ⟨J, hJ, Finset.mem_bUnion.2 ⟨i, Finset.mem_univ _, hp⟩⟩)

theorem eventually_split_many_inf_eq_filter (π : prepartition I) :
  ∀ᶠt : Finset (ι × ℝ) in at_top, π⊓split_many I t = (split_many I t).filter fun J => «expr↑ » J ⊆ π.Union :=
  by 
    refine' (eventually_not_disjoint_imp_le_of_mem_split_many π.boxes).mono fun t ht => _ 
    refine' le_antisymmₓ ((bUnion_le_iff _).2$ fun J hJ => _) (le_inf (fun J hJ => _) (filter_le _ _))
    ·
      refine' of_with_bot_mono _ 
      simp only [Finset.mem_image, exists_prop, mem_boxes, mem_filter]
      rintro _ ⟨J₁, h₁, rfl⟩ hne 
      refine' ⟨_, ⟨J₁, ⟨h₁, subset.trans _ (π.subset_Union hJ)⟩, rfl⟩, le_rfl⟩
      exact ht I J hJ J₁ h₁ (mt disjoint_iff.1 hne)
    ·
      rw [mem_filter] at hJ 
      rcases Set.mem_bUnion_iff.1 (hJ.2 J.upper_mem) with ⟨J', hJ', hmem⟩
      refine' ⟨J', hJ', ht I _ hJ' _ hJ.1$ box.not_disjoint_coe_iff_nonempty_inter.2 _⟩
      exact ⟨J.upper, hmem, J.upper_mem⟩

-- error in Analysis.BoxIntegral.Partition.Split: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_split_many_inf_eq_filter_of_finite
(s : set (prepartition I))
(hs : s.finite) : «expr∃ , »((t : finset «expr × »(ι, exprℝ())), ∀
 π «expr ∈ » s, «expr = »(«expr ⊓ »(π, split_many I t), (split_many I t).filter (λ
   J, «expr ⊆ »(«expr↑ »(J), π.Union)))) :=
begin
  have [] [] [":=", expr λ (π) (hπ : «expr ∈ »(π, s)), eventually_split_many_inf_eq_filter π],
  exact [expr (hs.eventually_all.2 this).exists]
end

/-- If `π` is a partition of `I`, then there exists a finite set `s` of hyperplanes such that
`split_many I s ≤ π`. -/
theorem is_partition.exists_split_many_le {I : box ι} {π : prepartition I} (h : is_partition π) :
  ∃ s, split_many I s ≤ π :=
  (eventually_split_many_inf_eq_filter π).exists.imp$
    fun s hs =>
      by 
        rwa [h.Union_eq, filter_of_true, inf_eq_right] at hs 
        exact fun J hJ => le_of_mem _ hJ

/-- For every prepartition `π` of `I` there exists a prepartition that covers exactly
`I \ π.Union`. -/
theorem exists_Union_eq_diff (π : prepartition I) : ∃ π' : prepartition I, π'.Union = I \ π.Union :=
  by 
    rcases π.eventually_split_many_inf_eq_filter.exists with ⟨s, hs⟩
    use (split_many I s).filter fun J => ¬(J : Set (ι → ℝ)) ⊆ π.Union 
    simp [←hs]

/-- If `π` is a prepartition of `I`, then `π.compl` is a prepartition of `I`
such that `π.compl.Union = I \ π.Union`. -/
def compl (π : prepartition I) : prepartition I :=
  π.exists_Union_eq_diff.some

@[simp]
theorem Union_compl (π : prepartition I) : π.compl.Union = I \ π.Union :=
  π.exists_Union_eq_diff.some_spec

/-- Since the definition of `box_integral.prepartition.compl` uses `Exists.some`,
the result depends only on `π.Union`. -/
theorem compl_congr {π₁ π₂ : prepartition I} (h : π₁.Union = π₂.Union) : π₁.compl = π₂.compl :=
  by 
    dunfold compl 
    congr 1
    rw [h]

theorem is_partition.compl_eq_bot {π : prepartition I} (h : is_partition π) : π.compl = ⊥ :=
  by 
    rw [←Union_eq_empty, Union_compl, h.Union_eq, diff_self]

@[simp]
theorem compl_top : (⊤ : prepartition I).Compl = ⊥ :=
  (is_partition_top I).compl_eq_bot

end Fintype

end Prepartition

end BoxIntegral

