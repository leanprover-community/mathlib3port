/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.MetricSpace.Polish
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# The Borel sigma-algebra on Polish spaces

We discuss several results pertaining to the relationship between the topology and the Borel
structure on Polish spaces.

## Main definitions and results

First, we define the class of analytic sets and establish its basic properties.

* `measure_theory.analytic_set s`: a set in a topological space is analytic if it is the continuous
  image of a Polish space. Equivalently, it is empty, or the image of `ℕ → ℕ`.
* `measure_theory.analytic_set.image_of_continuous`: a continuous image of an analytic set is
  analytic.
* `measurable_set.analytic_set`: in a Polish space, any Borel-measurable set is analytic.

Then, we show Lusin's theorem that two disjoint analytic sets can be separated by Borel sets.

* `measurably_separable s t` states that there exists a measurable set containing `s` and disjoint
  from `t`.
* `analytic_set.measurably_separable` shows that two disjoint analytic sets are separated by a
  Borel set.

Finally, we prove the Lusin-Souslin theorem that a continuous injective image of a Borel subset of
a Polish space is Borel. The proof of this nontrivial result relies on the above results on
analytic sets.

* `measurable_set.image_of_continuous_on_inj_on` asserts that, if `s` is a Borel measurable set in
  a Polish space, then the image of `s` under a continuous injective map is still Borel measurable.
* `continuous.measurable_embedding` states that a continuous injective map on a Polish space
  is a measurable embedding for the Borel sigma-algebra.
* `continuous_on.measurable_embedding` is the same result for a map restricted to a measurable set
  on which it is continuous.
* `measurable.measurable_embedding` states that a measurable injective map from a Polish space
  to a second-countable topological space is a measurable embedding.
* `is_clopenable_iff_measurable_set`: in a Polish space, a set is clopenable (i.e., it can be made
  open and closed by using a finer Polish topology) if and only if it is Borel-measurable.
-/


open Set Function PolishSpace PiNat TopologicalSpace Metric Filter

open TopologicalSpace MeasureTheory

variable {α : Type _} [TopologicalSpace α] {ι : Type _}

namespace MeasureTheory

/-! ### Analytic sets -/


/-- An analytic set is a set which is the continuous image of some Polish space. There are several
equivalent characterizations of this definition. For the definition, we pick one that avoids
universe issues: a set is analytic if and only if it is a continuous image of `ℕ → ℕ` (or if it
is empty). The above more usual characterization is given
in `analytic_set_iff_exists_polish_space_range`.

Warning: these are analytic sets in the context of descriptive set theory (which is why they are
registered in the namespace `measure_theory`). They have nothing to do with analytic sets in the
context of complex analysis. -/
irreducible_def AnalyticSet (s : Set α) : Prop :=
  s = ∅ ∨ ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Range f = s

theorem analytic_set_empty : AnalyticSet (∅ : Set α) := by
  rw [analytic_set]
  exact Or.inl rfl

theorem analytic_set_range_of_polish_space {β : Type _} [TopologicalSpace β] [PolishSpace β] {f : β → α}
    (f_cont : Continuous f) : AnalyticSet (Range f) := by
  cases is_empty_or_nonempty β
  · rw [range_eq_empty]
    exact analytic_set_empty
    
  · rw [analytic_set]
    obtain ⟨g, g_cont, hg⟩ : ∃ g : (ℕ → ℕ) → β, Continuous g ∧ surjective g := exists_nat_nat_continuous_surjective β
    refine' Or.inr ⟨f ∘ g, f_cont.comp g_cont, _⟩
    rwa [hg.range_comp]
    

/-- The image of an open set under a continuous map is analytic. -/
theorem _root_.is_open.analytic_set_image {β : Type _} [TopologicalSpace β] [PolishSpace β] {s : Set β} (hs : IsOpen s)
    {f : β → α} (f_cont : Continuous f) : AnalyticSet (f '' s) := by
  rw [image_eq_range]
  have : PolishSpace s := hs.polish_space
  exact analytic_set_range_of_polish_space (f_cont.comp continuous_subtype_coe)

/-- A set is analytic if and only if it is the continuous image of some Polish space. -/
theorem analytic_set_iff_exists_polish_space_range {s : Set α} :
    AnalyticSet s ↔
      ∃ (β : Type)(h : TopologicalSpace β)(h' : @PolishSpace β h)(f : β → α), @Continuous _ _ h _ f ∧ Range f = s :=
  by
  constructor
  · intro h
    rw [analytic_set] at h
    cases h
    · refine'
        ⟨Empty, by
          infer_instance, by
          infer_instance, Empty.elim, continuous_bot, _⟩
      rw [h]
      exact range_eq_empty _
      
    · exact
        ⟨ℕ → ℕ, by
          infer_instance, by
          infer_instance, h⟩
      
    
  · rintro ⟨β, h, h', f, f_cont, f_range⟩
    skip
    rw [← f_range]
    exact analytic_set_range_of_polish_space f_cont
    

/-- The continuous image of an analytic set is analytic -/
theorem AnalyticSet.image_of_continuous_on {β : Type _} [TopologicalSpace β] {s : Set α} (hs : AnalyticSet s)
    {f : α → β} (hf : ContinuousOn f s) : AnalyticSet (f '' s) := by
  rcases analytic_set_iff_exists_polish_space_range.1 hs with ⟨γ, γtop, γpolish, g, g_cont, gs⟩
  skip
  have : f '' s = range (f ∘ g) := by
    rw [range_comp, gs]
  rw [this]
  apply analytic_set_range_of_polish_space
  apply hf.comp_continuous g_cont fun x => _
  rw [← gs]
  exact mem_range_self _

theorem AnalyticSet.image_of_continuous {β : Type _} [TopologicalSpace β] {s : Set α} (hs : AnalyticSet s) {f : α → β}
    (hf : Continuous f) : AnalyticSet (f '' s) :=
  hs.image_of_continuous_on hf.ContinuousOn

/-- A countable intersection of analytic sets is analytic. -/
theorem AnalyticSet.Inter [hι : Nonempty ι] [Encodable ι] [T2Space α] {s : ι → Set α} (hs : ∀ n, AnalyticSet (s n)) :
    AnalyticSet (⋂ n, s n) := by
  rcases hι with ⟨i₀⟩
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
    `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, and the
    range of `x ↦ f 0 (x 0)` on `t` is exactly `⋂ n, s n`, so this set is analytic. -/
  choose β hβ h'β f f_cont f_range using fun n => analytic_set_iff_exists_polish_space_range.1 (hs n)
  skip
  let γ := ∀ n, β n
  let t : Set γ := ⋂ n, { x | f n (x n) = f i₀ (x i₀) }
  have t_closed : IsClosed t := by
    apply is_closed_Inter
    intro n
    exact is_closed_eq ((f_cont n).comp (continuous_apply n)) ((f_cont i₀).comp (continuous_apply i₀))
  have : PolishSpace t := t_closed.polish_space
  let F : t → α := fun x => f i₀ ((x : γ) i₀)
  have F_cont : Continuous F := (f_cont i₀).comp ((continuous_apply i₀).comp continuous_subtype_coe)
  have F_range : range F = ⋂ n : ι, s n := by
    apply subset.antisymm
    · rintro y ⟨x, rfl⟩
      apply mem_Inter.2 fun n => _
      have : f n ((x : γ) n) = F x := (mem_Inter.1 x.2 n : _)
      rw [← this, ← f_range n]
      exact mem_range_self _
      
    · intro y hy
      have A : ∀ n, ∃ x : β n, f n x = y := by
        intro n
        rw [← mem_range, f_range n]
        exact mem_Inter.1 hy n
      choose x hx using A
      have xt : x ∈ t := by
        apply mem_Inter.2 fun n => _
        simp [hx]
      refine' ⟨⟨x, xt⟩, _⟩
      exact hx i₀
      
  rw [← F_range]
  exact analytic_set_range_of_polish_space F_cont

/-- A countable union of analytic sets is analytic. -/
theorem AnalyticSet.Union [Encodable ι] {s : ι → Set α} (hs : ∀ n, AnalyticSet (s n)) : AnalyticSet (⋃ n, s n) := by
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
    coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using fun n => analytic_set_iff_exists_polish_space_range.1 (hs n)
  skip
  let γ := Σn, β n
  let F : γ → α := by
    rintro ⟨n, x⟩
    exact f n x
  have F_cont : Continuous F := continuous_sigma f_cont
  have F_range : range F = ⋃ n, s n := by
    rw [range_sigma_eq_Union_range]
    congr
    ext1 n
    rw [← f_range n]
  rw [← F_range]
  exact analytic_set_range_of_polish_space F_cont

theorem _root_.is_closed.analytic_set [PolishSpace α] {s : Set α} (hs : IsClosed s) : AnalyticSet s := by
  have : PolishSpace s := hs.polish_space
  rw [← @Subtype.range_val α s]
  exact analytic_set_range_of_polish_space continuous_subtype_coe

/-- Given a Borel-measurable set in a Polish space, there exists a finer Polish topology making
it clopen. This is in fact an equivalence, see `is_clopenable_iff_measurable_set`. -/
theorem _root_.measurable_set.is_clopenable [PolishSpace α] [MeasurableSpace α] [BorelSpace α] {s : Set α}
    (hs : MeasurableSet s) : IsClopenable s := by
  revert s
  apply MeasurableSet.induction_on_open
  · exact fun u hu => hu.IsClopenable
    
  · exact fun u hu h'u => h'u.Compl
    
  · exact fun f f_disj f_meas hf => is_clopenable.Union hf
    

theorem _root_.measurable_set.analytic_set {α : Type _} [t : TopologicalSpace α] [PolishSpace α] [MeasurableSpace α]
    [BorelSpace α] {s : Set α} (hs : MeasurableSet s) : AnalyticSet s := by
  /- For a short proof (avoiding measurable induction), one sees `s` as a closed set for a finer
    topology `t'`. It is analytic for this topology. As the identity from `t'` to `t` is continuous
    and the image of an analytic set is analytic, it follows that `s` is also analytic for `t`. -/
  obtain ⟨t', t't, t'_polish, s_closed, s_open⟩ :
    ∃ t' : TopologicalSpace α, t' ≤ t ∧ @PolishSpace α t' ∧ @IsClosed α t' s ∧ @IsOpen α t' s := hs.is_clopenable
  have A := @IsClosed.analytic_set α t' t'_polish s s_closed
  convert @analytic_set.image_of_continuous α t' α t s A id (continuous_id_of_le t't)
  simp only [id.def, image_id']

/-- Given a Borel-measurable function from a Polish space to a second-countable space, there exists
a finer Polish topology on the source space for which the function is continuous. -/
theorem _root_.measurable.exists_continuous {α β : Type _} [t : TopologicalSpace α] [PolishSpace α] [MeasurableSpace α]
    [BorelSpace α] [tβ : TopologicalSpace β] [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β] {f : α → β}
    (hf : Measurable f) : ∃ t' : TopologicalSpace α, t' ≤ t ∧ @Continuous α β t' tβ f ∧ @PolishSpace α t' := by
  obtain ⟨b, b_count, -, hb⟩ : ∃ b : Set (Set β), countable b ∧ ∅ ∉ b ∧ is_topological_basis b :=
    exists_countable_basis β
  have : Encodable b := b_count.to_encodable
  have : ∀ s : b, is_clopenable (f ⁻¹' s) := by
    intro s
    apply MeasurableSet.is_clopenable
    exact hf (hb.is_open s.2).MeasurableSet
  choose T Tt Tpolish Tclosed Topen using this
  obtain ⟨t', t'T, t't, t'_polish⟩ : ∃ t' : TopologicalSpace α, (∀ i, t' ≤ T i) ∧ t' ≤ t ∧ @PolishSpace α t' :=
    exists_polish_space_forall_le T Tt Tpolish
  refine' ⟨t', t't, _, t'_polish⟩
  apply hb.continuous _ fun s hs => _
  exact t'T ⟨s, hs⟩ _ (Topen ⟨s, hs⟩)

/-! ### Separating sets with measurable sets -/


/-- Two sets `u` and `v` in a measurable space are measurably separable if there
exists a measurable set containing `u` and disjoint from `v`.
This is mostly interesting for Borel-separable sets. -/
def MeasurablySeparable {α : Type _} [MeasurableSpace α] (s t : Set α) : Prop :=
  ∃ u, s ⊆ u ∧ Disjoint t u ∧ MeasurableSet u

theorem MeasurablySeparable.Union [Encodable ι] {α : Type _} [MeasurableSpace α] {s t : ι → Set α}
    (h : ∀ m n, MeasurablySeparable (s m) (t n)) : MeasurablySeparable (⋃ n, s n) (⋃ m, t m) := by
  choose u hsu htu hu using h
  refine' ⟨⋃ m, ⋂ n, u m n, _, _, _⟩
  · refine' Union_subset fun m => subset_Union_of_subset m _
    exact subset_Inter fun n => hsu m n
    
  · simp_rw [disjoint_Union_left, disjoint_Union_right]
    intro n m
    apply Disjoint.mono_right _ (htu m n)
    apply Inter_subset
    
  · refine' MeasurableSet.Union fun m => _
    exact MeasurableSet.Inter fun n => hu m n
    

/-- The hard part of the Lusin separation theorem saying that two disjoint analytic sets are
contained in disjoint Borel sets (see the full statement in `analytic_set.measurably_separable`).
Here, we prove this when our analytic sets are the ranges of functions from `ℕ → ℕ`.
-/
theorem measurably_separable_range_of_disjoint [T2Space α] [MeasurableSpace α] [BorelSpace α] {f g : (ℕ → ℕ) → α}
    (hf : Continuous f) (hg : Continuous g) (h : Disjoint (Range f) (Range g)) :
    MeasurablySeparable (Range f) (Range g) := by
  /- We follow [Kechris, *Classical Descriptive Set Theory* (Theorem 14.7)][kechris1995].
    If the ranges are not Borel-separated, then one can find two cylinders of length one whose images
    are not Borel-separated, and then two smaller cylinders of length two whose images are not
    Borel-separated, and so on. One thus gets two sequences of cylinders, that decrease to two
    points `x` and `y`. Their images are different by the disjointness assumption, hence contained
    in two disjoint open sets by the T2 property. By continuity, long enough cylinders around `x`
    and `y` have images which are separated by these two disjoint open sets, a contradiction.
    -/
  by_contra hfg
  have I :
    ∀ n x y,
      ¬measurably_separable (f '' cylinder x n) (g '' cylinder y n) →
        ∃ x' y',
          x' ∈ cylinder x n ∧
            y' ∈ cylinder y n ∧ ¬measurably_separable (f '' cylinder x' (n + 1)) (g '' cylinder y' (n + 1)) :=
    by
    intro n x y
    contrapose!
    intro H
    rw [← Union_cylinder_update x n, ← Union_cylinder_update y n, image_Union, image_Union]
    refine' measurably_separable.Union fun i j => _
    exact H _ _ (update_mem_cylinder _ _ _) (update_mem_cylinder _ _ _)
  -- consider the set of pairs of cylinders of some length whose images are not Borel-separated
  let A := { p : ℕ × (ℕ → ℕ) × (ℕ → ℕ) // ¬measurably_separable (f '' cylinder p.2.1 p.1) (g '' cylinder p.2.2 p.1) }
  -- for each such pair, one can find longer cylinders whose images are not Borel-separated either
  have : ∀ p : A, ∃ q : A, q.1.1 = p.1.1 + 1 ∧ q.1.2.1 ∈ cylinder p.1.2.1 p.1.1 ∧ q.1.2.2 ∈ cylinder p.1.2.2 p.1.1 := by
    rintro ⟨⟨n, x, y⟩, hp⟩
    rcases I n x y hp with ⟨x', y', hx', hy', h'⟩
    exact ⟨⟨⟨n + 1, x', y'⟩, h'⟩, rfl, hx', hy'⟩
  choose F hFn hFx hFy using this
  let p0 : A :=
    ⟨⟨0, fun n => 0, fun n => 0⟩, by
      simp [hfg]⟩
  -- construct inductively decreasing sequences of cylinders whose images are not separated
  let p : ℕ → A := fun n => (F^[n]) p0
  have prec : ∀ n, p (n + 1) = F (p n) := fun n => by
    simp only [p, iterate_succ']
  -- check that at the `n`-th step we deal with cylinders of length `n`
  have pn_fst : ∀ n, (p n).1.1 = n := by
    intro n
    induction' n with n IH
    · rfl
      
    · simp only [prec, hFn, IH]
      
  -- check that the cylinders we construct are indeed decreasing, by checking that the coordinates
  -- are stationary.
  have Ix : ∀ m n, m + 1 ≤ n → (p n).1.2.1 m = (p (m + 1)).1.2.1 m := by
    intro m
    apply Nat.le_induction
    · rfl
      
    intro n hmn IH
    have I : (F (p n)).val.snd.fst m = (p n).val.snd.fst m := by
      apply hFx (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec, I, IH]
  have Iy : ∀ m n, m + 1 ≤ n → (p n).1.2.2 m = (p (m + 1)).1.2.2 m := by
    intro m
    apply Nat.le_induction
    · rfl
      
    intro n hmn IH
    have I : (F (p n)).val.snd.snd m = (p n).val.snd.snd m := by
      apply hFy (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec, I, IH]
  -- denote by `x` and `y` the limit points of these two sequences of cylinders.
  set x : ℕ → ℕ := fun n => (p (n + 1)).1.2.1 n with hx
  set y : ℕ → ℕ := fun n => (p (n + 1)).1.2.2 n with hy
  -- by design, the cylinders around these points have images which are not Borel-separable.
  have M : ∀ n, ¬measurably_separable (f '' cylinder x n) (g '' cylinder y n) := by
    intro n
    convert (p n).2 using 3
    · rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff]
      intro i hi
      rw [hx]
      exact (Ix i n hi).symm
      
    · rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff]
      intro i hi
      rw [hy]
      exact (Iy i n hi).symm
      
  -- consider two open sets separating `f x` and `g y`.
  obtain ⟨u, v, u_open, v_open, xu, yv, huv⟩ : ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ g y ∈ v ∧ u ∩ v = ∅ := by
    apply t2_separation
    exact disjoint_iff_forall_ne.1 h _ (mem_range_self _) _ (mem_range_self _)
  let this : MetricSpace (ℕ → ℕ) := metric_space_nat_nat
  obtain ⟨εx, εxpos, hεx⟩ : ∃ (εx : ℝ)(H : εx > 0), Metric.Ball x εx ⊆ f ⁻¹' u := by
    apply Metric.mem_nhds_iff.1
    exact hf.continuous_at.preimage_mem_nhds (u_open.mem_nhds xu)
  obtain ⟨εy, εypos, hεy⟩ : ∃ (εy : ℝ)(H : εy > 0), Metric.Ball y εy ⊆ g ⁻¹' v := by
    apply Metric.mem_nhds_iff.1
    exact hg.continuous_at.preimage_mem_nhds (v_open.mem_nhds yv)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < min εx εy :=
    exists_pow_lt_of_lt_one (lt_minₓ εxpos εypos)
      (by
        norm_num)
  -- for large enough `n`, these open sets separate the images of long cylinders around `x` and `y`
  have B : measurably_separable (f '' cylinder x n) (g '' cylinder y n) := by
    refine' ⟨u, _, _, u_open.measurable_set⟩
    · rw [image_subset_iff]
      apply subset.trans _ hεx
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_leftₓ _ _))
      
    · have D : Disjoint v u := by
        rwa [disjoint_iff_inter_eq_empty, inter_comm]
      apply Disjoint.mono_left _ D
      change g '' cylinder y n ⊆ v
      rw [image_subset_iff]
      apply subset.trans _ hεy
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_rightₓ _ _))
      
  -- this is a contradiction.
  exact M n B

/-- The Lusin separation theorem: if two analytic sets are disjoint, then they are contained in
disjoint Borel sets. -/
theorem AnalyticSet.measurably_separable [T2Space α] [MeasurableSpace α] [BorelSpace α] {s t : Set α}
    (hs : AnalyticSet s) (ht : AnalyticSet t) (h : Disjoint s t) : MeasurablySeparable s t := by
  rw [analytic_set] at hs ht
  rcases hs with (rfl | ⟨f, f_cont, rfl⟩)
  · refine'
      ⟨∅, subset.refl _, by
        simp , MeasurableSet.empty⟩
    
  rcases ht with (rfl | ⟨g, g_cont, rfl⟩)
  · exact
      ⟨univ, subset_univ _, by
        simp , MeasurableSet.univ⟩
    
  exact measurably_separable_range_of_disjoint f_cont g_cont h

/-! ### Injective images of Borel sets -/


variable {γ : Type _} [tγ : TopologicalSpace γ] [PolishSpace γ]

include tγ

/-- The Lusin-Souslin theorem: the range of a continuous injective function defined on a Polish
space is Borel-measurable. -/
theorem measurable_set_range_of_continuous_injective {β : Type _} [TopologicalSpace β] [T2Space β] [MeasurableSpace β]
    [BorelSpace β] {f : γ → β} (f_cont : Continuous f) (f_inj : Injective f) : MeasurableSet (Range f) := by
  /- We follow [Fremlin, *Measure Theory* (volume 4, 423I)][fremlin_vol4].
    Let `b = {s i}` be a countable basis for `α`. When `s i` and `s j` are disjoint, their images are
    disjoint analytic sets, hence by the separation theorem one can find a Borel-measurable set
    `q i j` separating them.
    Let `E i = closure (f '' s i) ∩ ⋂ j, q i j \ q j i`. It contains `f '' (s i)` and it is
    measurable. Let `F n = ⋃ E i`, where the union is taken over those `i` for which `diam (s i)`
    is bounded by some number `u n` tending to `0` with `n`.
    We claim that `range f = ⋂ F n`, from which the measurability is obvious. The inclusion `⊆` is
    straightforward. To show `⊇`, consider a point `x` in the intersection. For each `n`, it belongs
    to some `E i` with `diam (s i) ≤ u n`. Pick a point `y i ∈ s i`. We claim that for such `i`
    and `j`, the intersection `s i ∩ s j` is nonempty: if it were empty, then thanks to the
    separating set `q i j` in the definition of `E i` one could not have `x ∈ E i ∩ E j`.
    Since these two sets have small diameter, it follows that `y i` and `y j` are close.
    Thus, `y` is a Cauchy sequence, converging to a limit `z`. We claim that `f z = x`, completing
    the proof.
    Otherwise, one could find open sets `v` and `w` separating `f z` from `x`. Then, for large `n`,
    the image `f '' (s i)` would be included in `v` by continuity of `f`, so its closure would be
    contained in the closure of `v`, and therefore it would be disjoint from `w`. This is a
    contradiction since `x` belongs both to this closure and to `w`. -/
  let this := upgradePolishSpace γ
  obtain ⟨b, b_count, b_nonempty, hb⟩ : ∃ b : Set (Set γ), countable b ∧ ∅ ∉ b ∧ is_topological_basis b :=
    exists_countable_basis γ
  have : Encodable b := b_count.to_encodable
  let A := { p : b × b // Disjoint (p.1 : Set γ) p.2 }
  -- for each pair of disjoint sets in the topological basis `b`, consider Borel sets separating
  -- their images, by injectivity of `f` and the Lusin separation theorem.
  have : ∀ p : A, ∃ q : Set β, f '' (p.1.1 : Set γ) ⊆ q ∧ Disjoint (f '' (p.1.2 : Set γ)) q ∧ MeasurableSet q := by
    intro p
    apply
      analytic_set.measurably_separable ((hb.is_open p.1.1.2).analytic_set_image f_cont)
        ((hb.is_open p.1.2.2).analytic_set_image f_cont)
    exact Disjoint.image p.2 (f_inj.inj_on univ) (subset_univ _) (subset_univ _)
  choose q hq1 hq2 q_meas using this
  -- define sets `E i` and `F n` as in the proof sketch above
  let E : b → Set β := fun s =>
    Closure (f '' s) ∩ ⋂ (t : b) (ht : Disjoint s.1 t.1), q ⟨(s, t), ht⟩ \ q ⟨(t, s), ht.symm⟩
  obtain ⟨u, u_anti, u_pos, u_lim⟩ : ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ tendsto u at_top (𝓝 0) :=
    exists_seq_strict_anti_tendsto (0 : ℝ)
  let F : ℕ → Set β := fun n => ⋃ (s : b) (hs : bounded s.1 ∧ diam s.1 ≤ u n), E s
  -- it is enough to show that `range f = ⋂ F n`, as the latter set is obviously measurable.
  suffices range f = ⋂ n, F n by
    have E_meas : ∀ s : b, MeasurableSet (E s) := by
      intro b
      refine' is_closed_closure.measurable_set.inter _
      refine' MeasurableSet.Inter fun s => _
      exact MeasurableSet.Inter_Prop fun hs => (q_meas _).diff (q_meas _)
    have F_meas : ∀ n, MeasurableSet (F n) := by
      intro n
      refine' MeasurableSet.Union fun s => _
      exact MeasurableSet.Union_Prop fun hs => E_meas _
    rw [this]
    exact MeasurableSet.Inter fun n => F_meas n
  -- we check both inclusions.
  apply subset.antisymm
  -- we start with the easy inclusion `range f ⊆ ⋂ F n`. One just needs to unfold the definitions.
  · rintro x ⟨y, rfl⟩
    apply mem_Inter.2 fun n => _
    obtain ⟨s, sb, ys, hs⟩ : ∃ (s : Set γ)(H : s ∈ b), y ∈ s ∧ s ⊆ ball y (u n / 2) := by
      apply hb.mem_nhds_iff.1
      exact ball_mem_nhds _ (half_pos (u_pos n))
    have diam_s : diam s ≤ u n := by
      apply (diam_mono hs bounded_ball).trans
      convert diam_ball (half_pos (u_pos n)).le
      ring
    refine' mem_Union.2 ⟨⟨s, sb⟩, _⟩
    refine' mem_Union.2 ⟨⟨Metric.Bounded.mono hs bounded_ball, diam_s⟩, _⟩
    apply mem_inter (subset_closure (mem_image_of_mem _ ys))
    refine' mem_Inter.2 fun t => mem_Inter.2 fun ht => ⟨_, _⟩
    · apply hq1
      exact mem_image_of_mem _ ys
      
    · apply disjoint_left.1 (hq2 ⟨(t, ⟨s, sb⟩), ht.symm⟩)
      exact mem_image_of_mem _ ys
      
    
  -- Now, let us prove the harder inclusion `⋂ F n ⊆ range f`.
  · intro x hx
    -- pick for each `n` a good set `s n` of small diameter for which `x ∈ E (s n)`.
    have C1 : ∀ n, ∃ (s : b)(hs : bounded s.1 ∧ diam s.1 ≤ u n), x ∈ E s := fun n => by
      simpa only [mem_Union] using mem_Inter.1 hx n
    choose s hs hxs using C1
    have C2 : ∀ n, (s n).1.Nonempty := by
      intro n
      rw [← ne_empty_iff_nonempty]
      intro hn
      have := (s n).2
      rw [hn] at this
      exact b_nonempty this
    -- choose a point `y n ∈ s n`.
    choose y hy using C2
    have I : ∀ m n, ((s m).1 ∩ (s n).1).Nonempty := by
      intro m n
      rw [← not_disjoint_iff_nonempty_inter]
      by_contra' h
      have A : x ∈ q ⟨(s m, s n), h⟩ \ q ⟨(s n, s m), h.symm⟩ :=
        have := mem_Inter.1 (hxs m).2 (s n)
        (mem_Inter.1 this h : _)
      have B : x ∈ q ⟨(s n, s m), h.symm⟩ \ q ⟨(s m, s n), h⟩ :=
        have := mem_Inter.1 (hxs n).2 (s m)
        (mem_Inter.1 this h.symm : _)
      exact A.2 B.1
    -- the points `y n` are nearby, and therefore they form a Cauchy sequence.
    have cauchy_y : CauchySeq y := by
      have : tendsto (fun n => 2 * u n) at_top (𝓝 0) := by
        simpa only [mul_zero] using u_lim.const_mul 2
      apply cauchy_seq_of_le_tendsto_0' (fun n => 2 * u n) (fun m n hmn => _) this
      rcases I m n with ⟨z, zsm, zsn⟩
      calc dist (y m) (y n) ≤ dist (y m) z + dist z (y n) := dist_triangle _ _ _ _ ≤ u m + u n :=
          add_le_add ((dist_le_diam_of_mem (hs m).1 (hy m) zsm).trans (hs m).2)
            ((dist_le_diam_of_mem (hs n).1 zsn (hy n)).trans (hs n).2)_ ≤ 2 * u m :=
          by
          linarith [u_anti.antitone hmn]
    have : Nonempty γ := ⟨y 0⟩
    -- let `z` be its limit.
    let z := limₓ at_top y
    have y_lim : tendsto y at_top (𝓝 z) := cauchy_y.tendsto_lim
    suffices f z = x by
      rw [← this]
      exact mem_range_self _
    -- assume for a contradiction that `f z ≠ x`.
    by_contra' hne
    -- introduce disjoint open sets `v` and `w` separating `f z` from `x`.
    obtain ⟨v, w, v_open, w_open, fzv, xw, hvw⟩ : ∃ v w : Set β, IsOpen v ∧ IsOpen w ∧ f z ∈ v ∧ x ∈ w ∧ v ∩ w = ∅ :=
      t2_separation hne
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ > (0 : ℝ), ball z δ ⊆ f ⁻¹' v := by
      apply Metric.mem_nhds_iff.1
      exact f_cont.continuous_at.preimage_mem_nhds (v_open.mem_nhds fzv)
    obtain ⟨n, hn⟩ : ∃ n, u n + dist (y n) z < δ :=
      have : tendsto (fun n => u n + dist (y n) z) at_top (𝓝 0) := by
        simpa only [add_zeroₓ] using u_lim.add (tendsto_iff_dist_tendsto_zero.1 y_lim)
      ((tendsto_order.1 this).2 _ δpos).exists
    -- for large enough `n`, the image of `s n` is contained in `v`, by continuity of `f`.
    have fsnv : f '' s n ⊆ v := by
      rw [image_subset_iff]
      apply subset.trans _ hδ
      intro a ha
      calc dist a z ≤ dist a (y n) + dist (y n) z := dist_triangle _ _ _ _ ≤ u n + dist (y n) z :=
          add_le_add_right ((dist_le_diam_of_mem (hs n).1 ha (hy n)).trans (hs n).2) _ _ < δ := hn
    -- as `x` belongs to the closure of `f '' (s n)`, it belongs to the closure of `v`.
    have : x ∈ Closure v := closure_mono fsnv (hxs n).1
    -- this is a contradiction, as `x` is supposed to belong to `w`, which is disjoint from
    -- the closure of `v`.
    exact disjoint_left.1 ((disjoint_iff_inter_eq_empty.2 hvw).closure_left w_open) this xw
    

theorem _root_.is_closed.measurable_set_image_of_continuous_on_inj_on {β : Type _} [TopologicalSpace β] [T2Space β]
    [MeasurableSpace β] [BorelSpace β] {s : Set γ} (hs : IsClosed s) {f : γ → β} (f_cont : ContinuousOn f s)
    (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  rw [image_eq_range]
  have : PolishSpace s := IsClosed.polish_space hs
  apply measurable_set_range_of_continuous_injective
  · rwa [continuous_on_iff_continuous_restrict] at f_cont
    
  · rwa [inj_on_iff_injective] at f_inj
    

variable [MeasurableSpace γ] [BorelSpace γ] {β : Type _} [tβ : TopologicalSpace β] [T2Space β] [MeasurableSpace β]
  [BorelSpace β] {s : Set γ} {f : γ → β}

include tβ

/-- The Lusin-Souslin theorem: if `s` is Borel-measurable in a Polish space, then its image under
a continuous injective map is also Borel-measurable. -/
theorem _root_.measurable_set.image_of_continuous_on_inj_on (hs : MeasurableSet s) (f_cont : ContinuousOn f s)
    (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  obtain ⟨t', t't, t'_polish, s_closed, s_open⟩ :
    ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @PolishSpace γ t' ∧ @IsClosed γ t' s ∧ @IsOpen γ t' s := hs.is_clopenable
  exact
    @IsClosed.measurable_set_image_of_continuous_on_inj_on γ t' t'_polish β _ _ _ _ s s_closed f (f_cont.mono_dom t't)
      f_inj

/-- The Lusin-Souslin theorem: if `s` is Borel-measurable in a Polish space, then its image under
a measurable injective map taking values in a second-countable topological space
is also Borel-measurable. -/
theorem _root_.measurable_set.image_of_measurable_inj_on [SecondCountableTopology β] (hs : MeasurableSet s)
    (f_meas : Measurable f) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  -- for a finer Polish topology, `f` is continuous. Therefore, one may apply the corresponding
  -- result for continuous maps.
  obtain ⟨t', t't, f_cont, t'_polish⟩ :
    ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @Continuous γ β t' tβ f ∧ @PolishSpace γ t' := f_meas.exists_continuous
  have M : measurable_set[@borel γ t'] s :=
    @Continuous.measurable γ γ t' (@borel γ t')
      (@BorelSpace.opens_measurable γ t' (@borel γ t')
        (by
          constructor
          rfl))
      tγ _ _ _ (continuous_id_of_le t't) s hs
  exact
    @MeasurableSet.image_of_continuous_on_inj_on γ t' t'_polish (@borel γ t')
      (by
        constructor
        rfl)
      β _ _ _ _ s f M (@Continuous.continuous_on γ β t' tβ f s f_cont) f_inj

/-- An injective continuous function on a Polish space is a measurable embedding. -/
theorem _root_.continuous.measurable_embedding (f_cont : Continuous f) (f_inj : Injective f) : MeasurableEmbedding f :=
  { Injective := f_inj, Measurable := f_cont.Measurable,
    measurable_set_image' := fun u hu => hu.image_of_continuous_on_inj_on f_cont.ContinuousOn (f_inj.InjOn _) }

/-- If `s` is Borel-measurable in a Polish space and `f` is continuous injective on `s`, then
the restriction of `f` to `s` is a measurable embedding. -/
theorem _root_.continuous_on.measurable_embedding (hs : MeasurableSet s) (f_cont : ContinuousOn f s)
    (f_inj : InjOn f s) : MeasurableEmbedding (s.restrict f) :=
  { Injective := inj_on_iff_injective.1 f_inj,
    Measurable := (continuous_on_iff_continuous_restrict.1 f_cont).Measurable,
    measurable_set_image' := by
      intro u hu
      have A : MeasurableSet ((coe : s → γ) '' u) := (MeasurableEmbedding.subtype_coe hs).measurable_set_image.2 hu
      have B : MeasurableSet (f '' ((coe : s → γ) '' u)) :=
        A.image_of_continuous_on_inj_on (f_cont.mono (Subtype.coe_image_subset s u))
          (f_inj.mono (Subtype.coe_image_subset s u))
      rwa [← image_comp] at B }

/-- An injective measurable function from a Polish space to a second-countable topological space
is a measurable embedding. -/
theorem _root_.measurable.measurable_embedding [SecondCountableTopology β] (f_meas : Measurable f)
    (f_inj : Injective f) : MeasurableEmbedding f :=
  { Injective := f_inj, Measurable := f_meas,
    measurable_set_image' := fun u hu => hu.image_of_measurable_inj_on f_meas (f_inj.InjOn _) }

omit tβ

/-- In a Polish space, a set is clopenable if and only if it is Borel-measurable. -/
theorem is_clopenable_iff_measurable_set : IsClopenable s ↔ MeasurableSet s := by
  -- we already know that a measurable set is clopenable. Conversely, assume that `s` is clopenable.
  refine' ⟨fun hs => _, fun hs => hs.IsClopenable⟩
  -- consider a finer topology `t'` in which `s` is open and closed.
  obtain ⟨t', t't, t'_polish, s_closed, s_open⟩ :
    ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @PolishSpace γ t' ∧ @IsClosed γ t' s ∧ @IsOpen γ t' s := hs
  -- the identity is continuous from `t'` to `tγ`.
  have C : @Continuous γ γ t' tγ id := continuous_id_of_le t't
  -- therefore, it is also a measurable embedding, by the Lusin-Souslin theorem
  have E :=
    @Continuous.measurable_embedding γ t' t'_polish (@borel γ t')
      (by
        constructor
        rfl)
      γ tγ (PolishSpace.t2_space γ) _ _ id C injective_id
  -- the set `s` is measurable for `t'` as it is closed.
  have M : @MeasurableSet γ (@borel γ t') s :=
    @IsClosed.measurable_set γ s t' (@borel γ t')
      (@BorelSpace.opens_measurable γ t' (@borel γ t')
        (by
          constructor
          rfl))
      s_closed
  -- therefore, its image under the measurable embedding `id` is also measurable for `tγ`.
  convert E.measurable_set_image.2 M
  simp only [id.def, image_id']

end MeasureTheory

