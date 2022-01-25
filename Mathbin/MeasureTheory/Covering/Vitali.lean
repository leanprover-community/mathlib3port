import Mathbin.Topology.MetricSpace.Basic
import Mathbin.MeasureTheory.Constructions.BorelSpace
import Mathbin.MeasureTheory.Covering.VitaliFamily

/-!
# Vitali covering theorems

The topological Vitali covering theorem, in its most classical version, states the following.
Consider a family of balls `(B (x_i, r_i))_{i ∈ I}` in a metric space, with uniformly bounded
radii. Then one can extract a disjoint subfamily indexed by `J ⊆ I`, such that any `B (x_i, r_i)`
is included in a ball `B (x_j, 5 r_j)`.

We prove this theorem in `vitali.exists_disjoint_subfamily_covering_enlargment_closed_ball`.
It is deduced from a more general version, called
`vitali.exists_disjoint_subfamily_covering_enlargment`, which applies to any family of sets
together with a size function `δ` (think "radius" or "diameter").

We deduce the measurable Vitali covering theorem. Assume one is given a family `t` of closed sets
with nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a
definite proportion of the ball `B (x, 6 r)` for a given measure `μ` (think of the situation
where `μ` is a doubling measure and `t` is a family of balls). Consider a set `s` at which the
family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`. Then one
can extract from `t` a disjoint subfamily that covers almost all `s`. It is proved in
`vitali.exists_disjoint_covering_ae`.

A way to restate this theorem is to say that the set of closed sets `a` with nonempty interior
covering a fixed proportion `1/C` of the ball `closed_ball x (3 * diam a)` forms a Vitali family.
This version is given in `vitali.vitali_family`.
-/


variable {α : Type _}

open Set Metric MeasureTheory TopologicalSpace Filter

open_locale Nnreal Classical Ennreal TopologicalSpace

namespace Vitali

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (u «expr ⊆ » t)
/-- Vitali covering theorem: given a set `t` of subsets of a type, one may extract a disjoint
subfamily `u` such that the `τ`-enlargment of this family covers all elements of `t`, where `τ > 1`
is any fixed number.

When `t` is a family of balls, the `τ`-enlargment of `ball x r` is `ball x ((1+2τ) r)`. In general,
it is expressed in terms of a function `δ` (think "radius" or "diameter"), positive and bounded on
all elements of `t`. The condition is that every element `a` of `t` should intersect an
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`.
-/
theorem exists_disjoint_subfamily_covering_enlargment (t : Set (Set α)) (δ : Set α → ℝ) (τ : ℝ) (hτ : 1 < τ)
    (δnonneg : ∀, ∀ a ∈ t, ∀, 0 ≤ δ a) (R : ℝ) (δle : ∀, ∀ a ∈ t, ∀, δ a ≤ R) (hne : ∀, ∀ a ∈ t, ∀, Set.Nonempty a) :
    ∃ (u : _)(_ : u ⊆ t), u.pairwise_disjoint id ∧ ∀, ∀ a ∈ t, ∀, ∃ b ∈ u, Set.Nonempty (a ∩ b) ∧ δ a ≤ τ * δ b := by
  let T : Set (Set (Set α)) :=
    { u |
      u ⊆ t ∧
        u.pairwise_disjoint id ∧
          ∀, ∀ a ∈ t, ∀, ∀, ∀ b ∈ u, ∀, Set.Nonempty (a ∩ b) → ∃ c ∈ u, (a ∩ c).Nonempty ∧ δ a ≤ τ * δ c }
  obtain ⟨u, uT, hu⟩ : ∃ u ∈ T, ∀, ∀ v ∈ T, ∀, u ⊆ v → v = u := by
    refine' Zorn.zorn_subset _ fun U UT hU => _
    refine' ⟨⋃₀U, _, fun s hs => subset_sUnion_of_mem hs⟩
    simp only [Set.sUnion_subset_iff, and_imp, exists_prop, forall_exists_index, Set.mem_set_of_eq]
    refine'
      ⟨fun u hu => (UT hu).1, (pairwise_disjoint_sUnion hU.directed_on).2 fun u hu => (UT hu).2.1,
        fun a hat b u uU hbu hab => _⟩
    obtain ⟨c, cu, ac, hc⟩ : ∃ (c : Set α)(H : c ∈ u), (a ∩ c).Nonempty ∧ δ a ≤ τ * δ c := (UT uU).2.2 a hat b hbu hab
    exact ⟨c, ⟨u, uU, cu⟩, ac, hc⟩
  refine' ⟨u, uT.1, uT.2.1, fun a hat => _⟩
  contrapose! hu
  have a_disj : ∀, ∀ c ∈ u, ∀, Disjoint a c := by
    intro c hc
    by_contra
    rw [not_disjoint_iff_nonempty_inter] at h
    obtain ⟨d, du, ad, hd⟩ : ∃ (d : Set α)(H : d ∈ u), (a ∩ d).Nonempty ∧ δ a ≤ τ * δ d := uT.2.2 a hat c hc h
    exact lt_irreflₓ _ ((hu d du ad).trans_le hd)
  let A := { a' | a' ∈ t ∧ ∀, ∀ c ∈ u, ∀, Disjoint a' c }
  have Anonempty : A.nonempty := ⟨a, hat, a_disj⟩
  let m := Sup (δ '' A)
  have bddA : BddAbove (δ '' A) := by
    refine' ⟨R, fun x xA => _⟩
    rcases(mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩
    exact δle a' ha'.1
  obtain ⟨a', a'A, ha'⟩ : ∃ a' ∈ A, m / τ ≤ δ a' := by
    have : 0 ≤ m := (δnonneg a hat).trans (le_cSup bddA (mem_image_of_mem _ ⟨hat, a_disj⟩))
    rcases eq_or_lt_of_le this with (mzero | mpos)
    · refine' ⟨a, ⟨hat, a_disj⟩, _⟩
      simpa only [← mzero, zero_div] using δnonneg a hat
      
    · have I : m / τ < m := by
        rw [div_lt_iff (zero_lt_one.trans hτ)]
        conv_lhs => rw [← mul_oneₓ m]
        exact (mul_lt_mul_left mpos).2 hτ
      rcases exists_lt_of_lt_cSup (nonempty_image_iff.2 Anonempty) I with ⟨x, xA, hx⟩
      rcases(mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩
      exact ⟨a', ha', hx.le⟩
      
  clear hat hu a_disj a
  have a'_ne_u : a' ∉ u := fun H => (hne _ a'A.1).ne_empty (disjoint_self.1 (a'A.2 _ H))
  refine' ⟨insert a' u, ⟨_, _, _⟩, subset_insert _ _, (ne_insert_of_not_mem _ a'_ne_u).symm⟩
  · rw [insert_subset]
    exact ⟨a'A.1, uT.1⟩
    
  · exact uT.2.1.insert fun b bu ba' => a'A.2 b bu
    
  · intro c ct b ba'u hcb
    by_cases' H : ∃ d ∈ u, Set.Nonempty (c ∩ d)
    · rcases H with ⟨d, du, hd⟩
      rcases uT.2.2 c ct d du hd with ⟨d', d'u, hd'⟩
      exact ⟨d', mem_insert_of_mem _ d'u, hd'⟩
      
    · push_neg  at H
      simp only [← not_disjoint_iff_nonempty_inter, not_not] at H
      rcases mem_insert_iff.1 ba'u with (rfl | H')
      · refine' ⟨b, mem_insert _ _, hcb, _⟩
        calc δ c ≤ m := le_cSup bddA (mem_image_of_mem _ ⟨ct, H⟩)_ = τ * (m / τ) := by
            field_simp [(zero_lt_one.trans hτ).ne']
            ring _ ≤ τ * δ b := mul_le_mul_of_nonneg_left ha' (zero_le_one.trans hτ.le)
        
      · rw [← not_disjoint_iff_nonempty_inter] at hcb
        exact (hcb (H _ H')).elim
        
      
    

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (u' «expr ⊆ » t')
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (u «expr ⊆ » t)
/-- Vitali covering theorem, closed balls version: given a family `t` of closed balls, one can
extract a disjoint subfamily `u ⊆ t` so that all balls in `t` are covered by the 5-times
dilations of balls in `u`. -/
theorem exists_disjoint_subfamily_covering_enlargment_closed_ball [MetricSpace α] (t : Set (Set α)) (R : ℝ)
    (ht : ∀, ∀ s ∈ t, ∀, ∃ x r, s = closed_ball x r ∧ r ≤ R) :
    ∃ (u : _)(_ : u ⊆ t),
      u.pairwise_disjoint id ∧ ∀, ∀ a ∈ t, ∀, ∃ x r, closed_ball x r ∈ u ∧ a ⊆ closed_ball x (5 * r) :=
  by
  rcases eq_empty_or_nonempty t with (rfl | tnonempty)
  · exact
      ⟨∅, subset.refl _, pairwise_disjoint_empty, by
        simp ⟩
    
  have : Inhabited α := by
    choose s hst using tnonempty
    choose x r hxr using ht s hst
    exact ⟨x⟩
  rcases eq_or_ne t {∅} with (rfl | t_ne_empty)
  · refine' ⟨{∅}, subset.refl _, _⟩
    simp only [true_andₓ, closed_ball_eq_empty, mem_singleton_iff, and_trueₓ, empty_subset, forall_eq,
      pairwise_disjoint_singleton, exists_const]
    exact
      ⟨-1, by
        simp only [Right.neg_neg_iff, zero_lt_one]⟩
    
  choose! x r hxr using ht
  have r_nonneg : ∀ a : Set α, a ∈ t → a.nonempty → 0 ≤ r a := by
    intro a hat a_nonempty
    rw [(hxr a hat).1] at a_nonempty
    simpa only [nonempty_closed_ball] using a_nonempty
  let t' := { a ∈ t | 0 ≤ r a }
  obtain ⟨u', u't', u'_disj, hu'⟩ :
    ∃ (u' : _)(_ : u' ⊆ t'), u'.pairwise_disjoint id ∧ ∀, ∀ a ∈ t', ∀, ∃ b ∈ u', Set.Nonempty (a ∩ b) ∧ r a ≤ 2 * r b :=
    by
    refine'
      exists_disjoint_subfamily_covering_enlargment t' r 2 one_lt_two (fun a ha => ha.2) R (fun a ha => (hxr a ha.1).2)
        fun a ha => _
    rw [(hxr a ha.1).1]
    simp only [ha.2, nonempty_closed_ball]
  have u'_nonempty : u'.nonempty := by
    have : ∃ a ∈ t, a ≠ ∅ := by
      contrapose! t_ne_empty
      apply subset.antisymm
      · simpa only using t_ne_empty
        
      · rcases tnonempty with ⟨a, hat⟩
        have := t_ne_empty a hat
        simpa only [this, singleton_subset_iff] using hat
        
    rcases this with ⟨a, hat, a_nonempty⟩
    have ranonneg : 0 ≤ r a := r_nonneg a hat (ne_empty_iff_nonempty.1 a_nonempty)
    rcases hu' a ⟨hat, ranonneg⟩ with ⟨b, bu', hb⟩
    exact ⟨b, bu'⟩
  refine' ⟨u', fun a ha => (u't' ha).1, u'_disj, fun a hat => _⟩
  rcases eq_empty_or_nonempty a with (rfl | a_nonempty)
  · rcases u'_nonempty with ⟨b, hb⟩
    refine' ⟨x b, r b, _, empty_subset _⟩
    rwa [← (hxr b (u't' hb).1).1]
    
  · have hat' : a ∈ t' := ⟨hat, r_nonneg a hat a_nonempty⟩
    obtain ⟨a', a'u', aa', raa'⟩ : ∃ (a' : Set α)(H : a' ∈ u'), (a ∩ a').Nonempty ∧ r a ≤ 2 * r a' := hu' a hat'
    refine' ⟨x a', r a', _, _⟩
    · convert a'u'
      exact (hxr a' (u't' a'u').1).1.symm
      
    · rw [(hxr a hat'.1).1] at aa'⊢
      rw [(hxr a' (u't' a'u').1).1] at aa'
      have : dist (x a) (x a') ≤ r a + r a' := dist_le_add_of_nonempty_closed_ball_inter_closed_ball aa'
      apply closed_ball_subset_closed_ball'
      linarith
      
    

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (u «expr ⊆ » t')
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (u «expr ⊆ » t)
/-- The measurable Vitali covering theorem. Assume one is given a family `t` of closed sets with
nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a definite
proportion of the ball `B (x, 6 r)` for a given measure `μ` (think of the situation where `μ` is
a doubling measure and `t` is a family of balls). Consider a (possible non-measurable) set `s`
at which the family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`.
Then one can extract from `t` a disjoint subfamily that covers almost all `s`. -/
theorem exists_disjoint_covering_ae [MetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [second_countable_topology α] (μ : Measureₓ α) [is_locally_finite_measure μ] (s : Set α) (t : Set (Set α))
    (hf : ∀, ∀ x ∈ s, ∀, ∀, ∀ ε > (0 : ℝ), ∀, ∃ a ∈ t, x ∈ a ∧ a ⊆ closed_ball x ε)
    (ht : ∀, ∀ a ∈ t, ∀, (Interior a).Nonempty) (h't : ∀, ∀ a ∈ t, ∀, IsClosed a) (C : ℝ≥0 )
    (h : ∀, ∀ a ∈ t, ∀, ∃ x ∈ a, μ (closed_ball x (3 * diam a)) ≤ C * μ a) :
    ∃ (u : _)(_ : u ⊆ t), countable u ∧ u.pairwise_disjoint id ∧ μ (s \ ⋃ a ∈ u, a) = 0 := by
  rcases eq_empty_or_nonempty s with (rfl | nonempty)
  · refine'
      ⟨∅, empty_subset _, countable_empty, pairwise_disjoint_empty, by
        simp only [measure_empty, Union_false, Union_empty, diff_self]⟩
    
  have : Inhabited α := by
    choose x hx using Nonempty
    exact ⟨x⟩
  have : ∀ x, ∃ r, 0 < r ∧ r ≤ 1 ∧ μ (closed_ball x (20 * r)) < ∞ := by
    intro x
    obtain ⟨R, Rpos, μR⟩ : ∃ (R : ℝ)(hR : 0 < R), μ (closed_ball x R) < ∞ :=
      (μ.finite_at_nhds x).exists_mem_basis nhds_basis_closed_ball
    refine' ⟨min 1 (R / 20), _, min_le_leftₓ _ _, _⟩
    · simp only [true_andₓ, lt_min_iff, zero_lt_one]
      linarith
      
    · apply lt_of_le_of_ltₓ (measure_mono _) μR
      apply closed_ball_subset_closed_ball
      calc 20 * min 1 (R / 20) ≤ 20 * (R / 20) :=
          mul_le_mul_of_nonneg_left (min_le_rightₓ _ _)
            (by
              norm_num)_ = R :=
          by
          ring
      
  choose r hr0 hr1 hrμ
  let t' := { a ∈ t | ∃ x, a ⊆ closed_ball x (r x) }
  obtain ⟨u, ut', u_disj, hu⟩ :
    ∃ (u : _)(_ : u ⊆ t'),
      u.pairwise_disjoint id ∧ ∀, ∀ a ∈ t', ∀, ∃ b ∈ u, Set.Nonempty (a ∩ b) ∧ diam a ≤ 2 * diam b :=
    by
    have A : ∀ a : Set α, a ∈ t' → diam a ≤ 2 := by
      rintro a ⟨hat, ⟨x, hax⟩⟩
      calc diam a ≤ 2 * 1 :=
          diam_le_of_subset_closed_ball zero_le_one (hax.trans $ closed_ball_subset_closed_ball $ hr1 x)_ = 2 :=
          mul_oneₓ _
    have B : ∀ a : Set α, a ∈ t' → a.nonempty := fun a hat' => Set.Nonempty.mono interior_subset (ht a hat'.1)
    exact exists_disjoint_subfamily_covering_enlargment t' diam 2 one_lt_two (fun a ha => diam_nonneg) 2 A B
  have ut : u ⊆ t := fun a hau => (ut' hau).1
  have u_count : countable u := u_disj.countable_of_nonempty_interior fun a ha => ht a (ut ha)
  refine' ⟨u, fun a hat' => (ut' hat').1, u_count, u_disj, _⟩
  refine' null_of_locally_null _ fun x hx => _
  let v := { a ∈ u | (a ∩ ball x (r x)).Nonempty }
  have vu : v ⊆ u := fun a ha => ha.1
  obtain ⟨R, μR, hR⟩ :
    ∃ R, μ (closed_ball x R) < ∞ ∧ ∀, ∀ a ∈ u, ∀, (a ∩ ball x (r x)).Nonempty → a ⊆ closed_ball x R := by
    have : ∀, ∀ a ∈ u, ∀, ∃ y, a ⊆ closed_ball y (r y) := fun a hau => (ut' hau).2
    choose! y hy using this
    have Idist_v : ∀, ∀ a ∈ v, ∀, dist (y a) x ≤ r (y a) + r x := by
      intro a hav
      apply dist_le_add_of_nonempty_closed_ball_inter_closed_ball
      exact hav.2.mono (inter_subset_inter (hy a hav.1) ball_subset_closed_ball)
    set R0 := Sup ((fun a => r (y a)) '' v) with hR0
    have R0_bdd : BddAbove ((fun a => r (y a)) '' v) := by
      refine' ⟨1, fun r' hr' => _⟩
      rcases(mem_image _ _ _).1 hr' with ⟨b, hb, rfl⟩
      exact hr1 _
    rcases le_totalₓ R0 (r x) with (H | H)
    · refine' ⟨20 * r x, hrμ x, fun a au hax => _⟩
      refine' (hy a au).trans _
      apply closed_ball_subset_closed_ball'
      have : r (y a) ≤ R0 := le_cSup R0_bdd (mem_image_of_mem _ ⟨au, hax⟩)
      linarith [(hr0 (y a)).le, (hr0 x).le, Idist_v a ⟨au, hax⟩]
      
    · have R0pos : 0 < R0 := (hr0 x).trans_le H
      have vnonempty : v.nonempty := by
        by_contra
        rw [← ne_empty_iff_nonempty, not_not] at h
        simp only [h, Real.Sup_empty, image_empty] at hR0
        exact lt_irreflₓ _ (R0pos.trans_le (le_of_eqₓ hR0))
      obtain ⟨a, hav, R0a⟩ : ∃ a ∈ v, R0 / 2 < r (y a) := by
        obtain ⟨r', r'mem, hr'⟩ : ∃ r' ∈ (fun a => r (y a)) '' v, R0 / 2 < r' :=
          exists_lt_of_lt_cSup (nonempty_image_iff.2 vnonempty) (half_lt_self R0pos)
        rcases(mem_image _ _ _).1 r'mem with ⟨a, hav, rfl⟩
        exact ⟨a, hav, hr'⟩
      refine' ⟨8 * R0, _, _⟩
      · apply lt_of_le_of_ltₓ (measure_mono _) (hrμ (y a))
        apply closed_ball_subset_closed_ball'
        rw [dist_comm]
        linarith [Idist_v a hav]
        
      · intro b bu hbx
        refine' (hy b bu).trans _
        apply closed_ball_subset_closed_ball'
        have : r (y b) ≤ R0 := le_cSup R0_bdd (mem_image_of_mem _ ⟨bu, hbx⟩)
        linarith [Idist_v b ⟨bu, hbx⟩]
        
      
  refine'
    ⟨_ ∩ ball x (r x), inter_mem_nhds_within _ (ball_mem_nhds _ (hr0 _)),
      nonpos_iff_eq_zero.mp (le_of_forall_le_of_dense fun ε εpos => _)⟩
  have I : (∑' a : v, μ a) < ∞ := by
    calc (∑' a : v, μ a) = μ (⋃ a ∈ v, a) := by
        rw [measure_bUnion (u_count.mono vu) _ fun a ha => (h't _ (vu.trans ut ha)).MeasurableSet]
        exact u_disj.subset vu _ ≤ μ (closed_ball x R) :=
        measure_mono (Union₂_subset fun a ha => hR a (vu ha) ha.2)_ < ∞ := μR
  obtain ⟨w, hw⟩ : ∃ w : Finset (↥v), (∑' a : { a // a ∉ w }, μ a) < ε / C := by
    have : ne_bot (at_top : Filter (Finset v)) := at_top_ne_bot
    have : 0 < ε / C := by
      simp only [Ennreal.div_pos_iff, εpos.ne', Ennreal.coe_ne_top, Ne.def, not_false_iff, and_selfₓ]
    exact ((tendsto_order.1 (Ennreal.tendsto_tsum_compl_at_top_zero I.ne)).2 _ this).exists
  choose! y hy using h
  have M :
    (s \ ⋃ (a : Set α) (H : a ∈ u), a) ∩ ball x (r x) ⊆
      ⋃ a : { a // a ∉ w }, closed_ball (y a) (3 * diam (a : Set α)) :=
    by
    intro z hz
    set k := ⋃ (a : v) (ha : a ∈ w), (a : Set α) with hk
    have k_closed : IsClosed k := is_closed_bUnion w.finite_to_set fun i hi => h't _ (ut (vu i.2))
    have z_notmem_k : z ∉ k := by
      simp only [not_exists, exists_prop, mem_Union, mem_sep_eq, forall_exists_index, SetCoe.exists, not_and,
        exists_and_distrib_right, Subtype.coe_mk]
      intro b hbv h'b h'z
      have : z ∈ (s \ ⋃ (a : Set α) (H : a ∈ u), a) ∩ ⋃ (a : Set α) (H : a ∈ u), a :=
        mem_inter (mem_of_mem_inter_left hz) (mem_bUnion (vu hbv) h'z)
      simpa only [diff_inter_self]
    have : ball x (r x) \ k ∈ 𝓝 z := by
      apply IsOpen.mem_nhds (is_open_ball.sdiff k_closed) _
      exact (mem_diff _).2 ⟨mem_of_mem_inter_right hz, z_notmem_k⟩
    obtain ⟨d, dpos, hd⟩ : ∃ (d : ℝ)(dpos : 0 < d), closed_ball z d ⊆ ball x (r x) \ k :=
      nhds_basis_closed_ball.mem_iff.1 this
    obtain ⟨a, hat, za, ad⟩ : ∃ a ∈ t, z ∈ a ∧ a ⊆ closed_ball z d :=
      hf z ((mem_diff _).1 (mem_of_mem_inter_left hz)).1 d dpos
    have ax : a ⊆ ball x (r x) := ad.trans (hd.trans (diff_subset (ball x (r x)) k))
    obtain ⟨b, bu, ab, bdiam⟩ : ∃ (b : Set α)(H : b ∈ u), (a ∩ b).Nonempty ∧ diam a ≤ 2 * diam b :=
      hu a ⟨hat, ⟨x, ax.trans ball_subset_closed_ball⟩⟩
    have bv : b ∈ v := by
      refine' ⟨bu, ab.mono _⟩
      rw [inter_comm]
      exact inter_subset_inter_right _ ax
    let b' : v := ⟨b, bv⟩
    have b'_notmem_w : b' ∉ w := by
      intro b'w
      have b'k : (b' : Set α) ⊆ k := Finset.subset_set_bUnion_of_mem b'w
      have : (ball x (r x) \ k ∩ k).Nonempty := ab.mono (inter_subset_inter (ad.trans hd) b'k)
      simpa only [diff_inter_self, not_nonempty_empty]
    let b'' : { a // a ∉ w } := ⟨b', b'_notmem_w⟩
    have zb : z ∈ closed_ball (y b) (3 * diam b) := by
      rcases ab with ⟨e, ⟨ea, eb⟩⟩
      have A : dist z e ≤ diam a := dist_le_diam_of_mem (bounded_closed_ball.mono ad) za ea
      have B : dist e (y b) ≤ diam b := by
        rcases(ut' bu).2 with ⟨c, hc⟩
        apply dist_le_diam_of_mem (bounded_closed_ball.mono hc) eb (hy b (ut bu)).1
      simp only [mem_closed_ball]
      linarith [dist_triangle z e (y b)]
    suffices H :
      closed_ball (y (b'' : Set α)) (3 * diam (b'' : Set α)) ⊆
        ⋃ a : { a // a ∉ w }, closed_ball (y (a : Set α)) (3 * diam (a : Set α))
    exact H zb
    exact subset_Union (fun a : { a // a ∉ w } => closed_ball (y a) (3 * diam (a : Set α))) b''
  have : Encodable v := (u_count.mono vu).toEncodable
  calc
    μ ((s \ ⋃ (a : Set α) (H : a ∈ u), a) ∩ ball x (r x)) ≤
        μ (⋃ a : { a // a ∉ w }, closed_ball (y a) (3 * diam (a : Set α))) :=
      measure_mono M _ ≤ ∑' a : { a // a ∉ w }, μ (closed_ball (y a) (3 * diam (a : Set α))) :=
      measure_Union_le _ _ ≤ ∑' a : { a // a ∉ w }, C * μ a :=
      Ennreal.tsum_le_tsum fun a => (hy a (ut (vu a.1.2))).2_ = C * ∑' a : { a // a ∉ w }, μ a :=
      Ennreal.tsum_mul_left _ ≤ C * (ε / C) := Ennreal.mul_le_mul le_rfl hw.le _ ≤ ε := Ennreal.mul_div_le

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (u «expr ⊆ » t)
/-- Assume that around every point there are arbitrarily small scales at which the measure is
doubling. Then the set of closed sets `a` with nonempty interior covering a fixed proportion `1/C`
of the ball `closed_ball x (3 * diam a)` forms a Vitali family. This is essentially a restatement
of the measurable Vitali theorem. -/
protected def VitaliFamily [MetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [second_countable_topology α]
    (μ : Measureₓ α) [is_locally_finite_measure μ] (C : ℝ≥0 )
    (h : ∀ x, ∀ ε > 0, ∀, ∃ r ∈ Ioc (0 : ℝ) ε, μ (closed_ball x (6 * r)) ≤ C * μ (closed_ball x r)) :
    VitaliFamily μ where
  SetsAt := fun x => { a | x ∈ a ∧ IsClosed a ∧ (Interior a).Nonempty ∧ μ (closed_ball x (3 * diam a)) ≤ C * μ a }
  MeasurableSet' := fun x a ha => ha.2.1.MeasurableSet
  nonempty_interior := fun x a ha => ha.2.2.1
  Nontrivial := fun x ε εpos => by
    obtain ⟨r, ⟨rpos, rε⟩, μr⟩ : ∃ r ∈ Ioc (0 : ℝ) ε, μ (closed_ball x (6 * r)) ≤ C * μ (closed_ball x r) := h x ε εpos
    refine' ⟨closed_ball x r, ⟨_, is_closed_ball, _, _⟩, closed_ball_subset_closed_ball rε⟩
    · simp only [rpos.le, mem_closed_ball, dist_self]
      
    · exact (nonempty_ball.2 rpos).mono ball_subset_interior_closed_ball
      
    · apply le_transₓ (measure_mono (closed_ball_subset_closed_ball _)) μr
      have : diam (closed_ball x r) ≤ 2 * r := diam_closed_ball rpos.le
      linarith
      
  covering := by
    intro s f fsubset ffine
    rcases eq_empty_or_nonempty s with (rfl | H)
    · exact
        ⟨∅, fun _ => ∅, by
          simp , by
          simp ⟩
      
    have : Inhabited α := by
      choose x hx using H
      exact ⟨x⟩
    let t := ⋃ x ∈ s, f x
    have A₁ : ∀, ∀ x ∈ s, ∀, ∀ ε : ℝ, 0 < ε → ∃ a ∈ t, x ∈ a ∧ a ⊆ closed_ball x ε := by
      intro x xs ε εpos
      rcases ffine x xs ε εpos with ⟨a, xa, hax⟩
      exact ⟨a, mem_bUnion xs xa, (fsubset x xs xa).1, hax⟩
    have A₂ : ∀, ∀ a ∈ t, ∀, (Interior a).Nonempty := by
      rintro a ha
      rcases mem_Union₂.1 ha with ⟨x, xs, xa⟩
      exact (fsubset x xs xa).2.2.1
    have A₃ : ∀, ∀ a ∈ t, ∀, IsClosed a := by
      rintro a ha
      rcases mem_Union₂.1 ha with ⟨x, xs, xa⟩
      exact (fsubset x xs xa).2.1
    have A₄ : ∀, ∀ a ∈ t, ∀, ∃ x ∈ a, μ (closed_ball x (3 * diam a)) ≤ C * μ a := by
      rintro a ha
      rcases mem_Union₂.1 ha with ⟨x, xs, xa⟩
      exact ⟨x, (fsubset x xs xa).1, (fsubset x xs xa).2.2.2⟩
    obtain ⟨u, ut, u_count, u_disj, μu⟩ :
      ∃ (u : _)(_ : u ⊆ t), u.countable ∧ u.pairwise Disjoint ∧ μ (s \ ⋃ a ∈ u, a) = 0 :=
      exists_disjoint_covering_ae μ s t A₁ A₂ A₃ C A₄
    have : ∀, ∀ a ∈ u, ∀, ∃ x ∈ s, a ∈ f x := fun a ha => mem_Union₂.1 (ut ha)
    choose! x hx using this
    have inj_on_x : inj_on x u := by
      intro a ha b hb hab
      have A : (a ∩ b).Nonempty := by
        refine' ⟨x a, mem_inter (fsubset _ (hx a ha).1 (hx a ha).2).1 _⟩
        rw [hab]
        exact (fsubset _ (hx b hb).1 (hx b hb).2).1
      contrapose A
      have : Disjoint a b := u_disj ha hb A
      simpa only [← not_disjoint_iff_nonempty_inter]
    refine' ⟨x '' u, Function.invFunOn x u, _, _, _, _⟩
    · intro y hy
      rcases(mem_image _ _ _).1 hy with ⟨a, au, rfl⟩
      exact (hx a au).1
      
    · rw [inj_on_x.pairwise_disjoint_image]
      intro a ha b hb hab
      simp only [Function.onFun, inj_on_x.left_inv_on_inv_fun_on ha, inj_on_x.left_inv_on_inv_fun_on hb, · ∘ ·]
      exact u_disj ha hb hab
      
    · intro y hy
      rcases(mem_image _ _ _).1 hy with ⟨a, ha, rfl⟩
      rw [inj_on_x.left_inv_on_inv_fun_on ha]
      exact (hx a ha).2
      
    · rw [bUnion_image]
      convert μu using 3
      exact Union₂_congr fun a ha => inj_on_x.left_inv_on_inv_fun_on ha
      

end Vitali

