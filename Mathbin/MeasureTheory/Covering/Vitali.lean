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


variable{α : Type _}

open Set Metric MeasureTheory TopologicalSpace Filter

open_locale Nnreal Classical Ennreal TopologicalSpace

namespace Vitali

-- error in MeasureTheory.Covering.Vitali: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Vitali covering theorem: given a set `t` of subsets of a type, one may extract a disjoint
subfamily `u` such that the `τ`-enlargment of this family covers all elements of `t`, where `τ > 1`
is any fixed number.

When `t` is a family of balls, the `τ`-enlargment of `ball x r` is `ball x ((1+2τ) r)`. In general,
it is expressed in terms of a function `δ` (think "radius" or "diameter"), positive and bounded on
all elements of `t`. The condition is that every element `a` of `t` should intersect an
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`.
-/
theorem exists_disjoint_subfamily_covering_enlargment
(t : set (set α))
(δ : set α → exprℝ())
(τ : exprℝ())
(hτ : «expr < »(1, τ))
(δnonneg : ∀ a «expr ∈ » t, «expr ≤ »(0, δ a))
(R : exprℝ())
(δle : ∀ a «expr ∈ » t, «expr ≤ »(δ a, R))
(hne : ∀
 a «expr ∈ » t, set.nonempty a) : «expr∃ , »((u «expr ⊆ » t), «expr ∧ »(u.pairwise_disjoint id, ∀
  a «expr ∈ » t, «expr∃ , »((b «expr ∈ » u), «expr ∧ »(set.nonempty «expr ∩ »(a, b), «expr ≤ »(δ a, «expr * »(τ, δ b)))))) :=
begin
  let [ident T] [":", expr set (set (set α))] [":=", expr {u | «expr ∧ »(«expr ⊆ »(u, t), «expr ∧ »(u.pairwise_disjoint id, ∀
     a «expr ∈ » t, ∀
     b «expr ∈ » u, set.nonempty «expr ∩ »(a, b) → «expr∃ , »((c «expr ∈ » u), «expr ∧ »(«expr ∩ »(a, c).nonempty, «expr ≤ »(δ a, «expr * »(τ, δ c))))))}],
  obtain ["⟨", ident u, ",", ident uT, ",", ident hu, "⟩", ":", expr «expr∃ , »((u «expr ∈ » T), ∀
    v «expr ∈ » T, «expr ⊆ »(u, v) → «expr = »(v, u))],
  { refine [expr zorn.zorn_subset _ (λ U UT hU, _)],
    refine [expr ⟨«expr⋃₀ »(U), _, λ s hs, subset_sUnion_of_mem hs⟩],
    simp [] [] ["only"] ["[", expr set.sUnion_subset_iff, ",", expr and_imp, ",", expr exists_prop, ",", expr forall_exists_index, ",", expr set.mem_set_of_eq, "]"] [] [],
    refine [expr ⟨λ
      u hu, (UT hu).1, (pairwise_disjoint_sUnion hU.directed_on).2 (λ u hu, (UT hu).2.1), λ a hat b u uU hbu hab, _⟩],
    obtain ["⟨", ident c, ",", ident cu, ",", ident ac, ",", ident hc, "⟩", ":", expr «expr∃ , »((c : set α)
      (H : «expr ∈ »(c, u)), «expr ∧ »(«expr ∩ »(a, c).nonempty, «expr ≤ »(δ a, «expr * »(τ, δ c)))), ":=", expr (UT uU).2.2 a hat b hbu hab],
    exact [expr ⟨c, ⟨u, uU, cu⟩, ac, hc⟩] },
  refine [expr ⟨u, uT.1, uT.2.1, λ a hat, _⟩],
  contrapose ["!"] [ident hu],
  have [ident a_disj] [":", expr ∀ c «expr ∈ » u, disjoint a c] [],
  { assume [binders (c hc)],
    by_contra [],
    rw [expr not_disjoint_iff_nonempty_inter] ["at", ident h],
    obtain ["⟨", ident d, ",", ident du, ",", ident ad, ",", ident hd, "⟩", ":", expr «expr∃ , »((d : set α)
      (H : «expr ∈ »(d, u)), «expr ∧ »(«expr ∩ »(a, d).nonempty, «expr ≤ »(δ a, «expr * »(τ, δ d)))), ":=", expr uT.2.2 a hat c hc h],
    exact [expr lt_irrefl _ ((hu d du ad).trans_le hd)] },
  let [ident A] [] [":=", expr {a' | «expr ∧ »(«expr ∈ »(a', t), ∀ c «expr ∈ » u, disjoint a' c)}],
  have [ident Anonempty] [":", expr A.nonempty] [":=", expr ⟨a, hat, a_disj⟩],
  let [ident m] [] [":=", expr Sup «expr '' »(δ, A)],
  have [ident bddA] [":", expr bdd_above «expr '' »(δ, A)] [],
  { refine [expr ⟨R, λ x xA, _⟩],
    rcases [expr (mem_image _ _ _).1 xA, "with", "⟨", ident a', ",", ident ha', ",", ident rfl, "⟩"],
    exact [expr δle a' ha'.1] },
  obtain ["⟨", ident a', ",", ident a'A, ",", ident ha', "⟩", ":", expr «expr∃ , »((a' «expr ∈ » A), «expr ≤ »(«expr / »(m, τ), δ a'))],
  { have [] [":", expr «expr ≤ »(0, m)] [":=", expr (δnonneg a hat).trans (le_cSup bddA (mem_image_of_mem _ ⟨hat, a_disj⟩))],
    rcases [expr eq_or_lt_of_le this, "with", ident mzero, "|", ident mpos],
    { refine [expr ⟨a, ⟨hat, a_disj⟩, _⟩],
      simpa [] [] ["only"] ["[", "<-", expr mzero, ",", expr zero_div, "]"] [] ["using", expr δnonneg a hat] },
    { have [ident I] [":", expr «expr < »(«expr / »(m, τ), m)] [],
      { rw [expr div_lt_iff (zero_lt_one.trans hτ)] [],
        conv_lhs [] [] { rw ["<-", expr mul_one m] },
        exact [expr (mul_lt_mul_left mpos).2 hτ] },
      rcases [expr exists_lt_of_lt_cSup (nonempty_image_iff.2 Anonempty) I, "with", "⟨", ident x, ",", ident xA, ",", ident hx, "⟩"],
      rcases [expr (mem_image _ _ _).1 xA, "with", "⟨", ident a', ",", ident ha', ",", ident rfl, "⟩"],
      exact [expr ⟨a', ha', hx.le⟩] } },
  clear [ident hat, ident hu, ident a_disj, ident a],
  have [ident a'_ne_u] [":", expr «expr ∉ »(a', u)] [":=", expr λ
   H, (hne _ a'A.1).ne_empty (disjoint_self.1 (a'A.2 _ H))],
  refine [expr ⟨insert a' u, ⟨_, _, _⟩, subset_insert _ _, (ne_insert_of_not_mem _ a'_ne_u).symm⟩],
  { rw [expr insert_subset] [],
    exact [expr ⟨a'A.1, uT.1⟩] },
  { exact [expr uT.2.1.insert (λ b bu ba', a'A.2 b bu)] },
  { assume [binders (c ct b ba'u hcb)],
    by_cases [expr H, ":", expr «expr∃ , »((d «expr ∈ » u), set.nonempty «expr ∩ »(c, d))],
    { rcases [expr H, "with", "⟨", ident d, ",", ident du, ",", ident hd, "⟩"],
      rcases [expr uT.2.2 c ct d du hd, "with", "⟨", ident d', ",", ident d'u, ",", ident hd', "⟩"],
      exact [expr ⟨d', mem_insert_of_mem _ d'u, hd'⟩] },
    { push_neg ["at", ident H],
      simp [] [] ["only"] ["[", "<-", expr not_disjoint_iff_nonempty_inter, ",", expr not_not, "]"] [] ["at", ident H],
      rcases [expr mem_insert_iff.1 ba'u, "with", ident rfl, "|", ident H'],
      { refine [expr ⟨b, mem_insert _ _, hcb, _⟩],
        calc
          «expr ≤ »(δ c, m) : le_cSup bddA (mem_image_of_mem _ ⟨ct, H⟩)
          «expr = »(..., «expr * »(τ, «expr / »(m, τ))) : by { field_simp [] ["[", expr (zero_lt_one.trans hτ).ne', "]"] [] [],
            ring [] }
          «expr ≤ »(..., «expr * »(τ, δ b)) : mul_le_mul_of_nonneg_left ha' (zero_le_one.trans hτ.le) },
      { rw ["<-", expr not_disjoint_iff_nonempty_inter] ["at", ident hcb],
        exact [expr (hcb (H _ H')).elim] } } }
end

/-- Vitali covering theorem, closed balls version: given a family `t` of closed balls, one can
extract a disjoint subfamily `u ⊆ t` so that all balls in `t` are covered by the 5-times
dilations of balls in `u`. -/
theorem exists_disjoint_subfamily_covering_enlargment_closed_ball [MetricSpace α] (t : Set (Set α)) (R : ℝ)
  (ht : ∀ s _ : s ∈ t, ∃ x r, s = closed_ball x r ∧ r ≤ R) :
  ∃ (u : _)(_ : u ⊆ t), u.pairwise_disjoint id ∧ ∀ a _ : a ∈ t, ∃ x r, closed_ball x r ∈ u ∧ a ⊆ closed_ball x (5*r) :=
  by 
    rcases eq_empty_or_nonempty t with (rfl | tnonempty)
    ·
      exact
        ⟨∅, subset.refl _, pairwise_disjoint_empty,
          by 
            simp ⟩
    haveI  : Inhabited α
    ·
      choose s hst using tnonempty 
      choose x r hxr using ht s hst 
      exact ⟨x⟩
    rcases eq_or_ne t {∅} with (rfl | t_ne_empty)
    ·
      refine' ⟨{∅}, subset.refl _, _⟩
      simp only [true_andₓ, closed_ball_eq_empty, mem_singleton_iff, and_trueₓ, empty_subset, forall_eq,
        pairwise_disjoint_singleton, exists_const]
      exact
        ⟨-1,
          by 
            simp only [Right.neg_neg_iff, zero_lt_one]⟩
    choose! x r hxr using ht 
    have r_nonneg : ∀ a : Set α, a ∈ t → a.nonempty → 0 ≤ r a
    ·
      intro a hat a_nonempty 
      rw [(hxr a hat).1] at a_nonempty 
      simpa only [nonempty_closed_ball] using a_nonempty 
    let t' := { a ∈ t | 0 ≤ r a }
    obtain ⟨u', u't', u'_disj, hu'⟩ :
      ∃ (u' : _)(_ : u' ⊆ t'),
        u'.pairwise_disjoint id ∧ ∀ a _ : a ∈ t', ∃ (b : _)(_ : b ∈ u'), Set.Nonempty (a ∩ b) ∧ r a ≤ 2*r b
    ·
      refine'
        exists_disjoint_subfamily_covering_enlargment t' r 2 one_lt_two (fun a ha => ha.2) R
          (fun a ha => (hxr a ha.1).2) fun a ha => _ 
      rw [(hxr a ha.1).1]
      simp only [ha.2, nonempty_closed_ball]
    have u'_nonempty : u'.nonempty
    ·
      have  : ∃ (a : _)(_ : a ∈ t), a ≠ ∅
      ·
        contrapose! t_ne_empty 
        apply subset.antisymm
        ·
          simpa only using t_ne_empty
        ·
          rcases tnonempty with ⟨a, hat⟩
          have  := t_ne_empty a hat 
          simpa only [this, singleton_subset_iff] using hat 
      rcases this with ⟨a, hat, a_nonempty⟩
      have ranonneg : 0 ≤ r a := r_nonneg a hat (ne_empty_iff_nonempty.1 a_nonempty)
      rcases hu' a ⟨hat, ranonneg⟩ with ⟨b, bu', hb⟩
      exact ⟨b, bu'⟩
    refine' ⟨u', fun a ha => (u't' ha).1, u'_disj, fun a hat => _⟩
    rcases eq_empty_or_nonempty a with (rfl | a_nonempty)
    ·
      rcases u'_nonempty with ⟨b, hb⟩
      refine' ⟨x b, r b, _, empty_subset _⟩
      rwa [←(hxr b (u't' hb).1).1]
    ·
      have hat' : a ∈ t' := ⟨hat, r_nonneg a hat a_nonempty⟩
      obtain ⟨a', a'u', aa', raa'⟩ : ∃ (a' : Set α)(H : a' ∈ u'), (a ∩ a').Nonempty ∧ r a ≤ 2*r a' := hu' a hat' 
      refine' ⟨x a', r a', _, _⟩
      ·
        convert a'u' 
        exact (hxr a' (u't' a'u').1).1.symm
      ·
        rw [(hxr a hat'.1).1] at aa'⊢
        rw [(hxr a' (u't' a'u').1).1] at aa' 
        have  : dist (x a) (x a') ≤ r a+r a' := dist_le_add_of_nonempty_closed_ball_inter_closed_ball aa' 
        apply closed_ball_subset_closed_ball' 
        linarith

-- error in MeasureTheory.Covering.Vitali: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- The measurable Vitali covering theorem. Assume one is given a family `t` of closed sets with
nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a definite
proportion of the ball `B (x, 6 r)` for a given measure `μ` (think of the situation where `μ` is
a doubling measure and `t` is a family of balls). Consider a (possible non-measurable) set `s`
at which the family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`.
Then one can extract from `t` a disjoint subfamily that covers almost all `s`. -/
theorem exists_disjoint_covering_ae
[metric_space α]
[measurable_space α]
[opens_measurable_space α]
[second_countable_topology α]
(μ : measure α)
[is_locally_finite_measure μ]
(s : set α)
(t : set (set α))
(hf : ∀
 x «expr ∈ » s, ∀
 ε «expr > » (0 : exprℝ()), «expr∃ , »((a «expr ∈ » t), «expr ∧ »(«expr ∈ »(x, a), «expr ⊆ »(a, closed_ball x ε))))
(ht : ∀ a «expr ∈ » t, (interior a).nonempty)
(h't : ∀ a «expr ∈ » t, is_closed a)
(C : «exprℝ≥0»())
(h : ∀
 a «expr ∈ » t, «expr∃ , »((x «expr ∈ » a), «expr ≤ »(μ (closed_ball x «expr * »(3, diam a)), «expr * »(C, μ a)))) : «expr∃ , »((u «expr ⊆ » t), «expr ∧ »(countable u, «expr ∧ »(u.pairwise_disjoint id, «expr = »(μ «expr \ »(s, «expr⋃ , »((a «expr ∈ » u), a)), 0)))) :=
begin
  rcases [expr eq_empty_or_nonempty s, "with", ident rfl, "|", ident nonempty],
  { refine [expr ⟨«expr∅»(), empty_subset _, countable_empty, pairwise_disjoint_empty, by simp [] [] ["only"] ["[", expr measure_empty, ",", expr Union_false, ",", expr Union_empty, ",", expr diff_self, "]"] [] []⟩] },
  haveI [] [":", expr inhabited α] [],
  { choose [] [ident x] [ident hx] ["using", expr nonempty],
    exact [expr ⟨x⟩] },
  have [] [":", expr ∀
   x, «expr∃ , »((r), «expr ∧ »(«expr < »(0, r), «expr ∧ »(«expr ≤ »(r, 1), «expr < »(μ (closed_ball x «expr * »(20, r)), «expr∞»()))))] [],
  { assume [binders (x)],
    obtain ["⟨", ident R, ",", ident Rpos, ",", ident μR, "⟩", ":", expr «expr∃ , »((R : exprℝ())
      (hR : «expr < »(0, R)), «expr < »(μ (closed_ball x R), «expr∞»())), ":=", expr (μ.finite_at_nhds x).exists_mem_basis nhds_basis_closed_ball],
    refine [expr ⟨min 1 «expr / »(R, 20), _, min_le_left _ _, _⟩],
    { simp [] [] ["only"] ["[", expr true_and, ",", expr lt_min_iff, ",", expr zero_lt_one, "]"] [] [],
      linarith [] [] [] },
    { apply [expr lt_of_le_of_lt (measure_mono _) μR],
      apply [expr closed_ball_subset_closed_ball],
      calc
        «expr ≤ »(«expr * »(20, min 1 «expr / »(R, 20)), «expr * »(20, «expr / »(R, 20))) : mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num [] [])
        «expr = »(..., R) : by ring [] } },
  choose [] [ident r] [ident hr] ["using", expr this],
  let [ident t'] [] [":=", expr {a ∈ t | «expr∃ , »((x), «expr ⊆ »(a, closed_ball x (r x)))}],
  obtain ["⟨", ident u, ",", ident ut', ",", ident u_disj, ",", ident hu, "⟩", ":", expr «expr∃ , »((u «expr ⊆ » t'), «expr ∧ »(u.pairwise_disjoint id, ∀
     a «expr ∈ » t', «expr∃ , »((b «expr ∈ » u), «expr ∧ »(set.nonempty «expr ∩ »(a, b), «expr ≤ »(diam a, «expr * »(2, diam b))))))],
  { have [ident A] [":", expr ∀ a : set α, «expr ∈ »(a, t') → «expr ≤ »(diam a, 2)] [],
    { rintros [ident a, "⟨", ident hat, ",", "⟨", ident x, ",", ident hax, "⟩", "⟩"],
      calc
        «expr ≤ »(diam a, diam (closed_ball x (r x))) : diam_mono hax bounded_closed_ball
        «expr ≤ »(..., «expr * »(2, r x)) : diam_closed_ball (hr x).1.le
        «expr ≤ »(..., «expr * »(2, 1)) : mul_le_mul_of_nonneg_left (hr x).2.1 zero_le_two
        «expr = »(..., 2) : by norm_num [] [] },
    have [ident B] [":", expr ∀
     a : set α, «expr ∈ »(a, t') → a.nonempty] [":=", expr λ a hat', set.nonempty.mono interior_subset (ht a hat'.1)],
    exact [expr exists_disjoint_subfamily_covering_enlargment t' diam 2 one_lt_two (λ a ha, diam_nonneg) 2 A B] },
  have [ident ut] [":", expr «expr ⊆ »(u, t)] [":=", expr λ a hau, (ut' hau).1],
  have [ident u_count] [":", expr countable u] [":=", expr u_disj.countable_of_nonempty_interior (λ
    a ha, ht a (ut ha))],
  refine [expr ⟨u, λ a hat', (ut' hat').1, u_count, u_disj, _⟩],
  refine [expr null_of_locally_null _ (λ x hx, _)],
  let [ident v] [] [":=", expr {a ∈ u | «expr ∩ »(a, ball x (r x)).nonempty}],
  have [ident vu] [":", expr «expr ⊆ »(v, u)] [":=", expr λ a ha, ha.1],
  obtain ["⟨", ident R, ",", ident μR, ",", ident hR, "⟩", ":", expr «expr∃ , »((R), «expr ∧ »(«expr < »(μ (closed_ball x R), «expr∞»()), ∀
     a «expr ∈ » u, «expr ∩ »(a, ball x (r x)).nonempty → «expr ⊆ »(a, closed_ball x R)))],
  { have [] [":", expr ∀
     a «expr ∈ » u, «expr∃ , »((y), «expr ⊆ »(a, closed_ball y (r y)))] [":=", expr λ a hau, (ut' hau).2],
    choose ["!"] [ident y] [ident hy] ["using", expr this],
    have [ident Idist_v] [":", expr ∀ a «expr ∈ » v, «expr ≤ »(dist (y a) x, «expr + »(r (y a), r x))] [],
    { assume [binders (a hav)],
      apply [expr dist_le_add_of_nonempty_closed_ball_inter_closed_ball],
      exact [expr hav.2.mono (inter_subset_inter (hy a hav.1) ball_subset_closed_ball)] },
    set [] [ident R0] [] [":="] [expr Sup «expr '' »(λ a, r (y a), v)] ["with", ident hR0],
    have [ident R0_bdd] [":", expr bdd_above «expr '' »(λ a, r (y a), v)] [],
    { refine [expr ⟨1, λ r' hr', _⟩],
      rcases [expr (mem_image _ _ _).1 hr', "with", "⟨", ident b, ",", ident hb, ",", ident rfl, "⟩"],
      exact [expr (hr _).2.1] },
    rcases [expr le_total R0 (r x), "with", ident H, "|", ident H],
    { refine [expr ⟨«expr * »(20, r x), (hr x).2.2, λ a au hax, _⟩],
      refine [expr (hy a au).trans _],
      apply [expr closed_ball_subset_closed_ball'],
      have [] [":", expr «expr ≤ »(r (y a), R0)] [":=", expr le_cSup R0_bdd (mem_image_of_mem _ ⟨au, hax⟩)],
      linarith [] [] ["[", expr (hr (y a)).1.le, ",", expr (hr x).1.le, ",", expr Idist_v a ⟨au, hax⟩, "]"] },
    { have [ident R0pos] [":", expr «expr < »(0, R0)] [":=", expr (hr x).1.trans_le H],
      have [ident vnonempty] [":", expr v.nonempty] [],
      { by_contra [],
        rw ["[", "<-", expr ne_empty_iff_nonempty, ",", expr not_not, "]"] ["at", ident h],
        simp [] [] ["only"] ["[", expr h, ",", expr real.Sup_empty, ",", expr image_empty, "]"] [] ["at", ident hR0],
        exact [expr lt_irrefl _ (R0pos.trans_le (le_of_eq hR0))] },
      obtain ["⟨", ident a, ",", ident hav, ",", ident R0a, "⟩", ":", expr «expr∃ , »((a «expr ∈ » v), «expr < »(«expr / »(R0, 2), r (y a)))],
      { obtain ["⟨", ident r', ",", ident r'mem, ",", ident hr', "⟩", ":", expr «expr∃ , »((r' «expr ∈ » «expr '' »(λ
            a, r (y a), v)), «expr < »(«expr / »(R0, 2), r')), ":=", expr exists_lt_of_lt_cSup (nonempty_image_iff.2 vnonempty) (half_lt_self R0pos)],
        rcases [expr (mem_image _ _ _).1 r'mem, "with", "⟨", ident a, ",", ident hav, ",", ident rfl, "⟩"],
        exact [expr ⟨a, hav, hr'⟩] },
      refine [expr ⟨«expr * »(8, R0), _, _⟩],
      { apply [expr lt_of_le_of_lt (measure_mono _) (hr (y a)).2.2],
        apply [expr closed_ball_subset_closed_ball'],
        rw [expr dist_comm] [],
        linarith [] [] ["[", expr Idist_v a hav, "]"] },
      { assume [binders (b bu hbx)],
        refine [expr (hy b bu).trans _],
        apply [expr closed_ball_subset_closed_ball'],
        have [] [":", expr «expr ≤ »(r (y b), R0)] [":=", expr le_cSup R0_bdd (mem_image_of_mem _ ⟨bu, hbx⟩)],
        linarith [] [] ["[", expr Idist_v b ⟨bu, hbx⟩, "]"] } } },
  refine [expr ⟨ball x (r x), _, le_antisymm (le_of_forall_le_of_dense (λ ε εpos, _)) bot_le⟩],
  { apply [expr mem_nhds_within_of_mem_nhds (is_open_ball.mem_nhds _)],
    simp [] [] ["only"] ["[", expr (hr x).left, ",", expr mem_ball, ",", expr dist_self, "]"] [] [] },
  have [ident I] [":", expr «expr < »(«expr∑' , »((a : v), μ a), «expr∞»())] [],
  { calc
      «expr = »(«expr∑' , »((a : v), μ a), μ «expr⋃ , »((a «expr ∈ » v), a)) : begin
        rw [expr measure_bUnion (u_count.mono vu) _ (λ a ha, (h't _ (vu.trans ut ha)).measurable_set)] [],
        exact [expr u_disj.subset vu]
      end
      «expr ≤ »(..., μ (closed_ball x R)) : measure_mono (bUnion_subset (λ a ha, hR a (vu ha) ha.2))
      «expr < »(..., «expr∞»()) : μR },
  obtain ["⟨", ident w, ",", ident hw, "⟩", ":", expr «expr∃ , »((w : finset «expr↥ »(v)), «expr < »(«expr∑' , »((a : {a // «expr ∉ »(a, w)}), μ a), «expr / »(ε, C)))],
  { haveI [] [":", expr ne_bot (at_top : filter (finset v))] [":=", expr at_top_ne_bot],
    have [] [":", expr «expr < »(0, «expr / »(ε, C))] [],
    by simp [] [] ["only"] ["[", expr ennreal.div_pos_iff, ",", expr εpos.ne', ",", expr ennreal.coe_ne_top, ",", expr ne.def, ",", expr not_false_iff, ",", expr and_self, "]"] [] [],
    exact [expr ((tendsto_order.1 (ennreal.tendsto_tsum_compl_at_top_zero I.ne)).2 _ this).exists] },
  choose ["!"] [ident y] [ident hy] ["using", expr h],
  have [ident M] [":", expr «expr ⊆ »(«expr ∩ »(«expr \ »(s, «expr⋃ , »((a : set α)
       (H : «expr ∈ »(a, u)), a)), ball x (r x)), «expr⋃ , »((a : {a // «expr ∉ »(a, w)}), closed_ball (y a) «expr * »(3, diam (a : set α))))] [],
  { assume [binders (z hz)],
    set [] [ident k] [] [":="] [expr «expr⋃ , »((a : v) (ha : «expr ∈ »(a, w)), (a : set α))] ["with", ident hk],
    have [ident k_closed] [":", expr is_closed k] [":=", expr is_closed_bUnion w.finite_to_set (λ
      i hi, h't _ (ut (vu i.2)))],
    have [ident z_notmem_k] [":", expr «expr ∉ »(z, k)] [],
    { simp [] [] ["only"] ["[", expr not_exists, ",", expr exists_prop, ",", expr mem_Union, ",", expr mem_sep_eq, ",", expr forall_exists_index, ",", expr set_coe.exists, ",", expr not_and, ",", expr exists_and_distrib_right, ",", expr subtype.coe_mk, "]"] [] [],
      assume [binders (b hbv h'b h'z)],
      have [] [":", expr «expr ∈ »(z, «expr ∩ »(«expr \ »(s, «expr⋃ , »((a : set α)
           (H : «expr ∈ »(a, u)), a)), «expr⋃ , »((a : set α)
          (H : «expr ∈ »(a, u)), a)))] [":=", expr mem_inter (mem_of_mem_inter_left hz) (mem_bUnion (vu hbv) h'z)],
      simpa [] [] ["only"] ["[", expr diff_inter_self, "]"] [] [] },
    have [] [":", expr «expr ∈ »(«expr \ »(ball x (r x), k), expr𝓝() z)] [],
    { apply [expr is_open.mem_nhds (is_open_ball.sdiff k_closed) _],
      exact [expr (mem_diff _).2 ⟨mem_of_mem_inter_right hz, z_notmem_k⟩] },
    obtain ["⟨", ident d, ",", ident dpos, ",", ident hd, "⟩", ":", expr «expr∃ , »((d : exprℝ())
      (dpos : «expr < »(0, d)), «expr ⊆ »(closed_ball z d, «expr \ »(ball x (r x), k))), ":=", expr nhds_basis_closed_ball.mem_iff.1 this],
    obtain ["⟨", ident a, ",", ident hat, ",", ident za, ",", ident ad, "⟩", ":", expr «expr∃ , »((a «expr ∈ » t), «expr ∧ »(«expr ∈ »(z, a), «expr ⊆ »(a, closed_ball z d))), ":=", expr hf z ((mem_diff _).1 (mem_of_mem_inter_left hz)).1 d dpos],
    have [ident ax] [":", expr «expr ⊆ »(a, ball x (r x))] [":=", expr ad.trans (hd.trans (diff_subset (ball x (r x)) k))],
    obtain ["⟨", ident b, ",", ident bu, ",", ident ab, ",", ident bdiam, "⟩", ":", expr «expr∃ , »((b : set α)
      (H : «expr ∈ »(b, u)), «expr ∧ »(«expr ∩ »(a, b).nonempty, «expr ≤ »(diam a, «expr * »(2, diam b)))), ":=", expr hu a ⟨hat, ⟨x, ax.trans ball_subset_closed_ball⟩⟩],
    have [ident bv] [":", expr «expr ∈ »(b, v)] [],
    { refine [expr ⟨bu, ab.mono _⟩],
      rw [expr inter_comm] [],
      exact [expr inter_subset_inter_right _ ax] },
    let [ident b'] [":", expr v] [":=", expr ⟨b, bv⟩],
    have [ident b'_notmem_w] [":", expr «expr ∉ »(b', w)] [],
    { assume [binders (b'w)],
      have [ident b'k] [":", expr «expr ⊆ »((b' : set α), k)] [":=", expr finset.subset_set_bUnion_of_mem b'w],
      have [] [":", expr «expr ∩ »(«expr \ »(ball x (r x), k), k).nonempty] [":=", expr ab.mono (inter_subset_inter (ad.trans hd) b'k)],
      simpa [] [] ["only"] ["[", expr diff_inter_self, ",", expr not_nonempty_empty, "]"] [] [] },
    let [ident b''] [":", expr {a // «expr ∉ »(a, w)}] [":=", expr ⟨b', b'_notmem_w⟩],
    have [ident zb] [":", expr «expr ∈ »(z, closed_ball (y b) «expr * »(3, diam b))] [],
    { rcases [expr ab, "with", "⟨", ident e, ",", "⟨", ident ea, ",", ident eb, "⟩", "⟩"],
      have [ident A] [":", expr «expr ≤ »(dist z e, diam a)] [":=", expr dist_le_diam_of_mem (bounded_closed_ball.mono ad) za ea],
      have [ident B] [":", expr «expr ≤ »(dist e (y b), diam b)] [],
      { rcases [expr (ut' bu).2, "with", "⟨", ident c, ",", ident hc, "⟩"],
        apply [expr dist_le_diam_of_mem (bounded_closed_ball.mono hc) eb (hy b (ut bu)).1] },
      simp [] [] ["only"] ["[", expr mem_closed_ball, "]"] [] [],
      linarith [] [] ["[", expr dist_triangle z e (y b), "]"] },
    suffices [ident H] [":", expr «expr ⊆ »(closed_ball (y (b'' : set α)) «expr * »(3, diam (b'' : set α)), «expr⋃ , »((a : {a // «expr ∉ »(a, w)}), closed_ball (y (a : set α)) «expr * »(3, diam (a : set α))))],
    from [expr H zb],
    exact [expr subset_Union (λ a : {a // «expr ∉ »(a, w)}, closed_ball (y a) «expr * »(3, diam (a : set α))) b''] },
  haveI [] [":", expr encodable v] [":=", expr (u_count.mono vu).to_encodable],
  calc
    «expr ≤ »(μ «expr ∩ »(«expr \ »(s, «expr⋃ , »((a : set α)
        (H : «expr ∈ »(a, u)), a)), ball x (r x)), μ «expr⋃ , »((a : {a // «expr ∉ »(a, w)}), closed_ball (y a) «expr * »(3, diam (a : set α)))) : measure_mono M
    «expr ≤ »(..., «expr∑' , »((a : {a // «expr ∉ »(a, w)}), μ (closed_ball (y a) «expr * »(3, diam (a : set α))))) : measure_Union_le _
    «expr ≤ »(..., «expr∑' , »((a : {a // «expr ∉ »(a, w)}), «expr * »(C, μ a))) : ennreal.tsum_le_tsum (λ
     a, (hy a (ut (vu a.1.2))).2)
    «expr = »(..., «expr * »(C, «expr∑' , »((a : {a // «expr ∉ »(a, w)}), μ a))) : ennreal.tsum_mul_left
    «expr ≤ »(..., «expr * »(C, «expr / »(ε, C))) : ennreal.mul_le_mul le_rfl hw.le
    «expr ≤ »(..., ε) : ennreal.mul_div_le
end

/-- Assume that around every point there are arbitrarily small scales at which the measure is
doubling. Then the set of closed sets `a` with nonempty interior covering a fixed proportion `1/C`
of the ball `closed_ball x (3 * diam a)` forms a Vitali family. This is essentially a restatement
of the measurable Vitali theorem. -/
protected def VitaliFamily [MetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [second_countable_topology α]
  (μ : Measureₓ α) [is_locally_finite_measure μ] (C :  ℝ≥0 )
  (h : ∀ x ε _ : ε > 0, ∃ (r : _)(_ : r ∈ Ioc (0 : ℝ) ε), μ (closed_ball x (6*r)) ≤ C*μ (closed_ball x r)) :
  VitaliFamily μ :=
  { SetsAt := fun x => { a | x ∈ a ∧ IsClosed a ∧ (Interior a).Nonempty ∧ μ (closed_ball x (3*diam a)) ≤ C*μ a },
    MeasurableSet' := fun x a ha => ha.2.1.MeasurableSet, nonempty_interior := fun x a ha => ha.2.2.1,
    Nontrivial :=
      fun x ε εpos =>
        by 
          obtain ⟨r, ⟨rpos, rε⟩, μr⟩ :
            ∃ (r : _)(_ : r ∈ Ioc (0 : ℝ) ε), μ (closed_ball x (6*r)) ≤ C*μ (closed_ball x r) := h x ε εpos 
          refine' ⟨closed_ball x r, ⟨_, is_closed_ball, _, _⟩, closed_ball_subset_closed_ball rε⟩
          ·
            simp only [rpos.le, mem_closed_ball, dist_self]
          ·
            exact (nonempty_ball.2 rpos).mono ball_subset_interior_closed_ball
          ·
            apply le_transₓ (measure_mono (closed_ball_subset_closed_ball _)) μr 
            have  : diam (closed_ball x r) ≤ 2*r := diam_closed_ball rpos.le 
            linarith,
    covering :=
      by 
        intro s f fsubset ffine 
        rcases eq_empty_or_nonempty s with (rfl | H)
        ·
          exact
            ⟨∅, fun _ => ∅,
              by 
                simp ,
              by 
                simp ⟩
        haveI  : Inhabited α
        ·
          choose x hx using H 
          exact ⟨x⟩
        let t := ⋃(x : _)(_ : x ∈ s), f x 
        have A₁ : ∀ x _ : x ∈ s, ∀ ε : ℝ, 0 < ε → ∃ (a : _)(_ : a ∈ t), x ∈ a ∧ a ⊆ closed_ball x ε
        ·
          intro x xs ε εpos 
          rcases ffine x xs ε εpos with ⟨a, xa, hax⟩
          exact ⟨a, mem_bUnion xs xa, (fsubset x xs xa).1, hax⟩
        have A₂ : ∀ a _ : a ∈ t, (Interior a).Nonempty
        ·
          rintro a ha 
          rcases mem_bUnion_iff.1 ha with ⟨x, xs, xa⟩
          exact (fsubset x xs xa).2.2.1
        have A₃ : ∀ a _ : a ∈ t, IsClosed a
        ·
          rintro a ha 
          rcases mem_bUnion_iff.1 ha with ⟨x, xs, xa⟩
          exact (fsubset x xs xa).2.1
        have A₄ : ∀ a _ : a ∈ t, ∃ (x : _)(_ : x ∈ a), μ (closed_ball x (3*diam a)) ≤ C*μ a
        ·
          rintro a ha 
          rcases mem_bUnion_iff.1 ha with ⟨x, xs, xa⟩
          exact ⟨x, (fsubset x xs xa).1, (fsubset x xs xa).2.2.2⟩
        obtain ⟨u, ut, u_count, u_disj, μu⟩ :
          ∃ (u : _)(_ : u ⊆ t), u.countable ∧ u.pairwise Disjoint ∧ μ (s \ ⋃(a : _)(_ : a ∈ u), a) = 0 :=
          exists_disjoint_covering_ae μ s t A₁ A₂ A₃ C A₄ 
        have  : ∀ a _ : a ∈ u, ∃ (x : _)(_ : x ∈ s), a ∈ f x := fun a ha => mem_bUnion_iff.1 (ut ha)
        choose! x hx using this 
        have inj_on_x : inj_on x u
        ·
          intro a ha b hb hab 
          have A : (a ∩ b).Nonempty
          ·
            refine' ⟨x a, mem_inter (fsubset _ (hx a ha).1 (hx a ha).2).1 _⟩
            rw [hab]
            exact (fsubset _ (hx b hb).1 (hx b hb).2).1
          contrapose A 
          have  : Disjoint a b := u_disj a ha b hb A 
          simpa only [←not_disjoint_iff_nonempty_inter]
        refine' ⟨x '' u, Function.invFunOn x u, _, _, _, _⟩
        ·
          intro y hy 
          rcases(mem_image _ _ _).1 hy with ⟨a, au, rfl⟩
          exact (hx a au).1
        ·
          rw [inj_on_x.pairwise_disjoint_image]
          intro a ha b hb hab 
          simp only [Function.onFun, Function.inv_fun_on_eq' inj_on_x, ha, hb, · ∘ ·]
          exact u_disj a ha b hb hab
        ·
          intro y hy 
          rcases(mem_image _ _ _).1 hy with ⟨a, ha, rfl⟩
          rw [Function.inv_fun_on_eq' inj_on_x ha]
          exact (hx a ha).2
        ·
          rw [bUnion_image]
          convert μu using 3 
          exact bUnion_congr fun a ha => Function.inv_fun_on_eq' inj_on_x ha }

end Vitali

