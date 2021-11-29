import Mathbin.Topology.Algebra.Ordered.Basic 
import Mathbin.Order.LiminfLimsup

/-!
# Lemmas about liminf and limsup in an order topology.
-/


open Filter

open_locale TopologicalSpace Classical

universe u v

variable{α : Type u}{β : Type v}

section LiminfLimsup

section OrderClosedTopology

variable[SemilatticeSup α][TopologicalSpace α][OrderTopology α]

theorem is_bounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·) :=
  match forall_le_or_exists_lt_sup a with 
  | Or.inl h => ⟨a, eventually_of_forall h⟩
  | Or.inr ⟨b, hb⟩ => ⟨b, ge_mem_nhds hb⟩

theorem Filter.Tendsto.is_bounded_under_le {f : Filter β} {u : β → α} {a : α} (h : tendsto u f (𝓝 a)) :
  f.is_bounded_under (· ≤ ·) u :=
  (is_bounded_le_nhds a).mono h

theorem Filter.Tendsto.bdd_above_range_of_cofinite {u : β → α} {a : α} (h : tendsto u cofinite (𝓝 a)) :
  BddAbove (Set.Range u) :=
  h.is_bounded_under_le.bdd_above_range_of_cofinite

theorem Filter.Tendsto.bdd_above_range {u : ℕ → α} {a : α} (h : tendsto u at_top (𝓝 a)) : BddAbove (Set.Range u) :=
  h.is_bounded_under_le.bdd_above_range

theorem is_cobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· ≥ ·) :=
  (is_bounded_le_nhds a).is_cobounded_flip

theorem Filter.Tendsto.is_cobounded_under_ge {f : Filter β} {u : β → α} {a : α} [ne_bot f] (h : tendsto u f (𝓝 a)) :
  f.is_cobounded_under (· ≥ ·) u :=
  h.is_bounded_under_le.is_cobounded_flip

end OrderClosedTopology

section OrderClosedTopology

variable[SemilatticeInf α][TopologicalSpace α][OrderTopology α]

theorem is_bounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·) :=
  @is_bounded_le_nhds (OrderDual α) _ _ _ a

theorem Filter.Tendsto.is_bounded_under_ge {f : Filter β} {u : β → α} {a : α} (h : tendsto u f (𝓝 a)) :
  f.is_bounded_under (· ≥ ·) u :=
  (is_bounded_ge_nhds a).mono h

theorem Filter.Tendsto.bdd_below_range_of_cofinite {u : β → α} {a : α} (h : tendsto u cofinite (𝓝 a)) :
  BddBelow (Set.Range u) :=
  h.is_bounded_under_ge.bdd_below_range_of_cofinite

theorem Filter.Tendsto.bdd_below_range {u : ℕ → α} {a : α} (h : tendsto u at_top (𝓝 a)) : BddBelow (Set.Range u) :=
  h.is_bounded_under_ge.bdd_below_range

theorem is_cobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· ≤ ·) :=
  (is_bounded_ge_nhds a).is_cobounded_flip

theorem Filter.Tendsto.is_cobounded_under_le {f : Filter β} {u : β → α} {a : α} [ne_bot f] (h : tendsto u f (𝓝 a)) :
  f.is_cobounded_under (· ≤ ·) u :=
  h.is_bounded_under_ge.is_cobounded_flip

end OrderClosedTopology

section ConditionallyCompleteLinearOrder

variable[ConditionallyCompleteLinearOrder α]

theorem lt_mem_sets_of_Limsup_lt {f : Filter α} {b} (h : f.is_bounded (· ≤ ·)) (l : f.Limsup < b) : ∀ᶠa in f, a < b :=
  let ⟨c, (h : ∀ᶠa in f, a ≤ c), hcb⟩ := exists_lt_of_cInf_lt h l 
  mem_of_superset h$ fun a hac => lt_of_le_of_ltₓ hac hcb

theorem gt_mem_sets_of_Liminf_gt : ∀ {f : Filter α} {b}, f.is_bounded (· ≥ ·) → b < f.Liminf → ∀ᶠa in f, b < a :=
  @lt_mem_sets_of_Limsup_lt (OrderDual α) _

variable[TopologicalSpace α][OrderTopology α]

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_Limsup_eq_Liminf {f : Filter α} {a : α} (hl : f.is_bounded (· ≤ ·)) (hg : f.is_bounded (· ≥ ·))
  (hs : f.Limsup = a) (hi : f.Liminf = a) : f ≤ 𝓝 a :=
  tendsto_order.2$
    And.intro (fun b hb => gt_mem_sets_of_Liminf_gt hg$ hi.symm ▸ hb)
      fun b hb => lt_mem_sets_of_Limsup_lt hl$ hs.symm ▸ hb

-- error in Topology.Algebra.Ordered.LiminfLimsup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem Limsup_nhds (a : α) : «expr = »(Limsup (expr𝓝() a), a) :=
cInf_eq_of_forall_ge_of_forall_gt_exists_lt (is_bounded_le_nhds a) (assume
 (a')
 (h : «expr ∈ »({n : α | «expr ≤ »(n, a')}, expr𝓝() a)), show «expr ≤ »(a, a'), from @mem_of_mem_nhds α _ a _ h) (assume
 (b)
 (hba : «expr < »(a, b)), show «expr∃ , »((c)
  (h : «expr ∈ »({n : α | «expr ≤ »(n, c)}, expr𝓝() a)), «expr < »(c, b)), from match dense_or_discrete a b with
 | or.inl ⟨c, hac, hcb⟩ := ⟨c, ge_mem_nhds hac, hcb⟩
 | or.inr ⟨_, h⟩ := ⟨a, (expr𝓝() a).sets_of_superset (gt_mem_nhds hba) h, hba⟩ end)

theorem Liminf_nhds : ∀ (a : α), Liminf (𝓝 a) = a :=
  @Limsup_nhds (OrderDual α) _ _ _

/-- If a filter is converging, its limsup coincides with its limit. -/
theorem Liminf_eq_of_le_nhds {f : Filter α} {a : α} [ne_bot f] (h : f ≤ 𝓝 a) : f.Liminf = a :=
  have hb_ge : is_bounded (· ≥ ·) f := (is_bounded_ge_nhds a).mono h 
  have hb_le : is_bounded (· ≤ ·) f := (is_bounded_le_nhds a).mono h 
  le_antisymmₓ
    (calc f.Liminf ≤ f.Limsup := Liminf_le_Limsup hb_le hb_ge 
      _ ≤ (𝓝 a).limsup := Limsup_le_Limsup_of_le h hb_ge.is_cobounded_flip (is_bounded_le_nhds a)
      _ = a := Limsup_nhds a
      )
    (calc a = (𝓝 a).liminf := (Liminf_nhds a).symm 
      _ ≤ f.Liminf := Liminf_le_Liminf_of_le h (is_bounded_ge_nhds a) hb_le.is_cobounded_flip
      )

/-- If a filter is converging, its liminf coincides with its limit. -/
theorem Limsup_eq_of_le_nhds : ∀ {f : Filter α} {a : α} [ne_bot f], f ≤ 𝓝 a → f.Limsup = a :=
  @Liminf_eq_of_le_nhds (OrderDual α) _ _ _

/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β → α} {a : α} [ne_bot f] (h : tendsto u f (𝓝 a)) :
  limsup f u = a :=
  Limsup_eq_of_le_nhds h

/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [ne_bot f] (h : tendsto u f (𝓝 a)) :
  liminf f u = a :=
  Liminf_eq_of_le_nhds h

/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value -/
theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminf f u = a) (hsup : limsup f u = a)
  (h : f.is_bounded_under (· ≤ ·) u :=  by 
    runTac 
      is_bounded_default)
  (h' : f.is_bounded_under (· ≥ ·) u :=  by 
    runTac 
      is_bounded_default) :
  tendsto u f (𝓝 a) :=
  le_nhds_of_Limsup_eq_Liminf h h' hsup hinf

-- error in Topology.Algebra.Ordered.LiminfLimsup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le
{f : filter β}
{u : β → α}
{a : α}
(hinf : «expr ≤ »(a, liminf f u))
(hsup : «expr ≤ »(limsup f u, a))
(h : f.is_bounded_under ((«expr ≤ »)) u . is_bounded_default)
(h' : f.is_bounded_under ((«expr ≥ »)) u . is_bounded_default) : tendsto u f (expr𝓝() a) :=
if hf : «expr = »(f, «expr⊥»()) then «expr ▸ »(hf.symm, tendsto_bot) else by haveI [] [":", expr ne_bot f] [":=", expr ⟨hf⟩]; exact [expr tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf) (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h']

-- error in Topology.Algebra.Ordered.LiminfLimsup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Assume that, for any `a < b`, a sequence can not be infinitely many times below `a` and
above `b`. If it is also ultimately bounded above and below, then it has to converge. This even
works if `a` and `b` are restricted to a dense subset.
-/
theorem tendsto_of_no_upcrossings
[densely_ordered α]
{f : filter β}
{u : β → α}
{s : set α}
(hs : dense s)
(H : ∀
 (a «expr ∈ » s)
 (b «expr ∈ » s), «expr < »(a, b) → «expr¬ »(«expr ∧ »(«expr∃ᶠ in , »((n), f, «expr < »(u n, a)), «expr∃ᶠ in , »((n), f, «expr < »(b, u n)))))
(h : f.is_bounded_under ((«expr ≤ »)) u . is_bounded_default)
(h' : f.is_bounded_under ((«expr ≥ »)) u . is_bounded_default) : «expr∃ , »((c : α), tendsto u f (expr𝓝() c)) :=
begin
  by_cases [expr hbot, ":", expr «expr = »(f, «expr⊥»())],
  { rw [expr hbot] [],
    exact [expr ⟨Inf «expr∅»(), tendsto_bot⟩] },
  haveI [] [":", expr ne_bot f] [":=", expr ⟨hbot⟩],
  refine [expr ⟨limsup f u, _⟩],
  apply [expr tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'],
  by_contra [ident hlt],
  push_neg ["at", ident hlt],
  obtain ["⟨", ident a, ",", "⟨", "⟨", ident la, ",", ident au, "⟩", ",", ident as, "⟩", "⟩", ":", expr «expr∃ , »((a), «expr ∧ »(«expr ∧ »(«expr < »(f.liminf u, a), «expr < »(a, f.limsup u)), «expr ∈ »(a, s))), ":=", expr dense_iff_inter_open.1 hs (set.Ioo (f.liminf u) (f.limsup u)) is_open_Ioo (set.nonempty_Ioo.2 hlt)],
  obtain ["⟨", ident b, ",", "⟨", "⟨", ident ab, ",", ident bu, "⟩", ",", ident bs, "⟩", "⟩", ":", expr «expr∃ , »((b), «expr ∧ »(«expr ∧ »(«expr < »(a, b), «expr < »(b, f.limsup u)), «expr ∈ »(b, s))), ":=", expr dense_iff_inter_open.1 hs (set.Ioo a (f.limsup u)) is_open_Ioo (set.nonempty_Ioo.2 au)],
  have [ident A] [":", expr «expr∃ᶠ in , »((n), f, «expr < »(u n, a))] [":=", expr frequently_lt_of_liminf_lt (is_bounded.is_cobounded_ge h) la],
  have [ident B] [":", expr «expr∃ᶠ in , »((n), f, «expr < »(b, u n))] [":=", expr frequently_lt_of_lt_limsup (is_bounded.is_cobounded_le h') bu],
  exact [expr H a as b bs ab ⟨A, B⟩]
end

end ConditionallyCompleteLinearOrder

end LiminfLimsup

