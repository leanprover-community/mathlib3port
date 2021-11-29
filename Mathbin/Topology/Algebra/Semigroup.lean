import Mathbin.Topology.Separation

/-!
# Idempotents in topological semigroups

This file provides a sufficient condition for a semigroup `M` to contain an idempotent (i.e. an
element `m` such that `m * m = m `), namely that `M` is a nonempty compact Hausdorff space where
right-multiplication by constants is continuous.

We also state a corresponding lemma guaranteeing that a subset of `M` contains an idempotent.
-/


-- error in Topology.Algebra.Semigroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any nonempty compact Hausdorff semigroup where right-multiplication is continuous contains
an idempotent, i.e. an `m` such that `m * m = m`. -/
@[to_additive #[expr "Any nonempty compact Hausdorff additive semigroup where right-addition is continuous\ncontains an idempotent, i.e. an `m` such that `m + m = m`"]]
theorem exists_idempotent_of_compact_t2_of_continuous_mul_left
{M}
[nonempty M]
[semigroup M]
[topological_space M]
[compact_space M]
[t2_space M]
(continuous_mul_left : ∀ r : M, continuous ((«expr * » r))) : «expr∃ , »((m : M), «expr = »(«expr * »(m, m), m)) :=
begin
  let [ident S] [":", expr set (set M)] [":=", expr {N : set M | «expr ∧ »(is_closed N, «expr ∧ »(N.nonempty, ∀
     m m' «expr ∈ » N, «expr ∈ »(«expr * »(m, m'), N)))}],
  suffices [] [":", expr «expr∃ , »((N «expr ∈ » S), ∀ N' «expr ∈ » S, «expr ⊆ »(N', N) → «expr = »(N', N))],
  { rcases [expr this, "with", "⟨", ident N, ",", "⟨", ident N_closed, ",", "⟨", ident m, ",", ident hm, "⟩", ",", ident N_mul, "⟩", ",", ident N_minimal, "⟩"],
    use [expr m],
    have [ident scaling_eq_self] [":", expr «expr = »(«expr '' »((«expr * » m), N), N)] [],
    { apply [expr N_minimal],
      { refine [expr ⟨(continuous_mul_left m).is_closed_map _ N_closed, ⟨_, ⟨m, hm, rfl⟩⟩, _⟩],
        rintros ["_", "_", "⟨", ident m'', ",", ident hm'', ",", ident rfl, "⟩", "⟨", ident m', ",", ident hm', ",", ident rfl, "⟩"],
        exact [expr ⟨«expr * »(«expr * »(m'', m), m'), N_mul _ _ (N_mul _ _ hm'' hm) hm', mul_assoc _ _ _⟩] },
      { rintros ["_", "⟨", ident m', ",", ident hm', ",", ident rfl, "⟩"],
        exact [expr N_mul _ _ hm' hm] } },
    have [ident absorbing_eq_self] [":", expr «expr = »(«expr ∩ »(N, {m' | «expr = »(«expr * »(m', m), m)}), N)] [],
    { apply [expr N_minimal],
      { refine [expr ⟨N_closed.inter ((t1_space.t1 m).preimage (continuous_mul_left m)), _, _⟩],
        { rw ["<-", expr scaling_eq_self] ["at", ident hm],
          exact [expr hm] },
        { rintros [ident m'', ident m', "⟨", ident mem'', ",", ident eq'', ":", expr «expr = »(_, m), "⟩", "⟨", ident mem', ",", ident eq', ":", expr «expr = »(_, m), "⟩"],
          refine [expr ⟨N_mul _ _ mem'' mem', _⟩],
          rw ["[", expr set.mem_set_of_eq, ",", expr mul_assoc, ",", expr eq', ",", expr eq'', "]"] [] } },
      apply [expr set.inter_subset_left] },
    rw ["<-", expr absorbing_eq_self] ["at", ident hm],
    exact [expr hm.2] },
  apply [expr zorn.zorn_superset],
  intros [ident c, ident hcs, ident hc],
  refine [expr ⟨«expr⋂₀ »(c), ⟨«expr $ »(is_closed_sInter, λ t ht, (hcs ht).1), _, _⟩, _⟩],
  { obtain [ident rfl, "|", ident hcnemp, ":=", expr c.eq_empty_or_nonempty],
    { rw [expr set.sInter_empty] [],
      apply [expr set.univ_nonempty] },
    convert [] [expr @is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ _ _ (c.nonempty_coe_sort.mpr hcnemp) (coe : c → set M) _ _ _ _] [],
    { simp [] [] ["only"] ["[", expr subtype.range_coe_subtype, ",", expr set.set_of_mem_eq, "]"] [] [] },
    { refine [expr directed_on_iff_directed.mp (zorn.chain.directed_on _)],
      exact [expr hc.symm] },
    { intro [ident i],
      exact [expr (hcs i.property).2.1] },
    { intro [ident i],
      exact [expr (hcs i.property).1.is_compact] },
    { intro [ident i],
      exact [expr (hcs i.property).1] } },
  { intros [ident m, ident m', ident hm, ident hm'],
    rw [expr set.mem_sInter] [],
    intros [ident t, ident ht],
    exact [expr (hcs ht).2.2 m m' (set.mem_sInter.mp hm t ht) (set.mem_sInter.mp hm' t ht)] },
  { intros [ident s, ident hs],
    exact [expr set.sInter_subset_of_mem hs] }
end

-- error in Topology.Algebra.Semigroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A version of `exists_idempotent_of_compact_t2_of_continuous_mul_left` where the idempotent lies
in some specified nonempty compact subsemigroup. -/
@[to_additive #[ident exists_idempotent_in_compact_add_subsemigroup,
   expr "A version of\n`exists_idempotent_of_compact_t2_of_continuous_add_left` where the idempotent lies in some specified\nnonempty compact additive subsemigroup."]]
theorem exists_idempotent_in_compact_subsemigroup
{M}
[semigroup M]
[topological_space M]
[t2_space M]
(continuous_mul_left : ∀ r : M, continuous ((«expr * » r)))
(s : set M)
(snemp : s.nonempty)
(s_compact : is_compact s)
(s_add : ∀
 x y «expr ∈ » s, «expr ∈ »(«expr * »(x, y), s)) : «expr∃ , »((m «expr ∈ » s), «expr = »(«expr * »(m, m), m)) :=
begin
  let [ident M'] [] [":=", expr {m // «expr ∈ »(m, s)}],
  letI [] [":", expr semigroup M'] [":=", expr { mul := λ p q, ⟨«expr * »(p.1, q.1), s_add _ _ p.2 q.2⟩,
     mul_assoc := λ p q r, subtype.eq (mul_assoc _ _ _) }],
  haveI [] [":", expr compact_space M'] [":=", expr is_compact_iff_compact_space.mp s_compact],
  haveI [] [":", expr nonempty M'] [":=", expr nonempty_subtype.mpr snemp],
  have [] [":", expr ∀
   p : M', continuous ((«expr * » p))] [":=", expr λ
   p, continuous_subtype_mk _ ((continuous_mul_left p.1).comp continuous_subtype_val)],
  obtain ["⟨", "⟨", ident m, ",", ident hm, "⟩", ",", ident idem, "⟩", ":=", expr exists_idempotent_of_compact_t2_of_continuous_mul_left this],
  exact [expr ⟨m, hm, subtype.ext_iff.mp idem⟩]
end

