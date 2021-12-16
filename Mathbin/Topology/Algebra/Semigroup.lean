import Mathbin.Topology.Separation

/-!
# Idempotents in topological semigroups

This file provides a sufficient condition for a semigroup `M` to contain an idempotent (i.e. an
element `m` such that `m * m = m `), namely that `M` is a nonempty compact Hausdorff space where
right-multiplication by constants is continuous.

We also state a corresponding lemma guaranteeing that a subset of `M` contains an idempotent.
-/


-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (m m' «expr ∈ » N)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (N «expr ∈ » S)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (N' «expr ∈ » S)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
      Any nonempty compact Hausdorff semigroup where right-multiplication is continuous contains
      an idempotent, i.e. an `m` such that `m * m = m`. -/
    @[
      toAdditive
        "Any nonempty compact Hausdorff additive semigroup where right-addition is continuous\ncontains an idempotent, i.e. an `m` such that `m + m = m`"
      ]
  theorem
    exists_idempotent_of_compact_t2_of_continuous_mul_left
    { M }
        [ Nonempty M ]
        [ Semigroupₓ M ]
        [ TopologicalSpace M ]
        [ CompactSpace M ]
        [ T2Space M ]
        ( continuous_mul_left : ∀ r : M , Continuous · * r )
      : ∃ m : M , m * m = m
    :=
      by
        let S : Set Set M := { N : Set M | IsClosed N ∧ N.nonempty ∧ ∀ m m' _ : m ∈ N _ : m' ∈ N , m * m' ∈ N }
          suffices : ∃ ( N : _ ) ( _ : N ∈ S ) , ∀ N' _ : N' ∈ S , N' ⊆ N → N' = N
          ·
            rcases this with ⟨ N , ⟨ N_closed , ⟨ m , hm ⟩ , N_mul ⟩ , N_minimal ⟩
              use m
              have scaling_eq_self : · * m '' N = N
              ·
                apply N_minimal
                  ·
                    refine' ⟨ continuous_mul_left m . IsClosedMap _ N_closed , ⟨ _ , ⟨ m , hm , rfl ⟩ ⟩ , _ ⟩
                      rintro _ _ ⟨ m'' , hm'' , rfl ⟩ ⟨ m' , hm' , rfl ⟩
                      exact ⟨ m'' * m * m' , N_mul _ _ N_mul _ _ hm'' hm hm' , mul_assocₓ _ _ _ ⟩
                  · rintro _ ⟨ m' , hm' , rfl ⟩ exact N_mul _ _ hm' hm
              have absorbing_eq_self : N ∩ { m' | m' * m = m } = N
              ·
                apply N_minimal
                  ·
                    refine' ⟨ N_closed.inter T1Space.t1 m . Preimage continuous_mul_left m , _ , _ ⟩
                      · rw [ ← scaling_eq_self ] at hm exact hm
                      ·
                        rintro m'' m' ⟨ mem'' , eq'' : _ = m ⟩ ⟨ mem' , eq' : _ = m ⟩
                          refine' ⟨ N_mul _ _ mem'' mem' , _ ⟩
                          rw [ Set.mem_set_of_eq , mul_assocₓ , eq' , eq'' ]
                  apply Set.inter_subset_left
              rw [ ← absorbing_eq_self ] at hm
              exact hm . 2
          apply Zorn.zorn_superset
          intro c hcs hc
          refine' ⟨ ⋂₀ c , ⟨ is_closed_sInter $ fun t ht => hcs ht . 1 , _ , _ ⟩ , _ ⟩
          ·
            obtain rfl | hcnemp := c.eq_empty_or_nonempty
              · rw [ Set.sInter_empty ] apply Set.univ_nonempty
              convert
                @ IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed
                  _ _ _ c.nonempty_coe_sort.mpr hcnemp ( coeₓ : c → Set M ) _ _ _ _
              · simp only [ Subtype.range_coe_subtype , Set.set_of_mem_eq ]
              · refine' directed_on_iff_directed.mp Zorn.Chain.directed_on _ exact hc.symm
              · intro i exact hcs i.property . 2 . 1
              · intro i exact hcs i.property . 1 . IsCompact
              · intro i exact hcs i.property . 1
          ·
            intro m m' hm hm'
              rw [ Set.mem_sInter ]
              intro t ht
              exact hcs ht . 2 . 2 m m' set.mem_sInter.mp hm t ht set.mem_sInter.mp hm' t ht
          · intro s hs exact Set.sInter_subset_of_mem hs

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x y «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (m «expr ∈ » s)
/-- A version of `exists_idempotent_of_compact_t2_of_continuous_mul_left` where the idempotent lies
in some specified nonempty compact subsemigroup. -/
@[toAdditive exists_idempotent_in_compact_add_subsemigroup
      "A version of\n`exists_idempotent_of_compact_t2_of_continuous_add_left` where the idempotent lies in some specified\nnonempty compact additive subsemigroup."]
theorem exists_idempotent_in_compact_subsemigroup {M} [Semigroupₓ M] [TopologicalSpace M] [T2Space M]
  (continuous_mul_left : ∀ r : M, Continuous (·*r)) (s : Set M) (snemp : s.nonempty) (s_compact : IsCompact s)
  (s_add : ∀ x y _ : x ∈ s _ : y ∈ s, (x*y) ∈ s) : ∃ (m : _)(_ : m ∈ s), (m*m) = m :=
  by 
    let M' := { m // m ∈ s }
    let this' : Semigroupₓ M' :=
      { mul := fun p q => ⟨p.1*q.1, s_add _ _ p.2 q.2⟩, mul_assoc := fun p q r => Subtype.eq (mul_assocₓ _ _ _) }
    have  : CompactSpace M' := is_compact_iff_compact_space.mp s_compact 
    have  : Nonempty M' := nonempty_subtype.mpr snemp 
    have  : ∀ p : M', Continuous (·*p) :=
      fun p => continuous_subtype_mk _ ((continuous_mul_left p.1).comp continuous_subtype_val)
    obtain ⟨⟨m, hm⟩, idem⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left this 
    exact ⟨m, hm, subtype.ext_iff.mp idem⟩

