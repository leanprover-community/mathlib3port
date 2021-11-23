import Mathbin.Tactic.Tfae 
import Mathbin.Order.Atoms 
import Mathbin.Order.OrderIsoNat 
import Mathbin.Order.Zorn 
import Mathbin.Data.Finset.Order

/-!
# Compactness properties for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `complete_lattice.is_compact_element`
 * `complete_lattice.is_compactly_generated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
 * `well_founded (>)`
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `∀ k, complete_lattice.is_compact_element k`

This is demonstrated by means of the following four lemmas:
 * `complete_lattice.well_founded.is_Sup_finite_compact`
 * `complete_lattice.is_Sup_finite_compact.is_sup_closed_compact`
 * `complete_lattice.is_sup_closed_compact.well_founded`
 * `complete_lattice.is_Sup_finite_compact_iff_all_elements_compact`

 We also show well-founded lattices are compactly generated
 (`complete_lattice.compactly_generated_of_well_founded`).

## References
- [G. Călugăreanu, *Lattice Concepts of Module Theory*][calugareanu]

## Tags

complete lattice, well-founded, compact
-/


variable{α : Type _}[CompleteLattice α]

namespace CompleteLattice

variable(α)

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `Sup`. -/
def is_sup_closed_compact : Prop :=
  ∀ s : Set α h : s.nonempty, (∀ a b, a ∈ s → b ∈ s → a⊔b ∈ s) → Sup s ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `Sup`. -/
def is_Sup_finite_compact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, «expr↑ » t ⊆ s ∧ Sup s = t.sup id

/-- An element `k` of a complete lattice is said to be compact if any set with `Sup`
above `k` has a finite subset with `Sup` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def is_compact_element {α : Type _} [CompleteLattice α] (k : α) :=
  ∀ s : Set α, k ≤ Sup s → ∃ t : Finset α, «expr↑ » t ⊆ s ∧ k ≤ t.sup id

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An element `k` is compact if and only if any directed set with `Sup` above
`k` already got above `k` at some point in the set. -/
theorem is_compact_element_iff_le_of_directed_Sup_le
(k : α) : «expr ↔ »(is_compact_element k, ∀
 s : set α, s.nonempty → directed_on ((«expr ≤ »)) s → «expr ≤ »(k, Sup s) → «expr∃ , »((x : α), «expr ∧ »(«expr ∈ »(x, s), «expr ≤ »(k, x)))) :=
begin
  classical,
  split,
  { by_cases [expr hbot, ":", expr «expr = »(k, «expr⊥»())],
    { rintros ["_", "_", "⟨", ident x, ",", ident hx, "⟩", "_", "_"],
      use [expr x],
      by simp [] [] ["only"] ["[", expr hx, ",", expr hbot, ",", expr bot_le, ",", expr and_self, "]"] [] [] },
    { intros [ident hk, ident s, ident hne, ident hdir, ident hsup],
      obtain ["⟨", ident t, ",", ident ht, "⟩", ":=", expr hk s hsup],
      have [ident tne] [":", expr t.nonempty] [],
      { by_contradiction [ident n],
        rw ["[", expr finset.nonempty_iff_ne_empty, ",", expr not_not, "]"] ["at", ident n],
        simp [] [] ["only"] ["[", expr n, ",", expr true_and, ",", expr set.empty_subset, ",", expr finset.coe_empty, ",", expr finset.sup_empty, ",", expr le_bot_iff, "]"] [] ["at", ident ht],
        exact [expr absurd ht hbot] },
      have [ident t_below_s] [":", expr ∀ x «expr ∈ » t, «expr∃ , »((y «expr ∈ » s), «expr ≤ »(x, y))] [],
      from [expr λ x hxt, ⟨x, ht.left hxt, by refl⟩],
      obtain ["⟨", ident x, ",", "⟨", ident hxs, ",", ident hsupx, "⟩", "⟩", ":=", expr finset.sup_le_of_le_directed s hne hdir t t_below_s],
      exact [expr ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩] } },
  { intros [ident hk, ident s, ident hsup],
    let [ident S] [":", expr set α] [":=", expr {x | «expr∃ , »((t : finset α), «expr ∧ »(«expr ⊆ »(«expr↑ »(t), s), «expr = »(x, t.sup id)))}],
    have [ident dir_US] [":", expr directed_on ((«expr ≤ »)) S] [],
    { rintros [ident x, "⟨", ident c, ",", ident hc, "⟩", ident y, "⟨", ident d, ",", ident hd, "⟩"],
      use [expr «expr ⊔ »(x, y)],
      split,
      { use [expr «expr ∪ »(c, d)],
        split,
        { simp [] [] ["only"] ["[", expr hc.left, ",", expr hd.left, ",", expr set.union_subset_iff, ",", expr finset.coe_union, ",", expr and_self, "]"] [] [] },
        { simp [] [] ["only"] ["[", expr hc.right, ",", expr hd.right, ",", expr finset.sup_union, "]"] [] [] } },
      simp [] [] ["only"] ["[", expr and_self, ",", expr le_sup_left, ",", expr le_sup_right, "]"] [] [] },
    have [ident sup_S] [":", expr «expr ≤ »(Sup s, Sup S)] [],
    { apply [expr Sup_le_Sup],
      intros [ident x, ident hx],
      use [expr {x}],
      simpa [] [] ["only"] ["[", expr and_true, ",", expr id.def, ",", expr finset.coe_singleton, ",", expr eq_self_iff_true, ",", expr finset.sup_singleton, ",", expr set.singleton_subset_iff, "]"] [] [] },
    have [ident Sne] [":", expr S.nonempty] [],
    { suffices [] [":", expr «expr ∈ »(«expr⊥»(), S)],
      from [expr set.nonempty_of_mem this],
      use [expr «expr∅»()],
      simp [] [] ["only"] ["[", expr set.empty_subset, ",", expr finset.coe_empty, ",", expr finset.sup_empty, ",", expr eq_self_iff_true, ",", expr and_self, "]"] [] [] },
    obtain ["⟨", ident j, ",", "⟨", ident hjS, ",", ident hjk, "⟩", "⟩", ":=", expr hk S Sne dir_US (le_trans hsup sup_S)],
    obtain ["⟨", ident t, ",", "⟨", ident htS, ",", ident htsup, "⟩", "⟩", ":=", expr hjS],
    use [expr t],
    exact [expr ⟨htS, by rwa ["<-", expr htsup] []⟩] }
end

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A compact element `k` has the property that any directed set lying strictly below `k` has
its Sup strictly below `k`. -/
theorem is_compact_element.directed_Sup_lt_of_lt
{α : Type*}
[complete_lattice α]
{k : α}
(hk : is_compact_element k)
{s : set α}
(hemp : s.nonempty)
(hdir : directed_on ((«expr ≤ »)) s)
(hbelow : ∀ x «expr ∈ » s, «expr < »(x, k)) : «expr < »(Sup s, k) :=
begin
  rw [expr is_compact_element_iff_le_of_directed_Sup_le] ["at", ident hk],
  by_contradiction [],
  have [ident sSup] [":", expr «expr ≤ »(Sup s, k)] [],
  from [expr Sup_le (λ s hs, (hbelow s hs).le)],
  replace [ident sSup] [":", expr «expr = »(Sup s, k)] [":=", expr eq_iff_le_not_lt.mpr ⟨sSup, h⟩],
  obtain ["⟨", ident x, ",", ident hxs, ",", ident hkx, "⟩", ":=", expr hk s hemp hdir sSup.symm.le],
  obtain [ident hxk, ":=", expr hbelow x hxs],
  exact [expr hxk.ne (hxk.le.antisymm hkx)]
end

theorem finset_sup_compact_of_compact {α β : Type _} [CompleteLattice α] {f : β → α} (s : Finset β)
  (h : ∀ x _ : x ∈ s, is_compact_element (f x)) : is_compact_element (s.sup f) :=
  by 
    classical 
    rw [is_compact_element_iff_le_of_directed_Sup_le]
    intro d hemp hdir hsup 
    change f with id ∘ f 
    rw [←Finset.sup_finset_image]
    apply Finset.sup_le_of_le_directed d hemp hdir 
    rintro x hx 
    obtain ⟨p, ⟨hps, rfl⟩⟩ := finset.mem_image.mp hx 
    specialize h p hps 
    rw [is_compact_element_iff_le_of_directed_Sup_le] at h 
    specialize h d hemp hdir (le_transₓ (Finset.le_sup hps) hsup)
    simpa only [exists_prop]

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem well_founded.is_Sup_finite_compact
(h : well_founded ((«expr > ») : α → α → exprProp())) : is_Sup_finite_compact α :=
begin
  intros [ident s],
  let [ident p] [":", expr set α] [":=", expr {x | «expr∃ , »((t : finset α), «expr ∧ »(«expr ⊆ »(«expr↑ »(t), s), «expr = »(t.sup id, x)))}],
  have [ident hp] [":", expr p.nonempty] [],
  { use ["[", expr «expr⊥»(), ",", expr «expr∅»(), "]"],
    simp [] [] [] [] [] [] },
  obtain ["⟨", ident m, ",", "⟨", ident t, ",", "⟨", ident ht₁, ",", ident ht₂, "⟩", "⟩", ",", ident hm, "⟩", ":=", expr well_founded.well_founded_iff_has_max'.mp h p hp],
  use [expr t],
  simp [] [] ["only"] ["[", expr ht₁, ",", expr ht₂, ",", expr true_and, "]"] [] [],
  apply [expr le_antisymm],
  { apply [expr Sup_le],
    intros [ident y, ident hy],
    classical,
    have [ident hy'] [":", expr «expr ∈ »((insert y t).sup id, p)] [],
    { use [expr insert y t],
      simp [] [] [] [] [] [],
      rw [expr set.insert_subset] [],
      exact [expr ⟨hy, ht₁⟩] },
    have [ident hm'] [":", expr «expr ≤ »(m, (insert y t).sup id)] [],
    { rw ["<-", expr ht₂] [],
      exact [expr finset.sup_mono (t.subset_insert y)] },
    rw ["<-", expr hm _ hy' hm'] [],
    simp [] [] [] [] [] [] },
  { rw ["[", "<-", expr ht₂, ",", expr finset.sup_id_eq_Sup, "]"] [],
    exact [expr Sup_le_Sup ht₁] }
end

theorem is_Sup_finite_compact.is_sup_closed_compact (h : is_Sup_finite_compact α) : is_sup_closed_compact α :=
  by 
    intro s hne hsc 
    obtain ⟨t, ht₁, ht₂⟩ := h s 
    clear h 
    cases' t.eq_empty_or_nonempty with h h
    ·
      subst h 
      rw [Finset.sup_empty] at ht₂ 
      rw [ht₂]
      simp [eq_singleton_bot_of_Sup_eq_bot_of_nonempty ht₂ hne]
    ·
      rw [ht₂]
      exact t.sup_closed_of_sup_closed h ht₁ hsc

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_sup_closed_compact.well_founded
(h : is_sup_closed_compact α) : well_founded ((«expr > ») : α → α → exprProp()) :=
begin
  refine [expr rel_embedding.well_founded_iff_no_descending_seq.mpr ⟨λ a, _⟩],
  suffices [] [":", expr «expr ∈ »(Sup (set.range a), set.range a)],
  { obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr set.mem_range.mp this],
    have [ident h'] [":", expr «expr < »(Sup (set.range a), a «expr + »(n, 1))] [],
    { change [expr «expr > »(_, _)] [] [],
      simp [] [] [] ["[", "<-", expr hn, ",", expr a.map_rel_iff, "]"] [] [] },
    apply [expr lt_irrefl (a «expr + »(n, 1))],
    apply [expr lt_of_le_of_lt _ h'],
    apply [expr le_Sup],
    apply [expr set.mem_range_self] },
  apply [expr h (set.range a)],
  { use [expr a 37],
    apply [expr set.mem_range_self] },
  { rintros [ident x, ident y, "⟨", ident m, ",", ident hm, "⟩", "⟨", ident n, ",", ident hn, "⟩"],
    use [expr «expr ⊔ »(m, n)],
    rw ["[", "<-", expr hm, ",", "<-", expr hn, "]"] [],
    apply [expr a.to_rel_hom.map_sup] }
end

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_Sup_finite_compact_iff_all_elements_compact : «expr ↔ »(is_Sup_finite_compact α, ∀
 k : α, is_compact_element k) :=
begin
  split,
  { intros [ident h, ident k, ident s, ident hs],
    obtain ["⟨", ident t, ",", "⟨", ident hts, ",", ident htsup, "⟩", "⟩", ":=", expr h s],
    use ["[", expr t, ",", expr hts, "]"],
    rwa ["<-", expr htsup] [] },
  { intros [ident h, ident s],
    obtain ["⟨", ident t, ",", "⟨", ident hts, ",", ident htsup, "⟩", "⟩", ":=", expr h (Sup s) s (by refl)],
    have [] [":", expr «expr = »(Sup s, t.sup id)] [],
    { suffices [] [":", expr «expr ≤ »(t.sup id, Sup s)],
      by { apply [expr le_antisymm]; assumption },
      simp [] [] ["only"] ["[", expr id.def, ",", expr finset.sup_le_iff, "]"] [] [],
      intros [ident x, ident hx],
      apply [expr le_Sup],
      exact [expr hts hx] },
    use ["[", expr t, ",", expr hts, "]"],
    assumption }
end

theorem well_founded_characterisations :
  tfae
    [WellFounded (· > · : α → α → Prop), is_Sup_finite_compact α, is_sup_closed_compact α,
      ∀ k : α, is_compact_element k] :=
  by 
    tfaeHave 1 → 2
    ·
      ·
        exact well_founded.is_Sup_finite_compact α 
    tfaeHave 2 → 3
    ·
      ·
        exact is_Sup_finite_compact.is_sup_closed_compact α 
    tfaeHave 3 → 1
    ·
      ·
        exact is_sup_closed_compact.well_founded α 
    tfaeHave 2 ↔ 4
    ·
      ·
        exact is_Sup_finite_compact_iff_all_elements_compact α 
    tfaeFinish

theorem well_founded_iff_is_Sup_finite_compact : WellFounded (· > · : α → α → Prop) ↔ is_Sup_finite_compact α :=
  (well_founded_characterisations α).out 0 1

theorem is_Sup_finite_compact_iff_is_sup_closed_compact : is_Sup_finite_compact α ↔ is_sup_closed_compact α :=
  (well_founded_characterisations α).out 1 2

theorem is_sup_closed_compact_iff_well_founded : is_sup_closed_compact α ↔ WellFounded (· > · : α → α → Prop) :=
  (well_founded_characterisations α).out 2 0

alias well_founded_iff_is_Sup_finite_compact ↔ _ IsSupFiniteCompact.well_founded

alias is_Sup_finite_compact_iff_is_sup_closed_compact ↔ _ IsSupClosedCompact.is_Sup_finite_compact

alias is_sup_closed_compact_iff_well_founded ↔ _ WellFounded.is_sup_closed_compact

end CompleteLattice

/-- A complete lattice is said to be compactly generated if any
element is the `Sup` of compact elements. -/
class IsCompactlyGenerated(α : Type _)[CompleteLattice α] : Prop where 
  exists_Sup_eq : ∀ x : α, ∃ s : Set α, (∀ x _ : x ∈ s, CompleteLattice.IsCompactElement x) ∧ Sup s = x

section 

variable{α}[IsCompactlyGenerated α]{a b : α}{s : Set α}

@[simp]
theorem Sup_compact_le_eq b : Sup { c:α | CompleteLattice.IsCompactElement c ∧ c ≤ b } = b :=
  by 
    rcases IsCompactlyGenerated.exists_Sup_eq b with ⟨s, hs, rfl⟩
    exact le_antisymmₓ (Sup_le fun c hc => hc.2) (Sup_le_Sup fun c cs => ⟨hs c cs, le_Sup cs⟩)

@[simp]
theorem Sup_compact_eq_top : Sup { a:α | CompleteLattice.IsCompactElement a } = ⊤ :=
  by 
    refine' Eq.trans (congr rfl (Set.ext fun x => _)) (Sup_compact_le_eq ⊤)
    exact (and_iff_left le_top).symm

theorem le_iff_compact_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, CompleteLattice.IsCompactElement c → c ≤ a → c ≤ b :=
  ⟨fun ab c hc ca => le_transₓ ca ab,
    fun h =>
      by 
        rw [←Sup_compact_le_eq a, ←Sup_compact_le_eq b]
        exact Sup_le_Sup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

/-- This property is sometimes referred to as `α` being upper continuous. -/
theorem inf_Sup_eq_of_directed_on (h : DirectedOn (· ≤ ·) s) : a⊓Sup s = ⨆(b : _)(_ : b ∈ s), a⊓b :=
  le_antisymmₓ
    (by 
      rw [le_iff_compact_le_imp]
      byCases' hs : s.nonempty
      ·
        intro c hc hcinf 
        rw [le_inf_iff] at hcinf 
        rw [CompleteLattice.is_compact_element_iff_le_of_directed_Sup_le] at hc 
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        exact (le_inf hcinf.1 cd).trans (le_bsupr d ds)
      ·
        rw [Set.not_nonempty_iff_eq_empty] at hs 
        simp [hs])
    supr_inf_le_inf_Sup

/-- This property is equivalent to `α` being upper continuous. -/
theorem inf_Sup_eq_supr_inf_sup_finset : a⊓Sup s = ⨆(t : Finset α)(H : «expr↑ » t ⊆ s), a⊓t.sup id :=
  le_antisymmₓ
    (by 
      rw [le_iff_compact_le_imp]
      intro c hc hcinf 
      rw [le_inf_iff] at hcinf 
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      exact (le_inf hcinf.1 ht2).trans (le_bsupr t ht1))
    (supr_le$ fun t => supr_le$ fun h => inf_le_inf_left _ ((Finset.sup_id_eq_Sup t).symm ▸ Sup_le_Sup h))

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem complete_lattice.set_independent_iff_finite
{s : set α} : «expr ↔ »(complete_lattice.set_independent s, ∀
 t : finset α, «expr ⊆ »(«expr↑ »(t), s) → complete_lattice.set_independent («expr↑ »(t) : set α)) :=
⟨λ hs t ht, hs.mono ht, λ h a ha, begin
   rw ["[", expr disjoint_iff, ",", expr inf_Sup_eq_supr_inf_sup_finset, ",", expr supr_eq_bot, "]"] [],
   intro [ident t],
   rw ["[", expr supr_eq_bot, ",", expr finset.sup_id_eq_Sup, "]"] [],
   intro [ident ht],
   classical,
   have [ident h'] [] [":=", expr (h (insert a t) _ (t.mem_insert_self a)).eq_bot],
   { rwa ["[", expr finset.coe_insert, ",", expr set.insert_diff_self_of_not_mem, "]"] ["at", ident h'],
     exact [expr λ con, ((set.mem_diff a).1 (ht con)).2 (set.mem_singleton a)] },
   { rw ["[", expr finset.coe_insert, ",", expr set.insert_subset, "]"] [],
     exact [expr ⟨ha, set.subset.trans ht (set.diff_subset _ _)⟩] }
 end⟩

theorem CompleteLattice.set_independent_Union_of_directed {η : Type _} {s : η → Set α} (hs : Directed (· ⊆ ·) s)
  (h : ∀ i, CompleteLattice.SetIndependent (s i)) : CompleteLattice.SetIndependent (⋃i, s i) :=
  by 
    byCases' hη : Nonempty η
    ·
      skip 
      rw [CompleteLattice.set_independent_iff_finite]
      intro t ht 
      obtain ⟨I, fi, hI⟩ := Set.finite_subset_Union t.finite_to_set ht 
      obtain ⟨i, hi⟩ := hs.finset_le fi.to_finset 
      exact (h i).mono (Set.Subset.trans hI$ Set.bUnion_subset$ fun j hj => hi j (fi.mem_to_finset.2 hj))
    ·
      rintro a ⟨_, ⟨i, _⟩, _⟩
      exfalso 
      exact hη ⟨i⟩

theorem CompleteLattice.independent_sUnion_of_directed {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s)
  (h : ∀ a _ : a ∈ s, CompleteLattice.SetIndependent a) : CompleteLattice.SetIndependent (⋃₀s) :=
  by 
    rw [Set.sUnion_eq_Union] <;>
      exact
        CompleteLattice.set_independent_Union_of_directed hs.directed_coe
          (by 
            simpa using h)

end 

namespace CompleteLattice

theorem compactly_generated_of_well_founded (h : WellFounded (· > · : α → α → Prop)) : IsCompactlyGenerated α :=
  by 
    rw [well_founded_iff_is_Sup_finite_compact, is_Sup_finite_compact_iff_all_elements_compact] at h 
    exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, Sup_singleton⟩⟩⟩

/-- A compact element `k` has the property that any `b < `k lies below a "maximal element below
`k`", which is to say `[⊥, k]` is coatomic. -/
theorem Iic_coatomic_of_compact_element {k : α} (h : is_compact_element k) : IsCoatomic (Set.Iic k) :=
  ⟨fun ⟨b, hbk⟩ =>
      by 
        byCases' htriv : b = k
        ·
          left 
          ext 
          simp only [htriv, Set.Iic.coe_top, Subtype.coe_mk]
        right 
        rcases Zorn.zorn_nonempty_partial_order₀ (Set.Iio k) _ b (lt_of_le_of_neₓ hbk htriv) with ⟨a, a₀, ba, h⟩
        ·
          refine' ⟨⟨a, le_of_ltₓ a₀⟩, ⟨ne_of_ltₓ a₀, fun c hck => by_contradiction$ fun c₀ => _⟩, ba⟩
          cases h c.1 (lt_of_le_of_neₓ c.2 fun con => c₀ (Subtype.ext con)) hck.le 
          exact lt_irreflₓ _ hck
        ·
          intro S SC cC I IS 
          byCases' hS : S.nonempty
          ·
            exact ⟨Sup S, h.directed_Sup_lt_of_lt hS cC.directed_on SC, fun _ => le_Sup⟩
          exact
            ⟨b, lt_of_le_of_neₓ hbk htriv,
              by 
                simp only [set.not_nonempty_iff_eq_empty.mp hS, Set.mem_empty_eq, forall_const, forall_prop_of_false,
                  not_false_iff]⟩⟩

theorem coatomic_of_top_compact (h : is_compact_element (⊤ : α)) : IsCoatomic α :=
  (@OrderIso.iicTop α _ _).is_coatomic_iff.mp (Iic_coatomic_of_compact_element h)

end CompleteLattice

section 

variable[IsModularLattice α][IsCompactlyGenerated α]

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance is_atomic_of_is_complemented [is_complemented α] : is_atomic α :=
⟨λ b, begin
   by_cases [expr h, ":", expr «expr ⊆ »({c : α | «expr ∧ »(complete_lattice.is_compact_element c, «expr ≤ »(c, b))}, {«expr⊥»()})],
   { left,
     rw ["[", "<-", expr Sup_compact_le_eq b, ",", expr Sup_eq_bot, "]"] [],
     exact [expr h] },
   { rcases [expr set.not_subset.1 h, "with", "⟨", ident c, ",", "⟨", ident hc, ",", ident hcb, "⟩", ",", ident hcbot, "⟩"],
     right,
     have [ident hc'] [] [":=", expr complete_lattice.Iic_coatomic_of_compact_element hc],
     rw ["<-", expr is_atomic_iff_is_coatomic] ["at", ident hc'],
     haveI [] [] [":=", expr hc'],
     obtain [ident con, "|", "⟨", ident a, ",", ident ha, ",", ident hac, "⟩", ":=", expr eq_bot_or_exists_atom_le (⟨c, le_refl c⟩ : set.Iic c)],
     { exfalso,
       apply [expr hcbot],
       simp [] [] ["only"] ["[", expr subtype.ext_iff, ",", expr set.Iic.coe_bot, ",", expr subtype.coe_mk, "]"] [] ["at", ident con],
       exact [expr con] },
     rw ["[", "<-", expr subtype.coe_le_coe, ",", expr subtype.coe_mk, "]"] ["at", ident hac],
     exact [expr ⟨a, ha.of_is_atom_coe_Iic, hac.trans hcb⟩] }
 end⟩

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- See Lemma 5.1, Călugăreanu -/
@[priority 100]
instance is_atomistic_of_is_complemented [is_complemented α] : is_atomistic α :=
⟨λ
 b, ⟨{a | «expr ∧ »(is_atom a, «expr ≤ »(a, b))}, begin
    symmetry,
    have [ident hle] [":", expr «expr ≤ »(Sup {a : α | «expr ∧ »(is_atom a, «expr ≤ »(a, b))}, b)] [":=", expr «expr $ »(Sup_le, λ
      _, and.right)],
    apply [expr (lt_or_eq_of_le hle).resolve_left (λ con, _)],
    obtain ["⟨", ident c, ",", ident hc, "⟩", ":=", expr exists_is_compl (⟨Sup {a : α | «expr ∧ »(is_atom a, «expr ≤ »(a, b))}, hle⟩ : set.Iic b)],
    obtain [ident rfl, "|", "⟨", ident a, ",", ident ha, ",", ident hac, "⟩", ":=", expr eq_bot_or_exists_atom_le c],
    { exact [expr ne_of_lt con (subtype.ext_iff.1 (eq_top_of_is_compl_bot hc))] },
    { apply [expr ha.1],
      rw [expr eq_bot_iff] [],
      apply [expr le_trans (le_inf _ hac) hc.1],
      rw ["[", "<-", expr subtype.coe_le_coe, ",", expr subtype.coe_mk, "]"] [],
      exact [expr le_Sup ⟨ha.of_is_atom_coe_Iic, a.2⟩] }
  end, λ _, and.left⟩⟩

-- error in Order.CompactlyGenerated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- See Theorem 6.6, Călugăreanu -/
theorem is_complemented_of_Sup_atoms_eq_top (h : «expr = »(Sup {a : α | is_atom a}, «expr⊤»())) : is_complemented α :=
⟨λ b, begin
   obtain ["⟨", ident s, ",", "⟨", ident s_ind, ",", ident b_inf_Sup_s, ",", ident s_atoms, "⟩", ",", ident s_max, "⟩", ":=", expr zorn.zorn_subset {s : set α | «expr ∧ »(complete_lattice.set_independent s, «expr ∧ »(«expr = »(«expr ⊓ »(b, Sup s), «expr⊥»()), ∀
      a «expr ∈ » s, is_atom a))} _],
   { refine [expr ⟨Sup s, le_of_eq b_inf_Sup_s, _⟩],
     rw ["[", "<-", expr h, ",", expr Sup_le_iff, "]"] [],
     intros [ident a, ident ha],
     rw ["<-", expr inf_eq_left] [],
     refine [expr (eq_bot_or_eq_of_le_atom ha inf_le_left).resolve_left (λ con, ha.1 _)],
     rw ["[", expr eq_bot_iff, ",", "<-", expr con, "]"] [],
     refine [expr le_inf (le_refl a) ((le_Sup _).trans le_sup_right)],
     rw ["<-", expr disjoint_iff] ["at", "*"],
     have [ident a_dis_Sup_s] [":", expr disjoint a (Sup s)] [":=", expr con.mono_right le_sup_right],
     rw ["<-", expr s_max «expr ∪ »(s, {a}) ⟨λ x hx, _, ⟨_, λ x hx, _⟩⟩ (set.subset_union_left _ _)] [],
     { exact [expr set.mem_union_right _ (set.mem_singleton _)] },
     { rw ["[", expr set.mem_union, ",", expr set.mem_singleton_iff, "]"] ["at", ident hx],
       by_cases [expr xa, ":", expr «expr = »(x, a)],
       { simp [] [] ["only"] ["[", expr xa, ",", expr set.mem_singleton, ",", expr set.insert_diff_of_mem, ",", expr set.union_singleton, "]"] [] [],
         exact [expr con.mono_right (le_trans (Sup_le_Sup (set.diff_subset s {a})) le_sup_right)] },
       { have [ident h] [":", expr «expr = »(«expr \ »(«expr ∪ »(s, {a}), {x}), «expr ∪ »(«expr \ »(s, {x}), {a}))] [],
         { simp [] [] ["only"] ["[", expr set.union_singleton, "]"] [] [],
           rw [expr set.insert_diff_of_not_mem] [],
           rw [expr set.mem_singleton_iff] [],
           exact [expr ne.symm xa] },
         rw ["[", expr h, ",", expr Sup_union, ",", expr Sup_singleton, "]"] [],
         apply [expr (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left (a_dis_Sup_s.mono_right _).symm],
         rw ["[", "<-", expr Sup_insert, ",", expr set.insert_diff_singleton, ",", expr set.insert_eq_of_mem (hx.resolve_right xa), "]"] [] } },
     { rw ["[", expr Sup_union, ",", expr Sup_singleton, ",", "<-", expr disjoint_iff, "]"] [],
       exact [expr b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm] },
     { rw ["[", expr set.mem_union, ",", expr set.mem_singleton_iff, "]"] ["at", ident hx],
       cases [expr hx] [],
       { exact [expr s_atoms x hx] },
       { rw [expr hx] [],
         exact [expr ha] } } },
   { intros [ident c, ident hc1, ident hc2],
     refine [expr ⟨«expr⋃₀ »(c), ⟨complete_lattice.independent_sUnion_of_directed hc2.directed_on (λ
         s hs, (hc1 hs).1), _, λ a ha, _⟩, λ _, set.subset_sUnion_of_mem⟩],
     { rw ["[", expr Sup_sUnion, ",", "<-", expr Sup_image, ",", expr inf_Sup_eq_of_directed_on, ",", expr supr_eq_bot, "]"] [],
       { intro [ident i],
         rw [expr supr_eq_bot] [],
         intro [ident hi],
         obtain ["⟨", ident x, ",", ident xc, ",", ident rfl, "⟩", ":=", expr (set.mem_image _ _ _).1 hi],
         exact [expr (hc1 xc).2.1] },
       { rw [expr directed_on_image] [],
         refine [expr hc2.directed_on.mono (λ s t, Sup_le_Sup)] } },
     { rcases [expr set.mem_sUnion.1 ha, "with", "⟨", ident s, ",", ident sc, ",", ident as, "⟩"],
       exact [expr (hc1 sc).2.2 a as] } }
 end⟩

/-- See Theorem 6.6, Călugăreanu -/
theorem is_complemented_of_is_atomistic [IsAtomistic α] : IsComplemented α :=
  is_complemented_of_Sup_atoms_eq_top Sup_atoms_eq_top

theorem is_complemented_iff_is_atomistic : IsComplemented α ↔ IsAtomistic α :=
  by 
    split  <;> intros 
    ·
      exact is_atomistic_of_is_complemented
    ·
      exact is_complemented_of_is_atomistic

end 

