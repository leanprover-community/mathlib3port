import Mathbin.Data.Set.Finite 
import Mathbin.Order.WellFounded 
import Mathbin.Order.OrderIsoNat 
import Mathbin.Algebra.Pointwise

/-!
# Well-founded sets

A well-founded subset of an ordered type is one on which the relation `<` is well-founded.

## Main Definitions
 * `set.well_founded_on s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
 * `set.is_wf s` indicates that `<` is well-founded when restricted to `s`.
 * `set.partially_well_ordered_on s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
 * `set.is_pwo s` indicates that any infinite sequence of elements in `s`
  contains an infinite monotone subsequence. Note that

### Definitions for Hahn Series
 * `set.add_antidiagonal s t a` and `set.mul_antidiagonal s t a` are the sets of pairs of elements
  from `s` and `t` that add/multiply to `a`.
 * `finset.add_antidiagonal` and `finset.mul_antidiagonal` are finite versions of
  `set.add_antidiagonal` and `set.mul_antidiagonal` defined when `s` and `t` are well-founded.

## Main Results
 * Higman's Lemma, `set.partially_well_ordered_on.partially_well_ordered_on_sublist_forall₂`,
  shows that if `r` is partially well-ordered on `s`, then `list.sublist_forall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
 * `set.well_founded_on_iff` relates `well_founded_on` to the well-foundedness of a relation on the
 original type, to avoid dealing with subtypes.
 * `set.is_wf.mono` shows that a subset of a well-founded subset is well-founded.
 * `set.is_wf.union` shows that the union of two well-founded subsets is well-founded.
 * `finset.is_wf` shows that all `finset`s are well-founded.

## References
 * [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
 * [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/


open_locale Pointwise

variable{α : Type _}

namespace Set

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- `s.well_founded_on r` indicates that the relation `r` is well-founded when restricted to `s`. -/
def well_founded_on (s : set α) (r : α → α → exprProp()) : exprProp() :=
well_founded (λ (a : s) (b : s), r a b)

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem well_founded_on_iff
{s : set α}
{r : α → α → exprProp()} : «expr ↔ »(s.well_founded_on r, well_founded (λ
  a b : α, «expr ∧ »(r a b, «expr ∧ »(«expr ∈ »(a, s), «expr ∈ »(b, s))))) :=
begin
  have [ident f] [":", expr rel_embedding (λ
    (a : s)
    (b : s), r a b) (λ
    a
    b : α, «expr ∧ »(r a b, «expr ∧ »(«expr ∈ »(a, s), «expr ∈ »(b, s))))] [":=", expr ⟨⟨coe, subtype.coe_injective⟩, λ
    a b, by simp [] [] [] [] [] []⟩],
  refine [expr ⟨λ h, _, f.well_founded⟩],
  rw [expr well_founded.well_founded_iff_has_min] [],
  intros [ident t, ident ht],
  by_cases [expr hst, ":", expr «expr ∩ »(s, t).nonempty],
  { rw ["<-", expr subtype.preimage_coe_nonempty] ["at", ident hst],
    rcases [expr well_founded.well_founded_iff_has_min.1 h «expr ⁻¹' »(coe, t) hst, "with", "⟨", "⟨", ident m, ",", ident ms, "⟩", ",", ident mt, ",", ident hm, "⟩"],
    exact [expr ⟨m, mt, λ (x xt) ⟨xm, xs, ms⟩, hm ⟨x, xs⟩ xt xm⟩] },
  { rcases [expr ht, "with", "⟨", ident m, ",", ident mt, "⟩"],
    exact [expr ⟨m, mt, λ (x xt) ⟨xm, xs, ms⟩, hst ⟨m, ⟨ms, mt⟩⟩⟩] }
end

theorem well_founded_on.induction {s : Set α} {r : α → α → Prop} (hs : s.well_founded_on r) {x : α} (hx : x ∈ s)
  {P : α → Prop} (hP : ∀ y (_ : y ∈ s), (∀ z (_ : z ∈ s), r z y → P z) → P y) : P x :=
  by 
    let Q : s → Prop := fun y => P y 
    change Q ⟨x, hx⟩
    refine' WellFounded.induction hs ⟨x, hx⟩ _ 
    rintro ⟨y, ys⟩ ih 
    exact hP _ ys fun z zs zy => ih ⟨z, zs⟩ zy

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance is_strict_order.subset
{s : set α}
{r : α → α → exprProp()}
[is_strict_order α r] : is_strict_order α (λ a b : α, «expr ∧ »(r a b, «expr ∧ »(«expr ∈ »(a, s), «expr ∈ »(b, s)))) :=
{ to_is_irrefl := ⟨λ a con, irrefl_of r a con.1⟩,
  to_is_trans := ⟨λ a b c ab bc, ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩ }

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem well_founded_on_iff_no_descending_seq
{s : set α}
{r : α → α → exprProp()}
[is_strict_order α r] : «expr ↔ »(s.well_founded_on r, ∀
 f : «expr ↪r »(((«expr > ») : exprℕ() → exprℕ() → exprProp()), r), «expr¬ »(«expr ⊆ »(range f, s))) :=
begin
  rw ["[", expr well_founded_on_iff, ",", expr rel_embedding.well_founded_iff_no_descending_seq, "]"] [],
  refine [expr ⟨λ h f con, begin
      refine [expr h.elim' ⟨⟨f, f.injective⟩, λ a b, _⟩],
      simp [] [] ["only"] ["[", expr con (mem_range_self a), ",", expr con (mem_range_self b), ",", expr and_true, ",", expr gt_iff_lt, ",", expr function.embedding.coe_fn_mk, ",", expr f.map_rel_iff, "]"] [] []
    end, λ h, ⟨λ con, _⟩⟩],
  rcases [expr con, "with", "⟨", ident f, ",", ident hf, "⟩"],
  have [ident hfs'] [":", expr ∀ n : exprℕ(), «expr ∈ »(f n, s)] [":=", expr λ n, (hf.2 n.lt_succ_self).2.2],
  refine [expr h ⟨f, λ a b, _⟩ (λ n hn, _)],
  { rw ["<-", expr hf] [],
    exact [expr ⟨λ h, ⟨h, hfs' _, hfs' _⟩, λ h, h.1⟩] },
  { rcases [expr set.mem_range.1 hn, "with", "⟨", ident m, ",", ident hm, "⟩"],
    rw ["<-", expr hm] [],
    apply [expr hfs'] }
end

section LT

variable[LT α]

/-- `s.is_wf` indicates that `<` is well-founded when restricted to `s`. -/
def is_wf (s : Set α) : Prop :=
  well_founded_on s (· < ·)

theorem is_wf_univ_iff : is_wf (univ : Set α) ↔ WellFounded (· < · : α → α → Prop) :=
  by 
    simp [is_wf, well_founded_on_iff]

variable{s t : Set α}

theorem is_wf.mono (h : is_wf t) (st : s ⊆ t) : is_wf s :=
  by 
    rw [is_wf, well_founded_on_iff] at *
    refine' Subrelation.wfₓ (fun x y xy => _) h 
    exact ⟨xy.1, st xy.2.1, st xy.2.2⟩

end LT

section PartialOrderₓ

variable[PartialOrderₓ α]{s t : Set α}{a : α}

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_wf_iff_no_descending_seq : «expr ↔ »(is_wf s, ∀
 f : «expr ↪o »(order_dual exprℕ(), α), «expr¬ »(«expr ⊆ »(range f, s))) :=
begin
  haveI [] [":", expr is_strict_order α (λ
    a
    b : α, «expr ∧ »(«expr < »(a, b), «expr ∧ »(«expr ∈ »(a, s), «expr ∈ »(b, s))))] [":=", expr { to_is_irrefl := ⟨λ
      x con, lt_irrefl x con.1⟩,
     to_is_trans := ⟨λ a b c ab bc, ⟨lt_trans ab.1 bc.1, ab.2.1, bc.2.2⟩⟩ }],
  rw ["[", expr is_wf, ",", expr well_founded_on_iff_no_descending_seq, "]"] [],
  exact [expr ⟨λ h f, h f.lt_embedding, λ h f, h (order_embedding.of_strict_mono f (λ _ _, f.map_rel_iff.2))⟩]
end

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_wf.union (hs : is_wf s) (ht : is_wf t) : is_wf «expr ∪ »(s, t) :=
begin
  classical,
  rw ["[", expr is_wf_iff_no_descending_seq, "]"] ["at", "*"],
  rintros [ident f, ident fst],
  have [ident h] [":", expr «expr ∨ »(infinite «expr ⁻¹' »(f, s), infinite «expr ⁻¹' »(f, t))] [],
  { have [ident h] [":", expr infinite (univ : set exprℕ())] [":=", expr infinite_univ],
    have [ident hpre] [":", expr «expr = »(«expr ⁻¹' »(f, «expr ∪ »(s, t)), set.univ)] [],
    { rw ["[", "<-", expr image_univ, ",", expr image_subset_iff, ",", expr univ_subset_iff, "]"] ["at", ident fst],
      exact [expr fst] },
    rw [expr preimage_union] ["at", ident hpre],
    rw ["<-", expr hpre] ["at", ident h],
    rw ["[", expr infinite, ",", expr infinite, "]"] [],
    rw [expr infinite] ["at", ident h],
    contrapose ["!"] [ident h],
    exact [expr finite.union h.1 h.2] },
  rw ["[", "<-", expr infinite_coe_iff, ",", "<-", expr infinite_coe_iff, "]"] ["at", ident h],
  cases [expr h] ["with", ident inf, ident inf]; haveI [] [] [":=", expr inf],
  { apply [expr hs ((nat.order_embedding_of_set «expr ⁻¹' »(f, s)).dual.trans f)],
    change [expr «expr ⊆ »(range (function.comp f (nat.order_embedding_of_set «expr ⁻¹' »(f, s))), s)] [] [],
    rw ["[", expr range_comp, ",", expr image_subset_iff, "]"] [],
    simp [] [] [] [] [] [] },
  { apply [expr ht ((nat.order_embedding_of_set «expr ⁻¹' »(f, t)).dual.trans f)],
    change [expr «expr ⊆ »(range (function.comp f (nat.order_embedding_of_set «expr ⁻¹' »(f, t))), t)] [] [],
    rw ["[", expr range_comp, ",", expr image_subset_iff, "]"] [],
    simp [] [] [] [] [] [] }
end

end PartialOrderₓ

end Set

namespace Set

/-- A subset is partially well-ordered by a relation `r` when any infinite sequence contains
  two elements where the first is related to the second by `r`. -/
def partially_well_ordered_on s (r : α → α → Prop) : Prop :=
  ∀ (f : ℕ → α), range f ⊆ s → ∃ m n : ℕ, m < n ∧ r (f m) (f n)

/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
def is_pwo [Preorderₓ α] s : Prop :=
  partially_well_ordered_on s (· ≤ · : α → α → Prop)

theorem partially_well_ordered_on.mono {s t : Set α} {r : α → α → Prop} (ht : t.partially_well_ordered_on r)
  (hsub : s ⊆ t) : s.partially_well_ordered_on r :=
  fun f hf => ht f (Set.Subset.trans hf hsub)

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem partially_well_ordered_on.image_of_monotone_on
{s : set α}
{r : α → α → exprProp()}
{β : Type*}
{r' : β → β → exprProp()}
(hs : s.partially_well_ordered_on r)
{f : α → β}
(hf : ∀
 a1
 a2 : α, «expr ∈ »(a1, s) → «expr ∈ »(a2, s) → r a1 a2 → r' (f a1) (f a2)) : «expr '' »(f, s).partially_well_ordered_on r' :=
λ g hg, begin
  have [ident h] [] [":=", expr λ n : exprℕ(), (mem_image _ _ _).1 (hg (mem_range_self n))],
  obtain ["⟨", ident m, ",", ident n, ",", ident hlt, ",", ident hmn, "⟩", ":=", expr hs (λ n, classical.some (h n)) _],
  { refine [expr ⟨m, n, hlt, _⟩],
    rw ["[", "<-", expr (classical.some_spec (h m)).2, ",", "<-", expr (classical.some_spec (h n)).2, "]"] [],
    exact [expr hf _ _ (classical.some_spec (h m)).1 (classical.some_spec (h n)).1 hmn] },
  { rintros ["_", "⟨", ident n, ",", ident rfl, "⟩"],
    exact [expr (classical.some_spec (h n)).1] }
end

section PartialOrderₓ

variable{s : Set α}{t : Set α}{r : α → α → Prop}

theorem partially_well_ordered_on.exists_monotone_subseq [IsRefl α r] [IsTrans α r] (h : s.partially_well_ordered_on r)
  (f : ℕ → α) (hf : range f ⊆ s) : ∃ g : ℕ ↪o ℕ, ∀ (m n : ℕ), m ≤ n → r (f (g m)) (f (g n)) :=
  by 
    obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
    ·
      refine' ⟨g, fun m n hle => _⟩
      obtain hlt | heq := lt_or_eq_of_leₓ hle
      ·
        exact h1 m n hlt
      ·
        rw [HEq]
        apply refl_of r
    ·
      exfalso 
      obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g) (subset.trans (range_comp_subset_range _ _) hf)
      exact h2 m n hlt hle

theorem partially_well_ordered_on_iff_exists_monotone_subseq [IsRefl α r] [IsTrans α r] :
  s.partially_well_ordered_on r ↔
    ∀ (f : ℕ → α), range f ⊆ s → ∃ g : ℕ ↪o ℕ, ∀ (m n : ℕ), m ≤ n → r (f (g m)) (f (g n)) :=
  by 
    classical 
    split  <;> intro h f hf
    ·
      exact h.exists_monotone_subseq f hf
    ·
      obtain ⟨g, gmon⟩ := h f hf 
      refine' ⟨g 0, g 1, g.lt_iff_lt.2 zero_lt_one, gmon _ _ zero_le_one⟩

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem partially_well_ordered_on.well_founded_on
[is_partial_order α r]
(h : s.partially_well_ordered_on r) : s.well_founded_on (λ a b, «expr ∧ »(r a b, «expr ≠ »(a, b))) :=
begin
  haveI [] [":", expr is_strict_order α (λ
    a
    b, «expr ∧ »(r a b, «expr ≠ »(a, b)))] [":=", expr { to_is_irrefl := ⟨λ a con, con.2 rfl⟩,
     to_is_trans := ⟨λ a b c ab bc, ⟨trans ab.1 bc.1, λ ac, ab.2 (antisymm ab.1 «expr ▸ »(ac.symm, bc.1))⟩⟩ }],
  rw [expr well_founded_on_iff_no_descending_seq] [],
  intros [ident f, ident con],
  obtain ["⟨", ident m, ",", ident n, ",", ident hlt, ",", ident hle, "⟩", ":=", expr h f con],
  exact [expr (f.map_rel_iff.2 hlt).2 (antisymm hle (f.map_rel_iff.2 hlt).1).symm]
end

variable[PartialOrderₓ α]

theorem is_pwo.is_wf (h : s.is_pwo) : s.is_wf :=
  by 
    rw [is_wf]
    convert h.well_founded_on 
    ext x y 
    rw [lt_iff_le_and_ne]

theorem is_pwo.exists_monotone_subseq (h : s.is_pwo) (f : ℕ → α) (hf : range f ⊆ s) : ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  h.exists_monotone_subseq f hf

theorem is_pwo_iff_exists_monotone_subseq : s.is_pwo ↔ ∀ (f : ℕ → α), range f ⊆ s → ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  partially_well_ordered_on_iff_exists_monotone_subseq

theorem is_pwo.prod (hs : s.is_pwo) (ht : t.is_pwo) : (s.prod t).IsPwo :=
  by 
    classical 
    rw [is_pwo_iff_exists_monotone_subseq] at *
    intro f hf 
    obtain ⟨g1, h1⟩ := hs (Prod.fst ∘ f) _ 
    swap
    ·
      rw [range_comp, image_subset_iff]
      refine' subset.trans hf _ 
      rintro ⟨x1, x2⟩ hx 
      simp only [mem_preimage, hx.1]
    obtain ⟨g2, h2⟩ := ht (Prod.snd ∘ f ∘ g1) _ 
    refine' ⟨g2.trans g1, fun m n mn => _⟩
    swap
    ·
      rw [range_comp, image_subset_iff]
      refine' subset.trans (range_comp_subset_range _ _) (subset.trans hf _)
      rintro ⟨x1, x2⟩ hx 
      simp only [mem_preimage, hx.2]
    simp only [RelEmbedding.coe_trans, Function.comp_app]
    exact ⟨h1 (g2.le_iff_le.2 mn), h2 mn⟩

theorem is_pwo.image_of_monotone {β : Type _} [PartialOrderₓ β] (hs : s.is_pwo) {f : α → β} (hf : Monotone f) :
  is_pwo (f '' s) :=
  hs.image_of_monotone_on fun _ _ _ _ ab => hf ab

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_pwo.union (hs : is_pwo s) (ht : is_pwo t) : is_pwo «expr ∪ »(s, t) :=
begin
  classical,
  rw ["[", expr is_pwo_iff_exists_monotone_subseq, "]"] ["at", "*"],
  rintros [ident f, ident fst],
  have [ident h] [":", expr «expr ∨ »(infinite «expr ⁻¹' »(f, s), infinite «expr ⁻¹' »(f, t))] [],
  { have [ident h] [":", expr infinite (univ : set exprℕ())] [":=", expr infinite_univ],
    have [ident hpre] [":", expr «expr = »(«expr ⁻¹' »(f, «expr ∪ »(s, t)), set.univ)] [],
    { rw ["[", "<-", expr image_univ, ",", expr image_subset_iff, ",", expr univ_subset_iff, "]"] ["at", ident fst],
      exact [expr fst] },
    rw [expr preimage_union] ["at", ident hpre],
    rw ["<-", expr hpre] ["at", ident h],
    rw ["[", expr infinite, ",", expr infinite, "]"] [],
    rw [expr infinite] ["at", ident h],
    contrapose ["!"] [ident h],
    exact [expr finite.union h.1 h.2] },
  rw ["[", "<-", expr infinite_coe_iff, ",", "<-", expr infinite_coe_iff, "]"] ["at", ident h],
  cases [expr h] ["with", ident inf, ident inf]; haveI [] [] [":=", expr inf],
  { obtain ["⟨", ident g, ",", ident hg, "⟩", ":=", expr hs «expr ∘ »(f, nat.order_embedding_of_set «expr ⁻¹' »(f, s)) _],
    { rw ["[", expr function.comp.assoc, ",", "<-", expr rel_embedding.coe_trans, "]"] ["at", ident hg],
      exact [expr ⟨_, hg⟩] },
    rw ["[", expr range_comp, ",", expr image_subset_iff, "]"] [],
    simp [] [] [] [] [] [] },
  { obtain ["⟨", ident g, ",", ident hg, "⟩", ":=", expr ht «expr ∘ »(f, nat.order_embedding_of_set «expr ⁻¹' »(f, t)) _],
    { rw ["[", expr function.comp.assoc, ",", "<-", expr rel_embedding.coe_trans, "]"] ["at", ident hg],
      exact [expr ⟨_, hg⟩] },
    rw ["[", expr range_comp, ",", expr image_subset_iff, "]"] [],
    simp [] [] [] [] [] [] }
end

end PartialOrderₓ

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_wf.is_pwo [linear_order α] {s : set α} (hs : s.is_wf) : s.is_pwo :=
λ f hf, begin
  rw ["[", expr is_wf, ",", expr well_founded_on_iff, "]"] ["at", ident hs],
  have [ident hrange] [":", expr (range f).nonempty] [":=", expr ⟨f 0, mem_range_self 0⟩],
  let [ident a] [] [":=", expr hs.min (range f) hrange],
  obtain ["⟨", ident m, ",", ident hm, "⟩", ":=", expr hs.min_mem (range f) hrange],
  refine [expr ⟨m, m.succ, m.lt_succ_self, le_of_not_lt (λ con, _)⟩],
  rw [expr hm] ["at", ident con],
  apply [expr hs.not_lt_min (range f) hrange (mem_range_self m.succ) ⟨con, hf (mem_range_self m.succ), hf _⟩],
  rw ["<-", expr hm] [],
  apply [expr mem_range_self]
end

theorem is_wf_iff_is_pwo [LinearOrderₓ α] {s : Set α} : s.is_wf ↔ s.is_pwo :=
  ⟨is_wf.is_pwo, is_pwo.is_wf⟩

end Set

namespace Finset

@[simp]
theorem partially_well_ordered_on {r : α → α → Prop} [IsRefl α r] (f : Finset α) :
  Set.PartiallyWellOrderedOn («expr↑ » f : Set α) r :=
  by 
    intro g hg 
    byCases' hinj : Function.Injective g
    ·
      exact (Set.infinite_of_injective_forall_mem hinj (Set.range_subset_iff.1 hg) f.finite_to_set).elim
    ·
      rw [Function.Injective] at hinj 
      pushNeg  at hinj 
      obtain ⟨m, n, gmgn, hne⟩ := hinj 
      cases' lt_or_gt_of_neₓ hne with hlt hlt <;>
        ·
          refine' ⟨_, _, hlt, _⟩
          rw [gmgn]
          exact refl_of r _

@[simp]
theorem is_pwo [PartialOrderₓ α] (f : Finset α) : Set.IsPwo («expr↑ » f : Set α) :=
  f.partially_well_ordered_on

@[simp]
theorem well_founded_on {r : α → α → Prop} [IsStrictOrder α r] (f : Finset α) :
  Set.WellFoundedOn («expr↑ » f : Set α) r :=
  by 
    rw [Set.well_founded_on_iff_no_descending_seq]
    intro g con 
    apply Set.infinite_of_injective_forall_mem g.injective (Set.range_subset_iff.1 con)
    exact f.finite_to_set

@[simp]
theorem is_wf [PartialOrderₓ α] (f : Finset α) : Set.IsWf («expr↑ » f : Set α) :=
  f.is_pwo.is_wf

end Finset

namespace Set

variable[PartialOrderₓ α]{s : Set α}{a : α}

theorem finite.is_pwo (h : s.finite) : s.is_pwo :=
  by 
    rw [←h.coe_to_finset]
    exact h.to_finset.is_pwo

@[simp]
theorem fintype.is_pwo [Fintype α] : s.is_pwo :=
  (finite.of_fintype s).IsPwo

@[simp]
theorem is_pwo_empty : is_pwo (∅ : Set α) :=
  finite_empty.IsPwo

@[simp]
theorem is_pwo_singleton a : is_pwo ({a} : Set α) :=
  (finite_singleton a).IsPwo

theorem is_pwo.insert a (hs : is_pwo s) : is_pwo (insert a s) :=
  by 
    rw [←union_singleton]
    exact hs.union (is_pwo_singleton a)

/-- `is_wf.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable def is_wf.min (hs : is_wf s) (hn : s.nonempty) : α :=
  hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)

theorem is_wf.min_mem (hs : is_wf s) (hn : s.nonempty) : hs.min hn ∈ s :=
  (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

theorem is_wf.not_lt_min (hs : is_wf s) (hn : s.nonempty) (ha : a ∈ s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype) (mem_univ (⟨a, ha⟩ : s))

@[simp]
theorem is_wf_min_singleton a {hs : is_wf ({a} : Set α)} {hn : ({a} : Set α).Nonempty} : hs.min hn = a :=
  eq_of_mem_singleton (is_wf.min_mem hs hn)

end Set

@[simp]
theorem Finset.is_wf_sup {ι : Type _} [PartialOrderₓ α] (f : Finset ι) (g : ι → Set α)
  (hf : ∀ (i : ι), i ∈ f → (g i).IsWf) : (f.sup g).IsWf :=
  by 
    classical 
    revert hf 
    apply f.induction_on
    ·
      intro h 
      simp [set.is_pwo_empty.is_wf]
    ·
      intro s f sf hf hsf 
      rw [Finset.sup_insert]
      exact (hsf s (Finset.mem_insert_self _ _)).union (hf fun s' s'f => hsf _ (Finset.mem_insert_of_mem s'f))

@[simp]
theorem Finset.is_pwo_sup {ι : Type _} [PartialOrderₓ α] (f : Finset ι) (g : ι → Set α)
  (hf : ∀ (i : ι), i ∈ f → (g i).IsPwo) : (f.sup g).IsPwo :=
  by 
    classical 
    revert hf 
    apply f.induction_on
    ·
      intro h 
      simp [set.is_pwo_empty.is_wf]
    ·
      intro s f sf hf hsf 
      rw [Finset.sup_insert]
      exact (hsf s (Finset.mem_insert_self _ _)).union (hf fun s' s'f => hsf _ (Finset.mem_insert_of_mem s'f))

namespace Set

variable[LinearOrderₓ α]{s t : Set α}{a : α}

theorem is_wf.min_le (hs : s.is_wf) (hn : s.nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
  le_of_not_ltₓ (hs.not_lt_min hn ha)

theorem is_wf.le_min_iff (hs : s.is_wf) (hn : s.nonempty) : a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
  ⟨fun ha b hb => le_transₓ ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩

theorem is_wf.min_le_min_of_subset {hs : s.is_wf} {hsn : s.nonempty} {ht : t.is_wf} {htn : t.nonempty} (hst : s ⊆ t) :
  ht.min htn ≤ hs.min hsn :=
  (is_wf.le_min_iff _ _).2 fun b hb => ht.min_le htn (hst hb)

theorem is_wf.min_union (hs : s.is_wf) (hsn : s.nonempty) (ht : t.is_wf) (htn : t.nonempty) :
  (hs.union ht).min (union_nonempty.2 (Or.intro_left _ hsn)) = min (hs.min hsn) (ht.min htn) :=
  by 
    refine'
      le_antisymmₓ
        (le_minₓ (is_wf.min_le_min_of_subset (subset_union_left _ _))
          (is_wf.min_le_min_of_subset (subset_union_right _ _)))
        _ 
    rw [min_le_iff]
    exact
      ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (Or.intro_left _ hsn)))).imp (hs.min_le _)
        (ht.min_le _)

end Set

namespace Set

variable{s : Set α}{t : Set α}

@[toAdditive]
theorem is_pwo.mul [OrderedCancelCommMonoid α] (hs : s.is_pwo) (ht : t.is_pwo) : is_pwo (s*t) :=
  by 
    rw [←image_mul_prod]
    exact (is_pwo.prod hs ht).image_of_monotone fun _ _ h => mul_le_mul' h.1 h.2

variable[LinearOrderedCancelCommMonoid α]

@[toAdditive]
theorem is_wf.mul (hs : s.is_wf) (ht : t.is_wf) : is_wf (s*t) :=
  (hs.is_pwo.mul ht.is_pwo).IsWf

@[toAdditive]
theorem is_wf.min_mul (hs : s.is_wf) (ht : t.is_wf) (hsn : s.nonempty) (htn : t.nonempty) :
  (hs.mul ht).min (hsn.mul htn) = hs.min hsn*ht.min htn :=
  by 
    refine' le_antisymmₓ (is_wf.min_le _ _ (mem_mul.2 ⟨_, _, hs.min_mem _, ht.min_mem _, rfl⟩)) _ 
    rw [is_wf.le_min_iff]
    rintro _ ⟨x, y, hx, hy, rfl⟩
    exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Set

namespace PartiallyWellOrderedOn

/-- In the context of partial well-orderings, a bad sequence is a nonincreasing sequence
  whose range is contained in a particular set `s`. One exists if and only if `s` is not
  partially well-ordered. -/
def is_bad_seq (r : α → α → Prop) (s : Set α) (f : ℕ → α) : Prop :=
  Set.Range f ⊆ s ∧ ∀ (m n : ℕ), m < n → ¬r (f m) (f n)

theorem iff_forall_not_is_bad_seq (r : α → α → Prop) (s : Set α) :
  s.partially_well_ordered_on r ↔ ∀ f, ¬is_bad_seq r s f :=
  by 
    rw [Set.PartiallyWellOrderedOn]
    apply forall_congrₓ fun f => _ 
    simp [is_bad_seq]

/-- This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`. -/
def is_min_bad_seq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α) : Prop :=
  ∀ (g : ℕ → α), (∀ (m : ℕ), m < n → f m = g m) → rk (g n) < rk (f n) → ¬is_bad_seq r s g

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a bad sequence `f`, this constructs a bad sequence that agrees with `f` on the first `n`
  terms and is minimal at `n`.
-/
noncomputable
def min_bad_seq_of_bad_seq
(r : α → α → exprProp())
(rk : α → exprℕ())
(s : set α)
(n : exprℕ())
(f : exprℕ() → α)
(hf : is_bad_seq r s f) : {g : exprℕ() → α // «expr ∧ »(∀
 m : exprℕ(), «expr < »(m, n) → «expr = »(f m, g m), «expr ∧ »(is_bad_seq r s g, is_min_bad_seq r rk s n g))} :=
begin
  classical,
  have [ident h] [":", expr «expr∃ , »((k : exprℕ())
    (g : exprℕ() → α), «expr ∧ »(∀
     m, «expr < »(m, n) → «expr = »(f m, g m), «expr ∧ »(is_bad_seq r s g, «expr = »(rk (g n), k))))] [":=", expr ⟨_, f, λ
    _ _, rfl, hf, rfl⟩],
  obtain ["⟨", ident h1, ",", ident h2, ",", ident h3, "⟩", ":=", expr classical.some_spec (nat.find_spec h)],
  refine [expr ⟨classical.some (nat.find_spec h), h1, by convert [] [expr h2] [], λ g hg1 hg2 con, _⟩],
  refine [expr nat.find_min h _ ⟨g, λ m mn, (h1 m mn).trans (hg1 m mn), by convert [] [expr con] [], rfl⟩],
  rwa ["<-", expr h3] []
end

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_min_bad_of_exists_bad
(r : α → α → exprProp())
(rk : α → exprℕ())
(s : set α) : «expr∃ , »((f), is_bad_seq r s f) → «expr∃ , »((f), «expr ∧ »(is_bad_seq r s f, ∀
  n, is_min_bad_seq r rk s n f)) :=
begin
  rintro ["⟨", ident f0, ",", "(", ident hf0, ":", expr is_bad_seq r s f0, ")", "⟩"],
  let [ident fs] [":", expr ∀
   n : exprℕ(), {f : exprℕ() → α // «expr ∧ »(is_bad_seq r s f, is_min_bad_seq r rk s n f)}] [],
  { refine [expr nat.rec _ _],
    { exact [expr ⟨(min_bad_seq_of_bad_seq r rk s 0 f0 hf0).1, (min_bad_seq_of_bad_seq r rk s 0 f0 hf0).2.2⟩] },
    { exact [expr λ
       n
       fn, ⟨(min_bad_seq_of_bad_seq r rk s «expr + »(n, 1) fn.1 fn.2.1).1, (min_bad_seq_of_bad_seq r rk s «expr + »(n, 1) fn.1 fn.2.1).2.2⟩] } },
  have [ident h] [":", expr ∀ m n, «expr ≤ »(m, n) → «expr = »((fs m).1 m, (fs n).1 m)] [],
  { intros [ident m, ident n, ident mn],
    obtain ["⟨", ident k, ",", ident rfl, "⟩", ":=", expr exists_add_of_le mn],
    clear [ident mn],
    induction [expr k] [] ["with", ident k, ident ih] [],
    { refl },
    rw ["[", expr ih, ",", expr (min_bad_seq_of_bad_seq r rk s «expr + »(m, k).succ (fs «expr + »(m, k)).1 (fs «expr + »(m, k)).2.1).2.1 m (nat.lt_succ_iff.2 (nat.add_le_add_left k.zero_le m)), "]"] [],
    refl },
  refine [expr ⟨λ
    n, (fs n).1 n, ⟨set.range_subset_iff.2 (λ n, (fs n).2.1.1 (mem_range_self n)), λ m n mn, _⟩, λ n g hg1 hg2, _⟩],
  { dsimp [] [] [] [],
    rw ["[", "<-", expr subtype.val_eq_coe, ",", expr h m n (le_of_lt mn), "]"] [],
    convert [] [expr (fs n).2.1.2 m n mn] [] },
  { convert [] [expr (fs n).2.2 g (λ m mn, eq.trans _ (hg1 m mn)) (lt_of_lt_of_le hg2 (le_refl _))] [],
    rw ["<-", expr h m n (le_of_lt mn)] [] }
end

theorem iff_not_exists_is_min_bad_seq {r : α → α → Prop} (rk : α → ℕ) {s : Set α} :
  s.partially_well_ordered_on r ↔ ¬∃ f, is_bad_seq r s f ∧ ∀ n, is_min_bad_seq r rk s n f :=
  by 
    rw [iff_forall_not_is_bad_seq, ←not_exists, not_congr]
    split 
    ·
      apply exists_min_bad_of_exists_bad 
    rintro ⟨f, hf1, hf2⟩
    exact ⟨f, hf1⟩

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Higman's Lemma, which states that for any reflexive, transitive relation `r` which is
  partially well-ordered on a set `s`, the relation `list.sublist_forall₂ r` is partially
  well-ordered on the set of lists of elements of `s`. That relation is defined so that
  `list.sublist_forall₂ r l₁ l₂` whenever `l₁` related pointwise by `r` to a sublist of `l₂`.  -/
theorem partially_well_ordered_on_sublist_forall₂
(r : α → α → exprProp())
[is_refl α r]
[is_trans α r]
{s : set α}
(h : s.partially_well_ordered_on r) : {l : list α | ∀
x, «expr ∈ »(x, l) → «expr ∈ »(x, s)}.partially_well_ordered_on (list.sublist_forall₂ r) :=
begin
  rcases [expr s.eq_empty_or_nonempty, "with", ident rfl, "|", "⟨", ident as, ",", ident has, "⟩"],
  { apply [expr partially_well_ordered_on.mono (finset.partially_well_ordered_on {list.nil})],
    { intros [ident l, ident hl],
      rw ["[", expr finset.mem_coe, ",", expr finset.mem_singleton, ",", expr list.eq_nil_iff_forall_not_mem, "]"] [],
      exact [expr hl] },
    apply_instance },
  haveI [] [":", expr inhabited α] [":=", expr ⟨as⟩],
  rw ["[", expr iff_not_exists_is_min_bad_seq list.length, "]"] [],
  rintro ["⟨", ident f, ",", ident hf1, ",", ident hf2, "⟩"],
  have [ident hnil] [":", expr ∀
   n, «expr ≠ »(f n, list.nil)] [":=", expr λ
   n con, hf1.2 n n.succ n.lt_succ_self «expr ▸ »(con.symm, list.sublist_forall₂.nil)],
  obtain ["⟨", ident g, ",", ident hg, "⟩", ":=", expr h.exists_monotone_subseq «expr ∘ »(list.head, f) _],
  swap,
  { simp [] [] ["only"] ["[", expr set.range_subset_iff, ",", expr function.comp_apply, "]"] [] [],
    exact [expr λ n, hf1.1 (set.mem_range_self n) _ (list.head_mem_self (hnil n))] },
  have [ident hf'] [] [":=", expr hf2 (g 0) (λ
    n, if «expr < »(n, g 0) then f n else list.tail (f (g «expr - »(n, g 0)))) (λ m hm, (if_pos hm).symm) _],
  swap,
  { simp [] [] ["only"] ["[", expr if_neg (lt_irrefl (g 0)), ",", expr tsub_self, "]"] [] [],
    rw ["[", expr list.length_tail, ",", "<-", expr nat.pred_eq_sub_one, "]"] [],
    exact [expr nat.pred_lt (λ con, hnil _ (list.length_eq_zero.1 con))] },
  rw ["[", expr is_bad_seq, "]"] ["at", ident hf'],
  push_neg ["at", ident hf'],
  obtain ["⟨", ident m, ",", ident n, ",", ident mn, ",", ident hmn, "⟩", ":=", expr hf' _],
  swap,
  { rw [expr set.range_subset_iff] [],
    rintro [ident n, ident x, ident hx],
    split_ifs ["at", ident hx] ["with", ident hn, ident hn],
    { exact [expr hf1.1 (set.mem_range_self _) _ hx] },
    { refine [expr hf1.1 (set.mem_range_self _) _ (list.tail_subset _ hx)] } },
  by_cases [expr hn, ":", expr «expr < »(n, g 0)],
  { apply [expr hf1.2 m n mn],
    rwa ["[", expr if_pos hn, ",", expr if_pos (mn.trans hn), "]"] ["at", ident hmn] },
  { obtain ["⟨", ident n', ",", ident rfl, "⟩", ":=", expr le_iff_exists_add.1 (not_lt.1 hn)],
    rw ["[", expr if_neg hn, ",", expr add_comm (g 0) n', ",", expr add_tsub_cancel_right, "]"] ["at", ident hmn],
    split_ifs ["at", ident hmn] ["with", ident hm, ident hm],
    { apply [expr hf1.2 m (g n') (lt_of_lt_of_le hm (g.monotone n'.zero_le))],
      exact [expr trans hmn (list.tail_sublist_forall₂_self _)] },
    { rw ["[", "<-", expr tsub_lt_iff_left (le_of_not_lt hm), "]"] ["at", ident mn],
      apply [expr hf1.2 _ _ (g.lt_iff_lt.2 mn)],
      rw ["[", "<-", expr list.cons_head_tail (hnil (g «expr - »(m, g 0))), ",", "<-", expr list.cons_head_tail (hnil (g n')), "]"] [],
      exact [expr list.sublist_forall₂.cons (hg _ _ (le_of_lt mn)) hmn] } }
end

end PartiallyWellOrderedOn

namespace IsPwo

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem submonoid_closure
[ordered_cancel_comm_monoid α]
{s : set α}
(hpos : ∀ x : α, «expr ∈ »(x, s) → «expr ≤ »(1, x))
(h : s.is_pwo) : is_pwo (submonoid.closure s : set α) :=
begin
  have [ident hl] [":", expr «expr ⊆ »((submonoid.closure s : set α), «expr '' »(list.prod, {l : list α | ∀
     x, «expr ∈ »(x, l) → «expr ∈ »(x, s)}))] [],
  { intros [ident x, ident hx],
    rw [expr set_like.mem_coe] ["at", ident hx],
    refine [expr submonoid.closure_induction hx (λ
      x hx, ⟨_, λ y hy, _, list.prod_singleton⟩) ⟨_, λ y hy, (list.not_mem_nil _ hy).elim, list.prod_nil⟩ _],
    { rwa [expr list.mem_singleton.1 hy] [] },
    rintros ["_", "_", "⟨", ident l, ",", ident hl, ",", ident rfl, "⟩", "⟨", ident l', ",", ident hl', ",", ident rfl, "⟩"],
    refine [expr ⟨_, λ y hy, _, list.prod_append⟩],
    cases [expr list.mem_append.1 hy] ["with", ident hy, ident hy],
    { exact [expr hl _ hy] },
    { exact [expr hl' _ hy] } },
  apply [expr ((h.partially_well_ordered_on_sublist_forall₂ ((«expr ≤ »))).image_of_monotone_on _).mono hl],
  intros [ident l1, ident l2, ident hl1, ident hl2, ident h12],
  obtain ["⟨", ident l, ",", ident hll1, ",", ident hll2, "⟩", ":=", expr list.sublist_forall₂_iff.1 h12],
  refine [expr le_trans (list.rel_prod (le_refl 1) (λ a b ab c d cd, mul_le_mul' ab cd) hll1) _],
  obtain ["⟨", ident l', ",", ident hl', "⟩", ":=", expr hll2.exists_perm_append],
  rw ["[", expr hl'.prod_eq, ",", expr list.prod_append, ",", "<-", expr mul_one l.prod, ",", expr mul_assoc, ",", expr one_mul, "]"] [],
  apply [expr mul_le_mul_left'],
  have [ident hl's] [] [":=", expr λ x hx, hl2 x (list.subset.trans (l.subset_append_right _) hl'.symm.subset hx)],
  clear [ident hl'],
  induction [expr l'] [] ["with", ident x1, ident x2, ident x3, ident x4, ident x5] [],
  { refl },
  rw ["[", expr list.prod_cons, ",", "<-", expr one_mul (1 : α), "]"] [],
  exact [expr mul_le_mul' (hpos x1 (hl's x1 (list.mem_cons_self x1 x2))) (x3 (λ
     x hx, hl's x (list.mem_cons_of_mem _ hx)))]
end

end IsPwo

/-- `set.mul_antidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
  that multiply to `a`. -/
@[toAdditive
      "`set.add_antidiagonal s t a` is the set of all pairs of an element in `s`\n  and an element in `t` that add to `a`."]
def mul_antidiagonal [Monoidₓ α] (s t : Set α) (a : α) : Set (α × α) :=
  { x | (x.1*x.2) = a ∧ x.1 ∈ s ∧ x.2 ∈ t }

namespace MulAntidiagonal

@[simp, toAdditive]
theorem mem_mul_antidiagonal [Monoidₓ α] {s t : Set α} {a : α} {x : α × α} :
  x ∈ mul_antidiagonal s t a ↔ (x.1*x.2) = a ∧ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.refl _

section CancelCommMonoid

variable[CancelCommMonoid α]{s t : Set α}{a : α}

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem fst_eq_fst_iff_snd_eq_snd
{x
 y : mul_antidiagonal s t a} : «expr ↔ »(«expr = »((x : «expr × »(α, α)).fst, (y : «expr × »(α, α)).fst), «expr = »((x : «expr × »(α, α)).snd, (y : «expr × »(α, α)).snd)) :=
⟨λ h, begin
   have [ident hx] [] [":=", expr x.2.1],
   rw ["[", expr subtype.val_eq_coe, ",", expr h, "]"] ["at", ident hx],
   apply [expr mul_left_cancel (hx.trans y.2.1.symm)]
 end, λ h, begin
   have [ident hx] [] [":=", expr x.2.1],
   rw ["[", expr subtype.val_eq_coe, ",", expr h, "]"] ["at", ident hx],
   apply [expr mul_right_cancel (hx.trans y.2.1.symm)]
 end⟩

@[toAdditive]
theorem eq_of_fst_eq_fst {x y : mul_antidiagonal s t a} (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
  Subtype.ext (Prod.extₓ h (mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd.1 h))

@[toAdditive]
theorem eq_of_snd_eq_snd {x y : mul_antidiagonal s t a} (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
  Subtype.ext (Prod.extₓ (mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd.2 h) h)

end CancelCommMonoid

section OrderedCancelCommMonoid

variable[OrderedCancelCommMonoid α](s t : Set α)(a : α)

@[toAdditive]
theorem eq_of_fst_le_fst_of_snd_le_snd {x y : mul_antidiagonal s t a} (h1 : (x : α × α).fst ≤ (y : α × α).fst)
  (h2 : (x : α × α).snd ≤ (y : α × α).snd) : x = y :=
  by 
    apply eq_of_fst_eq_fst 
    cases' eq_or_lt_of_le h1 with heq hlt
    ·
      exact HEq 
    exfalso 
    exact
      ne_of_ltₓ (mul_lt_mul_of_lt_of_le hlt h2)
        ((mem_mul_antidiagonal.1 x.2).1.trans (mem_mul_antidiagonal.1 y.2).1.symm)

variable{s}{t}

-- error in Order.WellFoundedSet: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]] theorem finite_of_is_pwo (hs : s.is_pwo) (ht : t.is_pwo) (a) : (mul_antidiagonal s t a).finite :=
begin
  by_contra [ident h],
  rw ["[", "<-", expr set.infinite, "]"] ["at", ident h],
  have [ident h1] [":", expr (mul_antidiagonal s t a).partially_well_ordered_on «expr ⁻¹'o »(prod.fst, («expr ≤ »))] [],
  { intros [ident f, ident hf],
    refine [expr hs «expr ∘ »(prod.fst, f) _],
    rw [expr range_comp] [],
    rintros ["_", "⟨", "⟨", ident x, ",", ident y, "⟩", ",", ident hxy, ",", ident rfl, "⟩"],
    exact [expr (mem_mul_antidiagonal.1 (hf hxy)).2.1] },
  have [ident h2] [":", expr (mul_antidiagonal s t a).partially_well_ordered_on «expr ⁻¹'o »(prod.snd, («expr ≤ »))] [],
  { intros [ident f, ident hf],
    refine [expr ht «expr ∘ »(prod.snd, f) _],
    rw [expr range_comp] [],
    rintros ["_", "⟨", "⟨", ident x, ",", ident y, "⟩", ",", ident hxy, ",", ident rfl, "⟩"],
    exact [expr (mem_mul_antidiagonal.1 (hf hxy)).2.2] },
  obtain ["⟨", ident g, ",", ident hg, "⟩", ":=", expr h1.exists_monotone_subseq (λ x, h.nat_embedding _ x) _],
  swap,
  { rintro ["_", "⟨", ident k, ",", ident rfl, "⟩"],
    exact [expr (infinite.nat_embedding (s.mul_antidiagonal t a) h _).2] },
  obtain ["⟨", ident m, ",", ident n, ",", ident mn, ",", ident h2', "⟩", ":=", expr h2 (λ
    x, h.nat_embedding _ (g x)) _],
  swap,
  { rintro ["_", "⟨", ident k, ",", ident rfl, "⟩"],
    exact [expr (infinite.nat_embedding (s.mul_antidiagonal t a) h _).2] },
  apply [expr ne_of_lt mn (g.injective ((h.nat_embedding _).injective _))],
  exact [expr eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ (le_of_lt mn)) h2']
end

end OrderedCancelCommMonoid

@[toAdditive]
theorem finite_of_is_wf [LinearOrderedCancelCommMonoid α] {s t : Set α} (hs : s.is_wf) (ht : t.is_wf) a :
  (mul_antidiagonal s t a).Finite :=
  finite_of_is_pwo hs.is_pwo ht.is_pwo a

end MulAntidiagonal

end Set

namespace Finset

variable[OrderedCancelCommMonoid α]

variable{s t : Set α}(hs : s.is_pwo)(ht : t.is_pwo)(a : α)

/-- `finset.mul_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in
  `s` and an element in `t` that multiply to `a`, but its construction requires proofs
  `hs` and `ht` that `s` and `t` are well-ordered. -/
@[toAdditive
      "`finset.add_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in\n  `s` and an element in `t` that add to `a`, but its construction requires proofs\n  `hs` and `ht` that `s` and `t` are well-ordered."]
noncomputable def mul_antidiagonal : Finset (α × α) :=
  (Set.MulAntidiagonal.finite_of_is_pwo hs ht a).toFinset

variable{hs}{ht}{u : Set α}{hu : u.is_pwo}{a}{x : α × α}

@[simp, toAdditive]
theorem mem_mul_antidiagonal : x ∈ mul_antidiagonal hs ht a ↔ (x.1*x.2) = a ∧ x.1 ∈ s ∧ x.2 ∈ t :=
  by 
    simp [mul_antidiagonal]

@[toAdditive]
theorem mul_antidiagonal_mono_left (hus : u ⊆ s) : Finset.mulAntidiagonal hu ht a ⊆ Finset.mulAntidiagonal hs ht a :=
  fun x hx =>
    by 
      rw [mem_mul_antidiagonal] at *
      exact ⟨hx.1, hus hx.2.1, hx.2.2⟩

@[toAdditive]
theorem mul_antidiagonal_mono_right (hut : u ⊆ t) : Finset.mulAntidiagonal hs hu a ⊆ Finset.mulAntidiagonal hs ht a :=
  fun x hx =>
    by 
      rw [mem_mul_antidiagonal] at *
      exact ⟨hx.1, hx.2.1, hut hx.2.2⟩

@[toAdditive]
theorem support_mul_antidiagonal_subset_mul : { a:α | (mul_antidiagonal hs ht a).Nonempty } ⊆ s*t :=
  fun x ⟨⟨a1, a2⟩, ha⟩ =>
    by 
      obtain ⟨hmul, h1, h2⟩ := mem_mul_antidiagonal.1 ha 
      exact ⟨a1, a2, h1, h2, hmul⟩

@[toAdditive]
theorem is_pwo_support_mul_antidiagonal : { a:α | (mul_antidiagonal hs ht a).Nonempty }.IsPwo :=
  (hs.mul ht).mono support_mul_antidiagonal_subset_mul

@[toAdditive]
theorem mul_antidiagonal_min_mul_min {α} [LinearOrderedCancelCommMonoid α] {s t : Set α} (hs : s.is_wf) (ht : t.is_wf)
  (hns : s.nonempty) (hnt : t.nonempty) :
  mul_antidiagonal hs.is_pwo ht.is_pwo (hs.min hns*ht.min hnt) = {(hs.min hns, ht.min hnt)} :=
  by 
    ext ⟨a1, a2⟩
    rw [mem_mul_antidiagonal, Finset.mem_singleton, Prod.ext_iff]
    split 
    ·
      rintro ⟨hast, has, hat⟩
      cases' eq_or_lt_of_le (hs.min_le hns has) with heq hlt
      ·
        refine' ⟨HEq.symm, _⟩
        rw [HEq] at hast 
        exact mul_left_cancelₓ hast
      ·
        contrapose hast 
        exact ne_of_gtₓ (mul_lt_mul_of_lt_of_le hlt (ht.min_le hnt hat))
    ·
      rintro ⟨ha1, ha2⟩
      rw [ha1, ha2]
      exact ⟨rfl, hs.min_mem _, ht.min_mem _⟩

end Finset

theorem WellFounded.is_wf [LT α] (h : WellFounded (· < · : α → α → Prop)) (s : Set α) : s.is_wf :=
  (Set.is_wf_univ_iff.2 h).mono (Set.subset_univ s)

