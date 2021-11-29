import Mathbin.Data.Equiv.Denumerable 
import Mathbin.Order.PreorderHom 
import Mathbin.Data.Nat.Lattice

/-!
# Relation embeddings from the naturals

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `nat_lt`/`nat_gt`: Make an order embedding `ℕ ↪ α` from an increasing/decreasing function `ℕ → α`.
* `monotonic_sequence_limit`: The limit of an eventually-constant monotone sequence `ℕ →ₘ α`.
* `monotonic_sequence_limit_index`: The index of the first occurence of `monotonic_sequence_limit`
  in the sequence.
-/


namespace RelEmbedding

variable {α : Type _} {r : α → α → Prop} [IsStrictOrder α r]

/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def nat_lt (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n+1))) : (· < · : ℕ → ℕ → Prop) ↪r r :=
  of_monotone f$
    fun a b h =>
      by 
        induction' b with b IH
        ·
          exact (Nat.not_lt_zeroₓ _ h).elim 
        cases' Nat.lt_succ_iff_lt_or_eq.1 h with h e
        ·
          exact trans (IH h) (H _)
        ·
          subst b 
          apply H

@[simp]
theorem nat_lt_apply {f : ℕ → α} {H : ∀ n : ℕ, r (f n) (f (n+1))} {n : ℕ} : nat_lt f H n = f n :=
  rfl

-- error in Order.OrderIsoNat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def nat_gt
(f : exprℕ() → α)
(H : ∀ n : exprℕ(), r (f «expr + »(n, 1)) (f n)) : «expr ↪r »(((«expr > ») : exprℕ() → exprℕ() → exprProp()), r) :=
by haveI [] [] [":=", expr is_strict_order.swap r]; exact [expr rel_embedding.swap (nat_lt f H)]

theorem well_founded_iff_no_descending_seq : WellFounded r ↔ IsEmpty ((· > · : ℕ → ℕ → Prop) ↪r r) :=
  ⟨fun ⟨h⟩ =>
      ⟨fun ⟨f, o⟩ =>
          suffices ∀ a, Acc r a → ∀ n, a ≠ f n from this (f 0) (h _) 0 rfl 
          fun a ac =>
            by 
              induction' ac with a _ IH 
              intro n h 
              subst a 
              exact IH (f (n+1)) (o.2 (Nat.lt_succ_selfₓ _)) _ rfl⟩,
    fun E =>
      ⟨fun a =>
          Classical.by_contradiction$
            fun na =>
              let ⟨f, h⟩ :=
                Classical.axiom_of_choice$
                  show ∀ x : { a // ¬Acc r a }, ∃ y : { a // ¬Acc r a }, r y.1 x.1 from
                    fun ⟨x, h⟩ =>
                      Classical.by_contradiction$
                        fun hn => h$ ⟨_, fun y h => Classical.by_contradiction$ fun na => hn ⟨⟨y, na⟩, h⟩⟩
              E.elim'
                ((nat_gt fun n => ((f^[n]) ⟨a, na⟩).1)$
                  fun n =>
                    by 
                      rw [Function.iterate_succ']
                      apply h)⟩⟩

end RelEmbedding

namespace Nat

variable (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s]

/-- An order embedding from `ℕ` to itself with a specified range -/
def order_embedding_of_set : ℕ ↪o ℕ :=
  (RelEmbedding.orderEmbeddingOfLtEmbedding
        (RelEmbedding.natLt (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype s)

/-- `nat.subtype.of_nat` as an order isomorphism between `ℕ` and an infinite decidable subset. -/
noncomputable def subtype.order_iso_of_nat : ℕ ≃o s :=
  RelIso.ofSurjective
    (RelEmbedding.orderEmbeddingOfLtEmbedding
      (RelEmbedding.natLt (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
    Nat.Subtype.of_nat_surjective

variable {s}

@[simp]
theorem order_embedding_of_set_apply {n : ℕ} : order_embedding_of_set s n = subtype.of_nat s n :=
  rfl

@[simp]
theorem subtype.order_iso_of_nat_apply {n : ℕ} : subtype.order_iso_of_nat s n = subtype.of_nat s n :=
  by 
    simp [subtype.order_iso_of_nat]

variable (s)

@[simp]
theorem order_embedding_of_set_range : Set.Range (Nat.orderEmbeddingOfSet s) = s :=
  by 
    ext x 
    rw [Set.mem_range, Nat.orderEmbeddingOfSet]
    split  <;> intro h
    ·
      obtain ⟨y, rfl⟩ := h 
      simp 
    ·
      refine' ⟨(Nat.Subtype.orderIsoOfNat s).symm ⟨x, h⟩, _⟩
      simp only [RelEmbedding.coe_trans, RelEmbedding.order_embedding_of_lt_embedding_apply, RelEmbedding.nat_lt_apply,
        Function.comp_app, OrderEmbedding.subtype_apply]
      rw [←subtype.order_iso_of_nat_apply, OrderIso.apply_symm_apply, Subtype.coe_mk]

end Nat

-- error in Order.OrderIsoNat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_increasing_or_nonincreasing_subseq'
{α : Type*}
(r : α → α → exprProp())
(f : exprℕ() → α) : «expr∃ , »((g : «expr ↪o »(exprℕ(), exprℕ())), «expr ∨ »(∀
  n : exprℕ(), r (f (g n)) (f (g «expr + »(n, 1))), ∀
  m n : exprℕ(), «expr < »(m, n) → «expr¬ »(r (f (g m)) (f (g n))))) :=
begin
  classical,
  let [ident bad] [":", expr set exprℕ()] [":=", expr {m | ∀ n, «expr < »(m, n) → «expr¬ »(r (f m) (f n))}],
  by_cases [expr hbad, ":", expr infinite bad],
  { haveI [] [] [":=", expr hbad],
    refine [expr ⟨nat.order_embedding_of_set bad, or.intro_right _ (λ m n mn, _)⟩],
    have [ident h] [] [":=", expr set.mem_range_self m],
    rw [expr nat.order_embedding_of_set_range bad] ["at", ident h],
    exact [expr h _ ((order_embedding.lt_iff_lt _).2 mn)] },
  { rw ["[", expr set.infinite_coe_iff, ",", expr set.infinite, ",", expr not_not, "]"] ["at", ident hbad],
    obtain ["⟨", ident m, ",", ident hm, "⟩", ":", expr «expr∃ , »((m), ∀
      n, «expr ≤ »(m, n) → «expr¬ »(«expr ∈ »(n, bad)))],
    { by_cases [expr he, ":", expr hbad.to_finset.nonempty],
      { refine [expr ⟨(hbad.to_finset.max' he).succ, λ
          n hn nbad, nat.not_succ_le_self _ (hn.trans (hbad.to_finset.le_max' n (hbad.mem_to_finset.2 nbad)))⟩] },
      { exact [expr ⟨0, λ n hn nbad, he ⟨n, hbad.mem_to_finset.2 nbad⟩⟩] } },
    have [ident h] [":", expr ∀
     n : exprℕ(), «expr∃ , »((n' : exprℕ()), «expr ∧ »(«expr < »(n, n'), r (f «expr + »(n, m)) (f «expr + »(n', m))))] [],
    { intro [ident n],
      have [ident h] [] [":=", expr hm _ (le_add_of_nonneg_left n.zero_le)],
      simp [] [] ["only"] ["[", expr exists_prop, ",", expr not_not, ",", expr set.mem_set_of_eq, ",", expr not_forall, "]"] [] ["at", ident h],
      obtain ["⟨", ident n', ",", ident hn1, ",", ident hn2, "⟩", ":=", expr h],
      obtain ["⟨", ident x, ",", ident hpos, ",", ident rfl, "⟩", ":=", expr exists_pos_add_of_lt hn1],
      refine [expr ⟨«expr + »(n, x), add_lt_add_left hpos n, _⟩],
      rw ["[", expr add_assoc, ",", expr add_comm x m, ",", "<-", expr add_assoc, "]"] [],
      exact [expr hn2] },
    let [ident g'] [":", expr exprℕ() → exprℕ()] [":=", expr @nat.rec (λ _, exprℕ()) m (λ n gn, nat.find (h gn))],
    exact [expr ⟨(rel_embedding.nat_lt (λ
        n, «expr + »(g' n, m)) (λ
        n, nat.add_lt_add_right (nat.find_spec (h (g' n))).1 m)).order_embedding_of_lt_embedding, or.intro_left _ (λ
       n, (nat.find_spec (h (g' n))).2)⟩] }
end

theorem exists_increasing_or_nonincreasing_subseq {α : Type _} (r : α → α → Prop) [IsTrans α r] (f : ℕ → α) :
  ∃ g : ℕ ↪o ℕ, (∀ m n : ℕ, m < n → r (f (g m)) (f (g n))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) :=
  by 
    obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
    ·
      refine' ⟨g, Or.intro_left _ fun m n mn => _⟩
      obtain ⟨x, rfl⟩ := le_iff_exists_add.1 (Nat.succ_le_iff.2 mn)
      induction' x with x ih
      ·
        apply hr
      ·
        apply IsTrans.trans _ _ _ _ (hr _)
        exact ih (lt_of_lt_of_leₓ m.lt_succ_self (Nat.le_add_rightₓ _ _))
    ·
      exact ⟨g, Or.intro_rightₓ _ hnr⟩

-- error in Order.OrderIsoNat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The "monotone chain condition" below is sometimes a convenient form of well foundedness. -/
theorem well_founded.monotone_chain_condition
(α : Type*)
[partial_order α] : «expr ↔ »(well_founded ((«expr > ») : α → α → exprProp()), ∀
 a : «expr →ₘ »(exprℕ(), α), «expr∃ , »((n), ∀ m, «expr ≤ »(n, m) → «expr = »(a n, a m))) :=
begin
  split; intros [ident h],
  { rw [expr well_founded.well_founded_iff_has_max'] ["at", ident h],
    intros [ident a],
    have [ident hne] [":", expr (set.range a).nonempty] [],
    { use [expr a 0],
      simp [] [] [] [] [] [] },
    obtain ["⟨", ident x, ",", "⟨", ident n, ",", ident hn, "⟩", ",", ident range_bounded, "⟩", ":=", expr h _ hne],
    use [expr n],
    intros [ident m, ident hm],
    rw ["<-", expr hn] ["at", ident range_bounded],
    symmetry,
    apply [expr range_bounded (a m) (set.mem_range_self _) (a.monotone hm)] },
  { rw [expr rel_embedding.well_founded_iff_no_descending_seq] [],
    refine [expr ⟨λ a, _⟩],
    obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr h (a.swap : «expr →r »(((«expr < ») : exprℕ() → exprℕ() → exprProp()), ((«expr < ») : α → α → exprProp()))).to_preorder_hom],
    exact [expr n.succ_ne_self.symm (rel_embedding.to_preorder_hom_injective _ (hn _ n.le_succ))] }
end

/-- Given an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partially-ordered
type, `monotonic_sequence_limit_index a` is the least natural number `n` for which `aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonic_sequence_limit_index a`
is defined, but is a junk value. -/
noncomputable def monotonicSequenceLimitIndex {α : Type _} [PartialOrderₓ α] (a : ℕ →ₘ α) : ℕ :=
  Inf { n | ∀ m, n ≤ m → a n = a m }

/-- The constant value of an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a
partially-ordered type. -/
noncomputable def monotonicSequenceLimit {α : Type _} [PartialOrderₓ α] (a : ℕ →ₘ α) :=
  a (monotonicSequenceLimitIndex a)

-- error in Order.OrderIsoNat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem well_founded.supr_eq_monotonic_sequence_limit
{α : Type*}
[complete_lattice α]
(h : well_founded ((«expr > ») : α → α → exprProp()))
(a : «expr →ₘ »(exprℕ(), α)) : «expr = »(«expr⨆ , »((m), a m), monotonic_sequence_limit a) :=
begin
  suffices [] [":", expr «expr ≤ »(«expr⨆ , »((m : exprℕ()), a m), monotonic_sequence_limit a)],
  { exact [expr le_antisymm this (le_supr a _)] },
  apply [expr supr_le],
  intros [ident m],
  by_cases [expr hm, ":", expr «expr ≤ »(m, monotonic_sequence_limit_index a)],
  { exact [expr a.monotone hm] },
  { replace [ident hm] [] [":=", expr le_of_not_le hm],
    let [ident S] [] [":=", expr {n | ∀ m, «expr ≤ »(n, m) → «expr = »(a n, a m)}],
    have [ident hInf] [":", expr «expr ∈ »(Inf S, S)] [],
    { refine [expr nat.Inf_mem _],
      rw [expr well_founded.monotone_chain_condition] ["at", ident h],
      exact [expr h a] },
    change [expr «expr ≤ »(Inf S, m)] [] ["at", ident hm],
    change [expr «expr ≤ »(a m, a (Inf S))] [] [],
    rw [expr hInf m hm] [] }
end

