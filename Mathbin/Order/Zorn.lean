/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Set.Pairwise

/-!
# Chains and Zorn's lemmas

This file defines chains for an arbitrary relation and proves several formulations of Zorn's Lemma,
along with Hausdorff's Maximality Principle.

## Main declarations

* `chain c`: A chain `c` is a set of comparable elements.
* `max_chain_spec`: Hausdorff's Maximality Principle.
* `exists_maximal_of_chains_bounded`: Zorn's Lemma. Many variants are offered.

## Variants

The primary statement of Zorn's lemma is `exists_maximal_of_chains_bounded`. Then it is specialized
to particular relations:
* `(≤)` with `zorn_partial_order`
* `(⊆)` with `zorn_subset`
* `(⊇)` with `zorn_superset`

Lemma names carry modifiers:
* `₀`: Quantifies over a set, as opposed to over a type.
* `_nonempty`: Doesn't ask to prove that the empty chain is bounded and lets you give an element
  that will be smaller than the maximal element found (the maximal element is no smaller than any
  other element, but it can also be incomparable to some).

## How-to

This file comes across as confusing to those who haven't yet used it, so here is a detailed
walkthrough:
1. Know what relation on which type/set you're looking for. See Variants above. You can discharge
  some conditions to Zorn's lemma directly using a `_nonempty` variant.
2. Write down the definition of your type/set, put a `suffices : ∃ m, ∀ a, m ≺ a → a ≺ m, { ... },`
  (or whatever you actually need) followed by a `apply some_version_of_zorn`.
3. Fill in the details. This is where you start talking about chains.

A typical proof using Zorn could look like this
```lean
lemma zorny_lemma : zorny_statement :=
begin
  let s : set α := {x | whatever x},
  suffices : ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x, -- or with another operator
  { exact proof_post_zorn },
  apply zorn.zorn_subset, -- or another variant
  rintro c hcs hc,
  obtain rfl | hcnemp := c.eq_empty_or_nonempty, -- you might need to disjunct on c empty or not
  { exact ⟨edge_case_construction,
      proof_that_edge_case_construction_respects_whatever,
      proof_that_edge_case_construction_contains_all_stuff_in_c⟩ },
  exact ⟨construction,
    proof_that_construction_respects_whatever,
    proof_that_construction_contains_all_stuff_in_c⟩,
end
```

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/


noncomputable section

universe u

open Set Classical

open_locale Classical

namespace Zorn

section Chain

parameter {α : Type u}(r : α → α → Prop)

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => r

/-- A chain is a subset `c` satisfying `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ c`. -/
def Chain (c : Set α) :=
  c.Pairwise fun x y => x ≺ y ∨ y ≺ x

parameter {r}

theorem Chain.total_of_refl [IsRefl α r] {c} (H : chain c) {x y} (hx : x ∈ c) (hy : y ∈ c) : x ≺ y ∨ y ≺ x :=
  if e : x = y then Or.inl (e ▸ refl _) else H hx hy e

theorem Chain.mono {c c'} : c' ⊆ c → chain c → chain c' :=
  Set.Pairwise.mono

theorem chain_of_trichotomous [IsTrichotomous α r] (s : Set α) : chain s := by
  intro a _ b _ hab
  obtain h | h | h := @trichotomous _ r _ a b
  · exact Or.inl h
    
  · exact (hab h).elim
    
  · exact Or.inr h
    

theorem chain_univ_iff : chain (Univ : Set α) ↔ IsTrichotomous α r := by
  refine' ⟨fun h => ⟨fun a b => _⟩, fun h => @chain_of_trichotomous _ _ h univ⟩
  rw [Or.left_comm, or_iff_not_imp_left]
  exact h trivialₓ trivialₓ

theorem Chain.directed_on [IsRefl α r] {c} (H : chain c) : DirectedOn (· ≺ ·) c := fun x hx y hy =>
  match H.total_of_refl hx hy with
  | Or.inl h => ⟨y, hy, h, refl _⟩
  | Or.inr h => ⟨x, hx, refl _, h⟩

theorem chain_insert {c : Set α} {a : α} (hc : chain c) (ha : ∀, ∀ b ∈ c, ∀, b ≠ a → a ≺ b ∨ b ≺ a) :
    chain (insert a c) :=
  forall_insert_of_forall (fun x hx => forall_insert_of_forall (hc hx) fun hneq => (ha x hx hneq).symm)
    (forall_insert_of_forall (fun x hx hneq => (ha x hx) fun h' => hneq h'.symm) fun h => (h rfl).rec _)

/-- `super_chain c₁ c₂` means that `c₂` is a chain that strictly includes `c₁`. -/
def SuperChain (c₁ c₂ : Set α) : Prop :=
  chain c₂ ∧ c₁ ⊂ c₂

/-- A chain `c` is a maximal chain if there does not exists a chain strictly including `c`. -/
def IsMaxChain (c : Set α) :=
  chain c ∧ ¬∃ c', super_chain c c'

/-- Given a set `c`, if there exists a chain `c'` strictly including `c`, then `succ_chain c`
is one of these chains. Otherwise it is `c`. -/
def SuccChain (c : Set α) : Set α :=
  if h : ∃ c', chain c ∧ super_chain c c' then some h else c

theorem succ_spec {c : Set α} (h : ∃ c', chain c ∧ super_chain c c') : super_chain c (succ_chain c) := by
  let ⟨c', hc'⟩ := h
  have : chain c ∧ super_chain c (some h) := @some_spec _ (fun c' => chain c ∧ super_chain c c') _
  simp [succ_chain, dif_pos, h, this.right]

theorem chain_succ {c : Set α} (hc : chain c) : chain (succ_chain c) :=
  if h : ∃ c', chain c ∧ super_chain c c' then (succ_spec h).left
  else by
    simp [succ_chain, dif_neg, h] <;> exact hc

theorem super_of_not_max {c : Set α} (hc₁ : chain c) (hc₂ : ¬is_max_chain c) : super_chain c (succ_chain c) := by
  simp [is_max_chain, not_and_distrib, not_forall_not] at hc₂
  cases' hc₂.neg_resolve_left hc₁ with c' hc'
  exact succ_spec ⟨c', hc₁, hc'⟩

theorem succ_increasing {c : Set α} : c ⊆ succ_chain c :=
  if h : ∃ c', chain c ∧ super_chain c c' then
    have : super_chain c (succ_chain c) := succ_spec h
    this.right.left
  else by
    simp [succ_chain, dif_neg, h, subset.refl]

/-- Set of sets reachable from `∅` using `succ_chain` and `⋃₀`. -/
inductive ChainClosure : Set (Set α)
  | succ : ∀ {s}, chain_closure s → chain_closure (succ_chain s)
  | union : ∀ {s}, (∀, ∀ a ∈ s, ∀, chain_closure a) → chain_closure (⋃₀s)

theorem chain_closure_empty : ∅ ∈ chain_closure := by
  have : chain_closure (⋃₀∅) := chain_closure.union fun a h => h.rec _
  simp at this <;> assumption

theorem chain_closure_closure : ⋃₀chain_closure ∈ chain_closure :=
  chain_closure.union fun s hs => hs

variable {c c₁ c₂ c₃ : Set α}

private theorem chain_closure_succ_total_aux (hc₁ : c₁ ∈ chain_closure) (hc₂ : c₂ ∈ chain_closure)
    (h : ∀ {c₃}, c₃ ∈ chain_closure → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain c₃ ⊆ c₂) : c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁ := by
  induction hc₁
  case succ c₃ hc₃ ih =>
    cases' ih with ih ih
    · have h := h hc₃ ih
      cases' h with h h
      · exact Or.inr (h ▸ subset.refl _)
        
      · exact Or.inl h
        
      
    · exact Or.inr (subset.trans ih succ_increasing)
      
  case union s hs ih =>
    refine' or_iff_not_imp_right.2 fun hn => sUnion_subset fun a ha => _
    apply (ih a ha).resolve_right
    apply mt (fun h => _) hn
    exact subset.trans h (subset_sUnion_of_mem ha)

private theorem chain_closure_succ_total (hc₁ : c₁ ∈ chain_closure) (hc₂ : c₂ ∈ chain_closure) (h : c₁ ⊆ c₂) :
    c₂ = c₁ ∨ succ_chain c₁ ⊆ c₂ := by
  induction hc₂ generalizing c₁ hc₁ h
  case succ c₂ hc₂ ih =>
    have h₁ : c₁ ⊆ c₂ ∨ @succ_chain α r c₂ ⊆ c₁ := (chain_closure_succ_total_aux hc₁ hc₂) fun c₁ => ih
    cases' h₁ with h₁ h₁
    · have h₂ := ih hc₁ h₁
      cases' h₂ with h₂ h₂
      · exact Or.inr <| h₂ ▸ subset.refl _
        
      · exact Or.inr <| subset.trans h₂ succ_increasing
        
      
    · exact Or.inl <| subset.antisymm h₁ h
      
  case union s hs ih =>
    apply Or.imp_left fun h' => subset.antisymm h' h
    apply Classical.by_contradiction
    simp [not_or_distrib, sUnion_subset_iff, not_forall]
    intro c₃ hc₃ h₁ h₂
    have h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) fun c₄ => ih _ hc₃
    cases' h with h h
    · have h' := ih c₃ hc₃ hc₁ h
      cases' h' with h' h'
      · exact h₁ <| h' ▸ subset.refl _
        
      · exact h₂ <| subset.trans h' <| subset_sUnion_of_mem hc₃
        
      
    · exact h₁ <| subset.trans succ_increasing h
      

theorem chain_closure_total (hc₁ : c₁ ∈ chain_closure) (hc₂ : c₂ ∈ chain_closure) : c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
  Or.imp_rightₓ succ_increasing.trans <|
    (chain_closure_succ_total_aux hc₁ hc₂) fun c₃ hc₃ => chain_closure_succ_total hc₃ hc₂

theorem chain_closure_succ_fixpoint (hc₁ : c₁ ∈ chain_closure) (hc₂ : c₂ ∈ chain_closure) (h_eq : succ_chain c₂ = c₂) :
    c₁ ⊆ c₂ := by
  induction hc₁
  case succ c₁ hc₁ h =>
    exact Or.elim (chain_closure_succ_total hc₁ hc₂ h) (fun h => h ▸ h_eq.symm ▸ subset.refl c₂) id
  case union s hs ih =>
    exact sUnion_subset fun c₁ hc₁ => ih c₁ hc₁

theorem chain_closure_succ_fixpoint_iff (hc : c ∈ chain_closure) : succ_chain c = c ↔ c = ⋃₀chain_closure :=
  ⟨fun h => (subset_sUnion_of_mem hc).antisymm (chain_closure_succ_fixpoint chain_closure_closure hc h), fun h =>
    Subset.antisymm
      (calc
        succ_chain c ⊆ ⋃₀{ c : Set α | c ∈ chain_closure } := subset_sUnion_of_mem <| chain_closure.succ hc
        _ = c := h.symm
        )
      succ_increasing⟩

theorem chain_chain_closure (hc : c ∈ chain_closure) : chain c := by
  induction hc
  case succ c hc h =>
    exact chain_succ h
  case union s hs h =>
    have h : ∀, ∀ c ∈ s, ∀, Zorn.Chain c := h
    exact fun hneq =>
      have : t₁ ⊆ t₂ ∨ t₂ ⊆ t₁ := chain_closure_total (hs _ ht₁) (hs _ ht₂)
      Or.elim this (fun ht => h t₂ ht₂ (ht hc₁) hc₂ hneq) fun ht => h t₁ ht₁ hc₁ (ht hc₂) hneq

theorem chain_empty : chain ∅ :=
  chain_chain_closure chain_closure_empty

theorem _root_.set.subsingleton.chain (hc : Set.Subsingleton c) : chain c := fun _ hx _ hy hne => (hne (hc hx hy)).elim

/-- An explicit maximal chain. `max_chain` is taken to be the union of all sets in `chain_closure`.
-/
def MaxChain :=
  ⋃₀chain_closure

/-- Hausdorff's maximality principle

There exists a maximal totally ordered subset of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
theorem max_chain_spec : is_max_chain max_chain :=
  Classical.by_contradiction fun h => by
    obtain ⟨h₁, H⟩ := super_of_not_max (chain_chain_closure chain_closure_closure) h
    obtain ⟨h₂, h₃⟩ := ssubset_iff_subset_ne.1 H
    exact h₃ ((chain_closure_succ_fixpoint_iff chain_closure_closure).mpr rfl).symm

/-- Zorn's lemma

If every chain has an upper bound, then there exists a maximal element. -/
theorem exists_maximal_of_chains_bounded (h : ∀ c, chain c → ∃ ub, ∀, ∀ a ∈ c, ∀, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  have : ∃ ub, ∀, ∀ a ∈ max_chain, ∀, a ≺ ub := h _ <| max_chain_spec.left
  let ⟨ub, (hub : ∀, ∀ a ∈ max_chain, ∀, a ≺ ub)⟩ := this
  ⟨ub, fun a ha =>
    have : chain (insert a max_chain) := (chain_insert max_chain_spec.left) fun b hb _ => Or.inr <| trans (hub b hb) ha
    have : a ∈ max_chain :=
      Classical.by_contradiction fun h : a ∉ max_chain =>
        max_chain_spec.right <| ⟨insert a max_chain, this, ssubset_insert h⟩
    hub a this⟩

/-- A variant of Zorn's lemma. If every nonempty chain of a nonempty type has an upper bound, then
there is a maximal element.
-/
theorem exists_maximal_of_nonempty_chains_bounded [Nonempty α]
    (h : ∀ c, chain c → c.Nonempty → ∃ ub, ∀, ∀ a ∈ c, ∀, a ≺ ub) (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) :
    ∃ m, ∀ a, m ≺ a → a ≺ m :=
  exists_maximal_of_chains_bounded
    (fun c hc =>
      (eq_empty_or_nonempty c).elim (fun h => ⟨Classical.arbitrary α, fun x hx => (h ▸ hx : x ∈ (∅ : Set α)).elim⟩)
        (h c hc))
    fun a b c => trans

end Chain

/-- This can be used to turn `zorn.chain (≥)` into `zorn.chain (≤)` and vice-versa. -/
--This lemma isn't under section `chain` because `parameters` messes up with it. Feel free to fix it
theorem Chain.symm {α : Type u} {s : Set α} {q : α → α → Prop} (h : Chain q s) : Chain (flip q) s :=
  h.mono' fun _ _ => Or.symm

theorem zorn_partial_order {α : Type u} [PartialOrderₓ α]
    (h : ∀ c : Set α, Chain (· ≤ ·) c → ∃ ub, ∀, ∀ a ∈ c, ∀, a ≤ ub) : ∃ m : α, ∀ a, m ≤ a → a = m :=
  let ⟨m, hm⟩ := @exists_maximal_of_chains_bounded α (· ≤ ·) h fun a b c => le_transₓ
  ⟨m, fun a ha => le_antisymmₓ (hm a ha) ha⟩

theorem zorn_nonempty_partial_order {α : Type u} [PartialOrderₓ α] [Nonempty α]
    (h : ∀ c : Set α, Chain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀, ∀ a ∈ c, ∀, a ≤ ub) : ∃ m : α, ∀ a, m ≤ a → a = m :=
  let ⟨m, hm⟩ := @exists_maximal_of_nonempty_chains_bounded α (· ≤ ·) _ h fun a b c => le_transₓ
  ⟨m, fun a ha => le_antisymmₓ (hm a ha) ha⟩

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (c «expr ⊆ » s)
theorem zorn_partial_order₀ {α : Type u} [PartialOrderₓ α] (s : Set α)
    (ih : ∀ c _ : c ⊆ s, Chain (· ≤ ·) c → ∃ ub ∈ s, ∀, ∀ z ∈ c, ∀, z ≤ ub) : ∃ m ∈ s, ∀, ∀ z ∈ s, ∀, m ≤ z → z = m :=
  let ⟨⟨m, hms⟩, h⟩ :=
    @zorn_partial_order { m // m ∈ s } _ fun c hc =>
      let ⟨ub, hubs, hub⟩ :=
        ih (Subtype.val '' c) (fun _ ⟨⟨x, hx⟩, _, h⟩ => h ▸ hx)
          (by
            rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq <;> refine' hc hpc hqc fun t => hpq (Subtype.ext_iff.1 t))
      ⟨⟨ub, hubs⟩, fun hc => hub _ ⟨_, hc, rfl⟩⟩
  ⟨m, hms, fun z hzs hmz => congr_argₓ Subtype.val (h ⟨z, hzs⟩ hmz)⟩

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (c «expr ⊆ » s)
theorem zorn_nonempty_partial_order₀ {α : Type u} [PartialOrderₓ α] (s : Set α)
    (ih : ∀ c _ : c ⊆ s, Chain (· ≤ ·) c → ∀, ∀ y ∈ c, ∀, ∃ ub ∈ s, ∀, ∀ z ∈ c, ∀, z ≤ ub) (x : α) (hxs : x ∈ s) :
    ∃ m ∈ s, x ≤ m ∧ ∀, ∀ z ∈ s, ∀, m ≤ z → z = m :=
  let ⟨⟨m, hms, hxm⟩, h⟩ :=
    @zorn_partial_order { m // m ∈ s ∧ x ≤ m } _ fun c hc =>
      c.eq_empty_or_nonempty.elim (fun hce => hce.symm ▸ ⟨⟨x, hxs, le_rfl⟩, fun _ => False.elim⟩) fun ⟨m, hmc⟩ =>
        let ⟨ub, hubs, hub⟩ :=
          ih (Subtype.val '' c) (image_subset_iff.2 fun z hzc => z.2.1)
            (by
              rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq <;>
                exact
                  hc hpc hqc
                    (mt
                      (by
                        rintro rfl <;> rfl)
                      hpq))
            m.1 (mem_image_of_mem _ hmc)
        ⟨⟨ub, hubs, le_transₓ m.2.2 <| hub m.1 <| mem_image_of_mem _ hmc⟩, fun a hac => hub a.1 ⟨a, hac, rfl⟩⟩
  ⟨m, hms, hxm, fun z hzs hmz => congr_argₓ Subtype.val <| h ⟨z, hzs, le_transₓ hxm hmz⟩ hmz⟩

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (c «expr ⊆ » S)
theorem zorn_subset {α : Type u} (S : Set (Set α))
    (h : ∀ c _ : c ⊆ S, Chain (· ⊆ ·) c → ∃ ub ∈ S, ∀, ∀ s ∈ c, ∀, s ⊆ ub) : ∃ m ∈ S, ∀, ∀ a ∈ S, ∀, m ⊆ a → a = m :=
  zorn_partial_order₀ S h

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (c «expr ⊆ » S)
theorem zorn_subset_nonempty {α : Type u} (S : Set (Set α))
    (H : ∀ c _ : c ⊆ S, Chain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀, ∀ s ∈ c, ∀, s ⊆ ub) x (hx : x ∈ S) :
    ∃ m ∈ S, x ⊆ m ∧ ∀, ∀ a ∈ S, ∀, m ⊆ a → a = m :=
  zorn_nonempty_partial_order₀ _ (fun c cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (c «expr ⊆ » S)
theorem zorn_superset {α : Type u} (S : Set (Set α))
    (h : ∀ c _ : c ⊆ S, Chain (· ⊆ ·) c → ∃ lb ∈ S, ∀, ∀ s ∈ c, ∀, lb ⊆ s) : ∃ m ∈ S, ∀, ∀ a ∈ S, ∀, a ⊆ m → a = m :=
  (@zorn_partial_order₀ (OrderDual (Set α)) _ S) fun c cS hc => h c cS hc.symm

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (c «expr ⊆ » S)
theorem zorn_superset_nonempty {α : Type u} (S : Set (Set α))
    (H : ∀ c _ : c ⊆ S, Chain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀, ∀ s ∈ c, ∀, lb ⊆ s) x (hx : x ∈ S) :
    ∃ m ∈ S, m ⊆ x ∧ ∀, ∀ a ∈ S, ∀, a ⊆ m → a = m :=
  @zorn_nonempty_partial_order₀ (OrderDual (Set α)) _ S (fun c cS hc y yc => H _ cS hc.symm ⟨y, yc⟩) _ hx

/-- Every chain is contained in a maximal chain. This generalizes Hausdorff's maximality principle.
-/
theorem Chain.max_chain_of_chain {α r} {c : Set α} (hc : Zorn.Chain r c) : ∃ M, @Zorn.IsMaxChain _ r M ∧ c ⊆ M := by
  obtain ⟨M, ⟨_, hM₀⟩, hM₁, hM₂⟩ := Zorn.zorn_subset_nonempty { s | c ⊆ s ∧ Zorn.Chain r s } _ c ⟨subset.rfl, hc⟩
  · refine' ⟨M, ⟨hM₀, _⟩, hM₁⟩
    rintro ⟨d, hd, hMd, hdM⟩
    exact hdM (hM₂ _ ⟨hM₁.trans hMd, hd⟩ hMd).le
    
  rintro cs hcs₀ hcs₁ ⟨s, hs⟩
  refine' ⟨⋃₀cs, ⟨fun _ ha => Set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, _⟩, fun _ => Set.subset_sUnion_of_mem⟩
  rintro y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz
  obtain rfl | hsseq := eq_or_ne sy sz
  · exact (hcs₀ hsy).right hysy hzsz hyz
    
  cases' hcs₁ hsy hsz hsseq with h h
  · exact (hcs₀ hsz).right (h hysy) hzsz hyz
    
  · exact (hcs₀ hsy).right hysy (h hzsz) hyz
    

theorem Chain.total {α : Type u} [Preorderₓ α] {c : Set α} (H : Chain (· ≤ ·) c) :
    ∀ {x y}, x ∈ c → y ∈ c → x ≤ y ∨ y ≤ x := fun x y => H.total_of_refl

theorem Chain.image {α β : Type _} (r : α → α → Prop) (s : β → β → Prop) (f : α → β) (h : ∀ x y, r x y → s (f x) (f y))
    {c : Set α} (hrc : Chain r c) : Chain s (f '' c) := fun y ⟨b, hb₁, hb₂⟩ =>
  ha₂ ▸ hb₂ ▸ fun hxy => (hrc ha₁ hb₁ <| ne_of_apply_ne f hxy).elim (Or.inl ∘ h _ _) (Or.inr ∘ h _ _)

end Zorn

theorem directed_of_chain {α β r} [IsRefl β r] {f : α → β} {c : Set α} (h : Zorn.Chain (f ⁻¹'o r) c) :
    Directed r fun x : { a : α // a ∈ c } => f x := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
  Classical.by_cases
    (fun hab : a = b => by
      simp only [hab, exists_prop, and_selfₓ, Subtype.exists] <;> exact ⟨b, hb, refl _⟩)
    fun hab =>
    (h ha hb hab).elim (fun h : r (f a) (f b) => ⟨⟨b, hb⟩, h, refl _⟩) fun h : r (f b) (f a) => ⟨⟨a, ha⟩, refl _, h⟩

