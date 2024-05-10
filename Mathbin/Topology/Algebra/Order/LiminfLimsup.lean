/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov, Yaël Dillies
-/
import Algebra.BigOperators.Intervals
import Algebra.Order.BigOperators.Group.Finset
import Algebra.Function.Indicator
import Order.LiminfLimsup
import Order.Filter.Archimedean
import Order.Filter.CountableInter
import Topology.Order.Basic

#align_import topology.algebra.order.liminf_limsup from "leanprover-community/mathlib"@"ce64cd319bb6b3e82f31c2d38e79080d377be451"

/-!
# Lemmas about liminf and limsup in an order topology.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main declarations

* `bounded_le_nhds_class`: Typeclass stating that neighborhoods are eventually bounded above.
* `bounded_ge_nhds_class`: Typeclass stating that neighborhoods are eventually bounded below.

## Implementation notes

The same lemmas are true in `ℝ`, `ℝ × ℝ`, `ι → ℝ`, `euclidean_space ι ℝ`. To avoid code
duplication, we provide an ad hoc axiomatisation of the properties we need.
-/


open Filter TopologicalSpace

open scoped Topology Classical

universe u v

variable {ι α β R S : Type _} {π : ι → Type _}

#print BoundedLENhdsClass /-
/-- Ad hoc typeclass stating that neighborhoods are eventually bounded above. -/
class BoundedLENhdsClass (α : Type _) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·)
#align bounded_le_nhds_class BoundedLENhdsClass
-/

#print BoundedGENhdsClass /-
/-- Ad hoc typeclass stating that neighborhoods are eventually bounded below. -/
class BoundedGENhdsClass (α : Type _) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·)
#align bounded_ge_nhds_class BoundedGENhdsClass
-/

section Preorder

variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]

section BoundedLENhdsClass

variable [BoundedLENhdsClass α] [BoundedLENhdsClass β] {f : Filter ι} {u : ι → α} {a : α}

#print isBounded_le_nhds /-
theorem isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·) :=
  BoundedLENhdsClass.isBounded_le_nhds _
#align is_bounded_le_nhds isBounded_le_nhds
-/

#print Filter.Tendsto.isBoundedUnder_le /-
theorem Filter.Tendsto.isBoundedUnder_le (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≤ ·) u :=
  (isBounded_le_nhds a).mono h
#align filter.tendsto.is_bounded_under_le Filter.Tendsto.isBoundedUnder_le
-/

#print Filter.Tendsto.bddAbove_range_of_cofinite /-
theorem Filter.Tendsto.bddAbove_range_of_cofinite [IsDirected α (· ≤ ·)]
    (h : Tendsto u cofinite (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range_of_cofinite
#align filter.tendsto.bdd_above_range_of_cofinite Filter.Tendsto.bddAbove_range_of_cofinite
-/

#print Filter.Tendsto.bddAbove_range /-
theorem Filter.Tendsto.bddAbove_range [IsDirected α (· ≤ ·)] {u : ℕ → α}
    (h : Tendsto u atTop (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range
#align filter.tendsto.bdd_above_range Filter.Tendsto.bddAbove_range
-/

#print isCobounded_ge_nhds /-
theorem isCobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· ≥ ·) :=
  (isBounded_le_nhds a).isCobounded_flip
#align is_cobounded_ge_nhds isCobounded_ge_nhds
-/

#print Filter.Tendsto.isCoboundedUnder_ge /-
theorem Filter.Tendsto.isCoboundedUnder_ge [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· ≥ ·) u :=
  h.isBoundedUnder_le.isCobounded_flip
#align filter.tendsto.is_cobounded_under_ge Filter.Tendsto.isCoboundedUnder_ge
-/

instance : BoundedGENhdsClass αᵒᵈ :=
  ⟨@isBounded_le_nhds α _ _ _⟩

instance : BoundedLENhdsClass (α × β) :=
  by
  refine' ⟨fun x => _⟩
  obtain ⟨a, ha⟩ := isBounded_le_nhds x.1
  obtain ⟨b, hb⟩ := isBounded_le_nhds x.2
  rw [← @Prod.mk.eta _ _ x, nhds_prod_eq]
  exact ⟨(a, b), ha.prod_mk hb⟩

instance [Finite ι] [∀ i, Preorder (π i)] [∀ i, TopologicalSpace (π i)]
    [∀ i, BoundedLENhdsClass (π i)] : BoundedLENhdsClass (∀ i, π i) :=
  by
  refine' ⟨fun x => _⟩
  rw [nhds_pi]
  choose f hf using fun i => isBounded_le_nhds (x i)
  exact ⟨f, eventually_pi hf⟩

end BoundedLENhdsClass

section BoundedGENhdsClass

variable [BoundedGENhdsClass α] [BoundedGENhdsClass β] {f : Filter ι} {u : ι → α} {a : α}

#print isBounded_ge_nhds /-
theorem isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·) :=
  BoundedGENhdsClass.isBounded_ge_nhds _
#align is_bounded_ge_nhds isBounded_ge_nhds
-/

#print Filter.Tendsto.isBoundedUnder_ge /-
theorem Filter.Tendsto.isBoundedUnder_ge (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≥ ·) u :=
  (isBounded_ge_nhds a).mono h
#align filter.tendsto.is_bounded_under_ge Filter.Tendsto.isBoundedUnder_ge
-/

#print Filter.Tendsto.bddBelow_range_of_cofinite /-
theorem Filter.Tendsto.bddBelow_range_of_cofinite [IsDirected α (· ≥ ·)]
    (h : Tendsto u cofinite (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range_of_cofinite
#align filter.tendsto.bdd_below_range_of_cofinite Filter.Tendsto.bddBelow_range_of_cofinite
-/

#print Filter.Tendsto.bddBelow_range /-
theorem Filter.Tendsto.bddBelow_range [IsDirected α (· ≥ ·)] {u : ℕ → α}
    (h : Tendsto u atTop (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range
#align filter.tendsto.bdd_below_range Filter.Tendsto.bddBelow_range
-/

#print isCobounded_le_nhds /-
theorem isCobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· ≤ ·) :=
  (isBounded_ge_nhds a).isCobounded_flip
#align is_cobounded_le_nhds isCobounded_le_nhds
-/

#print Filter.Tendsto.isCoboundedUnder_le /-
theorem Filter.Tendsto.isCoboundedUnder_le [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· ≤ ·) u :=
  h.isBoundedUnder_ge.isCobounded_flip
#align filter.tendsto.is_cobounded_under_le Filter.Tendsto.isCoboundedUnder_le
-/

instance : BoundedLENhdsClass αᵒᵈ :=
  ⟨@isBounded_ge_nhds α _ _ _⟩

instance : BoundedGENhdsClass (α × β) :=
  by
  refine' ⟨fun x => _⟩
  obtain ⟨a, ha⟩ := isBounded_ge_nhds x.1
  obtain ⟨b, hb⟩ := isBounded_ge_nhds x.2
  rw [← @Prod.mk.eta _ _ x, nhds_prod_eq]
  exact ⟨(a, b), ha.prod_mk hb⟩

instance [Finite ι] [∀ i, Preorder (π i)] [∀ i, TopologicalSpace (π i)]
    [∀ i, BoundedGENhdsClass (π i)] : BoundedGENhdsClass (∀ i, π i) :=
  by
  refine' ⟨fun x => _⟩
  rw [nhds_pi]
  choose f hf using fun i => isBounded_ge_nhds (x i)
  exact ⟨f, eventually_pi hf⟩

end BoundedGENhdsClass

#print OrderTop.to_BoundedLENhdsClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderTop.to_BoundedLENhdsClass [OrderTop α] : BoundedLENhdsClass α :=
  ⟨fun a => isBounded_le_of_top⟩
#align order_top.to_bounded_le_nhds_class OrderTop.to_BoundedLENhdsClass
-/

#print OrderBot.to_BoundedGENhdsClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderBot.to_BoundedGENhdsClass [OrderBot α] : BoundedGENhdsClass α :=
  ⟨fun a => isBounded_ge_of_bot⟩
#align order_bot.to_bounded_ge_nhds_class OrderBot.to_BoundedGENhdsClass
-/

#print OrderTopology.to_BoundedLENhdsClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderTopology.to_BoundedLENhdsClass [IsDirected α (· ≤ ·)]
    [OrderTopology α] : BoundedLENhdsClass α :=
  ⟨fun a =>
    ((isTop_or_exists_gt a).elim fun h => ⟨a, eventually_of_forall h⟩) <|
      Exists.imp fun b => ge_mem_nhds⟩
#align order_topology.to_bounded_le_nhds_class OrderTopology.to_BoundedLENhdsClass
-/

#print OrderTopology.to_BoundedGENhdsClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderTopology.to_BoundedGENhdsClass [IsDirected α (· ≥ ·)]
    [OrderTopology α] : BoundedGENhdsClass α :=
  ⟨fun a =>
    ((isBot_or_exists_lt a).elim fun h => ⟨a, eventually_of_forall h⟩) <|
      Exists.imp fun b => le_mem_nhds⟩
#align order_topology.to_bounded_ge_nhds_class OrderTopology.to_BoundedGENhdsClass
-/

end Preorder

section LiminfLimsup

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α]

variable [TopologicalSpace α] [OrderTopology α]

#print le_nhds_of_limsSup_eq_limsInf /-
/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_limsSup_eq_limsInf {f : Filter α} {a : α} (hl : f.IsBounded (· ≤ ·))
    (hg : f.IsBounded (· ≥ ·)) (hs : f.limsSup = a) (hi : f.limsInf = a) : f ≤ 𝓝 a :=
  tendsto_order.2 <|
    And.intro (fun b hb => gt_mem_sets_of_limsInf_gt hg <| hi.symm ▸ hb) fun b hb =>
      lt_mem_sets_of_limsSup_lt hl <| hs.symm ▸ hb
#align le_nhds_of_Limsup_eq_Liminf le_nhds_of_limsSup_eq_limsInf
-/

#print limsSup_nhds /-
theorem limsSup_nhds (a : α) : limsSup (𝓝 a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : {n : α | n ≤ a'} ∈ 𝓝 a) => show a ≤ a' from @mem_of_mem_nhds α _ a _ h)
    fun b (hba : a < b) =>
    show ∃ (c : _) (h : {n : α | n ≤ c} ∈ 𝓝 a), c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩
#align Limsup_nhds limsSup_nhds
-/

#print limsInf_nhds /-
theorem limsInf_nhds : ∀ a : α, limsInf (𝓝 a) = a :=
  @limsSup_nhds αᵒᵈ _ _ _
#align Liminf_nhds limsInf_nhds
-/

#print limsInf_eq_of_le_nhds /-
/-- If a filter is converging, its limsup coincides with its limit. -/
theorem limsInf_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.limsInf = a :=
  have hb_ge : IsBounded (· ≥ ·) f := (isBounded_ge_nhds a).mono h
  have hb_le : IsBounded (· ≤ ·) f := (isBounded_le_nhds a).mono h
  le_antisymm
    (calc
      f.limsInf ≤ f.limsSup := limsInf_le_limsSup hb_le hb_ge
      _ ≤ (𝓝 a).limsSup := (limsSup_le_limsSup_of_le h hb_ge.isCobounded_flip (isBounded_le_nhds a))
      _ = a := limsSup_nhds a)
    (calc
      a = (𝓝 a).limsInf := (limsInf_nhds a).symm
      _ ≤ f.limsInf := limsInf_le_limsInf_of_le h (isBounded_ge_nhds a) hb_le.isCobounded_flip)
#align Liminf_eq_of_le_nhds limsInf_eq_of_le_nhds
-/

#print limsSup_eq_of_le_nhds /-
/-- If a filter is converging, its liminf coincides with its limit. -/
theorem limsSup_eq_of_le_nhds : ∀ {f : Filter α} {a : α} [NeBot f], f ≤ 𝓝 a → f.limsSup = a :=
  @limsInf_eq_of_le_nhds αᵒᵈ _ _ _
#align Limsup_eq_of_le_nhds limsSup_eq_of_le_nhds
-/

#print Filter.Tendsto.limsup_eq /-
/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : limsup u f = a :=
  limsSup_eq_of_le_nhds h
#align filter.tendsto.limsup_eq Filter.Tendsto.limsup_eq
-/

#print Filter.Tendsto.liminf_eq /-
/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : liminf u f = a :=
  limsInf_eq_of_le_nhds h
#align filter.tendsto.liminf_eq Filter.Tendsto.liminf_eq
-/

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
#print tendsto_of_liminf_eq_limsup /-
/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value -/
theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminf u f = a)
    (hsup : limsup u f = a)
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    Tendsto u f (𝓝 a) :=
  le_nhds_of_limsSup_eq_limsInf h h' hsup hinf
#align tendsto_of_liminf_eq_limsup tendsto_of_liminf_eq_limsup
-/

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
#print tendsto_of_le_liminf_of_limsup_le /-
/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f)
    (hsup : limsup u f ≤ a)
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    Tendsto u f (𝓝 a) :=
  if hf : f = ⊥ then hf.symm ▸ tendsto_bot
  else
    haveI : ne_bot f := ⟨hf⟩
    tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'
#align tendsto_of_le_liminf_of_limsup_le tendsto_of_le_liminf_of_limsup_le
-/

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
#print tendsto_of_no_upcrossings /-
/-- Assume that, for any `a < b`, a sequence can not be infinitely many times below `a` and
above `b`. If it is also ultimately bounded above and below, then it has to converge. This even
works if `a` and `b` are restricted to a dense subset.
-/
theorem tendsto_of_no_upcrossings [DenselyOrdered α] {f : Filter β} {u : β → α} {s : Set α}
    (hs : Dense s) (H : ∀ a ∈ s, ∀ b ∈ s, a < b → ¬((∃ᶠ n in f, u n < a) ∧ ∃ᶠ n in f, b < u n))
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    ∃ c : α, Tendsto u f (𝓝 c) := by
  by_cases hbot : f = ⊥; · rw [hbot]; exact ⟨Inf ∅, tendsto_bot⟩
  haveI : ne_bot f := ⟨hbot⟩
  refine' ⟨limsup u f, _⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra! hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : ∃ᶠ n in f, u n < a := frequently_lt_of_liminf_lt (is_bounded.is_cobounded_ge h) la
  have B : ∃ᶠ n in f, b < u n := frequently_lt_of_lt_limsup (is_bounded.is_cobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩
#align tendsto_of_no_upcrossings tendsto_of_no_upcrossings
-/

variable [FirstCountableTopology α] {f : Filter β} [CountableInterFilter f] {u : β → α}

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
#print eventually_le_limsup /-
theorem eventually_le_limsup
    (hf : IsBoundedUnder (· ≤ ·) f u := by
      run_tac
        is_bounded_default) :
    ∀ᶠ b in f, u b ≤ f.limsup u :=
  by
  obtain ha | ha := isTop_or_exists_gt (f.limsup u)
  · exact eventually_of_forall fun _ => ha _
  by_cases H : IsGLB (Set.Ioi (f.limsup u)) (f.limsup u)
  · obtain ⟨u, -, -, hua, hu⟩ := H.exists_seq_antitone_tendsto ha
    have := fun n => eventually_lt_of_limsup_lt (hu n) hf
    exact
      (eventually_countable_forall.2 this).mono fun b hb =>
        ge_of_tendsto hua <| eventually_of_forall fun n => (hb _).le
  · obtain ⟨x, hx, xa⟩ : ∃ x, (∀ ⦃b⦄, f.limsup u < b → x ≤ b) ∧ f.limsup u < x :=
      by
      simp only [IsGLB, IsGreatest, lowerBounds, upperBounds, Set.mem_Ioi, Set.mem_setOf_eq,
        not_and, Classical.not_forall, not_le, exists_prop] at H
      exact H fun x hx => le_of_lt hx
    filter_upwards [eventually_lt_of_limsup_lt xa hf] with y hy
    contrapose! hy
    exact hx hy
#align eventually_le_limsup eventually_le_limsup
-/

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
#print eventually_liminf_le /-
theorem eventually_liminf_le
    (hf : IsBoundedUnder (· ≥ ·) f u := by
      run_tac
        is_bounded_default) :
    ∀ᶠ b in f, f.liminf u ≤ u b :=
  @eventually_le_limsup αᵒᵈ _ _ _ _ _ _ _ _ hf
#align eventually_liminf_le eventually_liminf_le
-/

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [FirstCountableTopology α] [OrderTopology α]
  {f : Filter β} [CountableInterFilter f] {u : β → α}

#print limsup_eq_bot /-
@[simp]
theorem limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥ :=
  ⟨fun h =>
    (EventuallyLE.trans eventually_le_limsup <| eventually_of_forall fun _ => h.le).mono fun x hx =>
      le_antisymm hx bot_le,
    fun h => by rw [limsup_congr h]; exact limsup_const_bot⟩
#align limsup_eq_bot limsup_eq_bot
-/

#print liminf_eq_top /-
@[simp]
theorem liminf_eq_top : f.liminf u = ⊤ ↔ u =ᶠ[f] ⊤ :=
  @limsup_eq_bot αᵒᵈ _ _ _ _ _ _ _ _
#align liminf_eq_top liminf_eq_top
-/

end CompleteLinearOrder

end LiminfLimsup

section Monotone

variable {F : Filter ι} [NeBot F] [CompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [CompleteLinearOrder S] [TopologicalSpace S] [OrderTopology S]

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
#print Antitone.map_limsSup_of_continuousAt /-
/-- An antitone function between complete linear ordered spaces sends a `filter.Limsup`
to the `filter.liminf` of the image if it is continuous at the `Limsup`. -/
theorem Antitone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsSup) : f F.limsSup = F.liminf f :=
  by
  apply le_antisymm
  · have A : {a : R | ∀ᶠ n : R in F, n ≤ a}.Nonempty := ⟨⊤, by simp⟩
    rw [Limsup, f_decr.map_Inf_of_continuous_at' f_cont A]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, Liminf, lt_sSup_iff, eventually_map, Set.mem_setOf_eq, exists_prop,
      Set.mem_image, exists_exists_and_eq_and] at hc ⊢
    rcases hc with ⟨d, hd, h'd⟩
    refine' ⟨f d, _, h'd⟩
    filter_upwards [hd] with x hx using f_decr hx
  · rcases eq_or_lt_of_le (bot_le : ⊥ ≤ F.Limsup) with (h | Limsup_ne_bot)
    · rw [← h]
      apply liminf_le_of_frequently_le
      apply frequently_of_forall
      intro x
      exact f_decr bot_le
    by_cases h' : ∃ c, c < F.Limsup ∧ Set.Ioo c F.Limsup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : ∃ᶠ n in F, F.Limsup ≤ n :=
        by
        apply
          (frequently_lt_of_lt_Limsup
              (by
                run_tac
                  is_bounded_default)
              c_lt).mono
        intro x hx
        by_contra!
        have : (Set.Ioo c F.Limsup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simpa [hc]
      apply liminf_le_of_frequently_le
      exact B.mono fun x hx => f_decr hx
    by_contra! H
    obtain ⟨l, l_lt, h'l⟩ : ∃ l < F.Limsup, Set.Ioc l F.Limsup ⊆ {x : R | f x < F.liminf f}
    exact exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H) ⟨⊥, Limsup_ne_bot⟩
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.Limsup).Nonempty :=
      by
      contrapose! h'
      refine' ⟨l, l_lt, by rwa [Set.not_nonempty_iff_eq_empty] at h'⟩
    have B : F.liminf f ≤ f m := by
      apply liminf_le_of_frequently_le
      apply
        (frequently_lt_of_lt_Limsup
            (by
              run_tac
                is_bounded_default)
            m_lt).mono
      intro x hx
      exact f_decr hx.le
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)
#align antitone.map_Limsup_of_continuous_at Antitone.map_limsSup_of_continuousAt
-/

#print Antitone.map_limsup_of_continuousAt /-
/-- A continuous antitone function between complete linear ordered spaces sends a `filter.limsup`
to the `filter.liminf` of the images. -/
theorem Antitone.map_limsup_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a)) : f (F.limsup a) = F.liminf (f ∘ a) :=
  f_decr.map_limsSup_of_continuousAt f_cont
#align antitone.map_limsup_of_continuous_at Antitone.map_limsup_of_continuousAt
-/

#print Antitone.map_limsInf_of_continuousAt /-
/-- An antitone function between complete linear ordered spaces sends a `filter.Liminf`
to the `filter.limsup` of the image if it is continuous at the `Liminf`. -/
theorem Antitone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsInf) : f F.limsInf = F.limsup f :=
  @Antitone.map_limsSup_of_continuousAt (OrderDual R) (OrderDual S) _ _ _ _ _ _ _ _ f f_decr.dual
    f_cont
#align antitone.map_Liminf_of_continuous_at Antitone.map_limsInf_of_continuousAt
-/

#print Antitone.map_liminf_of_continuousAt /-
/-- A continuous antitone function between complete linear ordered spaces sends a `filter.liminf`
to the `filter.limsup` of the images. -/
theorem Antitone.map_liminf_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a)) : f (F.liminf a) = F.limsup (f ∘ a) :=
  f_decr.map_limsInf_of_continuousAt f_cont
#align antitone.map_liminf_of_continuous_at Antitone.map_liminf_of_continuousAt
-/

#print Monotone.map_limsSup_of_continuousAt /-
/-- A monotone function between complete linear ordered spaces sends a `filter.Limsup`
to the `filter.limsup` of the image if it is continuous at the `Limsup`. -/
theorem Monotone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsSup) : f F.limsSup = F.limsup f :=
  @Antitone.map_limsSup_of_continuousAt R (OrderDual S) _ _ _ _ _ _ _ _ f f_incr f_cont
#align monotone.map_Limsup_of_continuous_at Monotone.map_limsSup_of_continuousAt
-/

#print Monotone.map_limsup_of_continuousAt /-
/-- A continuous monotone function between complete linear ordered spaces sends a `filter.limsup`
to the `filter.limsup` of the images. -/
theorem Monotone.map_limsup_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a)) : f (F.limsup a) = F.limsup (f ∘ a) :=
  f_incr.map_limsSup_of_continuousAt f_cont
#align monotone.map_limsup_of_continuous_at Monotone.map_limsup_of_continuousAt
-/

#print Monotone.map_limsInf_of_continuousAt /-
/-- A monotone function between complete linear ordered spaces sends a `filter.Liminf`
to the `filter.liminf` of the image if it is continuous at the `Liminf`. -/
theorem Monotone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsInf) : f F.limsInf = F.liminf f :=
  @Antitone.map_limsInf_of_continuousAt R (OrderDual S) _ _ _ _ _ _ _ _ f f_incr f_cont
#align monotone.map_Liminf_of_continuous_at Monotone.map_limsInf_of_continuousAt
-/

#print Monotone.map_liminf_of_continuousAt /-
/-- A continuous monotone function between complete linear ordered spaces sends a `filter.liminf`
to the `filter.liminf` of the images. -/
theorem Monotone.map_liminf_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a)) : f (F.liminf a) = F.liminf (f ∘ a) :=
  f_incr.map_limsInf_of_continuousAt f_cont
#align monotone.map_liminf_of_continuous_at Monotone.map_liminf_of_continuousAt
-/

end Monotone

section InfiAndSupr

open scoped Topology

open Filter Set

variable [CompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]

#print iInf_eq_of_forall_le_of_tendsto /-
theorem iInf_eq_of_forall_le_of_tendsto {x : R} {as : ι → R} (x_le : ∀ i, x ≤ as i) {F : Filter ι}
    [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) : (⨅ i, as i) = x :=
  by
  refine' iInf_eq_of_forall_ge_of_forall_gt_exists_lt (fun i => x_le i) _
  apply fun w x_lt_w => ‹Filter.NeBot F›.nonempty_of_mem (eventually_lt_of_tendsto_lt x_lt_w as_lim)
#align infi_eq_of_forall_le_of_tendsto iInf_eq_of_forall_le_of_tendsto
-/

#print iSup_eq_of_forall_le_of_tendsto /-
theorem iSup_eq_of_forall_le_of_tendsto {x : R} {as : ι → R} (le_x : ∀ i, as i ≤ x) {F : Filter ι}
    [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) : (⨆ i, as i) = x :=
  @iInf_eq_of_forall_le_of_tendsto ι (OrderDual R) _ _ _ x as le_x F _ as_lim
#align supr_eq_of_forall_le_of_tendsto iSup_eq_of_forall_le_of_tendsto
-/

#print iUnion_Ici_eq_Ioi_of_lt_of_tendsto /-
theorem iUnion_Ici_eq_Ioi_of_lt_of_tendsto (x : R) {as : ι → R} (x_lt : ∀ i, x < as i)
    {F : Filter ι} [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) :
    (⋃ i : ι, Ici (as i)) = Ioi x :=
  by
  have obs : x ∉ range as := by
    intro maybe_x_is
    rcases mem_range.mp maybe_x_is with ⟨i, hi⟩
    simpa only [hi, lt_self_iff_false] using x_lt i
  rw [← iInf_eq_of_forall_le_of_tendsto (fun i => (x_lt i).le) as_lim] at *
  exact iUnion_Ici_eq_Ioi_iInf obs
#align Union_Ici_eq_Ioi_of_lt_of_tendsto iUnion_Ici_eq_Ioi_of_lt_of_tendsto
-/

#print iUnion_Iic_eq_Iio_of_lt_of_tendsto /-
theorem iUnion_Iic_eq_Iio_of_lt_of_tendsto (x : R) {as : ι → R} (lt_x : ∀ i, as i < x)
    {F : Filter ι} [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) :
    (⋃ i : ι, Iic (as i)) = Iio x :=
  @iUnion_Ici_eq_Ioi_of_lt_of_tendsto ι Rᵒᵈ _ _ _ _ _ lt_x F _ as_lim
#align Union_Iic_eq_Iio_of_lt_of_tendsto iUnion_Iic_eq_Iio_of_lt_of_tendsto
-/

end InfiAndSupr

section Indicator

open scoped BigOperators

#print limsup_eq_tendsto_sum_indicator_nat_atTop /-
theorem limsup_eq_tendsto_sum_indicator_nat_atTop (s : ℕ → Set α) :
    limsup s atTop =
      {ω |
        Tendsto (fun n => ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → ℕ) ω) atTop
          atTop} :=
  by
  ext ω
  simp only [limsup_eq_infi_supr_of_nat, ge_iff_le, Set.iSup_eq_iUnion, Set.iInf_eq_iInter,
    Set.mem_iInter, Set.mem_iUnion, exists_prop]
  constructor
  · intro hω
    refine'
      tendsto_at_top_at_top_of_monotone'
        (fun n m hnm =>
          Finset.sum_mono_set_of_nonneg (fun i => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
            (Finset.range_mono hnm))
        _
    rintro ⟨i, h⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at h
    induction' i with k hk
    · obtain ⟨j, hj₁, hj₂⟩ := hω 1
      refine'
        not_lt.2 (h <| j + 1)
          (lt_of_le_of_lt (finset.sum_const_zero.symm : 0 = ∑ k in Finset.range (j + 1), 0).le _)
      refine'
        Finset.sum_lt_sum (fun m _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          ⟨j - 1, Finset.mem_range.2 (lt_of_le_of_lt (Nat.sub_le _ _) j.lt_succ_self), _⟩
      rw [Nat.sub_add_cancel hj₁, Set.indicator_of_mem hj₂]
      exact zero_lt_one
    · rw [imp_false] at hk
      push_neg at hk
      obtain ⟨i, hi⟩ := hk
      obtain ⟨j, hj₁, hj₂⟩ := hω (i + 1)
      replace hi : ∑ k in Finset.range i, (s (k + 1)).indicator 1 ω = k + 1 := le_antisymm (h i) hi
      refine' not_lt.2 (h <| j + 1) _
      rw [← Finset.sum_range_add_sum_Ico _ (i.le_succ.trans (hj₁.trans j.le_succ)), hi]
      refine' lt_add_of_pos_right _ _
      rw [(finset.sum_const_zero.symm : 0 = ∑ k in Finset.Ico i (j + 1), 0)]
      refine'
        Finset.sum_lt_sum (fun m _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          ⟨j - 1,
            Finset.mem_Ico.2
              ⟨(Nat.le_sub_iff_add_le (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁)).2 hj₁,
                lt_of_le_of_lt (Nat.sub_le _ _) j.lt_succ_self⟩,
            _⟩
      rw [Nat.sub_add_cancel (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁),
        Set.indicator_of_mem hj₂]
      exact zero_lt_one
  · rintro hω i
    rw [Set.mem_setOf_eq, tendsto_at_top_at_top] at hω
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, h⟩ := hω (i + 1)
    have : ∑ k in Finset.range j, (s (k + 1)).indicator 1 ω ≤ i :=
      by
      have hle : ∀ j ≤ i, ∑ k in Finset.range j, (s (k + 1)).indicator 1 ω ≤ i :=
        by
        refine' fun j hij =>
          (Finset.sum_le_card_nsmul _ _ _ _ : _ ≤ (Finset.range j).card • 1).trans _
        · exact fun m hm => Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
        · simpa only [Finset.card_range, smul_eq_mul, mul_one]
      by_cases hij : j < i
      · exact hle _ hij.le
      · rw [← Finset.sum_range_add_sum_Ico _ (not_lt.1 hij)]
        suffices ∑ k in Finset.Ico i j, (s (k + 1)).indicator 1 ω = 0
          by
          rw [this, add_zero]
          exact hle _ le_rfl
        rw [Finset.sum_eq_zero fun m hm => _]
        exact Set.indicator_of_not_mem (hcon _ <| (Finset.mem_Ico.1 hm).1.trans m.le_succ) _
    exact not_le.2 (lt_of_lt_of_le i.lt_succ_self <| h _ le_rfl) this
#align limsup_eq_tendsto_sum_indicator_nat_at_top limsup_eq_tendsto_sum_indicator_nat_atTop
-/

#print limsup_eq_tendsto_sum_indicator_atTop /-
theorem limsup_eq_tendsto_sum_indicator_atTop (R : Type _) [StrictOrderedSemiring R] [Archimedean R]
    (s : ℕ → Set α) :
    limsup s atTop =
      {ω |
        Tendsto (fun n => ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → R) ω) atTop
          atTop} :=
  by
  rw [limsup_eq_tendsto_sum_indicator_nat_atTop s]
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [(_ :
      (fun n => ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → R) ω) = fun n =>
        ↑(∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → ℕ) ω))]
  · exact tendsto_coe_nat_at_top_iff.symm
  · ext n
    simp only [Set.indicator, Pi.one_apply, Finset.sum_boole, Nat.cast_id]
#align limsup_eq_tendsto_sum_indicator_at_top limsup_eq_tendsto_sum_indicator_atTop
-/

end Indicator

