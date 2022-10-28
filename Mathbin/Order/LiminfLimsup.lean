/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
import Mathbin.Order.Filter.Cofinite
import Mathbin.Order.Hom.CompleteLattice

/-!
# liminfs and limsups of functions and filters

Defines the Liminf/Limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `Limsup f` (`Liminf f`) where `f` is a filter taking values in a conditionally complete
lattice. `Limsup f` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`Liminf f`). To work with the Limsup along a function `u` use `Limsup (map u f)`.

Usually, one defines the Limsup as `Inf (Sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `Inf_n (Sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `Limsup (λx, 1/x)` on ℝ. Then
there is no guarantee that the quantity above really decreases (the value of the `Sup` beforehand is
not really well defined, as one can not use ∞), so that the Inf could be anything. So one can not
use this `Inf Sup ...` definition in conditionally complete lattices, and one has to use a less
tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/


open Filter Set

open Filter

variable {α β γ ι : Type _}

namespace Filter

section Relation

/-- `f.is_bounded (≺)`: the filter `f` is eventually bounded w.r.t. the relation `≺`, i.e.
eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `≤` or `≥`. -/
def IsBounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ᶠ x in f, r x b

/-- `f.is_bounded_under (≺) u`: the image of the filter `f` under `u` is eventually bounded w.r.t.
the relation `≺`, i.e. eventually, it is bounded by some uniform bound. -/
def IsBoundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsBounded r

variable {r : α → α → Prop} {f g : Filter α}

/-- `f` is eventually bounded if and only if, there exists an admissible set on which it is
bounded. -/
theorem is_bounded_iff : f.IsBounded r ↔ ∃ s ∈ f.Sets, ∃ b, s ⊆ { x | r x b } :=
  Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨s, hs, b, hb⟩ => ⟨b, mem_of_superset hs hb⟩

/-- A bounded function `u` is in particular eventually bounded. -/
theorem is_bounded_under_of {f : Filter β} {u : β → α} : (∃ b, ∀ x, r (u x) b) → f.IsBoundedUnder r u
  | ⟨b, hb⟩ => ⟨b, show ∀ᶠ x in f, r (u x) b from eventually_of_forall hb⟩

theorem is_bounded_bot : IsBounded r ⊥ ↔ Nonempty α := by simp [is_bounded, exists_true_iff_nonempty]

theorem is_bounded_top : IsBounded r ⊤ ↔ ∃ t, ∀ x, r x t := by simp [is_bounded, eq_univ_iff_forall]

theorem is_bounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ ∃ t, ∀ x ∈ s, r x t := by simp [is_bounded, subset_def]

theorem is_bounded_sup [IsTrans α r] (hr : ∀ b₁ b₂, ∃ b, r b₁ b ∧ r b₂ b) :
    IsBounded r f → IsBounded r g → IsBounded r (f ⊔ g)
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ =>
    let ⟨b, rb₁b, rb₂b⟩ := hr b₁ b₂
    ⟨b, eventually_sup.mpr ⟨h₁.mono fun x h => trans h rb₁b, h₂.mono fun x h => trans h rb₂b⟩⟩

theorem IsBounded.mono (h : f ≤ g) : IsBounded r g → IsBounded r f
  | ⟨b, hb⟩ => ⟨b, h hb⟩

theorem IsBoundedUnder.mono {f g : Filter β} {u : β → α} (h : f ≤ g) : g.IsBoundedUnder r u → f.IsBoundedUnder r u :=
  fun hg => hg.mono (map_mono h)

theorem IsBoundedUnder.mono_le [Preorder β] {l : Filter α} {u v : α → β} (hu : IsBoundedUnder (· ≤ ·) l u)
    (hv : v ≤ᶠ[l] u) : IsBoundedUnder (· ≤ ·) l v :=
  hu.imp fun b hb => (eventually_map.1 hb).mp <| hv.mono fun x => le_trans

theorem IsBoundedUnder.mono_ge [Preorder β] {l : Filter α} {u v : α → β} (hu : IsBoundedUnder (· ≥ ·) l u)
    (hv : u ≤ᶠ[l] v) : IsBoundedUnder (· ≥ ·) l v :=
  @IsBoundedUnder.mono_le α βᵒᵈ _ _ _ _ hu hv

theorem is_bounded_under_const [IsRefl α r] {l : Filter β} {a : α} : IsBoundedUnder r l fun _ => a :=
  ⟨a, eventually_map.2 <| eventually_of_forall fun _ => refl _⟩

theorem IsBounded.is_bounded_under {q : β → β → Prop} {u : α → β} (hf : ∀ a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) :
    f.IsBounded r → f.IsBoundedUnder q u
  | ⟨b, h⟩ => ⟨u b, show ∀ᶠ x in f, q (u x) (u b) from h.mono fun x => hf x b⟩

theorem not_is_bounded_under_of_tendsto_at_top [Preorder β] [NoMaxOrder β] {f : α → β} {l : Filter α} [l.ne_bot]
    (hf : Tendsto f l atTop) : ¬IsBoundedUnder (· ≤ ·) l f := by
  rintro ⟨b, hb⟩
  rw [eventually_map] at hb
  obtain ⟨b', h⟩ := exists_gt b
  have hb' := (tendsto_at_top.mp hf) b'
  have : { x : α | f x ≤ b } ∩ { x : α | b' ≤ f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_lt h) (le_trans hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')).ne_empty this

theorem not_is_bounded_under_of_tendsto_at_bot [Preorder β] [NoMinOrder β] {f : α → β} {l : Filter α} [l.ne_bot]
    (hf : Tendsto f l atBot) : ¬IsBoundedUnder (· ≥ ·) l f :=
  @not_is_bounded_under_of_tendsto_at_top α βᵒᵈ _ _ _ _ _ hf

theorem IsBoundedUnder.bdd_above_range_of_cofinite [SemilatticeSup β] {f : α → β}
    (hf : IsBoundedUnder (· ≤ ·) cofinite f) : BddAbove (Range f) := by
  rcases hf with ⟨b, hb⟩
  haveI : Nonempty β := ⟨b⟩
  rw [← image_univ, ← union_compl_self { x | f x ≤ b }, image_union, bdd_above_union]
  exact ⟨⟨b, ball_image_iff.2 fun x => id⟩, (hb.image f).BddAbove⟩

theorem IsBoundedUnder.bdd_below_range_of_cofinite [SemilatticeInf β] {f : α → β}
    (hf : IsBoundedUnder (· ≥ ·) cofinite f) : BddBelow (Range f) :=
  @IsBoundedUnder.bdd_above_range_of_cofinite α βᵒᵈ _ _ hf

theorem IsBoundedUnder.bdd_above_range [SemilatticeSup β] {f : ℕ → β} (hf : IsBoundedUnder (· ≤ ·) atTop f) :
    BddAbove (Range f) := by
  rw [← Nat.cofinite_eq_at_top] at hf
  exact hf.bdd_above_range_of_cofinite

theorem IsBoundedUnder.bdd_below_range [SemilatticeInf β] {f : ℕ → β} (hf : IsBoundedUnder (· ≥ ·) atTop f) :
    BddBelow (Range f) :=
  @IsBoundedUnder.bdd_above_range βᵒᵈ _ _ hf

/-- `is_cobounded (≺) f` states that the filter `f` does not tend to infinity w.r.t. `≺`. This is
also called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.is_cobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀ a, ∀ᶠ n in f, a ≤ n`
would not work as well in this case.
-/
def IsCobounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ a, (∀ᶠ x in f, r x a) → r b a

/-- `is_cobounded_under (≺) f u` states that the image of the filter `f` under the map `u` does not
tend to infinity w.r.t. `≺`. This is also called frequently bounded. Will be usually instantiated
with `≤` or `≥`. -/
def IsCoboundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsCobounded r

/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter.-/
theorem IsCobounded.mk [IsTrans α r] (a : α) (h : ∀ s ∈ f, ∃ x ∈ s, r a x) : f.IsCobounded r :=
  ⟨a, fun y s =>
    let ⟨x, h₁, h₂⟩ := h _ s
    trans h₂ h₁⟩

/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
theorem IsBounded.is_cobounded_flip [IsTrans α r] [NeBot f] : f.IsBounded r → f.IsCobounded (flip r)
  | ⟨a, ha⟩ =>
    ⟨a, fun b hb =>
      let ⟨x, rxa, rbx⟩ := (ha.And hb).exists
      show r b a from trans rbx rxa⟩

theorem IsBounded.is_cobounded_ge [Preorder α] [NeBot f] (h : f.IsBounded (· ≤ ·)) : f.IsCobounded (· ≥ ·) :=
  h.is_cobounded_flip

theorem IsBounded.is_cobounded_le [Preorder α] [NeBot f] (h : f.IsBounded (· ≥ ·)) : f.IsCobounded (· ≤ ·) :=
  h.is_cobounded_flip

theorem is_cobounded_bot : IsCobounded r ⊥ ↔ ∃ b, ∀ x, r b x := by simp [is_cobounded]

theorem is_cobounded_top : IsCobounded r ⊤ ↔ Nonempty α := by
  simp (config := { contextual := true }) [is_cobounded, eq_univ_iff_forall, exists_true_iff_nonempty]

theorem is_cobounded_principal (s : Set α) : (𝓟 s).IsCobounded r ↔ ∃ b, ∀ a, (∀ x ∈ s, r x a) → r b a := by
  simp [is_cobounded, subset_def]

theorem IsCobounded.mono (h : f ≤ g) : f.IsCobounded r → g.IsCobounded r
  | ⟨b, hb⟩ => ⟨b, fun a ha => hb a (h ha)⟩

end Relation

theorem is_cobounded_le_of_bot [Preorder α] [OrderBot α] {f : Filter α} : f.IsCobounded (· ≤ ·) :=
  ⟨⊥, fun a h => bot_le⟩

theorem is_cobounded_ge_of_top [Preorder α] [OrderTop α] {f : Filter α} : f.IsCobounded (· ≥ ·) :=
  ⟨⊤, fun a h => le_top⟩

theorem is_bounded_le_of_top [Preorder α] [OrderTop α] {f : Filter α} : f.IsBounded (· ≤ ·) :=
  ⟨⊤, eventually_of_forall fun _ => le_top⟩

theorem is_bounded_ge_of_bot [Preorder α] [OrderBot α] {f : Filter α} : f.IsBounded (· ≥ ·) :=
  ⟨⊥, eventually_of_forall fun _ => bot_le⟩

@[simp]
theorem _root_.order_iso.is_bounded_under_le_comp [Preorder α] [Preorder β] (e : α ≃o β) {l : Filter γ} {u : γ → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≤ ·) l u :=
  e.Surjective.exists.trans <| exists_congr fun a => by simp only [eventually_map, e.le_iff_le]

@[simp]
theorem _root_.order_iso.is_bounded_under_ge_comp [Preorder α] [Preorder β] (e : α ≃o β) {l : Filter γ} {u : γ → α} :
    (IsBoundedUnder (· ≥ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≥ ·) l u :=
  e.dual.is_bounded_under_le_comp

@[simp, to_additive]
theorem is_bounded_under_le_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≥ ·) l u :=
  (OrderIso.inv α).is_bounded_under_ge_comp

@[simp, to_additive]
theorem is_bounded_under_ge_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≥ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (OrderIso.inv α).is_bounded_under_le_comp

theorem IsBoundedUnder.sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≤ ·) u → f.IsBoundedUnder (· ≤ ·) v → f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a
  | ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩, ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ =>
    ⟨bu ⊔ bv, show ∀ᶠ x in f, u x ⊔ v x ≤ bu ⊔ bv by filter_upwards [hu, hv] with _ using sup_le_sup⟩

@[simp]
theorem is_bounded_under_le_sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a) ↔ f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≤ ·) v :=
  ⟨fun h =>
    ⟨h.mono_le <| eventually_of_forall fun _ => le_sup_left, h.mono_le <| eventually_of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩

theorem IsBoundedUnder.inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≥ ·) u → f.IsBoundedUnder (· ≥ ·) v → f.IsBoundedUnder (· ≥ ·) fun a => u a ⊓ v a :=
  @IsBoundedUnder.sup αᵒᵈ β _ _ _ _

@[simp]
theorem is_bounded_under_ge_inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≥ ·) fun a => u a ⊓ v a) ↔ f.IsBoundedUnder (· ≥ ·) u ∧ f.IsBoundedUnder (· ≥ ·) v :=
  @is_bounded_under_le_sup αᵒᵈ _ _ _ _ _

theorem is_bounded_under_le_abs [LinearOrderedAddCommGroup α] {f : Filter β} {u : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => abs (u a)) ↔ f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≥ ·) u :=
  is_bounded_under_le_sup.trans <| and_congr Iff.rfl is_bounded_under_le_neg

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `is_bounded_default` in the statements,
in the form `(hf : f.is_bounded (≥) . is_bounded_default)`. -/
unsafe def is_bounded_default : tactic Unit :=
  tactic.applyc `` is_cobounded_le_of_bot <|>
    tactic.applyc `` is_cobounded_ge_of_top <|>
      tactic.applyc `` is_bounded_le_of_top <|> tactic.applyc `` is_bounded_ge_of_bot

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

/-- The `Limsup` of a filter `f` is the infimum of the `a` such that, eventually for `f`,
holds `x ≤ a`. -/
def limsup (f : Filter α) : α :=
  inf { a | ∀ᶠ n in f, n ≤ a }

/-- The `Liminf` of a filter `f` is the supremum of the `a` such that, eventually for `f`,
holds `x ≥ a`. -/
def liminf (f : Filter α) : α :=
  sup { a | ∀ᶠ n in f, a ≤ n }

/- warning: filter.limsup clashes with filter.Limsup -> Filter.limsup
warning: filter.limsup -> Filter.limsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : ConditionallyCompleteLattice.{u_1} α], (β -> α) -> (Filter.{u_2} β) -> α
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align filter.limsup Filter.limsupₓ'. -/
/-- The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that,
eventually for `f`, holds `u x ≤ a`. -/
def limsup (u : β → α) (f : Filter β) : α :=
  limsup (map u f)

/- warning: filter.liminf clashes with filter.Liminf -> Filter.liminf
warning: filter.liminf -> Filter.liminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : ConditionallyCompleteLattice.{u_1} α], (β -> α) -> (Filter.{u_2} β) -> α
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align filter.liminf Filter.liminfₓ'. -/
/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that,
eventually for `f`, holds `u x ≥ a`. -/
def liminf (u : β → α) (f : Filter β) : α :=
  liminf (map u f)

/-- The `blimsup` of a function `u` along a filter `f`, bounded by a predicate `p`, is the infimum
of the `a` such that, eventually for `f`, `u x ≤ a` whenever `p x` holds. -/
def blimsup (u : β → α) (f : Filter β) (p : β → Prop) :=
  inf { a | ∀ᶠ x in f, p x → u x ≤ a }

/-- The `bliminf` of a function `u` along a filter `f`, bounded by a predicate `p`, is the supremum
of the `a` such that, eventually for `f`, `a ≤ u x` whenever `p x` holds. -/
def bliminf (u : β → α) (f : Filter β) (p : β → Prop) :=
  sup { a | ∀ᶠ x in f, p x → a ≤ u x }

section

variable {f : Filter β} {u : β → α} {p : β → Prop}

theorem limsup_eq : limsup u f = inf { a | ∀ᶠ n in f, u n ≤ a } :=
  rfl

theorem liminf_eq : liminf u f = sup { a | ∀ᶠ n in f, a ≤ u n } :=
  rfl

theorem blimsup_eq : blimsup u f p = inf { a | ∀ᶠ x in f, p x → u x ≤ a } :=
  rfl

theorem bliminf_eq : bliminf u f p = sup { a | ∀ᶠ x in f, p x → a ≤ u x } :=
  rfl

end

@[simp]
theorem blimsup_true (f : Filter β) (u : β → α) : (blimsup u f fun x => True) = limsup u f := by
  simp [blimsup_eq, limsup_eq]

@[simp]
theorem bliminf_true (f : Filter β) (u : β → α) : (bliminf u f fun x => True) = liminf u f := by
  simp [bliminf_eq, liminf_eq]

theorem blimsup_eq_limsup_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    blimsup u f p = limsup (u ∘ (coe : { x | p x } → β)) (comap coe f) := by
  simp only [blimsup_eq, limsup_eq, Function.comp_app, eventually_comap, SetCoe.forall, Subtype.coe_mk, mem_set_of_eq]
  congr
  ext a
  exact
    eventually_congr
      (eventually_of_forall fun x => ⟨fun hx y hy hxy => hxy.symm ▸ hx (hxy ▸ hy), fun hx hx' => hx x hx' rfl⟩)

theorem bliminf_eq_liminf_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    bliminf u f p = liminf (u ∘ (coe : { x | p x } → β)) (comap coe f) :=
  @blimsup_eq_limsup_subtype αᵒᵈ β _ f u p

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem Limsup_le_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, n ≤ a) : limsup f ≤ a :=
  cInf_le hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_Liminf_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, a ≤ n) : a ≤ liminf f :=
  le_cSup hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsup_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, u n ≤ a) : limsup u f ≤ a :=
  cInf_le hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_liminf_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, a ≤ u n) : a ≤ liminf u f :=
  le_cSup hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_Limsup_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, n ≤ b) → a ≤ b) : a ≤ limsup f :=
  le_cInf hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem Liminf_le_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, b ≤ n) → b ≤ a) : liminf f ≤ a :=
  cSup_le hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_limsup_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, u n ≤ b) → a ≤ b) : a ≤ limsup u f :=
  le_cInf hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, b ≤ u n) → b ≤ a) : liminf u f ≤ a :=
  cSup_le hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem Liminf_le_Limsup {f : Filter α} [NeBot f]
    (h₁ : f.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h₂ : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default) :
    liminf f ≤ limsup f :=
  (Liminf_le_of_le h₂) fun a₀ ha₀ =>
    (le_Limsup_of_le h₁) fun a₁ ha₁ =>
      show a₀ ≤ a₁ from
        let ⟨b, hb₀, hb₁⟩ := (ha₀.And ha₁).exists
        le_trans hb₀ hb₁

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_limsup {f : Filter β} [NeBot f] {u : β → α}
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    liminf u f ≤ limsup u f :=
  Liminf_le_Limsup h h'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem Limsup_le_Limsup {f g : Filter α}
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ a, (∀ᶠ n in g, n ≤ a) → ∀ᶠ n in f, n ≤ a) : limsup f ≤ limsup g :=
  cInf_le_cInf hf hg h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem Liminf_le_Liminf {f g : Filter α}
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ a, (∀ᶠ n in f, a ≤ n) → ∀ᶠ n in g, a ≤ n) : liminf f ≤ liminf g :=
  cSup_le_cSup hg hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsup_le_limsup {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β} (h : u ≤ᶠ[f] v)
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hv : f.IsBoundedUnder (· ≤ ·) v := by
      run_tac
        is_bounded_default) :
    limsup u f ≤ limsup v f :=
  (Limsup_le_Limsup hu hv) fun b => h.trans

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_liminf {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a ≤ v a)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hv : f.IsCoboundedUnder (· ≥ ·) v := by
      run_tac
        is_bounded_default) :
    liminf u f ≤ liminf v f :=
  @limsup_le_limsup βᵒᵈ α _ _ _ _ h hv hu

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem Limsup_le_Limsup_of_le {f g : Filter α} (h : f ≤ g)
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default) :
    limsup f ≤ limsup g :=
  Limsup_le_Limsup hf hg fun a ha => h ha

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem Liminf_le_Liminf_of_le {f g : Filter α} (h : g ≤ f)
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default) :
    liminf f ≤ liminf g :=
  Liminf_le_Liminf hf hg fun a ha => h ha

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsup_le_limsup_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : f ≤ g) {u : α → β}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hg : g.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    limsup u f ≤ limsup u g :=
  Limsup_le_Limsup_of_le (map_mono h) hf hg

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_liminf_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : g ≤ f) {u : α → β}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hg : g.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    liminf u f ≤ liminf u g :=
  Liminf_le_Liminf_of_le (map_mono h) hf hg

theorem Limsup_principal {s : Set α} (h : BddAbove s) (hs : s.Nonempty) : limsup (𝓟 s) = sup s := by
  simp [Limsup] <;> exact cInf_upper_bounds_eq_cSup h hs

theorem Liminf_principal {s : Set α} (h : BddBelow s) (hs : s.Nonempty) : liminf (𝓟 s) = inf s :=
  @Limsup_principal αᵒᵈ _ s h hs

theorem limsup_congr {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : limsup u f = limsup v f := by
  rw [limsup_eq]
  congr with b
  exact eventually_congr (h.mono fun x hx => by simp [hx])

theorem liminf_congr {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : liminf u f = liminf v f :=
  @limsup_congr βᵒᵈ _ _ _ _ _ h

theorem limsup_const {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f] (b : β) :
    limsup (fun x => b) f = b := by simpa only [limsup_eq, eventually_const] using cInf_Ici

theorem liminf_const {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f] (b : β) :
    liminf (fun x => b) f = b :=
  @limsup_const βᵒᵈ α _ f _ b

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Limsup_bot : limsup (⊥ : Filter α) = ⊥ :=
  bot_unique <| Inf_le <| by simp

@[simp]
theorem Liminf_bot : liminf (⊥ : Filter α) = ⊤ :=
  top_unique <| le_Sup <| by simp

@[simp]
theorem Limsup_top : limsup (⊤ : Filter α) = ⊤ :=
  top_unique <| le_Inf <| by simp [eq_univ_iff_forall] <;> exact fun b hb => top_unique <| hb _

@[simp]
theorem Liminf_top : liminf (⊤ : Filter α) = ⊥ :=
  bot_unique <| Sup_le <| by simp [eq_univ_iff_forall] <;> exact fun b hb => bot_unique <| hb _

@[simp]
theorem blimsup_false {f : Filter β} {u : β → α} : (blimsup u f fun x => False) = ⊥ := by simp [blimsup_eq]

@[simp]
theorem bliminf_false {f : Filter β} {u : β → α} : (bliminf u f fun x => False) = ⊤ := by simp [bliminf_eq]

/-- Same as limsup_const applied to `⊥` but without the `ne_bot f` assumption -/
theorem limsup_const_bot {f : Filter β} : limsup (fun x : β => (⊥ : α)) f = (⊥ : α) := by
  rw [limsup_eq, eq_bot_iff]
  exact Inf_le (eventually_of_forall fun x => le_rfl)

/-- Same as limsup_const applied to `⊤` but without the `ne_bot f` assumption -/
theorem liminf_const_top {f : Filter β} : liminf (fun x : β => (⊤ : α)) f = (⊤ : α) :=
  @limsup_const_bot αᵒᵈ β _ _

theorem HasBasis.Limsup_eq_infi_Sup {ι} {p : ι → Prop} {s} {f : Filter α} (h : f.HasBasis p s) :
    limsup f = ⨅ (i) (hi : p i), sup (s i) :=
  le_antisymm (le_infi₂ fun i hi => Inf_le <| h.eventually_iff.2 ⟨i, hi, fun x => le_Sup⟩)
    (le_Inf fun a ha =>
      let ⟨i, hi, ha⟩ := h.eventually_iff.1 ha
      infi₂_le_of_le _ hi <| Sup_le ha)

theorem HasBasis.Liminf_eq_supr_Inf {p : ι → Prop} {s : ι → Set α} {f : Filter α} (h : f.HasBasis p s) :
    liminf f = ⨆ (i) (hi : p i), inf (s i) :=
  @HasBasis.Limsup_eq_infi_Sup αᵒᵈ _ _ _ _ _ h

theorem Limsup_eq_infi_Sup {f : Filter α} : limsup f = ⨅ s ∈ f, sup s :=
  f.basis_sets.Limsup_eq_infi_Sup

theorem Liminf_eq_supr_Inf {f : Filter α} : liminf f = ⨆ s ∈ f, inf s :=
  @Limsup_eq_infi_Sup αᵒᵈ _ _

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem limsup_le_supr {f : Filter β} {u : β → α} : limsup u f ≤ ⨆ n, u n :=
  limsup_le_of_le
    (by
      run_tac
        is_bounded_default)
    (eventually_of_forall (le_supr u))

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem infi_le_liminf {f : Filter β} {u : β → α} : (⨅ n, u n) ≤ liminf u f :=
  le_liminf_of_le
    (by
      run_tac
        is_bounded_default)
    (eventually_of_forall (infi_le u))

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_infi_supr {f : Filter β} {u : β → α} : limsup u f = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
  (f.basis_sets.map u).Limsup_eq_infi_Sup.trans <| by simp only [Sup_image, id]

theorem limsup_eq_infi_supr_of_nat {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i ≥ n, u i :=
  (at_top_basis.map u).Limsup_eq_infi_Sup.trans <| by simp only [Sup_image, infi_const] <;> rfl

theorem limsup_eq_infi_supr_of_nat' {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i : ℕ, u (i + n) := by
  simp only [limsup_eq_infi_supr_of_nat, supr_ge_eq_supr_nat_add]

theorem HasBasis.limsup_eq_infi_supr {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α} (h : f.HasBasis p s) :
    limsup u f = ⨅ (i) (hi : p i), ⨆ a ∈ s i, u a :=
  (h.map u).Limsup_eq_infi_Sup.trans <| by simp only [Sup_image, id]

theorem blimsup_eq_infi_bsupr {f : Filter β} {p : β → Prop} {u : β → α} :
    blimsup u f p = ⨅ s ∈ f, ⨆ (b) (hb : p b ∧ b ∈ s), u b := by
  refine' le_antisymm (Inf_le_Inf _) (infi_le_iff.mpr fun a ha => le_Inf_iff.mpr fun a' ha' => _)
  · rintro - ⟨s, rfl⟩
    simp only [mem_set_of_eq, le_infi_iff]
    conv =>
    congr
    ext
    rw [Imp.swap]
    refine' eventually_imp_distrib_left.mpr fun h => eventually_iff_exists_mem.2 ⟨s, h, fun x h₁ h₂ => _⟩
    exact @le_supr₂ α β (fun b => p b ∧ b ∈ s) _ (fun b hb => u b) x ⟨h₂, h₁⟩
    
  · obtain ⟨s, hs, hs'⟩ := eventually_iff_exists_mem.mp ha'
    simp_rw [Imp.swap] at hs'
    exact (le_infi_iff.mp (ha s) hs).trans (by simpa only [supr₂_le_iff, and_imp] )
    

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_supr_infi {f : Filter β} {u : β → α} : liminf u f = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
  @limsup_eq_infi_supr αᵒᵈ β _ _ _

theorem liminf_eq_supr_infi_of_nat {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i ≥ n, u i :=
  @limsup_eq_infi_supr_of_nat αᵒᵈ _ u

theorem liminf_eq_supr_infi_of_nat' {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i : ℕ, u (i + n) :=
  @limsup_eq_infi_supr_of_nat' αᵒᵈ _ _

theorem HasBasis.liminf_eq_supr_infi {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α} (h : f.HasBasis p s) :
    liminf u f = ⨆ (i) (hi : p i), ⨅ a ∈ s i, u a :=
  @HasBasis.limsup_eq_infi_supr αᵒᵈ _ _ _ _ _ _ _ h

theorem bliminf_eq_supr_binfi {f : Filter β} {p : β → Prop} {u : β → α} :
    bliminf u f p = ⨆ s ∈ f, ⨅ (b) (hb : p b ∧ b ∈ s), u b :=
  @blimsup_eq_infi_bsupr αᵒᵈ β _ f p u

theorem limsup_eq_Inf_Sup {ι R : Type _} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    limsup a F = inf ((fun I => sup (a '' I)) '' F.Sets) := by
  refine' le_antisymm _ _
  · rw [limsup_eq]
    refine' Inf_le_Inf fun x hx => _
    rcases(mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩
    filter_upwards [I_mem_F] with i hi
    exact hI ▸ le_Sup (mem_image_of_mem _ hi)
    
  · refine' le_Inf_iff.mpr fun b hb => Inf_le_of_le (mem_image_of_mem _ <| filter.mem_sets.mpr hb) <| Sup_le _
    rintro _ ⟨_, h, rfl⟩
    exact h
    

theorem liminf_eq_Sup_Inf {ι R : Type _} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    liminf a F = sup ((fun I => inf (a '' I)) '' F.Sets) :=
  @Filter.limsup_eq_Inf_Sup ι (OrderDual R) _ _ a

@[simp]
theorem liminf_nat_add (f : ℕ → α) (k : ℕ) : liminf (fun i => f (i + k)) atTop = liminf f atTop := by
  simp_rw [liminf_eq_supr_infi_of_nat]
  exact supr_infi_ge_nat_add f k

@[simp]
theorem limsup_nat_add (f : ℕ → α) (k : ℕ) : limsup (fun i => f (i + k)) atTop = limsup f atTop :=
  @liminf_nat_add αᵒᵈ _ f k

theorem liminf_le_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, u a ≤ x) : liminf u f ≤ x := by
  rw [liminf_eq]
  refine' Sup_le fun b hb => _
  have hbx : ∃ᶠ a in f, b ≤ x := by
    revert h
    rw [← not_imp_not, not_frequently, not_frequently]
    exact fun h => hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.some_spec

theorem le_limsup_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, x ≤ u a) : x ≤ limsup u f :=
  @liminf_le_of_frequently_le' _ βᵒᵈ _ _ _ _ h

/-- If `f : α → α` is a morphism of complete lattices, then the limsup of its iterates of any
`a : α` is a fixed point. -/
@[simp]
theorem CompleteLatticeHom.apply_limsup_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (limsup (fun n => (f^[n]) a) atTop) = limsup (fun n => (f^[n]) a) atTop := by
  rw [limsup_eq_infi_supr_of_nat', map_infi]
  simp_rw [_root_.map_supr, ← Function.comp_apply f, ← Function.iterate_succ' f, ← Nat.add_succ]
  conv_rhs => rw [infi_split _ ((· < ·) (0 : ℕ))]
  simp only [not_lt, le_zero_iff, infi_infi_eq_left, add_zero, infi_nat_gt_zero_eq, left_eq_inf]
  refine' (infi_le (fun i => ⨆ j, (f^[j + (i + 1)]) a) 0).trans _
  simp only [zero_add, Function.comp_app, supr_le_iff]
  exact fun i => le_supr (fun i => (f^[i]) a) (i + 1)

/-- If `f : α → α` is a morphism of complete lattices, then the liminf of its iterates of any
`a : α` is a fixed point. -/
theorem CompleteLatticeHom.apply_liminf_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (liminf (fun n => (f^[n]) a) atTop) = liminf (fun n => (f^[n]) a) atTop :=
  (CompleteLatticeHom.dual f).apply_limsup_iterate _

variable {f g : Filter β} {p q : β → Prop} {u v : β → α}

theorem blimsup_mono (h : ∀ x, p x → q x) : blimsup u f p ≤ blimsup u f q :=
  Inf_le_Inf fun a ha => ha.mono <| by tauto

theorem bliminf_antitone (h : ∀ x, p x → q x) : bliminf u f q ≤ bliminf u f p :=
  Sup_le_Sup fun a ha => ha.mono <| by tauto

theorem mono_blimsup' (h : ∀ᶠ x in f, u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  Inf_le_Inf fun a ha => (ha.And h).mono fun x hx hx' => hx.2.trans (hx.1 hx')

theorem mono_blimsup (h : ∀ x, u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  mono_blimsup' <| eventually_of_forall h

theorem mono_bliminf' (h : ∀ᶠ x in f, u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  Sup_le_Sup fun a ha => (ha.And h).mono fun x hx hx' => (hx.1 hx').trans hx.2

theorem mono_bliminf (h : ∀ x, u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  mono_bliminf' <| eventually_of_forall h

theorem bliminf_antitone_filter (h : f ≤ g) : bliminf u g p ≤ bliminf u f p :=
  Sup_le_Sup fun a ha => ha.filter_mono h

theorem blimsup_monotone_filter (h : f ≤ g) : blimsup u f p ≤ blimsup u g p :=
  Inf_le_Inf fun a ha => ha.filter_mono h

@[simp]
theorem blimsup_and_le_inf : (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f p ⊓ blimsup u f q :=
  le_inf (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]
theorem bliminf_sup_le_and : bliminf u f p ⊔ bliminf u f q ≤ bliminf u f fun x => p x ∧ q x :=
  @blimsup_and_le_inf αᵒᵈ β _ f p q u

/-- See also `filter.blimsup_or_eq_sup`. -/
@[simp]
theorem blimsup_sup_le_or : blimsup u f p ⊔ blimsup u f q ≤ blimsup u f fun x => p x ∨ q x :=
  sup_le (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

/-- See also `filter.bliminf_or_eq_inf`. -/
@[simp]
theorem bliminf_or_le_inf : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f p ⊓ bliminf u f q :=
  @blimsup_sup_le_or αᵒᵈ β _ f p q u

end CompleteLattice

section CompleteDistribLattice

variable [CompleteDistribLattice α] {f : Filter β} {p q : β → Prop} {u : β → α}

@[simp]
theorem blimsup_or_eq_sup : (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ blimsup u f q := by
  refine' le_antisymm _ blimsup_sup_le_or
  simp only [blimsup_eq, Inf_sup_eq, sup_Inf_eq, le_infi₂_iff, mem_set_of_eq]
  refine' fun a' ha' a ha => Inf_le ((ha.And ha').mono fun b h hb => _)
  exact Or.elim hb (fun hb => le_sup_of_le_left <| h.1 hb) fun hb => le_sup_of_le_right <| h.2 hb

@[simp]
theorem bliminf_or_eq_inf : (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bliminf u f q :=
  @blimsup_or_eq_sup αᵒᵈ β _ f p q u

theorem sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsup (fun x => a ⊔ u x) f := by
  simp only [limsup_eq_infi_supr, supr_sup_eq, sup_binfi_eq]
  congr
  ext s
  congr
  ext hs
  congr
  exact (bsupr_const (nonempty_of_mem hs)).symm

theorem inf_liminf [NeBot f] (a : α) : a ⊓ liminf u f = liminf (fun x => a ⊓ u x) f :=
  @sup_limsup αᵒᵈ β _ f _ _ _

theorem sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f := by
  simp only [liminf_eq_supr_infi]
  rw [sup_comm, bsupr_sup (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  simp_rw [binfi_sup_eq, @sup_comm _ _ a]

theorem inf_limsup (a : α) : a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f :=
  @sup_liminf αᵒᵈ β _ f _ _

end CompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] (f : Filter β) (u : β → α)

theorem limsup_compl : limsup u fᶜ = liminf (compl ∘ u) f := by
  simp only [limsup_eq_infi_supr, liminf_eq_supr_infi, compl_infi, compl_supr]

theorem liminf_compl : liminf u fᶜ = limsup (compl ∘ u) f := by
  simp only [limsup_eq_infi_supr, liminf_eq_supr_infi, compl_infi, compl_supr]

theorem limsup_sdiff (a : α) : limsup u f \ a = limsup (fun b => u b \ a) f := by
  simp only [limsup_eq_infi_supr, sdiff_eq]
  rw [binfi_inf (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  simp_rw [inf_comm, inf_bsupr_eq, inf_comm]

theorem liminf_sdiff [NeBot f] (a : α) : liminf u f \ a = liminf (fun b => u b \ a) f := by
  simp only [sdiff_eq, @inf_comm _ _ _ (aᶜ), inf_liminf]

theorem sdiff_limsup [NeBot f] (a : α) : a \ limsup u f = liminf (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  simp only [sdiff_eq, liminf_compl, (· ∘ ·), compl_inf, compl_compl, sup_limsup]

theorem sdiff_liminf (a : α) : a \ liminf u f = limsup (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  simp only [sdiff_eq, limsup_compl, (· ∘ ·), compl_inf, compl_compl, sup_liminf]

end CompleteBooleanAlgebra

section SetLattice

variable {p : ι → Prop} {s : ι → Set α}

theorem cofinite.blimsup_set_eq : blimsup s cofinite p = { x | { n | p n ∧ x ∈ s n }.Infinite } := by
  simp only [blimsup_eq, le_eq_subset, eventually_cofinite, not_forall, Inf_eq_sInter, exists_prop]
  ext x
  refine' ⟨fun h => _, fun hx t h => _⟩ <;> contrapose! h
  · simp only [mem_sInter, mem_set_of_eq, not_forall, exists_prop]
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩
    
  · exact hx.mono fun i hi => ⟨hi.1, fun hit => h (hit hi.2)⟩
    

theorem cofinite.bliminf_set_eq : bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.Finite } := by
  rw [← compl_inj_iff]
  simpa only [bliminf_eq_supr_binfi, compl_infi, compl_supr, ← blimsup_eq_infi_bsupr, cofinite.blimsup_set_eq]

/-- In other words, `limsup cofinite s` is the set of elements lying inside the family `s`
infinitely often. -/
theorem cofinite.limsup_set_eq : limsup s cofinite = { x | { n | x ∈ s n }.Infinite } := by
  simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and_iff]

/-- In other words, `liminf cofinite s` is the set of elements lying outside the family `s`
finitely often. -/
theorem cofinite.liminf_set_eq : liminf s cofinite = { x | { n | x ∉ s n }.Finite } := by
  simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and_iff]

end SetLattice

section ConditionallyCompleteLinearOrder

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem frequently_lt_of_lt_Limsup {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : a < limsup f) : ∃ᶠ n in f, a < n := by
  contrapose! h
  simp only [not_frequently, not_lt] at h
  exact Limsup_le_of_le hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem frequently_lt_of_Liminf_lt {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : liminf f < a) : ∃ᶠ n in f, n < a :=
  @frequently_lt_of_lt_Limsup (OrderDual α) f _ a hf h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem eventually_lt_of_lt_liminf {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β} {b : β}
    (h : b < liminf u f)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    ∀ᶠ a in f, b < u a := by
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β)(hc : c ∈ { c : β | ∀ᶠ n : α in f, c ≤ u n }), b < c := exists_lt_of_lt_cSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_le hbc hx

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem eventually_lt_of_limsup_lt {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β} {b : β}
    (h : limsup u f < b)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    ∀ᶠ a in f, u a < b :=
  @eventually_lt_of_lt_liminf _ βᵒᵈ _ _ _ _ h hu

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_limsup_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {b : β}
    (hu_le : ∃ᶠ x in f, b ≤ u x)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    b ≤ limsup u f := by
  revert hu_le
  rw [← not_imp_not, not_frequently]
  simp_rw [← lt_iff_not_ge]
  exact fun h => eventually_lt_of_limsup_lt h hu

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {b : β}
    (hu_le : ∃ᶠ x in f, u x ≤ b)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    liminf u f ≤ b :=
  @le_limsup_of_frequently_le _ βᵒᵈ _ f u b hu_le hu

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem frequently_lt_of_lt_limsup {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h : b < limsup u f) : ∃ᶠ x in f, b < u x := by
  contrapose! h
  apply Limsup_le_of_le hu
  simpa using h

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem frequently_lt_of_liminf_lt {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (h : liminf u f < b) : ∃ᶠ x in f, u x < b :=
  @frequently_lt_of_lt_limsup _ βᵒᵈ _ f u b hu h

end ConditionallyCompleteLinearOrder

end Filter

section Order

open Filter

theorem Monotone.is_bounded_under_le_comp [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ] {g : β → γ}
    {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f := by
  refine' ⟨_, fun h => h.IsBoundedUnder hg⟩
  rintro ⟨c, hc⟩
  rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : ∃ b, ∀ a ≥ b, c < g a := eventually_at_top.1 (hg'.eventually_gt_at_top c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_le hx⟩

theorem Monotone.is_bounded_under_ge_comp [Nonempty β] [LinearOrder β] [Preorder γ] [NoMinOrder γ] {g : β → γ}
    {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atBot atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual.is_bounded_under_le_comp hg'

theorem Antitone.is_bounded_under_le_comp [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ] {g : β → γ}
    {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atBot atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual_right.is_bounded_under_ge_comp hg'

theorem Antitone.is_bounded_under_ge_comp [Nonempty β] [LinearOrder β] [Preorder γ] [NoMinOrder γ] {g : β → γ}
    {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atTop atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f :=
  hg.dual_right.is_bounded_under_le_comp hg'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem GaloisConnection.l_limsup_le [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ] {f : Filter α}
    {v : α → β} {l : β → γ} {u : γ → β} (gc : GaloisConnection l u)
    (hlv : f.IsBoundedUnder (· ≤ ·) fun x => l (v x) := by
      run_tac
        is_bounded_default)
    (hv_co : f.IsCoboundedUnder (· ≤ ·) v := by
      run_tac
        is_bounded_default) :
    l (limsup v f) ≤ limsup (fun x => l (v x)) f := by
  refine' le_Limsup_of_le hlv fun c hc => _
  rw [Filter.eventually_map] at hc
  simp_rw [gc _ _] at hc⊢
  exact Limsup_le_of_le hv_co hc

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem OrderIso.limsup_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ] {f : Filter α}
    {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hu_co : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hgu : f.IsBoundedUnder (· ≤ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default)
    (hgu_co : f.IsCoboundedUnder (· ≤ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default) :
    g (limsup u f) = limsup (fun x => g (u x)) f := by
  refine' le_antisymm (g.to_galois_connection.l_limsup_le hgu hu_co) _
  rw [← g.symm.symm_apply_apply <| limsup (fun x => g (u x)) f, g.symm_symm]
  refine' g.monotone _
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  nth_rw 0 [hf]
  refine' g.symm.to_galois_connection.l_limsup_le _ hgu_co
  simp_rw [g.symm_apply_apply]
  exact hu

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic is_bounded_default -/
theorem OrderIso.liminf_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ] {f : Filter α}
    {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hu_co : f.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hgu : f.IsBoundedUnder (· ≥ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default)
    (hgu_co : f.IsCoboundedUnder (· ≥ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default) :
    g (liminf u f) = liminf (fun x => g (u x)) f :=
  @OrderIso.limsup_apply α βᵒᵈ γᵒᵈ _ _ f u g.dual hu hu_co hgu hgu_co

end Order

