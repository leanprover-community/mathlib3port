/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Bool.Set
import Mathbin.Data.Nat.Basic
import Mathbin.Order.Bounds

/-!
# Theory of complete lattices

## Main definitions

* `Sup` and `Inf` are the supremum and the infimum of a set;
* `supr (f : ι → α)` and `infi (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `Sup` and `Inf` of the range of this function;
* `class complete_lattice`: a bounded lattice such that `Sup s` is always the least upper boundary
  of `s` and `Inf s` is always the greatest lower boundary of `s`;
* `class complete_linear_order`: a linear ordered complete lattice.

## Naming conventions

We use `Sup`/`Inf`/`supr`/`infi` for the corresponding functions in the statement. Sometimes we
also use `bsupr`/`binfi` for "bounded" supremum or infimum, i.e. one of `⨆ i ∈ s, f i`,
`⨆ i (hi : p i), f i`, or more generally `⨆ i (hi : p i), f i hi`.

## Notation

* `⨆ i, f i` : `supr f`, the supremum of the range of `f`;
* `⨅ i, f i` : `infi f`, the infimum of the range of `f`.
-/


open Set Function

variable {α β β₂ : Type _} {ι ι₂ : Sort _}

/-- class for the `Sup` operator -/
class HasSupₓ (α : Type _) where
  sup : Set α → α

/-- class for the `Inf` operator -/
class HasInfₓ (α : Type _) where
  inf : Set α → α

export HasSupₓ (sup)

export HasInfₓ (inf)

/-- Supremum of a set -/
add_decl_doc HasSupₓ.sup

/-- Infimum of a set -/
add_decl_doc HasInfₓ.inf

/-- Indexed supremum -/
def supr [HasSupₓ α] {ι} (s : ι → α) : α :=
  sup (Range s)

/-- Indexed infimum -/
def infi [HasInfₓ α] {ι} (s : ι → α) : α :=
  inf (Range s)

instance (priority := 50) has_Inf_to_nonempty α [HasInfₓ α] : Nonempty α :=
  ⟨inf ∅⟩

instance (priority := 50) has_Sup_to_nonempty α [HasSupₓ α] : Nonempty α :=
  ⟨sup ∅⟩

-- mathport name: «expr⨆ , »
notation3 "⨆ " (...) ", " r:(scoped f => supr f) => r

-- mathport name: «expr⨅ , »
notation3 "⨅ " (...) ", " r:(scoped f => infi f) => r

instance α [HasInfₓ α] : HasSupₓ (OrderDual α) :=
  ⟨(inf : Set α → α)⟩

instance α [HasSupₓ α] : HasInfₓ (OrderDual α) :=
  ⟨(sup : Set α → α)⟩

/-- Note that we rarely use `complete_semilattice_Sup`
(in fact, any such object is always a `complete_lattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[ancestor PartialOrderₓ HasSupₓ]
class CompleteSemilatticeSup (α : Type _) extends PartialOrderₓ α, HasSupₓ α where
  le_Sup : ∀ s, ∀, ∀ a ∈ s, ∀, a ≤ Sup s
  Sup_le : ∀ s a, (∀, ∀ b ∈ s, ∀, b ≤ a) → Sup s ≤ a

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

@[ematch]
theorem le_Sup : a ∈ s → a ≤ sup s :=
  CompleteSemilatticeSup.le_Sup s a

theorem Sup_le : (∀, ∀ b ∈ s, ∀, b ≤ a) → sup s ≤ a :=
  CompleteSemilatticeSup.Sup_le s a

theorem is_lub_Sup (s : Set α) : IsLub s (sup s) :=
  ⟨fun x => le_Sup, fun x => Sup_le⟩

theorem IsLub.Sup_eq (h : IsLub s a) : sup s = a :=
  (is_lub_Sup s).unique h

theorem le_Sup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ sup s :=
  le_transₓ h (le_Sup hb)

theorem Sup_le_Sup (h : s ⊆ t) : sup s ≤ sup t :=
  (is_lub_Sup s).mono (is_lub_Sup t) h

@[simp]
theorem Sup_le_iff : sup s ≤ a ↔ ∀, ∀ b ∈ s, ∀, b ≤ a :=
  is_lub_le_iff (is_lub_Sup s)

theorem le_Sup_iff : a ≤ sup s ↔ ∀, ∀ b ∈ UpperBounds s, ∀, a ≤ b :=
  ⟨fun h b hb => le_transₓ h (Sup_le hb), fun hb => hb _ fun x => le_Sup⟩

theorem le_supr_iff {s : ι → α} : a ≤ supr s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [supr, le_Sup_iff, UpperBounds]

theorem Sup_le_Sup_of_forall_exists_le (h : ∀, ∀ x ∈ s, ∀, ∃ y ∈ t, x ≤ y) : sup s ≤ sup t :=
  le_Sup_iff.2 fun b hb =>
    Sup_le fun a ha =>
      let ⟨c, hct, hac⟩ := h a ha
      hac.trans (hb hct)

-- We will generalize this to conditionally complete lattices in `cSup_singleton`.
theorem Sup_singleton {a : α} : sup {a} = a :=
  is_lub_singleton.Sup_eq

end

/-- Note that we rarely use `complete_semilattice_Inf`
(in fact, any such object is always a `complete_lattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[ancestor PartialOrderₓ HasInfₓ]
class CompleteSemilatticeInf (α : Type _) extends PartialOrderₓ α, HasInfₓ α where
  Inf_le : ∀ s, ∀, ∀ a ∈ s, ∀, Inf s ≤ a
  le_Inf : ∀ s a, (∀, ∀ b ∈ s, ∀, a ≤ b) → a ≤ Inf s

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

@[ematch]
theorem Inf_le : a ∈ s → inf s ≤ a :=
  CompleteSemilatticeInf.Inf_le s a

theorem le_Inf : (∀, ∀ b ∈ s, ∀, a ≤ b) → a ≤ inf s :=
  CompleteSemilatticeInf.le_Inf s a

theorem is_glb_Inf (s : Set α) : IsGlb s (inf s) :=
  ⟨fun a => Inf_le, fun a => le_Inf⟩

theorem IsGlb.Inf_eq (h : IsGlb s a) : inf s = a :=
  (is_glb_Inf s).unique h

theorem Inf_le_of_le (hb : b ∈ s) (h : b ≤ a) : inf s ≤ a :=
  le_transₓ (Inf_le hb) h

theorem Inf_le_Inf (h : s ⊆ t) : inf t ≤ inf s :=
  (is_glb_Inf s).mono (is_glb_Inf t) h

@[simp]
theorem le_Inf_iff : a ≤ inf s ↔ ∀, ∀ b ∈ s, ∀, a ≤ b :=
  le_is_glb_iff (is_glb_Inf s)

theorem Inf_le_iff : inf s ≤ a ↔ ∀, ∀ b ∈ LowerBounds s, ∀, b ≤ a :=
  ⟨fun h b hb => le_transₓ (le_Inf hb) h, fun hb => hb _ fun x => Inf_le⟩

theorem infi_le_iff {s : ι → α} : infi s ≤ a ↔ ∀ b, (∀ i, b ≤ s i) → b ≤ a := by
  simp [infi, Inf_le_iff, LowerBounds]

theorem Inf_le_Inf_of_forall_exists_le (h : ∀, ∀ x ∈ s, ∀, ∃ y ∈ t, y ≤ x) : inf t ≤ inf s :=
  le_of_forall_le
    (by
      simp only [le_Inf_iff]
      introv h₀ h₁
      rcases h _ h₁ with ⟨y, hy, hy'⟩
      solve_by_elim [le_transₓ _ hy'])

-- We will generalize this to conditionally complete lattices in `cInf_singleton`.
theorem Inf_singleton {a : α} : inf {a} = a :=
  is_glb_singleton.Inf_eq

end

/-- A complete lattice is a bounded lattice which
  has suprema and infima for every subset. -/
@[protect_proj, ancestor Lattice CompleteSemilatticeSup CompleteSemilatticeInf HasTop HasBot]
class CompleteLattice (α : Type _) extends Lattice α, CompleteSemilatticeSup α, CompleteSemilatticeInf α, HasTop α,
  HasBot α where
  le_top : ∀ x : α, x ≤ ⊤
  bot_le : ∀ x : α, ⊥ ≤ x

-- see Note [lower instance priority]
instance (priority := 100) CompleteLattice.toBoundedOrder [h : CompleteLattice α] : BoundedOrder α :=
  { h with }

/-- Create a `complete_lattice` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup, bot, top
  ..complete_lattice_of_Inf my_T _ }
```
-/
def completeLatticeOfInf (α : Type _) [H1 : PartialOrderₓ α] [H2 : HasInfₓ α]
    (is_glb_Inf : ∀ s : Set α, IsGlb s (inf s)) : CompleteLattice α :=
  { H1, H2 with bot := inf Univ, bot_le := fun x => (is_glb_Inf Univ).1 trivialₓ, top := inf ∅,
    le_top := fun a =>
      (is_glb_Inf ∅).2 <| by
        simp ,
    sup := fun a b => inf { x | a ≤ x ∧ b ≤ x }, inf := fun a b => inf {a, b},
    le_inf := fun a b c hab hac => by
      apply (is_glb_Inf _).2
      simp [*],
    inf_le_right := fun a b => (is_glb_Inf _).1 <| mem_insert_of_mem _ <| mem_singleton _,
    inf_le_left := fun a b => (is_glb_Inf _).1 <| mem_insert _ _,
    sup_le := fun a b c hac hbc =>
      (is_glb_Inf _).1 <| by
        simp [*],
    le_sup_left := fun a b => (is_glb_Inf _).2 fun x => And.left,
    le_sup_right := fun a b => (is_glb_Inf _).2 fun x => And.right, le_Inf := fun s a ha => (is_glb_Inf s).2 ha,
    Inf_le := fun s a ha => (is_glb_Inf s).1 ha, sup := fun s => inf (UpperBounds s),
    le_Sup := fun s a ha => (is_glb_Inf (UpperBounds s)).2 fun b hb => hb ha,
    Sup_le := fun s a ha => (is_glb_Inf (UpperBounds s)).1 ha }

/-- Any `complete_semilattice_Inf` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Inf`.
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type _) [CompleteSemilatticeInf α] : CompleteLattice α :=
  completeLatticeOfInf α fun s => is_glb_Inf s

/-- Create a `complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf, bot, top
  ..complete_lattice_of_Sup my_T _ }
```
-/
def completeLatticeOfSup (α : Type _) [H1 : PartialOrderₓ α] [H2 : HasSupₓ α]
    (is_lub_Sup : ∀ s : Set α, IsLub s (sup s)) : CompleteLattice α :=
  { H1, H2 with top := sup Univ, le_top := fun x => (is_lub_Sup Univ).1 trivialₓ, bot := sup ∅,
    bot_le := fun x =>
      (is_lub_Sup ∅).2 <| by
        simp ,
    sup := fun a b => sup {a, b},
    sup_le := fun a b c hac hbc =>
      (is_lub_Sup _).2
        (by
          simp [*]),
    le_sup_left := fun a b => (is_lub_Sup _).1 <| mem_insert _ _,
    le_sup_right := fun a b => (is_lub_Sup _).1 <| mem_insert_of_mem _ <| mem_singleton _,
    inf := fun a b => sup { x | x ≤ a ∧ x ≤ b },
    le_inf := fun a b c hab hac =>
      (is_lub_Sup _).1 <| by
        simp [*],
    inf_le_left := fun a b => (is_lub_Sup _).2 fun x => And.left,
    inf_le_right := fun a b => (is_lub_Sup _).2 fun x => And.right, inf := fun s => sup (LowerBounds s),
    Sup_le := fun s a ha => (is_lub_Sup s).2 ha, le_Sup := fun s a ha => (is_lub_Sup s).1 ha,
    Inf_le := fun s a ha => (is_lub_Sup (LowerBounds s)).2 fun b hb => hb ha,
    le_Inf := fun s a ha => (is_lub_Sup (LowerBounds s)).1 ha }

/-- Any `complete_semilattice_Sup` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Sup`.
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type _) [CompleteSemilatticeSup α] : CompleteLattice α :=
  completeLatticeOfSup α fun s => is_lub_Sup s

-- ././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure
/-- A complete linear order is a linear order whose lattice structure is complete. -/
class CompleteLinearOrder (α : Type _) extends CompleteLattice α,
  "././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure"

namespace OrderDual

variable (α)

instance [CompleteLattice α] : CompleteLattice (OrderDual α) :=
  { OrderDual.lattice α, OrderDual.hasSupₓ α, OrderDual.hasInfₓ α, OrderDual.boundedOrder α with
    le_Sup := @CompleteLattice.Inf_le α _, Sup_le := @CompleteLattice.le_Inf α _, Inf_le := @CompleteLattice.le_Sup α _,
    le_Inf := @CompleteLattice.Sup_le α _ }

instance [CompleteLinearOrder α] : CompleteLinearOrder (OrderDual α) :=
  { OrderDual.completeLattice α, OrderDual.linearOrder α with }

end OrderDual

section

variable [CompleteLattice α] {s t : Set α} {a b : α}

theorem Inf_le_Sup (hs : s.Nonempty) : inf s ≤ sup s :=
  is_glb_le_is_lub (is_glb_Inf s) (is_lub_Sup s) hs

theorem Sup_union {s t : Set α} : sup (s ∪ t) = sup s⊔sup t :=
  ((is_lub_Sup s).union (is_lub_Sup t)).Sup_eq

theorem Sup_inter_le {s t : Set α} : sup (s ∩ t) ≤ sup s⊓sup t :=
  Sup_le fun b hb => le_inf (le_Sup hb.1) (le_Sup hb.2)

/-
  Sup_le (assume a ⟨a_s, a_t⟩, le_inf (le_Sup a_s) (le_Sup a_t))
-/
theorem Inf_union {s t : Set α} : inf (s ∪ t) = inf s⊓inf t :=
  ((is_glb_Inf s).union (is_glb_Inf t)).Inf_eq

theorem le_Inf_inter {s t : Set α} : inf s⊔inf t ≤ inf (s ∩ t) :=
  @Sup_inter_le (OrderDual α) _ _ _

@[simp]
theorem Sup_empty : sup ∅ = (⊥ : α) :=
  (@is_lub_empty α _ _).Sup_eq

@[simp]
theorem Inf_empty : inf ∅ = (⊤ : α) :=
  (@is_glb_empty α _ _).Inf_eq

@[simp]
theorem Sup_univ : sup Univ = (⊤ : α) :=
  (@is_lub_univ α _ _).Sup_eq

@[simp]
theorem Inf_univ : inf Univ = (⊥ : α) :=
  (@is_glb_univ α _ _).Inf_eq

-- TODO(Jeremy): get this automatically
@[simp]
theorem Sup_insert {a : α} {s : Set α} : sup (insert a s) = a⊔sup s :=
  ((is_lub_Sup s).insert a).Sup_eq

@[simp]
theorem Inf_insert {a : α} {s : Set α} : inf (insert a s) = a⊓inf s :=
  ((is_glb_Inf s).insert a).Inf_eq

theorem Sup_le_Sup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : sup s ≤ sup t :=
  le_transₓ (Sup_le_Sup h) (le_of_eqₓ (trans Sup_insert bot_sup_eq))

theorem Inf_le_Inf_of_subset_insert_top (h : s ⊆ insert ⊤ t) : inf t ≤ inf s :=
  le_transₓ (le_of_eqₓ (trans top_inf_eq.symm Inf_insert.symm)) (Inf_le_Inf h)

theorem Sup_pair {a b : α} : sup {a, b} = a⊔b :=
  (@is_lub_pair α _ a b).Sup_eq

theorem Inf_pair {a b : α} : inf {a, b} = a⊓b :=
  (@is_glb_pair α _ a b).Inf_eq

@[simp]
theorem Inf_eq_top : inf s = ⊤ ↔ ∀, ∀ a ∈ s, ∀, a = ⊤ :=
  Iff.intro (fun h a ha => top_unique <| h ▸ Inf_le ha) fun h => top_unique <| le_Inf fun a ha => top_le_iff.2 <| h a ha

theorem eq_singleton_top_of_Inf_eq_top_of_nonempty {s : Set α} (h_inf : inf s = ⊤) (hne : s.Nonempty) : s = {⊤} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [Inf_eq_top] at h_inf
  exact ⟨hne, h_inf⟩

@[simp]
theorem Sup_eq_bot : sup s = ⊥ ↔ ∀, ∀ a ∈ s, ∀, a = ⊥ :=
  @Inf_eq_top (OrderDual α) _ _

theorem eq_singleton_bot_of_Sup_eq_bot_of_nonempty {s : Set α} (h_sup : sup s = ⊥) (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [Sup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `cSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem Sup_eq_of_forall_le_of_forall_lt_exists_gt (_ : ∀, ∀ a ∈ s, ∀, a ≤ b) (H : ∀ w, w < b → ∃ a ∈ s, w < a) :
    sup s = b :=
  have h : sup s < b ∨ sup s = b := lt_or_eq_of_leₓ (Sup_le ‹∀, ∀ a ∈ s, ∀, a ≤ b›)
  have : ¬sup s < b := fun this : sup s < b =>
    let ⟨a, _, _⟩ := H (sup s) ‹sup s < b›
    -- a ∈ s, Sup s < a
    have : sup s < sup s := lt_of_lt_of_leₓ ‹sup s < a› (le_Sup ‹a ∈ s›)
    show False from lt_irreflₓ _ this
  show sup s = b from Or.resolve_left h this

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `cInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem Inf_eq_of_forall_ge_of_forall_gt_exists_lt (_ : ∀, ∀ a ∈ s, ∀, b ≤ a) (H : ∀ w, b < w → ∃ a ∈ s, a < w) :
    inf s = b :=
  @Sup_eq_of_forall_le_of_forall_lt_exists_gt (OrderDual α) _ _ ‹_› ‹_› ‹_›

end

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s t : Set α} {a b : α}

theorem Inf_lt_iff : inf s < b ↔ ∃ a ∈ s, a < b :=
  is_glb_lt_iff (is_glb_Inf s)

theorem lt_Sup_iff : b < sup s ↔ ∃ a ∈ s, b < a :=
  lt_is_lub_iff (is_lub_Sup s)

theorem Sup_eq_top : sup s = ⊤ ↔ ∀, ∀ b < ⊤, ∀, ∃ a ∈ s, b < a :=
  Iff.intro
    (fun b hb => by
      rwa [← h, lt_Sup_iff] at hb)
    fun h =>
    top_unique <|
      le_of_not_gtₓ fun h' =>
        let ⟨a, ha, h⟩ := h _ h'
        lt_irreflₓ a <| lt_of_le_of_ltₓ (le_Sup ha) h

theorem Inf_eq_bot : inf s = ⊥ ↔ ∀, ∀ b > ⊥, ∀, ∃ a ∈ s, a < b :=
  @Sup_eq_top (OrderDual α) _ _

theorem lt_supr_iff {f : ι → α} : a < supr f ↔ ∃ i, a < f i :=
  lt_Sup_iff.trans exists_range_iff

theorem infi_lt_iff {f : ι → α} : infi f < a ↔ ∃ i, f i < a :=
  Inf_lt_iff.trans exists_range_iff

end CompleteLinearOrder

/-
### supr & infi
-/
section

variable [CompleteLattice α] {s t : ι → α} {a b : α}

-- TODO: this declaration gives error when starting smt state
--@[ematch]
theorem le_supr (s : ι → α) (i : ι) : s i ≤ supr s :=
  le_Sup ⟨i, rfl⟩

@[ematch]
theorem le_supr' (s : ι → α) (i : ι) : s i ≤ supr s :=
  le_Sup ⟨i, rfl⟩

/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] theorem le_supr' (s : ι → α) (i : ι) : (: s i :) ≤ (: supr s :) :=
le_Sup ⟨i, rfl⟩
-/
theorem is_lub_supr : IsLub (Range s) (⨆ j, s j) :=
  is_lub_Sup _

theorem IsLub.supr_eq (h : IsLub (Range s) a) : (⨆ j, s j) = a :=
  h.Sup_eq

theorem is_glb_infi : IsGlb (Range s) (⨅ j, s j) :=
  is_glb_Inf _

theorem IsGlb.infi_eq (h : IsGlb (Range s) a) : (⨅ j, s j) = a :=
  h.Inf_eq

theorem le_supr_of_le (i : ι) (h : a ≤ s i) : a ≤ supr s :=
  le_transₓ h (le_supr _ i)

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem le_bsupr {p : ι → Prop} {f : ∀ i h : p i, α} (i : ι) (hi : p i) : f i hi ≤ ⨆ (i) (hi), f i hi :=
  le_supr_of_le i <| le_supr (f i) hi

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem le_bsupr_of_le {p : ι → Prop} {f : ∀ i h : p i, α} (i : ι) (hi : p i) (h : a ≤ f i hi) :
    a ≤ ⨆ (i) (hi), f i hi :=
  le_transₓ h (le_bsupr i hi)

theorem supr_le (h : ∀ i, s i ≤ a) : supr s ≤ a :=
  Sup_le fun b ⟨i, Eq⟩ => Eq ▸ h i

theorem bsupr_le {p : ι → Prop} {f : ∀ i h : p i, α} (h : ∀ i hi, f i hi ≤ a) : (⨆ (i) (hi : p i), f i hi) ≤ a :=
  supr_le fun i => supr_le <| h i

theorem bsupr_le_supr (p : ι → Prop) (f : ι → α) : (⨆ (i) (H : p i), f i) ≤ ⨆ i, f i :=
  bsupr_le fun i hi => le_supr f i

theorem supr_le_supr (h : ∀ i, s i ≤ t i) : supr s ≤ supr t :=
  supr_le fun i => le_supr_of_le i (h i)

theorem supr_le_supr2 {t : ι₂ → α} (h : ∀ i, ∃ j, s i ≤ t j) : supr s ≤ supr t :=
  supr_le fun j => Exists.elim (h j) le_supr_of_le

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem bsupr_le_bsupr {p : ι → Prop} {f g : ∀ i hi : p i, α} (h : ∀ i hi, f i hi ≤ g i hi) :
    (⨆ (i) (hi), f i hi) ≤ ⨆ (i) (hi), g i hi :=
  bsupr_le fun i hi => le_transₓ (h i hi) (le_bsupr i hi)

theorem supr_le_supr_const (h : ι → ι₂) : (⨆ i : ι, a) ≤ ⨆ j : ι₂, a :=
  supr_le <| le_supr _ ∘ h

theorem bsupr_le_bsupr' {p q : ι → Prop} (hpq : ∀ i, p i → q i) {f : ι → α} :
    (⨆ (i) (hpi : p i), f i) ≤ ⨆ (i) (hqi : q i), f i :=
  supr_le_supr fun i => supr_le_supr_const (hpq i)

@[simp]
theorem supr_le_iff : supr s ≤ a ↔ ∀ i, s i ≤ a :=
  (is_lub_le_iff is_lub_supr).trans forall_range_iff

theorem supr_lt_iff : supr s < a ↔ ∃ b < a, ∀ i, s i ≤ b :=
  ⟨fun h => ⟨supr s, h, fun i => le_supr s i⟩, fun ⟨b, hba, hsb⟩ => (supr_le hsb).trans_lt hba⟩

theorem Sup_eq_supr {s : Set α} : sup s = ⨆ a ∈ s, a :=
  le_antisymmₓ (Sup_le fun b h => le_supr_of_le b <| le_supr _ h) (supr_le fun b => supr_le fun h => le_Sup h)

theorem Sup_eq_supr' {α} [HasSupₓ α] (s : Set α) : sup s = ⨆ x : s, (x : α) := by
  rw [supr, Subtype.range_coe]

theorem Sup_sUnion {s : Set (Set α)} : sup (⋃₀s) = ⨆ t ∈ s, sup t := by
  apply le_antisymmₓ
  · apply Sup_le fun b hb => _
    rcases hb with ⟨t, ts, bt⟩
    apply le_transₓ _ (le_supr _ t)
    exact le_transₓ (le_Sup bt) (le_supr _ ts)
    
  · apply supr_le fun t => _
    exact supr_le fun ts => Sup_le_Sup fun x xt => ⟨t, ts, xt⟩
    

theorem Monotone.le_map_supr [CompleteLattice β] {f : α → β} (hf : Monotone f) : (⨆ i, f (s i)) ≤ f (supr s) :=
  supr_le fun i => hf <| le_supr _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i h)
theorem Monotone.le_map_supr2 [CompleteLattice β] {f : α → β} (hf : Monotone f) {ι' : ι → Sort _} (s : ∀ i, ι' i → α) :
    (⨆ (i) (h : ι' i), f (s i h)) ≤ f (⨆ (i) (h : ι' i), s i h) :=
  calc
    (⨆ (i) (h), f (s i h)) ≤ ⨆ i, f (⨆ h, s i h) := supr_le_supr fun i => hf.le_map_supr
    _ ≤ f (⨆ (i) (h : ι' i), s i h) := hf.le_map_supr
    

theorem Monotone.le_map_Sup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    (⨆ a ∈ s, f a) ≤ f (sup s) := by
  rw [Sup_eq_supr] <;> exact hf.le_map_supr2 _

theorem OrderIso.map_supr [CompleteLattice β] (f : α ≃o β) (x : ι → α) : f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <|
    f.Surjective.forall.2 fun x => by
      simp only [f.le_iff_le, supr_le_iff]

theorem OrderIso.map_Sup [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sup s) = ⨆ a ∈ s, f a := by
  simp only [Sup_eq_supr, OrderIso.map_supr]

theorem supr_comp_le {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨆ x, f (g x)) ≤ ⨆ y, f y :=
  supr_le_supr2 fun x => ⟨_, le_rfl⟩

theorem Monotone.supr_comp_eq [Preorderₓ β] {f : β → α} (hf : Monotone f) {s : ι → β} (hs : ∀ x, ∃ i, x ≤ s i) :
    (⨆ x, f (s x)) = ⨆ y, f y :=
  le_antisymmₓ (supr_comp_le _ _) (supr_le_supr2 fun x => (hs x).imp fun i hi => hf hi)

theorem Function.Surjective.supr_comp {α : Type _} [HasSupₓ α] {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → α) :
    (⨆ x, g (f x)) = ⨆ y, g y := by
  simp only [supr, hf.range_comp]

theorem supr_congr {α : Type _} [HasSupₓ α] {f : ι → α} {g : ι₂ → α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y := by
  convert h1.supr_comp g
  exact (funext h2).symm

-- TODO: finish doesn't do well here.
@[congr]
theorem supr_congr_Prop {α : Type _} [HasSupₓ α] {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : supr f₁ = supr f₂ := by
  have := propext pq
  subst this
  congr with x
  apply f

theorem infi_le (s : ι → α) (i : ι) : infi s ≤ s i :=
  Inf_le ⟨i, rfl⟩

@[ematch]
theorem infi_le' (s : ι → α) (i : ι) : infi s ≤ s i :=
  Inf_le ⟨i, rfl⟩

theorem infi_le_of_le (i : ι) (h : s i ≤ a) : infi s ≤ a :=
  le_transₓ (infi_le _ i) h

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem binfi_le {p : ι → Prop} {f : ∀ i hi : p i, α} (i : ι) (hi : p i) : (⨅ (i) (hi), f i hi) ≤ f i hi :=
  infi_le_of_le i <| infi_le (f i) hi

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem binfi_le_of_le {p : ι → Prop} {f : ∀ i hi : p i, α} (i : ι) (hi : p i) (h : f i hi ≤ a) :
    (⨅ (i) (hi), f i hi) ≤ a :=
  le_transₓ (binfi_le i hi) h

theorem le_infi (h : ∀ i, a ≤ s i) : a ≤ infi s :=
  le_Inf fun b ⟨i, Eq⟩ => Eq ▸ h i

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem le_binfi {p : ι → Prop} {f : ∀ i h : p i, α} (h : ∀ i hi, a ≤ f i hi) : a ≤ ⨅ (i) (hi), f i hi :=
  le_infi fun i => le_infi <| h i

theorem infi_le_binfi (p : ι → Prop) (f : ι → α) : (⨅ i, f i) ≤ ⨅ (i) (H : p i), f i :=
  le_binfi fun i hi => infi_le f i

theorem infi_le_infi (h : ∀ i, s i ≤ t i) : infi s ≤ infi t :=
  le_infi fun i => infi_le_of_le i (h i)

theorem infi_le_infi2 {t : ι₂ → α} (h : ∀ j, ∃ i, s i ≤ t j) : infi s ≤ infi t :=
  le_infi fun j => Exists.elim (h j) infi_le_of_le

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem binfi_le_binfi {p : ι → Prop} {f g : ∀ i h : p i, α} (h : ∀ i hi, f i hi ≤ g i hi) :
    (⨅ (i) (hi), f i hi) ≤ ⨅ (i) (hi), g i hi :=
  le_binfi fun i hi => le_transₓ (binfi_le i hi) (h i hi)

theorem infi_le_infi_const (h : ι₂ → ι) : (⨅ i : ι, a) ≤ ⨅ j : ι₂, a :=
  le_infi <| infi_le _ ∘ h

@[simp]
theorem le_infi_iff : a ≤ infi s ↔ ∀ i, a ≤ s i :=
  ⟨fun this : a ≤ infi s => fun i => le_transₓ this (infi_le _ _), le_infi⟩

theorem Inf_eq_infi {s : Set α} : inf s = ⨅ a ∈ s, a :=
  @Sup_eq_supr (OrderDual α) _ _

theorem Inf_eq_infi' {α} [HasInfₓ α] (s : Set α) : inf s = ⨅ a : s, a :=
  @Sup_eq_supr' (OrderDual α) _ _

theorem Monotone.map_infi_le [CompleteLattice β] {f : α → β} (hf : Monotone f) : f (infi s) ≤ ⨅ i, f (s i) :=
  le_infi fun i => hf <| infi_le _ _

theorem Monotone.map_infi2_le [CompleteLattice β] {f : α → β} (hf : Monotone f) {ι' : ι → Sort _} (s : ∀ i, ι' i → α) :
    f (⨅ (i) (h : ι' i), s i h) ≤ ⨅ (i) (h : ι' i), f (s i h) :=
  @Monotone.le_map_supr2 (OrderDual α) (OrderDual β) _ _ _ f hf.dual _ _

theorem Monotone.map_Inf_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) : f (inf s) ≤ ⨅ a ∈ s, f a :=
  by
  rw [Inf_eq_infi] <;> exact hf.map_infi2_le _

theorem OrderIso.map_infi [CompleteLattice β] (f : α ≃o β) (x : ι → α) : f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_supr f.dual _

theorem OrderIso.map_Inf [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (inf s) = ⨅ a ∈ s, f a :=
  OrderIso.map_Sup f.dual _

theorem le_infi_comp {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨅ y, f y) ≤ ⨅ x, f (g x) :=
  infi_le_infi2 fun x => ⟨_, le_rfl⟩

theorem Monotone.infi_comp_eq [Preorderₓ β] {f : β → α} (hf : Monotone f) {s : ι → β} (hs : ∀ x, ∃ i, s i ≤ x) :
    (⨅ x, f (s x)) = ⨅ y, f y :=
  le_antisymmₓ (infi_le_infi2 fun x => (hs x).imp fun i hi => hf hi) (le_infi_comp _ _)

theorem Function.Surjective.infi_comp {α : Type _} [HasInfₓ α] {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → α) :
    (⨅ x, g (f x)) = ⨅ y, g y :=
  @Function.Surjective.supr_comp _ _ (OrderDual α) _ f hf g

theorem infi_congr {α : Type _} [HasInfₓ α] {f : ι → α} {g : ι₂ → α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y :=
  @supr_congr _ _ (OrderDual α) _ _ _ h h1 h2

@[congr]
theorem infi_congr_Prop {α : Type _} [HasInfₓ α] {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : infi f₁ = infi f₂ :=
  @supr_congr_Prop (OrderDual α) _ p q f₁ f₂ pq f

theorem supr_const_le {x : α} : (⨆ h : ι, x) ≤ x :=
  supr_le fun _ => le_rfl

theorem le_infi_const {x : α} : x ≤ ⨅ h : ι, x :=
  le_infi fun _ => le_rfl

-- We will generalize this to conditionally complete lattices in `cinfi_const`.
theorem infi_const [Nonempty ι] {a : α} : (⨅ b : ι, a) = a := by
  rw [infi, range_const, Inf_singleton]

-- We will generalize this to conditionally complete lattices in `csupr_const`.
theorem supr_const [Nonempty ι] {a : α} : (⨆ b : ι, a) = a :=
  @infi_const (OrderDual α) _ _ _ _

@[simp]
theorem infi_top : (⨅ i : ι, ⊤ : α) = ⊤ :=
  top_unique <| le_infi fun i => le_rfl

@[simp]
theorem supr_bot : (⨆ i : ι, ⊥ : α) = ⊥ :=
  @infi_top (OrderDual α) _ _

@[simp]
theorem infi_eq_top : infi s = ⊤ ↔ ∀ i, s i = ⊤ :=
  Inf_eq_top.trans forall_range_iff

@[simp]
theorem supr_eq_bot : supr s = ⊥ ↔ ∀ i, s i = ⊥ :=
  Sup_eq_bot.trans forall_range_iff

@[simp]
theorem infi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  le_antisymmₓ (infi_le _ _) (le_infi fun h => le_rfl)

@[simp]
theorem infi_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨅ h : p, f h) = ⊤ :=
  le_antisymmₓ le_top <| le_infi fun h => (hp h).elim

@[simp]
theorem supr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  le_antisymmₓ (supr_le fun h => le_rfl) (le_supr _ _)

@[simp]
theorem supr_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨆ h : p, f h) = ⊥ :=
  le_antisymmₓ (supr_le fun h => (hp h).elim) bot_le

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `csupr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem supr_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b) (h₂ : ∀ w, w < b → ∃ i, w < f i) :
    (⨆ i : ι, f i) = b :=
  Sup_eq_of_forall_le_of_forall_lt_exists_gt (forall_range_iff.mpr h₁) fun w hw => exists_range_iff.mpr <| h₂ w hw

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `cinfi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem infi_eq_of_forall_ge_of_forall_gt_exists_lt {f : ι → α} (h₁ : ∀ i, b ≤ f i) (h₂ : ∀ w, b < w → ∃ i, f i < w) :
    (⨅ i : ι, f i) = b :=
  @supr_eq_of_forall_le_of_forall_lt_exists_gt (OrderDual α) _ _ _ ‹_› ‹_› ‹_›

theorem supr_eq_dif {p : Prop} [Decidable p] (a : p → α) : (⨆ h : p, a h) = if h : p then a h else ⊥ := by
  by_cases' p <;> simp [h]

theorem supr_eq_if {p : Prop} [Decidable p] (a : α) : (⨆ h : p, a) = if p then a else ⊥ :=
  supr_eq_dif fun _ => a

theorem infi_eq_dif {p : Prop} [Decidable p] (a : p → α) : (⨅ h : p, a h) = if h : p then a h else ⊤ :=
  @supr_eq_dif (OrderDual α) _ _ _ _

theorem infi_eq_if {p : Prop} [Decidable p] (a : α) : (⨅ h : p, a) = if p then a else ⊤ :=
  infi_eq_dif fun _ => a

-- TODO: should this be @[simp]?
theorem infi_comm {f : ι → ι₂ → α} : (⨅ i, ⨅ j, f i j) = ⨅ j, ⨅ i, f i j :=
  le_antisymmₓ (le_infi fun i => le_infi fun j => infi_le_of_le j <| infi_le _ i)
    (le_infi fun j => le_infi fun i => infi_le_of_le i <| infi_le _ j)

/- TODO: this is strange. In the proof below, we get exactly the desired
   among the equalities, but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/
-- TODO: should this be @[simp]?
theorem supr_comm {f : ι → ι₂ → α} : (⨆ i, ⨆ j, f i j) = ⨆ j, ⨆ i, f i j :=
  @infi_comm (OrderDual α) _ _ _ _

@[simp]
theorem infi_infi_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨅ x, ⨅ h : x = b, f x h) = f b rfl :=
  le_antisymmₓ (infi_le_of_le b <| infi_le _ rfl)
    (le_infi fun b' =>
      le_infi fun eq =>
        match b', Eq with
        | _, rfl => le_rfl)

@[simp]
theorem infi_infi_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨅ x, ⨅ h : b = x, f x h) = f b rfl :=
  le_antisymmₓ (infi_le_of_le b <| infi_le _ rfl)
    (le_infi fun b' =>
      le_infi fun eq =>
        match b', Eq with
        | _, rfl => le_rfl)

@[simp]
theorem supr_supr_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨆ x, ⨆ h : x = b, f x h) = f b rfl :=
  @infi_infi_eq_left (OrderDual α) _ _ _ _

@[simp]
theorem supr_supr_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨆ x, ⨆ h : b = x, f x h) = f b rfl :=
  @infi_infi_eq_right (OrderDual α) _ _ _ _

attribute [ematch] le_reflₓ

theorem infi_subtype {p : ι → Prop} {f : Subtype p → α} : (⨅ x, f x) = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymmₓ (le_infi fun i => le_infi fun this : p i => infi_le _ _)
    (le_infi fun ⟨i, h⟩ => infi_le_of_le i <| infi_le _ _)

theorem infi_subtype' {p : ι → Prop} {f : ∀ i, p i → α} : (⨅ (i) (h : p i), f i h) = ⨅ x : Subtype p, f x x.property :=
  (@infi_subtype _ _ _ p fun x => f x.val x.property).symm

theorem infi_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨅ i : s, f i) = ⨅ (t : ι) (H : t ∈ s), f t :=
  infi_subtype

theorem infi_inf_eq {f g : ι → α} : (⨅ x, f x⊓g x) = (⨅ x, f x)⊓⨅ x, g x :=
  le_antisymmₓ (le_inf (le_infi fun i => infi_le_of_le i inf_le_left) (le_infi fun i => infi_le_of_le i inf_le_right))
    (le_infi fun i => le_inf (inf_le_of_left_le <| infi_le _ _) (inf_le_of_right_le <| infi_le _ _))

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/
theorem infi_inf [h : Nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x)⊓a = ⨅ x, f x⊓a := by
  rw [infi_inf_eq, infi_const]

theorem inf_infi [Nonempty ι] {f : ι → α} {a : α} : (a⊓⨅ x, f x) = ⨅ x, a⊓f x := by
  rw [inf_comm, infi_inf] <;> simp [inf_comm]

theorem binfi_inf {p : ι → Prop} {f : ∀ i hi : p i, α} {a : α} (h : ∃ i, p i) :
    (⨅ (i) (h : p i), f i h)⊓a = ⨅ (i) (h : p i), f i h⊓a := by
  have : Nonempty { i // p i } :=
      let ⟨i, hi⟩ := h
      ⟨⟨i, hi⟩⟩ <;>
    rw [infi_subtype', infi_subtype', infi_inf]

theorem inf_binfi {p : ι → Prop} {f : ∀ i hi : p i, α} {a : α} (h : ∃ i, p i) :
    (a⊓⨅ (i) (h : p i), f i h) = ⨅ (i) (h : p i), a⊓f i h := by
  simpa only [inf_comm] using binfi_inf h

theorem supr_sup_eq {f g : ι → α} : (⨆ x, f x⊔g x) = (⨆ x, f x)⊔⨆ x, g x :=
  @infi_inf_eq (OrderDual α) ι _ _ _

theorem supr_sup [h : Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x)⊔a = ⨆ x, f x⊔a :=
  @infi_inf (OrderDual α) _ _ _ _ _

theorem sup_supr [Nonempty ι] {f : ι → α} {a : α} : (a⊔⨆ x, f x) = ⨆ x, a⊔f x :=
  @inf_infi (OrderDual α) _ _ _ _ _

/-! ### `supr` and `infi` under `Prop` -/


@[simp]
theorem infi_false {s : False → α} : infi s = ⊤ :=
  le_antisymmₓ le_top (le_infi fun i => False.elim i)

@[simp]
theorem supr_false {s : False → α} : supr s = ⊥ :=
  le_antisymmₓ (supr_le fun i => False.elim i) bot_le

theorem infi_true {s : True → α} : infi s = s trivialₓ :=
  infi_pos trivialₓ

theorem supr_true {s : True → α} : supr s = s trivialₓ :=
  supr_pos trivialₓ

@[simp]
theorem infi_exists {p : ι → Prop} {f : Exists p → α} : (⨅ x, f x) = ⨅ i, ⨅ h : p i, f ⟨i, h⟩ :=
  le_antisymmₓ (le_infi fun i => le_infi fun this : p i => infi_le _ _)
    (le_infi fun ⟨i, h⟩ => infi_le_of_le i <| infi_le _ _)

@[simp]
theorem supr_exists {p : ι → Prop} {f : Exists p → α} : (⨆ x, f x) = ⨆ i, ⨆ h : p i, f ⟨i, h⟩ :=
  @infi_exists (OrderDual α) _ _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (h₁ h₂)
theorem infi_and {p q : Prop} {s : p ∧ q → α} : infi s = ⨅ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymmₓ (le_infi fun i => le_infi fun j => infi_le _ _) (le_infi fun ⟨i, h⟩ => infi_le_of_le i <| infi_le _ _)

/-- The symmetric case of `infi_and`, useful for rewriting into a infimum over a conjunction -/
theorem infi_and' {p q : Prop} {s : p → q → α} : (⨅ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨅ h : p ∧ q, s h.1 h.2 := by
  symm
  exact infi_and

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (h₁ h₂)
theorem supr_and {p q : Prop} {s : p ∧ q → α} : supr s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  @infi_and (OrderDual α) _ _ _ _

/-- The symmetric case of `supr_and`, useful for rewriting into a supremum over a conjunction -/
theorem supr_and' {p q : Prop} {s : p → q → α} : (⨆ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨆ h : p ∧ q, s h.1 h.2 := by
  symm
  exact supr_and

theorem infi_or {p q : Prop} {s : p ∨ q → α} : infi s = (⨅ h : p, s (Or.inl h))⊓⨅ h : q, s (Or.inr h) :=
  le_antisymmₓ (le_inf (infi_le_infi2 fun j => ⟨_, le_rfl⟩) (infi_le_infi2 fun j => ⟨_, le_rfl⟩))
    (le_infi fun i =>
      match i with
      | Or.inl i => inf_le_of_left_le <| infi_le _ _
      | Or.inr j => inf_le_of_right_le <| infi_le _ _)

theorem supr_or {p q : Prop} {s : p ∨ q → α} : (⨆ x, s x) = (⨆ i, s (Or.inl i))⊔⨆ j, s (Or.inr j) :=
  @infi_or (OrderDual α) _ _ _ _

section

variable (p : ι → Prop) [DecidablePred p]

theorem supr_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨆ i, if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h)⊔⨆ (i) (h : ¬p i), g i h := by
  rw [← supr_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]

theorem supr_ite (f g : ι → α) : (⨆ i, if p i then f i else g i) = (⨆ (i) (h : p i), f i)⊔⨆ (i) (h : ¬p i), g i :=
  supr_dite _ _ _

theorem infi_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨅ i, if h : p i then f i h else g i h) = (⨅ (i) (h : p i), f i h)⊓⨅ (i) (h : ¬p i), g i h :=
  supr_dite p (show ∀ i, p i → OrderDual α from f) g

theorem infi_ite (f g : ι → α) : (⨅ i, if p i then f i else g i) = (⨅ (i) (h : p i), f i)⊓⨅ (i) (h : ¬p i), g i :=
  infi_dite _ _ _

end

theorem Sup_range {α : Type _} [HasSupₓ α] {f : ι → α} : sup (Range f) = supr f :=
  rfl

theorem Inf_range {α : Type _} [HasInfₓ α] {f : ι → α} : inf (Range f) = infi f :=
  rfl

theorem supr_range' {α} [HasSupₓ α] (g : β → α) (f : ι → β) : (⨆ b : Range f, g b) = ⨆ i, g (f i) := by
  rw [supr, supr, ← image_eq_range, ← range_comp]

theorem infi_range' {α} [HasInfₓ α] (g : β → α) (f : ι → β) : (⨅ b : Range f, g b) = ⨅ i, g (f i) :=
  @supr_range' _ _ (OrderDual α) _ _ _

theorem infi_range {g : β → α} {f : ι → β} : (⨅ b ∈ Range f, g b) = ⨅ i, g (f i) := by
  rw [← infi_subtype'', infi_range']

theorem supr_range {g : β → α} {f : ι → β} : (⨆ b ∈ Range f, g b) = ⨆ i, g (f i) :=
  @infi_range (OrderDual α) _ _ _ _ _

theorem Inf_image' {α} [HasInfₓ α] {s : Set β} {f : β → α} : inf (f '' s) = ⨅ a : s, f a := by
  rw [infi, image_eq_range]

theorem Sup_image' {α} [HasSupₓ α] {s : Set β} {f : β → α} : sup (f '' s) = ⨆ a : s, f a :=
  @Inf_image' _ (OrderDual α) _ _ _

theorem Inf_image {s : Set β} {f : β → α} : inf (f '' s) = ⨅ a ∈ s, f a := by
  rw [← infi_subtype'', Inf_image']

theorem Sup_image {s : Set β} {f : β → α} : sup (f '' s) = ⨆ a ∈ s, f a :=
  @Inf_image (OrderDual α) _ _ _ _

/-
### supr and infi under set constructions
-/
theorem infi_emptyset {f : β → α} : (⨅ x ∈ (∅ : Set β), f x) = ⊤ := by
  simp

theorem supr_emptyset {f : β → α} : (⨆ x ∈ (∅ : Set β), f x) = ⊥ := by
  simp

theorem infi_univ {f : β → α} : (⨅ x ∈ (Univ : Set β), f x) = ⨅ x, f x := by
  simp

theorem supr_univ {f : β → α} : (⨆ x ∈ (Univ : Set β), f x) = ⨆ x, f x := by
  simp

theorem infi_union {f : β → α} {s t : Set β} : (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x)⊓⨅ x ∈ t, f x := by
  simp only [← infi_inf_eq, infi_or]

theorem infi_split (f : β → α) (p : β → Prop) : (⨅ i, f i) = (⨅ (i) (h : p i), f i)⊓⨅ (i) (h : ¬p i), f i := by
  simpa [Classical.em] using @infi_union _ _ _ f { i | p i } { i | ¬p i }

theorem infi_split_single (f : β → α) (i₀ : β) : (⨅ i, f i) = f i₀⊓⨅ (i) (h : i ≠ i₀), f i := by
  convert infi_split _ _ <;> simp

theorem infi_le_infi_of_subset {f : β → α} {s t : Set β} (h : s ⊆ t) : (⨅ x ∈ t, f x) ≤ ⨅ x ∈ s, f x := by
  rw [(union_eq_self_of_subset_left h).symm, infi_union] <;> exact inf_le_left

theorem supr_union {f : β → α} {s t : Set β} : (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x)⊔⨆ x ∈ t, f x :=
  @infi_union (OrderDual α) _ _ _ _ _

theorem supr_split (f : β → α) (p : β → Prop) : (⨆ i, f i) = (⨆ (i) (h : p i), f i)⊔⨆ (i) (h : ¬p i), f i :=
  @infi_split (OrderDual α) _ _ _ _

theorem supr_split_single (f : β → α) (i₀ : β) : (⨆ i, f i) = f i₀⊔⨆ (i) (h : i ≠ i₀), f i :=
  @infi_split_single (OrderDual α) _ _ _ _

theorem supr_le_supr_of_subset {f : β → α} {s t : Set β} (h : s ⊆ t) : (⨆ x ∈ s, f x) ≤ ⨆ x ∈ t, f x :=
  @infi_le_infi_of_subset (OrderDual α) _ _ _ _ _ h

theorem infi_insert {f : β → α} {s : Set β} {b : β} : (⨅ x ∈ insert b s, f x) = f b⊓⨅ x ∈ s, f x :=
  Eq.trans infi_union <| congr_argₓ (fun x : α => x⊓⨅ x ∈ s, f x) infi_infi_eq_left

theorem supr_insert {f : β → α} {s : Set β} {b : β} : (⨆ x ∈ insert b s, f x) = f b⊔⨆ x ∈ s, f x :=
  Eq.trans supr_union <| congr_argₓ (fun x : α => x⊔⨆ x ∈ s, f x) supr_supr_eq_left

theorem infi_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : Set β), f x) = f b := by
  simp

theorem infi_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : Set β), f x) = f a⊓f b := by
  rw [infi_insert, infi_singleton]

theorem supr_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : Set β), f x) = f b :=
  @infi_singleton (OrderDual α) _ _ _ _

theorem supr_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : Set β), f x) = f a⊔f b := by
  rw [supr_insert, supr_singleton]

theorem infi_image {γ} {f : β → γ} {g : γ → α} {t : Set β} : (⨅ c ∈ f '' t, g c) = ⨅ b ∈ t, g (f b) := by
  rw [← Inf_image, ← Inf_image, ← image_comp]

theorem supr_image {γ} {f : β → γ} {g : γ → α} {t : Set β} : (⨆ c ∈ f '' t, g c) = ⨆ b ∈ t, g (f b) :=
  @infi_image (OrderDual α) _ _ _ _ _ _

theorem supr_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) : (⨆ j, extendₓ e f ⊥ j) = ⨆ i, f i := by
  rw [supr_split _ fun j => ∃ i, e i = j]
  simp (config := { contextual := true })[extend_apply he, extend_apply', @supr_comm _ β ι]

/-!
### `supr` and `infi` under `Type`
-/


theorem supr_of_empty' {α ι} [HasSupₓ α] [IsEmpty ι] (f : ι → α) : supr f = sup (∅ : Set α) :=
  congr_argₓ sup (range_eq_empty f)

theorem supr_of_empty [IsEmpty ι] (f : ι → α) : supr f = ⊥ :=
  (supr_of_empty' f).trans Sup_empty

theorem infi_of_empty' {α ι} [HasInfₓ α] [IsEmpty ι] (f : ι → α) : infi f = inf (∅ : Set α) :=
  congr_argₓ inf (range_eq_empty f)

theorem infi_of_empty [IsEmpty ι] (f : ι → α) : infi f = ⊤ :=
  @supr_of_empty (OrderDual α) _ _ _ f

theorem supr_bool_eq {f : Bool → α} : (⨆ b : Bool, f b) = f true⊔f false := by
  rw [supr, Bool.range_eq, Sup_pair, sup_comm]

theorem infi_bool_eq {f : Bool → α} : (⨅ b : Bool, f b) = f true⊓f false :=
  @supr_bool_eq (OrderDual α) _ _

theorem sup_eq_supr (x y : α) : x⊔y = ⨆ b : Bool, cond b x y := by
  rw [supr_bool_eq, Bool.cond_tt, Bool.cond_ff]

theorem inf_eq_infi (x y : α) : x⊓y = ⨅ b : Bool, cond b x y :=
  @sup_eq_supr (OrderDual α) _ _ _

theorem is_glb_binfi {s : Set β} {f : β → α} : IsGlb (f '' s) (⨅ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, infi_subtype'] using @is_glb_infi α s _ (f ∘ coe)

theorem supr_subtype {p : ι → Prop} {f : Subtype p → α} : (⨆ x, f x) = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  @infi_subtype (OrderDual α) _ _ _ _

theorem supr_subtype' {p : ι → Prop} {f : ∀ i, p i → α} : (⨆ (i) (h : p i), f i h) = ⨆ x : Subtype p, f x x.property :=
  (@supr_subtype _ _ _ p fun x => f x.val x.property).symm

theorem supr_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨆ i : s, f i) = ⨆ (t : ι) (H : t ∈ s), f t :=
  supr_subtype

theorem is_lub_bsupr {s : Set β} {f : β → α} : IsLub (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, supr_subtype'] using @is_lub_supr α s _ (f ∘ coe)

theorem infi_sigma {p : β → Type _} {f : Sigma p → α} : (⨅ x, f x) = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  eq_of_forall_le_iff fun c => by
    simp only [le_infi_iff, Sigma.forall]

theorem supr_sigma {p : β → Type _} {f : Sigma p → α} : (⨆ x, f x) = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  @infi_sigma (OrderDual α) _ _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem infi_prod {γ : Type _} {f : β × γ → α} : (⨅ x, f x) = ⨅ (i) (j), f (i, j) :=
  eq_of_forall_le_iff fun c => by
    simp only [le_infi_iff, Prod.forall]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem supr_prod {γ : Type _} {f : β × γ → α} : (⨆ x, f x) = ⨆ (i) (j), f (i, j) :=
  @infi_prod (OrderDual α) _ _ _ _

theorem infi_sum {γ : Type _} {f : Sum β γ → α} : (⨅ x, f x) = (⨅ i, f (Sum.inl i))⊓⨅ j, f (Sum.inr j) :=
  eq_of_forall_le_iff fun c => by
    simp only [le_inf_iff, le_infi_iff, Sum.forall]

theorem supr_sum {γ : Type _} {f : Sum β γ → α} : (⨆ x, f x) = (⨆ i, f (Sum.inl i))⊔⨆ j, f (Sum.inr j) :=
  @infi_sum (OrderDual α) _ _ _ _

theorem supr_option (f : Option β → α) : (⨆ o, f o) = f none⊔⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by
    simp only [supr_le_iff, sup_le_iff, Option.forall]

theorem infi_option (f : Option β → α) : (⨅ o, f o) = f none⊓⨅ b, f (Option.some b) :=
  @supr_option (OrderDual α) _ _ _

/-- A version of `supr_option` useful for rewriting right-to-left. -/
theorem supr_option_elim (a : α) (f : β → α) : (⨆ o : Option β, o.elim a f) = a⊔⨆ b, f b := by
  simp [supr_option]

/-- A version of `infi_option` useful for rewriting right-to-left. -/
theorem infi_option_elim (a : α) (f : β → α) : (⨅ o : Option β, o.elim a f) = a⊓⨅ b, f b :=
  @supr_option_elim (OrderDual α) _ _ _ _

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
theorem supr_ne_bot_subtype (f : ι → α) : (⨆ i : { i // f i ≠ ⊥ }, f i) = ⨆ i, f i := by
  by_cases' htriv : ∀ i, f i = ⊥
  · simp only [htriv, supr_bot]
    
  refine' le_antisymmₓ (supr_comp_le f _) (supr_le_supr2 _)
  intro i
  by_cases' hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
    
  · exact ⟨⟨i, hi⟩, rfl.le⟩
    

/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
theorem infi_ne_top_subtype (f : ι → α) : (⨅ i : { i // f i ≠ ⊤ }, f i) = ⨅ i, f i :=
  @supr_ne_bot_subtype (OrderDual α) ι _ f

/-!
### `supr` and `infi` under `ℕ`
-/


theorem supr_ge_eq_supr_nat_add {u : ℕ → α} (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) := by
  apply le_antisymmₓ <;> simp only [supr_le_iff]
  · exact fun i hi =>
      le_Sup
        ⟨i - n, by
          dsimp only
          rw [tsub_add_cancel_of_le hi]⟩
    
  · exact fun i => le_Sup ⟨i + n, supr_pos (Nat.le_add_leftₓ _ _)⟩
    

theorem infi_ge_eq_infi_nat_add {u : ℕ → α} (n : ℕ) : (⨅ i ≥ n, u i) = ⨅ i, u (i + n) :=
  @supr_ge_eq_supr_nat_add (OrderDual α) _ _ _

theorem Monotone.supr_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : (⨆ n, f (n + k)) = ⨆ n, f n :=
  le_antisymmₓ (supr_le fun i => le_rfl.trans (le_supr _ (i + k))) (supr_le_supr fun i => hf (Nat.le_add_rightₓ i k))

@[simp]
theorem supr_infi_ge_nat_add (f : ℕ → α) (k : ℕ) : (⨆ n, ⨅ i ≥ n, f (i + k)) = ⨆ n, ⨅ i ≥ n, f i := by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m hnm =>
    le_infi fun i => (infi_le _ i).trans (le_infi fun h => infi_le _ (hnm.trans h))
  rw [← Monotone.supr_nat_add hf k]
  · simp_rw [infi_ge_eq_infi_nat_add, ← Nat.add_assoc]
    

theorem sup_supr_nat_succ (u : ℕ → α) : (u 0⊔⨆ i, u (i + 1)) = ⨆ i, u i := by
  refine' eq_of_forall_ge_iff fun c => _
  simp only [sup_le_iff, supr_le_iff]
  refine' ⟨fun h => _, fun h => ⟨h _, fun i => h _⟩⟩
  rintro (_ | i)
  exacts[h.1, h.2 i]

theorem inf_infi_nat_succ (u : ℕ → α) : (u 0⊓⨅ i, u (i + 1)) = ⨅ i, u i :=
  @sup_supr_nat_succ (OrderDual α) _ u

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

theorem supr_eq_top (f : ι → α) : supr f = ⊤ ↔ ∀, ∀ b < ⊤, ∀, ∃ i, b < f i := by
  simp only [← Sup_range, Sup_eq_top, Set.exists_range_iff]

theorem infi_eq_bot (f : ι → α) : infi f = ⊥ ↔ ∀, ∀ b > ⊥, ∀, ∃ i, f i < b := by
  simp only [← Inf_range, Inf_eq_bot, Set.exists_range_iff]

end CompleteLinearOrder

/-!
### Instances
-/


instance Prop.completeLattice : CompleteLattice Prop :=
  { Prop.boundedOrder, Prop.distribLattice with sup := fun s => ∃ a ∈ s, a, le_Sup := fun s a h p => ⟨a, h, p⟩,
    Sup_le := fun s a h ⟨b, h', p⟩ => h b h' p, inf := fun s => ∀ a : Prop, a ∈ s → a, Inf_le := fun s a h p => p a h,
    le_Inf := fun s a h p b hb => h b hb p }

@[simp]
theorem Inf_Prop_eq {s : Set Prop} : inf s = ∀, ∀ p ∈ s, ∀, p :=
  rfl

@[simp]
theorem Sup_Prop_eq {s : Set Prop} : sup s = ∃ p ∈ s, p :=
  rfl

@[simp]
theorem infi_Prop_eq {ι : Sort _} {p : ι → Prop} : (⨅ i, p i) = ∀ i, p i :=
  le_antisymmₓ (fun h i => h _ ⟨i, rfl⟩) fun h p ⟨i, Eq⟩ => Eq ▸ h i

@[simp]
theorem supr_Prop_eq {ι : Sort _} {p : ι → Prop} : (⨆ i, p i) = ∃ i, p i :=
  le_antisymmₓ (fun ⟨q, ⟨i, (Eq : p i = q)⟩, hq⟩ => ⟨i, Eq.symm ▸ hq⟩) fun ⟨i, hi⟩ => ⟨p i, ⟨i, rfl⟩, hi⟩

instance Pi.hasSupₓ {α : Type _} {β : α → Type _} [∀ i, HasSupₓ (β i)] : HasSupₓ (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩

instance Pi.hasInfₓ {α : Type _} {β : α → Type _} [∀ i, HasInfₓ (β i)] : HasInfₓ (∀ i, β i) :=
  ⟨fun s i => ⨅ f : s, (f : ∀ i, β i) i⟩

instance Pi.completeLattice {α : Type _} {β : α → Type _} [∀ i, CompleteLattice (β i)] : CompleteLattice (∀ i, β i) :=
  { Pi.boundedOrder, Pi.lattice with sup := sup, inf := inf,
    le_Sup := fun s f hf i => le_supr (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩,
    Inf_le := fun s f hf i => infi_le (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩,
    Sup_le := fun s f hf i => supr_le fun g => hf g g.2 i, le_Inf := fun s f hf i => le_infi fun g => hf g g.2 i }

theorem Inf_apply {α : Type _} {β : α → Type _} [∀ i, HasInfₓ (β i)] {s : Set (∀ a, β a)} {a : α} :
    (inf s) a = ⨅ f : s, (f : ∀ a, β a) a :=
  rfl

@[simp]
theorem infi_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, HasInfₓ (β i)] {f : ι → ∀ a, β a} {a : α} :
    (⨅ i, f i) a = ⨅ i, f i a := by
  rw [infi, Inf_apply, infi, infi, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ← range_comp]

theorem Sup_apply {α : Type _} {β : α → Type _} [∀ i, HasSupₓ (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sup s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl

theorem unary_relation_Sup_iff {α : Type _} (s : Set (α → Prop)) {a : α} : sup s a ↔ ∃ r : α → Prop, r ∈ s ∧ r a := by
  change (∃ _, _) ↔ _
  simp [-eq_iff_iff]

theorem binary_relation_Sup_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sup s a b ↔ ∃ r : α → β → Prop, r ∈ s ∧ r a b := by
  change (∃ _, _) ↔ _
  simp [-eq_iff_iff]

@[simp]
theorem supr_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, HasSupₓ (β i)] {f : ι → ∀ a, β a} {a : α} :
    (⨆ i, f i) a = ⨆ i, f i a :=
  @infi_apply α (fun i => OrderDual (β i)) _ _ f a

section CompleteLattice

variable [Preorderₓ α] [CompleteLattice β]

theorem monotone_Sup_of_monotone {s : Set (α → β)} (m_s : ∀, ∀ f ∈ s, ∀, Monotone f) : Monotone (sup s) := fun x y h =>
  supr_le fun f => le_supr_of_le f <| m_s f f.2 h

theorem monotone_Inf_of_monotone {s : Set (α → β)} (m_s : ∀, ∀ f ∈ s, ∀, Monotone f) : Monotone (inf s) := fun x y h =>
  le_infi fun f => infi_le_of_le f <| m_s f f.2 h

end CompleteLattice

namespace Prod

variable (α β)

instance [HasInfₓ α] [HasInfₓ β] : HasInfₓ (α × β) :=
  ⟨fun s => (inf (Prod.fst '' s), inf (Prod.snd '' s))⟩

instance [HasSupₓ α] [HasSupₓ β] : HasSupₓ (α × β) :=
  ⟨fun s => (sup (Prod.fst '' s), sup (Prod.snd '' s))⟩

instance [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.hasSupₓ α β, Prod.hasInfₓ α β with
    le_Sup := fun s p hab => ⟨le_Sup <| mem_image_of_mem _ hab, le_Sup <| mem_image_of_mem _ hab⟩,
    Sup_le := fun s p h =>
      ⟨Sup_le <| ball_image_of_ball fun p hp => (h p hp).1, Sup_le <| ball_image_of_ball fun p hp => (h p hp).2⟩,
    Inf_le := fun s p hab => ⟨Inf_le <| mem_image_of_mem _ hab, Inf_le <| mem_image_of_mem _ hab⟩,
    le_Inf := fun s p h =>
      ⟨le_Inf <| ball_image_of_ball fun p hp => (h p hp).1, le_Inf <| ball_image_of_ball fun p hp => (h p hp).2⟩ }

end Prod

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/-- This is a weaker version of `sup_Inf_eq` -/
theorem sup_Inf_le_infi_sup : a⊔inf s ≤ ⨅ b ∈ s, a⊔b :=
  le_infi fun i => le_infi fun h => sup_le_sup_left (Inf_le h) _

/-- This is a weaker version of `Inf_sup_eq` -/
theorem Inf_sup_le_infi_sup : inf s⊔a ≤ ⨅ b ∈ s, b⊔a :=
  le_infi fun i => le_infi fun h => sup_le_sup_right (Inf_le h) _

/-- This is a weaker version of `inf_Sup_eq` -/
theorem supr_inf_le_inf_Sup : (⨆ b ∈ s, a⊓b) ≤ a⊓sup s :=
  supr_le fun i => supr_le fun h => inf_le_inf_left _ (le_Sup h)

/-- This is a weaker version of `Sup_inf_eq` -/
theorem supr_inf_le_Sup_inf : (⨆ b ∈ s, b⊓a) ≤ sup s⊓a :=
  supr_le fun i => supr_le fun h => inf_le_inf_right _ (le_Sup h)

theorem disjoint_Sup_left {a : Set α} {b : α} (d : Disjoint (sup a) b) {i} (hi : i ∈ a) : Disjoint i b :=
  (supr_le_iff.mp (supr_le_iff.mp (supr_inf_le_Sup_inf.trans (d : _)) i : _) hi : _)

theorem disjoint_Sup_right {a : Set α} {b : α} (d : Disjoint b (sup a)) {i} (hi : i ∈ a) : Disjoint b i :=
  (supr_le_iff.mp (supr_le_iff.mp (supr_inf_le_inf_Sup.trans (d : _)) i : _) hi : _)

end CompleteLattice

/-- Pullback a `complete_lattice` along an injection. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.completeLattice [HasSup α] [HasInf α] [HasSupₓ α] [HasInfₓ α] [HasTop α] [HasBot α]
    [CompleteLattice β] (f : α → β) (hf : Function.Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_Sup : ∀ s, f (sup s) = sup (f '' s))
    (map_Inf : ∀ s, f (inf s) = inf (f '' s)) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α :=
  { -- we cannot use bounded_order.lift here as the `has_le` instance doesn't exist yet
        hf.Lattice
      f map_sup map_inf with
    sup := sup, le_Sup := fun s a h => (le_Sup <| mem_image_of_mem f h).trans (map_Sup _).Ge,
    Sup_le := fun s a h => (map_Sup _).le.trans <| Sup_le <| Set.ball_image_of_ball <| h, inf := inf,
    Inf_le := fun s a h => (map_Inf _).le.trans <| Inf_le <| mem_image_of_mem f h,
    le_Inf := fun s a h => (le_Inf <| Set.ball_image_of_ball <| h).trans (map_Inf _).Ge, top := ⊤,
    le_top := fun a => (@le_top β _ _ _).trans map_top.Ge, bot := ⊥, bot_le := fun a => map_bot.le.trans bot_le }

/-! ### Supremum independence-/


namespace CompleteLattice

variable [CompleteLattice α]

/-- An independent set of elements in a complete lattice is one in which every element is disjoint
  from the `Sup` of the rest. -/
def SetIndependent (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint a (sup (s \ {a}))

variable {s : Set α} (hs : SetIndependent s)

@[simp]
theorem set_independent_empty : SetIndependent (∅ : Set α) := fun x hx => (Set.not_mem_empty x hx).elim

theorem SetIndependent.mono {t : Set α} (hst : t ⊆ s) : SetIndependent t := fun a ha =>
  (hs (hst ha)).mono_right (Sup_le_Sup (diff_subset_diff_left hst))

/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem SetIndependent.disjoint {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : x ≠ y) : Disjoint x y :=
  disjoint_Sup_right (hs hx)
    ((mem_diff y).mpr
      ⟨hy, by
        simp [h.symm]⟩)

include hs

/-- If the elements of a set are independent, then any element is disjoint from the `Sup` of some
subset of the rest. -/
theorem SetIndependent.disjoint_Sup {x : α} {y : Set α} (hx : x ∈ s) (hy : y ⊆ s) (hxy : x ∉ y) : Disjoint x (sup y) :=
  by
  have := (hs.mono <| insert_subset.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_diff_of_mem _ (mem_singleton _), diff_singleton_eq_self hxy] at this
  exact this

omit hs

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (j «expr ≠ » i)
/-- An independent indexed family of elements in a complete lattice is one in which every element
  is disjoint from the `supr` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this sense if
  and only the natural map from the direct sum of the submodules to the module is injective. -/
def Independent {ι : Sort _} {α : Type _} [CompleteLattice α] (t : ι → α) : Prop :=
  ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j)

theorem set_independent_iff {α : Type _} [CompleteLattice α] (s : Set α) :
    SetIndependent s ↔ Independent (coe : s → α) := by
  simp_rw [independent, set_independent, SetCoe.forall, Sup_eq_supr]
  refine' forall₂_congrₓ fun a ha => _
  congr 2
  convert supr_subtype.symm
  simp [supr_and]

variable {t : ι → α} (ht : Independent t)

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (j «expr ≠ » i)
theorem independent_def : Independent t ↔ ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j) :=
  Iff.rfl

theorem independent_def' {ι : Type _} {t : ι → α} : Independent t ↔ ∀ i, Disjoint (t i) (sup (t '' { j | j ≠ i })) := by
  simp_rw [Sup_image]
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (j «expr ≠ » i)
theorem independent_def'' {ι : Type _} {t : ι → α} :
    Independent t ↔ ∀ i, Disjoint (t i) (sup { a | ∃ (j : _)(_ : j ≠ i), t j = a }) := by
  rw [independent_def']
  tidy

@[simp]
theorem independent_empty (t : Empty → α) : Independent t :=
  fun.

@[simp]
theorem independent_pempty (t : Pempty → α) : Independent t :=
  fun.

/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem Independent.disjoint {x y : ι} (h : x ≠ y) : Disjoint (t x) (t y) :=
  disjoint_Sup_right (ht x)
    ⟨y, by
      simp [h.symm]⟩

theorem Independent.mono {ι : Type _} {α : Type _} [CompleteLattice α] {s t : ι → α} (hs : Independent s)
    (hst : t ≤ s) : Independent t := fun i => (hs i).mono (hst i) (supr_le_supr fun j => supr_le_supr fun _ => hst j)

/-- Composing an independent indexed family with an injective function on the index results in
another indepedendent indexed family. -/
theorem Independent.comp {ι ι' : Sort _} {α : Type _} [CompleteLattice α] {s : ι → α} (hs : Independent s) (f : ι' → ι)
    (hf : Function.Injective f) : Independent (s ∘ f) := fun i =>
  (hs (f i)).mono_right
    (by
      refine' (supr_le_supr fun i => _).trans (supr_comp_le _ f)
      exact supr_le_supr_const hf.ne)

/-- Composing an indepedent indexed family with an order isomorphism on the elements results in
another indepedendent indexed family. -/
theorem Independent.map_order_iso {ι : Sort _} {α β : Type _} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β)
    {a : ι → α} (ha : Independent a) : Independent (f ∘ a) := fun i =>
  ((ha i).map_order_iso f).mono_right (f.Monotone.le_map_supr2 _)

@[simp]
theorem independent_map_order_iso_iff {ι : Sort _} {α β : Type _} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β)
    {a : ι → α} : Independent (f ∘ a) ↔ Independent a :=
  ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_argₓ (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_order_iso f.symm,
    fun h => h.map_order_iso f⟩

/-- If the elements of a set are independent, then any element is disjoint from the `supr` of some
subset of the rest. -/
theorem Independent.disjoint_bsupr {ι : Type _} {α : Type _} [CompleteLattice α] {t : ι → α} (ht : Independent t)
    {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ i ∈ y, t i) :=
  Disjoint.mono_right (bsupr_le_bsupr' fun i hi => (ne_of_mem_of_not_mem hi hx : _)) (ht x)

end CompleteLattice

