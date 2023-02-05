/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot

! This file was ported from Lean 3 source module order.filter.bases
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Prod.Pprod
import Mathbin.Data.Set.Countable
import Mathbin.Order.Filter.Prod

/-!
# Filter bases

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A filter basis `B : filter_basis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection. Compared to filters, filter bases do not require that any set containing
an element of `B` belongs to `B`.
A filter basis `B` can be used to construct `B.filter : filter α` such that a set belongs
to `B.filter` if and only if it contains an element of `B`.

Given an indexing type `ι`, a predicate `p : ι → Prop`, and a map `s : ι → set α`,
the proposition `h : filter.is_basis p s` makes sure the range of `s` bounded by `p`
(ie. `s '' set_of p`) defines a filter basis `h.filter_basis`.

If one already has a filter `l` on `α`, `filter.has_basis l p s` (where `p : ι → Prop`
and `s : ι → set α` as above) means that a set belongs to `l` if and
only if it contains some `s i` with `p i`. It implies `h : filter.is_basis p s`, and
`l = h.filter_basis.filter`. The point of this definition is that checking statements
involving elements of `l` often reduces to checking them on the basis elements.

We define a function `has_basis.index (h : filter.has_basis l p s) (t) (ht : t ∈ l)` that returns
some index `i` such that `p i` and `s i ⊆ t`. This function can be useful to avoid manual
destruction of `h.mem_iff.mpr ht` using `cases` or `let`.

This file also introduces more restricted classes of bases, involving monotonicity or
countability. In particular, for `l : filter α`, `l.is_countably_generated` means
there is a countable set of sets which generates `s`. This is reformulated in term of bases,
and consequences are derived.

## Main statements

* `has_basis.mem_iff`, `has_basis.mem_of_superset`, `has_basis.mem_of_mem` : restate `t ∈ f`
  in terms of a basis;
* `basis_sets` : all sets of a filter form a basis;
* `has_basis.inf`, `has_basis.inf_principal`, `has_basis.prod`, `has_basis.prod_self`,
  `has_basis.map`, `has_basis.comap` : combinators to construct filters of `l ⊓ l'`,
  `l ⊓ 𝓟 t`, `l ×ᶠ l'`, `l ×ᶠ l`, `l.map f`, `l.comap f` respectively;
* `has_basis.le_iff`, `has_basis.ge_iff`, has_basis.le_basis_iff` : restate `l ≤ l'` in terms
  of bases.
* `has_basis.tendsto_right_iff`, `has_basis.tendsto_left_iff`, `has_basis.tendsto_iff` : restate
  `tendsto f l l'` in terms of bases.
* `is_countably_generated_iff_exists_antitone_basis` : proves a filter is
  countably generated if and only if it admits a basis parametrized by a
  decreasing sequence of sets indexed by `ℕ`.
* `tendsto_iff_seq_tendsto ` : an abstract version of "sequentially continuous implies continuous".

## Implementation notes

As with `Union`/`bUnion`/`sUnion`, there are three different approaches to filter bases:

* `has_basis l s`, `s : set (set α)`;
* `has_basis l s`, `s : ι → set α`;
* `has_basis l p s`, `p : ι → Prop`, `s : ι → set α`.

We use the latter one because, e.g., `𝓝 x` in an `emetric_space` or in a `metric_space` has a basis
of this form. The other two can be emulated using `s = id` or `p = λ _, true`.

With this approach sometimes one needs to `simp` the statement provided by the `has_basis`
machinery, e.g., `simp only [exists_prop, true_and]` or `simp only [forall_const]` can help
with the case `p = λ _, true`.
-/


open Set Filter

open Filter Classical

section Sort

variable {α β γ : Type _} {ι ι' : Sort _}

#print FilterBasis /-
/-- A filter basis `B` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure FilterBasis (α : Type _) where
  sets : Set (Set α)
  Nonempty : sets.Nonempty
  inter_sets {x y} : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y
#align filter_basis FilterBasis
-/

#print FilterBasis.nonempty_sets /-
instance FilterBasis.nonempty_sets (B : FilterBasis α) : Nonempty B.sets :=
  B.Nonempty.to_subtype
#align filter_basis.nonempty_sets FilterBasis.nonempty_sets
-/

/-- If `B` is a filter basis on `α`, and `U` a subset of `α` then we can write `U ∈ B` as
on paper. -/
@[reducible]
instance {α : Type _} : Membership (Set α) (FilterBasis α) :=
  ⟨fun U B => U ∈ B.sets⟩

-- For illustration purposes, the filter basis defining (at_top : filter ℕ)
instance : Inhabited (FilterBasis ℕ) :=
  ⟨{  sets := range Ici
      Nonempty := ⟨Ici 0, mem_range_self 0⟩
      inter_sets := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        refine' ⟨Ici (max n m), mem_range_self _, _⟩
        rintro p p_in
        constructor <;> rw [mem_Ici] at *
        exact le_of_max_le_left p_in
        exact le_of_max_le_right p_in }⟩

#print Filter.asBasis /-
/-- View a filter as a filter basis. -/
def Filter.asBasis (f : Filter α) : FilterBasis α :=
  ⟨f.sets, ⟨univ, univ_mem⟩, fun x y hx hy => ⟨x ∩ y, inter_mem hx hy, subset_rfl⟩⟩
#align filter.as_basis Filter.asBasis
-/

#print Filter.IsBasis /-
/-- `is_basis p s` means the image of `s` bounded by `p` is a filter basis. -/
protected structure Filter.IsBasis (p : ι → Prop) (s : ι → Set α) : Prop where
  Nonempty : ∃ i, p i
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ s k ⊆ s i ∩ s j
#align filter.is_basis Filter.IsBasis
-/

namespace Filter

namespace IsBasis

#print Filter.IsBasis.filterBasis /-
/-- Constructs a filter basis from an indexed family of sets satisfying `is_basis`. -/
protected def filterBasis {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s) : FilterBasis α
    where
  sets := { t | ∃ i, p i ∧ s i = t }
  Nonempty :=
    let ⟨i, hi⟩ := h.Nonempty
    ⟨s i, ⟨i, hi, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    rcases h.inter hi hj with ⟨k, hk, hk'⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hk'⟩
#align filter.is_basis.filter_basis Filter.IsBasis.filterBasis
-/

variable {p : ι → Prop} {s : ι → Set α} (h : IsBasis p s)

/- warning: filter.is_basis.mem_filter_basis_iff -> Filter.IsBasis.mem_filterBasis_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} (h : Filter.IsBasis.{u1, u2} α ι p s) {U : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) U (Filter.IsBasis.filterBasis.{u1, u2} α ι p s h)) (Exists.{u2} ι (fun (i : ι) => And (p i) (Eq.{succ u1} (Set.{u1} α) (s i) U)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} (h : Filter.IsBasis.{u2, u1} α ι p s) {U : Set.{u2} α}, Iff (Membership.mem.{u2, u2} (Set.{u2} α) (FilterBasis.{u2} α) (instMembershipSetFilterBasis.{u2} α) U (Filter.IsBasis.filterBasis.{u2, u1} α ι p s h)) (Exists.{u1} ι (fun (i : ι) => And (p i) (Eq.{succ u2} (Set.{u2} α) (s i) U)))
Case conversion may be inaccurate. Consider using '#align filter.is_basis.mem_filter_basis_iff Filter.IsBasis.mem_filterBasis_iffₓ'. -/
theorem mem_filterBasis_iff {U : Set α} : U ∈ h.FilterBasis ↔ ∃ i, p i ∧ s i = U :=
  Iff.rfl
#align filter.is_basis.mem_filter_basis_iff Filter.IsBasis.mem_filterBasis_iff

end IsBasis

end Filter

namespace FilterBasis

#print FilterBasis.filter /-
/-- The filter associated to a filter basis. -/
protected def filter (B : FilterBasis α) : Filter α
    where
  sets := { s | ∃ t ∈ B, t ⊆ s }
  univ_sets :=
    let ⟨s, s_in⟩ := B.Nonempty
    ⟨s, s_in, s.subset_univ⟩
  sets_of_superset := fun x y ⟨s, s_in, h⟩ hxy => ⟨s, s_in, Set.Subset.trans h hxy⟩
  inter_sets := fun x y ⟨s, s_in, hs⟩ ⟨t, t_in, ht⟩ =>
    let ⟨u, u_in, u_sub⟩ := B.inter_sets s_in t_in
    ⟨u, u_in, Set.Subset.trans u_sub <| Set.inter_subset_inter hs ht⟩
#align filter_basis.filter FilterBasis.filter
-/

/- warning: filter_basis.mem_filter_iff -> FilterBasis.mem_filter_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (B : FilterBasis.{u1} α) {U : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (FilterBasis.filter.{u1} α B)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) s B) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) s B) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s U)))
but is expected to have type
  forall {α : Type.{u1}} (B : FilterBasis.{u1} α) {U : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (FilterBasis.filter.{u1} α B)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (instMembershipSetFilterBasis.{u1} α) s B) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s U)))
Case conversion may be inaccurate. Consider using '#align filter_basis.mem_filter_iff FilterBasis.mem_filter_iffₓ'. -/
theorem mem_filter_iff (B : FilterBasis α) {U : Set α} : U ∈ B.filterₓ ↔ ∃ s ∈ B, s ⊆ U :=
  Iff.rfl
#align filter_basis.mem_filter_iff FilterBasis.mem_filter_iff

#print FilterBasis.mem_filter_of_mem /-
theorem mem_filter_of_mem (B : FilterBasis α) {U : Set α} : U ∈ B → U ∈ B.filterₓ := fun U_in =>
  ⟨U, U_in, Subset.refl _⟩
#align filter_basis.mem_filter_of_mem FilterBasis.mem_filter_of_mem
-/

/- warning: filter_basis.eq_infi_principal -> FilterBasis.eq_infᵢ_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (B : FilterBasis.{u1} α), Eq.{succ u1} (Filter.{u1} α) (FilterBasis.filter.{u1} α B) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (FilterBasis.sets.{u1} α B)) (fun (s : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (FilterBasis.sets.{u1} α B)) => Filter.principal.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (FilterBasis.sets.{u1} α B)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (FilterBasis.sets.{u1} α B)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (FilterBasis.sets.{u1} α B)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (FilterBasis.sets.{u1} α B)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x (FilterBasis.sets.{u1} α B)))))) s)))
but is expected to have type
  forall {α : Type.{u1}} (B : FilterBasis.{u1} α), Eq.{succ u1} (Filter.{u1} α) (FilterBasis.filter.{u1} α B) (infᵢ.{u1, succ u1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Set.Elem.{u1} (Set.{u1} α) (FilterBasis.sets.{u1} α B)) (fun (s : Set.Elem.{u1} (Set.{u1} α) (FilterBasis.sets.{u1} α B)) => Filter.principal.{u1} α (Subtype.val.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) x (FilterBasis.sets.{u1} α B)) s)))
Case conversion may be inaccurate. Consider using '#align filter_basis.eq_infi_principal FilterBasis.eq_infᵢ_principalₓ'. -/
theorem eq_infᵢ_principal (B : FilterBasis α) : B.filterₓ = ⨅ s : B.sets, 𝓟 s :=
  by
  have : Directed (· ≥ ·) fun s : B.sets => 𝓟 (s : Set α) :=
    by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use W, W_in
    simp only [ge_iff_le, le_principal_iff, mem_principal, Subtype.coe_mk]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_infi_of_directed this]
#align filter_basis.eq_infi_principal FilterBasis.eq_infᵢ_principal

#print FilterBasis.generate /-
protected theorem generate (B : FilterBasis α) : generate B.sets = B.filterₓ :=
  by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact generate_sets.superset (generate_sets.basic V_in) h
  · rw [sets_iff_generate]
    apply mem_filter_of_mem
#align filter_basis.generate FilterBasis.generate
-/

end FilterBasis

namespace Filter

namespace IsBasis

variable {p : ι → Prop} {s : ι → Set α}

#print Filter.IsBasis.filter /-
/-- Constructs a filter from an indexed family of sets satisfying `is_basis`. -/
protected def filter (h : IsBasis p s) : Filter α :=
  h.FilterBasis.filterₓ
#align filter.is_basis.filter Filter.IsBasis.filter
-/

/- warning: filter.is_basis.mem_filter_iff -> Filter.IsBasis.mem_filter_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} (h : Filter.IsBasis.{u1, u2} α ι p s) {U : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (Filter.IsBasis.filter.{u1, u2} α ι p s h)) (Exists.{u2} ι (fun (i : ι) => And (p i) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) U)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} (h : Filter.IsBasis.{u2, u1} α ι p s) {U : Set.{u2} α}, Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) U (Filter.IsBasis.filter.{u2, u1} α ι p s h)) (Exists.{u1} ι (fun (i : ι) => And (p i) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s i) U)))
Case conversion may be inaccurate. Consider using '#align filter.is_basis.mem_filter_iff Filter.IsBasis.mem_filter_iffₓ'. -/
protected theorem mem_filter_iff (h : IsBasis p s) {U : Set α} :
    U ∈ h.filterₓ ↔ ∃ i, p i ∧ s i ⊆ U :=
  by
  erw [h.filter_basis.mem_filter_iff]
  simp only [mem_filter_basis_iff h, exists_prop]
  constructor
  · rintro ⟨_, ⟨i, pi, rfl⟩, h⟩
    tauto
  · tauto
#align filter.is_basis.mem_filter_iff Filter.IsBasis.mem_filter_iff

/- warning: filter.is_basis.filter_eq_generate -> Filter.IsBasis.filter_eq_generate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} (h : Filter.IsBasis.{u1, u2} α ι p s), Eq.{succ u1} (Filter.{u1} α) (Filter.IsBasis.filter.{u1, u2} α ι p s h) (Filter.generate.{u1} α (setOf.{u1} (Set.{u1} α) (fun (U : Set.{u1} α) => Exists.{u2} ι (fun (i : ι) => And (p i) (Eq.{succ u1} (Set.{u1} α) (s i) U)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} (h : Filter.IsBasis.{u2, u1} α ι p s), Eq.{succ u2} (Filter.{u2} α) (Filter.IsBasis.filter.{u2, u1} α ι p s h) (Filter.generate.{u2} α (setOf.{u2} (Set.{u2} α) (fun (U : Set.{u2} α) => Exists.{u1} ι (fun (i : ι) => And (p i) (Eq.{succ u2} (Set.{u2} α) (s i) U)))))
Case conversion may be inaccurate. Consider using '#align filter.is_basis.filter_eq_generate Filter.IsBasis.filter_eq_generateₓ'. -/
theorem filter_eq_generate (h : IsBasis p s) : h.filterₓ = generate { U | ∃ i, p i ∧ s i = U } := by
  erw [h.filter_basis.generate] <;> rfl
#align filter.is_basis.filter_eq_generate Filter.IsBasis.filter_eq_generate

end IsBasis

#print Filter.HasBasis /-
/-- We say that a filter `l` has a basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
protected structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ (i : _)(hi : p i), s i ⊆ t
#align filter.has_basis Filter.HasBasis
-/

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

#print Filter.hasBasis_generate /-
theorem hasBasis_generate (s : Set (Set α)) :
    (generate s).HasBasis (fun t => Set.Finite t ∧ t ⊆ s) fun t => ⋂₀ t :=
  ⟨fun U => by simp only [mem_generate_iff, exists_prop, and_assoc, and_left_comm]⟩
#align filter.has_basis_generate Filter.hasBasis_generate
-/

#print Filter.FilterBasis.ofSets /-
/-- The smallest filter basis containing a given collection of sets. -/
def FilterBasis.ofSets (s : Set (Set α)) : FilterBasis α
    where
  sets := interₛ '' { t | Set.Finite t ∧ t ⊆ s }
  Nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, interₛ_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact
      ⟨⋂₀ (a ∪ b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩, by
        rw [sInter_union]⟩
#align filter.filter_basis.of_sets Filter.FilterBasis.ofSets
-/

/-- Definition of `has_basis` unfolded with implicit set argument. -/
theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t ∈ l ↔ ∃ (i : _)(hi : p i), s i ⊆ t :=
  hl.mem_iff' t
#align filter.has_basis.mem_iff Filter.HasBasis.mem_iffₓ

/- warning: filter.has_basis.eq_of_same_basis -> Filter.HasBasis.eq_of_same_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Filter.HasBasis.{u1, u2} α ι l' p s) -> (Eq.{succ u1} (Filter.{u1} α) l l')
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {l' : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Filter.HasBasis.{u2, u1} α ι l' p s) -> (Eq.{succ u2} (Filter.{u2} α) l l')
Case conversion may be inaccurate. Consider using '#align filter.has_basis.eq_of_same_basis Filter.HasBasis.eq_of_same_basisₓ'. -/
theorem HasBasis.eq_of_same_basis (hl : l.HasBasis p s) (hl' : l'.HasBasis p s) : l = l' :=
  by
  ext t
  rw [hl.mem_iff, hl'.mem_iff]
#align filter.has_basis.eq_of_same_basis Filter.HasBasis.eq_of_same_basis

theorem hasBasis_iff : l.HasBasis p s ↔ ∀ t, t ∈ l ↔ ∃ (i : _)(hi : p i), s i ⊆ t :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
#align filter.has_basis_iff Filter.hasBasis_iffₓ

/- warning: filter.has_basis.ex_mem -> Filter.HasBasis.ex_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Exists.{u2} ι (fun (i : ι) => p i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Exists.{u1} ι (fun (i : ι) => p i))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.ex_mem Filter.HasBasis.ex_memₓ'. -/
theorem HasBasis.ex_mem (h : l.HasBasis p s) : ∃ i, p i :=
  let ⟨i, pi, h⟩ := h.mem_iff.mp univ_mem
  ⟨i, pi⟩
#align filter.has_basis.ex_mem Filter.HasBasis.ex_mem

/- warning: filter.has_basis.nonempty -> Filter.HasBasis.nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Nonempty.{u2} ι)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Nonempty.{u1} ι)
Case conversion may be inaccurate. Consider using '#align filter.has_basis.nonempty Filter.HasBasis.nonemptyₓ'. -/
protected theorem HasBasis.nonempty (h : l.HasBasis p s) : Nonempty ι :=
  nonempty_of_exists h.ex_mem
#align filter.has_basis.nonempty Filter.HasBasis.nonempty

/- warning: filter.is_basis.has_basis -> Filter.IsBasis.hasBasis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} (h : Filter.IsBasis.{u1, u2} α ι p s), Filter.HasBasis.{u1, u2} α ι (Filter.IsBasis.filter.{u1, u2} α ι p s h) p s
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} (h : Filter.IsBasis.{u2, u1} α ι p s), Filter.HasBasis.{u2, u1} α ι (Filter.IsBasis.filter.{u2, u1} α ι p s h) p s
Case conversion may be inaccurate. Consider using '#align filter.is_basis.has_basis Filter.IsBasis.hasBasisₓ'. -/
protected theorem IsBasis.hasBasis (h : IsBasis p s) : HasBasis h.filterₓ p s :=
  ⟨fun t => by simp only [h.mem_filter_iff, exists_prop]⟩
#align filter.is_basis.has_basis Filter.IsBasis.hasBasis

/- warning: filter.has_basis.mem_of_superset -> Filter.HasBasis.mem_of_superset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {t : Set.{u1} α} {i : ι}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (p i) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) t) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} {t : Set.{u2} α} {i : ι}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (p i) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s i) t) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t l)
Case conversion may be inaccurate. Consider using '#align filter.has_basis.mem_of_superset Filter.HasBasis.mem_of_supersetₓ'. -/
theorem HasBasis.mem_of_superset (hl : l.HasBasis p s) (hi : p i) (ht : s i ⊆ t) : t ∈ l :=
  hl.mem_iff.2 ⟨i, hi, ht⟩
#align filter.has_basis.mem_of_superset Filter.HasBasis.mem_of_superset

/- warning: filter.has_basis.mem_of_mem -> Filter.HasBasis.mem_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {i : ι}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (p i) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (s i) l)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} {i : ι}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (p i) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (s i) l)
Case conversion may be inaccurate. Consider using '#align filter.has_basis.mem_of_mem Filter.HasBasis.mem_of_memₓ'. -/
theorem HasBasis.mem_of_mem (hl : l.HasBasis p s) (hi : p i) : s i ∈ l :=
  hl.mem_of_superset hi <| Subset.refl _
#align filter.has_basis.mem_of_mem Filter.HasBasis.mem_of_mem

#print Filter.HasBasis.index /-
/-- Index of a basis set such that `s i ⊆ t` as an element of `subtype p`. -/
noncomputable def HasBasis.index (h : l.HasBasis p s) (t : Set α) (ht : t ∈ l) : { i : ι // p i } :=
  ⟨(h.mem_iff.1 ht).some, (h.mem_iff.1 ht).choose_spec.fst⟩
#align filter.has_basis.index Filter.HasBasis.index
-/

/- warning: filter.has_basis.property_index -> Filter.HasBasis.property_index is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {t : Set.{u1} α} (h : Filter.HasBasis.{u1, u2} α ι l p s) (ht : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l), p ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι (fun (i : ι) => p i)) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (coeSubtype.{u2} ι (fun (i : ι) => p i))))) (Filter.HasBasis.index.{u1, u2} α ι l p s h t ht))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} {t : Set.{u2} α} (h : Filter.HasBasis.{u2, u1} α ι l p s) (ht : Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t l), p (Subtype.val.{u1} ι (fun (i : ι) => p i) (Filter.HasBasis.index.{u2, u1} α ι l p s h t ht))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.property_index Filter.HasBasis.property_indexₓ'. -/
theorem HasBasis.property_index (h : l.HasBasis p s) (ht : t ∈ l) : p (h.index t ht) :=
  (h.index t ht).2
#align filter.has_basis.property_index Filter.HasBasis.property_index

/- warning: filter.has_basis.set_index_mem -> Filter.HasBasis.set_index_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {t : Set.{u1} α} (h : Filter.HasBasis.{u1, u2} α ι l p s) (ht : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (s ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι (fun (i : ι) => p i)) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (coeSubtype.{u2} ι (fun (i : ι) => p i))))) (Filter.HasBasis.index.{u1, u2} α ι l p s h t ht))) l
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} {t : Set.{u2} α} (h : Filter.HasBasis.{u2, u1} α ι l p s) (ht : Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t l), Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (s (Subtype.val.{u1} ι (fun (i : ι) => p i) (Filter.HasBasis.index.{u2, u1} α ι l p s h t ht))) l
Case conversion may be inaccurate. Consider using '#align filter.has_basis.set_index_mem Filter.HasBasis.set_index_memₓ'. -/
theorem HasBasis.set_index_mem (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ∈ l :=
  h.mem_of_mem <| h.property_index _
#align filter.has_basis.set_index_mem Filter.HasBasis.set_index_mem

/- warning: filter.has_basis.set_index_subset -> Filter.HasBasis.set_index_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {t : Set.{u1} α} (h : Filter.HasBasis.{u1, u2} α ι l p s) (ht : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι (fun (i : ι) => p i)) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => p i)) ι (coeSubtype.{u2} ι (fun (i : ι) => p i))))) (Filter.HasBasis.index.{u1, u2} α ι l p s h t ht))) t
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} {t : Set.{u2} α} (h : Filter.HasBasis.{u2, u1} α ι l p s) (ht : Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t l), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s (Subtype.val.{u1} ι (fun (i : ι) => p i) (Filter.HasBasis.index.{u2, u1} α ι l p s h t ht))) t
Case conversion may be inaccurate. Consider using '#align filter.has_basis.set_index_subset Filter.HasBasis.set_index_subsetₓ'. -/
theorem HasBasis.set_index_subset (h : l.HasBasis p s) (ht : t ∈ l) : s (h.index t ht) ⊆ t :=
  (h.mem_iff.1 ht).choose_spec.snd
#align filter.has_basis.set_index_subset Filter.HasBasis.set_index_subset

/- warning: filter.has_basis.is_basis -> Filter.HasBasis.isBasis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Filter.IsBasis.{u1, u2} α ι p s)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Filter.IsBasis.{u2, u1} α ι p s)
Case conversion may be inaccurate. Consider using '#align filter.has_basis.is_basis Filter.HasBasis.isBasisₓ'. -/
theorem HasBasis.isBasis (h : l.HasBasis p s) : IsBasis p s :=
  { Nonempty :=
      let ⟨i, hi, H⟩ := h.mem_iff.mp univ_mem
      ⟨i, hi⟩
    inter := fun i j hi hj => by
      simpa [h.mem_iff] using l.inter_sets (h.mem_of_mem hi) (h.mem_of_mem hj) }
#align filter.has_basis.is_basis Filter.HasBasis.isBasis

/- warning: filter.has_basis.filter_eq -> Filter.HasBasis.filter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} (h : Filter.HasBasis.{u1, u2} α ι l p s), Eq.{succ u1} (Filter.{u1} α) (Filter.IsBasis.filter.{u1, u2} α ι p s (Filter.HasBasis.isBasis.{u1, u2} α ι l p s h)) l
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} (h : Filter.HasBasis.{u2, u1} α ι l p s), Eq.{succ u2} (Filter.{u2} α) (Filter.IsBasis.filter.{u2, u1} α ι p s (Filter.HasBasis.isBasis.{u1, u2} α ι l p s h)) l
Case conversion may be inaccurate. Consider using '#align filter.has_basis.filter_eq Filter.HasBasis.filter_eqₓ'. -/
theorem HasBasis.filter_eq (h : l.HasBasis p s) : h.IsBasis.filterₓ = l :=
  by
  ext U
  simp [h.mem_iff, is_basis.mem_filter_iff]
#align filter.has_basis.filter_eq Filter.HasBasis.filter_eq

/- warning: filter.has_basis.eq_generate -> Filter.HasBasis.eq_generate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Eq.{succ u1} (Filter.{u1} α) l (Filter.generate.{u1} α (setOf.{u1} (Set.{u1} α) (fun (U : Set.{u1} α) => Exists.{u2} ι (fun (i : ι) => And (p i) (Eq.{succ u1} (Set.{u1} α) (s i) U))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Eq.{succ u2} (Filter.{u2} α) l (Filter.generate.{u2} α (setOf.{u2} (Set.{u2} α) (fun (U : Set.{u2} α) => Exists.{u1} ι (fun (i : ι) => And (p i) (Eq.{succ u2} (Set.{u2} α) (s i) U))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.eq_generate Filter.HasBasis.eq_generateₓ'. -/
theorem HasBasis.eq_generate (h : l.HasBasis p s) : l = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [← h.is_basis.filter_eq_generate, h.filter_eq]
#align filter.has_basis.eq_generate Filter.HasBasis.eq_generate

#print Filter.generate_eq_generate_inter /-
theorem generate_eq_generate_inter (s : Set (Set α)) :
    generate s = generate (interₛ '' { t | Set.Finite t ∧ t ⊆ s }) := by
  erw [(filter_basis.of_sets s).generate, ← (has_basis_generate s).filter_eq] <;> rfl
#align filter.generate_eq_generate_inter Filter.generate_eq_generate_inter
-/

#print Filter.ofSets_filter_eq_generate /-
theorem ofSets_filter_eq_generate (s : Set (Set α)) : (FilterBasis.ofSets s).filterₓ = generate s :=
  by rw [← (filter_basis.of_sets s).generate, generate_eq_generate_inter s] <;> rfl
#align filter.of_sets_filter_eq_generate Filter.ofSets_filter_eq_generate
-/

#print FilterBasis.hasBasis /-
protected theorem FilterBasis.hasBasis {α : Type _} (B : FilterBasis α) :
    HasBasis B.filterₓ (fun s : Set α => s ∈ B) id :=
  ⟨fun t => B.mem_filter_iff⟩
#align filter_basis.has_basis FilterBasis.hasBasis
-/

/- warning: filter.has_basis.to_has_basis' -> Filter.HasBasis.to_has_basis' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall (i : ι), (p i) -> (Exists.{u3} ι' (fun (i' : ι') => And (p' i') (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s' i') (s i))))) -> (forall (i' : ι'), (p' i') -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (s' i') l)) -> (Filter.HasBasis.{u1, u3} α ι' l p' s')
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} {l : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u3} α)}, (Filter.HasBasis.{u3, u2} α ι l p s) -> (forall (i : ι), (p i) -> (Exists.{u1} ι' (fun (i' : ι') => And (p' i') (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s' i') (s i))))) -> (forall (i' : ι'), (p' i') -> (Membership.mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (instMembershipSetFilter.{u3} α) (s' i') l)) -> (Filter.HasBasis.{u3, u1} α ι' l p' s')
Case conversion may be inaccurate. Consider using '#align filter.has_basis.to_has_basis' Filter.HasBasis.to_has_basis'ₓ'. -/
theorem HasBasis.to_has_basis' (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → s' i' ∈ l) : l.HasBasis p' s' :=
  by
  refine' ⟨fun t => ⟨fun ht => _, fun ⟨i', hi', ht⟩ => mem_of_superset (h' i' hi') ht⟩⟩
  rcases hl.mem_iff.1 ht with ⟨i, hi, ht⟩
  rcases h i hi with ⟨i', hi', hs's⟩
  exact ⟨i', hi', subset.trans hs's ht⟩
#align filter.has_basis.to_has_basis' Filter.HasBasis.to_has_basis'

/- warning: filter.has_basis.to_has_basis -> Filter.HasBasis.to_hasBasis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall (i : ι), (p i) -> (Exists.{u3} ι' (fun (i' : ι') => And (p' i') (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s' i') (s i))))) -> (forall (i' : ι'), (p' i') -> (Exists.{u2} ι (fun (i : ι) => And (p i) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) (s' i'))))) -> (Filter.HasBasis.{u1, u3} α ι' l p' s')
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} {l : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u3} α)}, (Filter.HasBasis.{u3, u2} α ι l p s) -> (forall (i : ι), (p i) -> (Exists.{u1} ι' (fun (i' : ι') => And (p' i') (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s' i') (s i))))) -> (forall (i' : ι'), (p' i') -> (Exists.{u2} ι (fun (i : ι) => And (p i) (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i) (s' i'))))) -> (Filter.HasBasis.{u3, u1} α ι' l p' s')
Case conversion may be inaccurate. Consider using '#align filter.has_basis.to_has_basis Filter.HasBasis.to_hasBasisₓ'. -/
theorem HasBasis.to_hasBasis (hl : l.HasBasis p s) (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i)
    (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') : l.HasBasis p' s' :=
  hl.to_has_basis' h fun i' hi' =>
    let ⟨i, hi, hss'⟩ := h' i' hi'
    hl.mem_iff.2 ⟨i, hi, hss'⟩
#align filter.has_basis.to_has_basis Filter.HasBasis.to_hasBasis

/- warning: filter.has_basis.to_subset -> Filter.HasBasis.to_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {t : ι -> (Set.{u1} α)}, (forall (i : ι), (p i) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (t i) (s i))) -> (forall (i : ι), (p i) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (t i) l)) -> (Filter.HasBasis.{u1, u2} α ι l p t))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall {t : ι -> (Set.{u2} α)}, (forall (i : ι), (p i) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (t i) (s i))) -> (forall (i : ι), (p i) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (t i) l)) -> (Filter.HasBasis.{u2, u1} α ι l p t))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.to_subset Filter.HasBasis.to_subsetₓ'. -/
theorem HasBasis.to_subset (hl : l.HasBasis p s) {t : ι → Set α} (h : ∀ i, p i → t i ⊆ s i)
    (ht : ∀ i, p i → t i ∈ l) : l.HasBasis p t :=
  hl.to_has_basis' (fun i hi => ⟨i, hi, h i hi⟩) ht
#align filter.has_basis.to_subset Filter.HasBasis.to_subset

/- warning: filter.has_basis.eventually_iff -> Filter.HasBasis.eventually_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {q : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => q x) l) (Exists.{u2} ι (fun (i : ι) => And (p i) (forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) -> (q x)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall {q : α -> Prop}, Iff (Filter.Eventually.{u2} α (fun (x : α) => q x) l) (Exists.{u1} ι (fun (i : ι) => And (p i) (forall {{x : α}}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s i)) -> (q x)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.eventually_iff Filter.HasBasis.eventually_iffₓ'. -/
theorem HasBasis.eventually_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∀ᶠ x in l, q x) ↔ ∃ i, p i ∧ ∀ ⦃x⦄, x ∈ s i → q x := by simpa using hl.mem_iff
#align filter.has_basis.eventually_iff Filter.HasBasis.eventually_iff

/- warning: filter.has_basis.frequently_iff -> Filter.HasBasis.frequently_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {q : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (x : α) => q x) l) (forall (i : ι), (p i) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) => q x)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall {q : α -> Prop}, Iff (Filter.Frequently.{u2} α (fun (x : α) => q x) l) (forall (i : ι), (p i) -> (Exists.{succ u2} α (fun (x : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s i)) (q x)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.frequently_iff Filter.HasBasis.frequently_iffₓ'. -/
theorem HasBasis.frequently_iff (hl : l.HasBasis p s) {q : α → Prop} :
    (∃ᶠ x in l, q x) ↔ ∀ i, p i → ∃ x ∈ s i, q x := by simp [Filter.Frequently, hl.eventually_iff]
#align filter.has_basis.frequently_iff Filter.HasBasis.frequently_iff

theorem HasBasis.exists_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P t → P s) : (∃ s ∈ l, P s) ↔ ∃ (i : _)(hi : p i), P (s i) :=
  ⟨fun ⟨s, hs, hP⟩ =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    ⟨i, hi, mono his hP⟩,
    fun ⟨i, hi, hP⟩ => ⟨s i, hl.mem_of_mem hi, hP⟩⟩
#align filter.has_basis.exists_iff Filter.HasBasis.exists_iffₓ

/- warning: filter.has_basis.forall_iff -> Filter.HasBasis.forall_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {P : (Set.{u1} α) -> Prop}, (forall {{s : Set.{u1} α}} {{t : Set.{u1} α}}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (P s) -> (P t)) -> (Iff (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) -> (P s)) (forall (i : ι), (p i) -> (P (s i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall {P : (Set.{u2} α) -> Prop}, (forall {{s : Set.{u2} α}} {{t : Set.{u2} α}}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (P s) -> (P t)) -> (Iff (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s l) -> (P s)) (forall (i : ι), (p i) -> (P (s i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.forall_iff Filter.HasBasis.forall_iffₓ'. -/
theorem HasBasis.forall_iff (hl : l.HasBasis p s) {P : Set α → Prop}
    (mono : ∀ ⦃s t⦄, s ⊆ t → P s → P t) : (∀ s ∈ l, P s) ↔ ∀ i, p i → P (s i) :=
  ⟨fun H i hi => H (s i) <| hl.mem_of_mem hi, fun H s hs =>
    let ⟨i, hi, his⟩ := hl.mem_iff.1 hs
    mono his (H i hi)⟩
#align filter.has_basis.forall_iff Filter.HasBasis.forall_iff

/- warning: filter.has_basis.ne_bot_iff -> Filter.HasBasis.neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Iff (Filter.NeBot.{u1} α l) (forall {i : ι}, (p i) -> (Set.Nonempty.{u1} α (s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Iff (Filter.NeBot.{u2} α l) (forall {i : ι}, (p i) -> (Set.Nonempty.{u2} α (s i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.ne_bot_iff Filter.HasBasis.neBot_iffₓ'. -/
theorem HasBasis.neBot_iff (hl : l.HasBasis p s) : NeBot l ↔ ∀ {i}, p i → (s i).Nonempty :=
  forall_mem_nonempty_iff_neBot.symm.trans <| hl.forall_iff fun _ _ => Nonempty.mono
#align filter.has_basis.ne_bot_iff Filter.HasBasis.neBot_iff

/- warning: filter.has_basis.eq_bot_iff -> Filter.HasBasis.eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Iff (Eq.{succ u1} (Filter.{u1} α) l (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Exists.{u2} ι (fun (i : ι) => And (p i) (Eq.{succ u1} (Set.{u1} α) (s i) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Iff (Eq.{succ u2} (Filter.{u2} α) l (Bot.bot.{u2} (Filter.{u2} α) (CompleteLattice.toBot.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)))) (Exists.{u1} ι (fun (i : ι) => And (p i) (Eq.{succ u2} (Set.{u2} α) (s i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.eq_bot_iff Filter.HasBasis.eq_bot_iffₓ'. -/
theorem HasBasis.eq_bot_iff (hl : l.HasBasis p s) : l = ⊥ ↔ ∃ i, p i ∧ s i = ∅ :=
  not_iff_not.1 <|
    neBot_iff.symm.trans <|
      hl.neBot_iff.trans <| by simp only [not_exists, not_and, nonempty_iff_ne_empty]
#align filter.has_basis.eq_bot_iff Filter.HasBasis.eq_bot_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print Filter.generate_neBot_iff /-
theorem generate_neBot_iff {s : Set (Set α)} :
    NeBot (generate s) ↔ ∀ (t) (_ : t ⊆ s), t.Finite → (⋂₀ t).Nonempty :=
  (hasBasis_generate s).neBot_iff.trans <| by simp only [← and_imp, and_comm']
#align filter.generate_ne_bot_iff Filter.generate_neBot_iff
-/

#print Filter.basis_sets /-
theorem basis_sets (l : Filter α) : l.HasBasis (fun s : Set α => s ∈ l) id :=
  ⟨fun t => exists_mem_subset_iff.symm⟩
#align filter.basis_sets Filter.basis_sets
-/

#print Filter.asBasis_filter /-
theorem asBasis_filter (f : Filter α) : f.asBasis.filterₓ = f := by
  ext t <;> exact exists_mem_subset_iff
#align filter.as_basis_filter Filter.asBasis_filter
-/

/- warning: filter.has_basis_self -> Filter.hasBasis_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {P : (Set.{u1} α) -> Prop}, Iff (Filter.HasBasis.{u1, succ u1} α (Set.{u1} α) l (fun (s : Set.{u1} α) => And (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) (P s)) (id.{succ u1} (Set.{u1} α))) (forall (t : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l) -> (Exists.{succ u1} (Set.{u1} α) (fun (r : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) r l) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) r l) => And (P r) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) r t)))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {P : (Set.{u1} α) -> Prop}, Iff (Filter.HasBasis.{u1, succ u1} α (Set.{u1} α) l (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) (P s)) (id.{succ u1} (Set.{u1} α))) (forall (t : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t l) -> (Exists.{succ u1} (Set.{u1} α) (fun (r : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) r l) (And (P r) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) r t)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_self Filter.hasBasis_selfₓ'. -/
theorem hasBasis_self {l : Filter α} {P : Set α → Prop} :
    HasBasis l (fun s => s ∈ l ∧ P s) id ↔ ∀ t ∈ l, ∃ r ∈ l, P r ∧ r ⊆ t :=
  by
  simp only [has_basis_iff, exists_prop, id, and_assoc']
  exact
    forall_congr' fun s =>
      ⟨fun h => h.1, fun h => ⟨h, fun ⟨t, hl, hP, hts⟩ => mem_of_superset hl hts⟩⟩
#align filter.has_basis_self Filter.hasBasis_self

/- warning: filter.has_basis.comp_surjective -> Filter.HasBasis.comp_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {g : ι' -> ι}, (Function.Surjective.{u3, u2} ι' ι g) -> (Filter.HasBasis.{u1, u3} α ι' l (Function.comp.{u3, u2, 1} ι' ι Prop p g) (Function.comp.{u3, u2, succ u1} ι' ι (Set.{u1} α) s g)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} {l : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)}, (Filter.HasBasis.{u3, u2} α ι l p s) -> (forall {g : ι' -> ι}, (Function.Surjective.{u1, u2} ι' ι g) -> (Filter.HasBasis.{u3, u1} α ι' l (Function.comp.{u1, u2, 1} ι' ι Prop p g) (Function.comp.{u1, u2, succ u3} ι' ι (Set.{u3} α) s g)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.comp_surjective Filter.HasBasis.comp_surjectiveₓ'. -/
theorem HasBasis.comp_surjective (h : l.HasBasis p s) {g : ι' → ι} (hg : Function.Surjective g) :
    l.HasBasis (p ∘ g) (s ∘ g) :=
  ⟨fun t => h.mem_iff.trans hg.exists⟩
#align filter.has_basis.comp_surjective Filter.HasBasis.comp_surjective

/- warning: filter.has_basis.comp_equiv -> Filter.HasBasis.comp_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall (e : Equiv.{u3, u2} ι' ι), Filter.HasBasis.{u1, u3} α ι' l (Function.comp.{u3, u2, 1} ι' ι Prop p (coeFn.{max 1 (imax u3 u2) (imax u2 u3), imax u3 u2} (Equiv.{u3, u2} ι' ι) (fun (_x : Equiv.{u3, u2} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{u3, u2} ι' ι) e)) (Function.comp.{u3, u2, succ u1} ι' ι (Set.{u1} α) s (coeFn.{max 1 (imax u3 u2) (imax u2 u3), imax u3 u2} (Equiv.{u3, u2} ι' ι) (fun (_x : Equiv.{u3, u2} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{u3, u2} ι' ι) e)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} {l : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)}, (Filter.HasBasis.{u3, u2} α ι l p s) -> (forall (e : Equiv.{u1, u2} ι' ι), Filter.HasBasis.{u3, u1} α ι' l (Function.comp.{u1, u2, 1} ι' ι Prop p (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{u1, u2} ι' ι) e)) (Function.comp.{u1, u2, succ u3} ι' ι (Set.{u3} α) s (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{u1, u2} ι' ι) e)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.comp_equiv Filter.HasBasis.comp_equivₓ'. -/
theorem HasBasis.comp_equiv (h : l.HasBasis p s) (e : ι' ≃ ι) : l.HasBasis (p ∘ e) (s ∘ e) :=
  h.comp_surjective e.Surjective
#align filter.has_basis.comp_equiv Filter.HasBasis.comp_equiv

/- warning: filter.has_basis.restrict -> Filter.HasBasis.restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {q : ι -> Prop}, (forall (i : ι), (p i) -> (Exists.{u2} ι (fun (j : ι) => And (p j) (And (q j) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s j) (s i)))))) -> (Filter.HasBasis.{u1, u2} α ι l (fun (i : ι) => And (p i) (q i)) s))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall {q : ι -> Prop}, (forall (i : ι), (p i) -> (Exists.{u1} ι (fun (j : ι) => And (p j) (And (q j) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s j) (s i)))))) -> (Filter.HasBasis.{u2, u1} α ι l (fun (i : ι) => And (p i) (q i)) s))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.restrict Filter.HasBasis.restrictₓ'. -/
/-- If `{s i | p i}` is a basis of a filter `l` and each `s i` includes `s j` such that
`p j ∧ q j`, then `{s j | p j ∧ q j}` is a basis of `l`. -/
theorem HasBasis.restrict (h : l.HasBasis p s) {q : ι → Prop}
    (hq : ∀ i, p i → ∃ j, p j ∧ q j ∧ s j ⊆ s i) : l.HasBasis (fun i => p i ∧ q i) s :=
  by
  refine' ⟨fun t => ⟨fun ht => _, fun ⟨i, hpi, hti⟩ => h.mem_iff.2 ⟨i, hpi.1, hti⟩⟩⟩
  rcases h.mem_iff.1 ht with ⟨i, hpi, hti⟩
  rcases hq i hpi with ⟨j, hpj, hqj, hji⟩
  exact ⟨j, ⟨hpj, hqj⟩, subset.trans hji hti⟩
#align filter.has_basis.restrict Filter.HasBasis.restrict

/- warning: filter.has_basis.restrict_subset -> Filter.HasBasis.restrict_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {V : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) V l) -> (Filter.HasBasis.{u1, u2} α ι l (fun (i : ι) => And (p i) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) V)) s))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall {V : Set.{u2} α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) V l) -> (Filter.HasBasis.{u2, u1} α ι l (fun (i : ι) => And (p i) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s i) V)) s))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.restrict_subset Filter.HasBasis.restrict_subsetₓ'. -/
/-- If `{s i | p i}` is a basis of a filter `l` and `V ∈ l`, then `{s i | p i ∧ s i ⊆ V}`
is a basis of `l`. -/
theorem HasBasis.restrict_subset (h : l.HasBasis p s) {V : Set α} (hV : V ∈ l) :
    l.HasBasis (fun i => p i ∧ s i ⊆ V) s :=
  h.restrict fun i hi =>
    (h.mem_iff.1 (inter_mem hV (h.mem_of_mem hi))).imp fun j hj =>
      ⟨hj.fst, subset_inter_iff.1 hj.snd⟩
#align filter.has_basis.restrict_subset Filter.HasBasis.restrict_subset

#print Filter.HasBasis.hasBasis_self_subset /-
theorem HasBasis.hasBasis_self_subset {p : Set α → Prop} (h : l.HasBasis (fun s => s ∈ l ∧ p s) id)
    {V : Set α} (hV : V ∈ l) : l.HasBasis (fun s => s ∈ l ∧ p s ∧ s ⊆ V) id := by
  simpa only [and_assoc'] using h.restrict_subset hV
#align filter.has_basis.has_basis_self_subset Filter.HasBasis.hasBasis_self_subset
-/

/- warning: filter.has_basis.ge_iff -> Filter.HasBasis.ge_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι' : Sort.{u2}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι' l' p' s') -> (Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l l') (forall (i' : ι'), (p' i') -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (s' i') l)))
but is expected to have type
  forall {α : Type.{u2}} {ι' : Sort.{u1}} {l : Filter.{u2} α} {l' : Filter.{u2} α} {p' : ι' -> Prop} {s' : ι' -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι' l' p' s') -> (Iff (LE.le.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) l l') (forall (i' : ι'), (p' i') -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (s' i') l)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.ge_iff Filter.HasBasis.ge_iffₓ'. -/
theorem HasBasis.ge_iff (hl' : l'.HasBasis p' s') : l ≤ l' ↔ ∀ i', p' i' → s' i' ∈ l :=
  ⟨fun h i' hi' => h <| hl'.mem_of_mem hi', fun h s hs =>
    let ⟨i', hi', hs⟩ := hl'.mem_iff.1 hs
    mem_of_superset (h _ hi') hs⟩
#align filter.has_basis.ge_iff Filter.HasBasis.ge_iff

theorem HasBasis.le_iff (hl : l.HasBasis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ (i : _)(hi : p i), s i ⊆ t :=
  by simp only [le_def, hl.mem_iff]
#align filter.has_basis.le_iff Filter.HasBasis.le_iffₓ

theorem HasBasis.le_basis_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    l ≤ l' ↔ ∀ i', p' i' → ∃ (i : _)(hi : p i), s i ⊆ s' i' := by simp only [hl'.ge_iff, hl.mem_iff]
#align filter.has_basis.le_basis_iff Filter.HasBasis.le_basis_iffₓ

theorem HasBasis.ext (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s')
    (h : ∀ i, p i → ∃ i', p' i' ∧ s' i' ⊆ s i) (h' : ∀ i', p' i' → ∃ i, p i ∧ s i ⊆ s' i') :
    l = l' := by
  apply le_antisymm
  · rw [hl.le_basis_iff hl']
    simpa using h'
  · rw [hl'.le_basis_iff hl]
    simpa using h
#align filter.has_basis.ext Filter.HasBasis.extₓ

/- warning: filter.has_basis.inf' -> Filter.HasBasis.inf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Filter.HasBasis.{u1, u3} α ι' l' p' s') -> (Filter.HasBasis.{u1, max 1 u2 u3} α (PProd.{u2, u3} ι ι') (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l l') (fun (i : PProd.{u2, u3} ι ι') => And (p (PProd.fst.{u2, u3} ι ι' i)) (p' (PProd.snd.{u2, u3} ι ι' i))) (fun (i : PProd.{u2, u3} ι ι') => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s (PProd.fst.{u2, u3} ι ι' i)) (s' (PProd.snd.{u2, u3} ι ι' i))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} {l : Filter.{u3} α} {l' : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u3} α)}, (Filter.HasBasis.{u3, u2} α ι l p s) -> (Filter.HasBasis.{u3, u1} α ι' l' p' s') -> (Filter.HasBasis.{u3, max (max 1 u2) u1} α (PProd.{u2, u1} ι ι') (HasInf.inf.{u3} (Filter.{u3} α) (Filter.instHasInfFilter.{u3} α) l l') (fun (i : PProd.{u2, u1} ι ι') => And (p (PProd.fst.{u2, u1} ι ι' i)) (p' (PProd.snd.{u2, u1} ι ι' i))) (fun (i : PProd.{u2, u1} ι ι') => Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (s (PProd.fst.{u2, u1} ι ι' i)) (s' (PProd.snd.{u2, u1} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.inf' Filter.HasBasis.inf'ₓ'. -/
theorem HasBasis.inf' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  ⟨by
    intro t
    constructor
    · simp only [mem_inf_iff, exists_prop, hl.mem_iff, hl'.mem_iff]
      rintro ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩
      use ⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'
    · rintro ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩
      exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_mem hi') H⟩
#align filter.has_basis.inf' Filter.HasBasis.inf'

/- warning: filter.has_basis.inf -> Filter.HasBasis.inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {ι : Type.{u2}} {ι' : Type.{u3}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, succ u2} α ι l p s) -> (Filter.HasBasis.{u1, succ u3} α ι' l' p' s') -> (Filter.HasBasis.{u1, max (succ u2) (succ u3)} α (Prod.{u2, u3} ι ι') (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l l') (fun (i : Prod.{u2, u3} ι ι') => And (p (Prod.fst.{u2, u3} ι ι' i)) (p' (Prod.snd.{u2, u3} ι ι' i))) (fun (i : Prod.{u2, u3} ι ι') => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s (Prod.fst.{u2, u3} ι ι' i)) (s' (Prod.snd.{u2, u3} ι ι' i))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {ι : Type.{u3}} {ι' : Type.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, succ u3} α ι l p s) -> (Filter.HasBasis.{u1, succ u2} α ι' l' p' s') -> (Filter.HasBasis.{u1, max (succ u3) (succ u2)} α (Prod.{u3, u2} ι ι') (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l l') (fun (i : Prod.{u3, u2} ι ι') => And (p (Prod.fst.{u3, u2} ι ι' i)) (p' (Prod.snd.{u3, u2} ι ι' i))) (fun (i : Prod.{u3, u2} ι ι') => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (s (Prod.fst.{u3, u2} ι ι' i)) (s' (Prod.snd.{u3, u2} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.inf Filter.HasBasis.infₓ'. -/
theorem HasBasis.inf {ι ι' : Type _} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  (hl.inf' hl').to_hasBasis (fun i hi => ⟨⟨i.1, i.2⟩, hi, Subset.rfl⟩) fun i hi =>
    ⟨⟨i.1, i.2⟩, hi, Subset.rfl⟩
#align filter.has_basis.inf Filter.HasBasis.inf

/- warning: filter.has_basis_infi' -> Filter.hasBasis_infᵢ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : ι -> Type.{u3}} {l : ι -> (Filter.{u1} α)} {p : forall (i : ι), (ι' i) -> Prop} {s : forall (i : ι), (ι' i) -> (Set.{u1} α)}, (forall (i : ι), Filter.HasBasis.{u1, succ u3} α (ι' i) (l i) (p i) (s i)) -> (Filter.HasBasis.{u1, max (succ u2) (succ (max u2 u3))} α (Prod.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i)) (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => l i)) (fun (If : Prod.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i)) => And (Set.Finite.{u2} ι (Prod.fst.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i) If)) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (Prod.fst.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i) If)) -> (p i (Prod.snd.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i) If i)))) (fun (If : Prod.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i)) => Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (Prod.fst.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i) If)) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (Prod.fst.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i) If)) => s i (Prod.snd.{u2, max u2 u3} (Set.{u2} ι) (forall (i : ι), ι' i) If i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : ι -> Type.{u2}} {l : ι -> (Filter.{u1} α)} {p : forall (i : ι), (ι' i) -> Prop} {s : forall (i : ι), (ι' i) -> (Set.{u1} α)}, (forall (i : ι), Filter.HasBasis.{u1, succ u2} α (ι' i) (l i) (p i) (s i)) -> (Filter.HasBasis.{u1, max (succ u3) (succ u2)} α (Prod.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i)) (infᵢ.{u1, succ u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => l i)) (fun (If : Prod.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i)) => And (Set.Finite.{u3} ι (Prod.fst.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i) If)) (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i (Prod.fst.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i) If)) -> (p i (Prod.snd.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i) If i)))) (fun (If : Prod.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i)) => Set.interᵢ.{u1, succ u3} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i (Prod.fst.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i) If)) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i (Prod.fst.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i) If)) => s i (Prod.snd.{u3, max u3 u2} (Set.{u3} ι) (forall (i : ι), ι' i) If i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_infi' Filter.hasBasis_infᵢ'ₓ'. -/
theorem hasBasis_infᵢ' {ι : Type _} {ι' : ι → Type _} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => ⋂ i ∈ If.1, s i (If.2 i) :=
  ⟨by
    intro t
    constructor
    · simp only [mem_infi', (hl _).mem_iff]
      rintro ⟨I, hI, V, hV, -, rfl, -⟩
      choose u hu using hV
      exact ⟨⟨I, u⟩, ⟨hI, fun i _ => (hu i).1⟩, Inter_mono fun i => Inter_mono fun hi => (hu i).2⟩
    · rintro ⟨⟨I, f⟩, ⟨hI₁, hI₂⟩, hsub⟩
      refine' mem_of_superset _ hsub
      exact (bInter_mem hI₁).mpr fun i hi => mem_infi_of_mem i <| (hl i).mem_of_mem <| hI₂ _ hi⟩
#align filter.has_basis_infi' Filter.hasBasis_infᵢ'

/- warning: filter.has_basis_infi -> Filter.hasBasis_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : ι -> Type.{u3}} {l : ι -> (Filter.{u1} α)} {p : forall (i : ι), (ι' i) -> Prop} {s : forall (i : ι), (ι' i) -> (Set.{u1} α)}, (forall (i : ι), Filter.HasBasis.{u1, succ u3} α (ι' i) (l i) (p i) (s i)) -> (Filter.HasBasis.{u1, max (succ u2) (succ (max u2 u3))} α (Sigma.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i))) (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => l i)) (fun (If : Sigma.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i))) => And (Set.Finite.{u2} ι (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) (forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)), p ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)))))) i) (Sigma.snd.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If i))) (fun (If : Sigma.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i))) => Set.interᵢ.{u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) => s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x (Sigma.fst.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If)))))) i) (Sigma.snd.{u2, max u2 u3} (Set.{u2} ι) (fun (I : Set.{u2} ι) => forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), ι' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i)) If i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : ι -> Type.{u2}} {l : ι -> (Filter.{u1} α)} {p : forall (i : ι), (ι' i) -> Prop} {s : forall (i : ι), (ι' i) -> (Set.{u1} α)}, (forall (i : ι), Filter.HasBasis.{u1, succ u2} α (ι' i) (l i) (p i) (s i)) -> (Filter.HasBasis.{u1, max (succ u3) (succ u2)} α (Sigma.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i))) (infᵢ.{u1, succ u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => l i)) (fun (If : Sigma.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i))) => And (Set.Finite.{u3} ι (Sigma.fst.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i)) If)) (forall (i : Set.Elem.{u3} ι (Sigma.fst.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i)) If)), p (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x (Sigma.fst.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i)) If)) i) (Sigma.snd.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i)) If i))) (fun (If : Sigma.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i))) => Set.interᵢ.{u1, succ u3} α (Set.Elem.{u3} ι (Sigma.fst.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i)) If)) (fun (i : Set.Elem.{u3} ι (Sigma.fst.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i)) If)) => s (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x (Sigma.fst.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i)) If)) i) (Sigma.snd.{u3, max u3 u2} (Set.{u3} ι) (fun (I : Set.{u3} ι) => forall (i : Set.Elem.{u3} ι I), ι' (Subtype.val.{succ u3} ι (fun (x : ι) => Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) i)) If i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_infi Filter.hasBasis_infᵢₓ'. -/
theorem hasBasis_infᵢ {ι : Type _} {ι' : ι → Type _} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis
      (fun If : ΣI : Set ι, ∀ i : I, ι' i => If.1.Finite ∧ ∀ i : If.1, p i (If.2 i)) fun If =>
      ⋂ i : If.1, s i (If.2 i) :=
  by
  refine' ⟨fun t => ⟨fun ht => _, _⟩⟩
  · rcases(has_basis_infi' hl).mem_iff.mp ht with ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    exact
      ⟨⟨I, fun i => f i⟩, ⟨hI, subtype.forall.mpr hf⟩, trans_rel_right _ (Inter_subtype _ _) hsub⟩
  · rintro ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    refine' mem_of_superset _ hsub
    cases hI.nonempty_fintype
    exact Inter_mem.2 fun i => mem_infi_of_mem i <| (hl i).mem_of_mem <| hf _
#align filter.has_basis_infi Filter.hasBasis_infᵢ

/- warning: filter.has_basis_infi_of_directed' -> Filter.hasBasis_infᵢ_of_directed' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : ι -> Type.{u3}} [_inst_1 : Nonempty.{succ u2} ι] {l : ι -> (Filter.{u1} α)} (s : forall (i : ι), (ι' i) -> (Set.{u1} α)) (p : forall (i : ι), (ι' i) -> Prop), (forall (i : ι), Filter.HasBasis.{u1, succ u3} α (ι' i) (l i) (p i) (s i)) -> (Directed.{u1, succ u2} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) l) -> (Filter.HasBasis.{u1, max (succ u2) (succ u3)} α (Sigma.{u2, u3} ι (fun (i : ι) => ι' i)) (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => l i)) (fun (ii' : Sigma.{u2, u3} ι (fun (i : ι) => ι' i)) => p (Sigma.fst.{u2, u3} ι (fun (i : ι) => ι' i) ii') (Sigma.snd.{u2, u3} ι (fun (i : ι) => ι' i) ii')) (fun (ii' : Sigma.{u2, u3} ι (fun (i : ι) => ι' i)) => s (Sigma.fst.{u2, u3} ι (fun (i : ι) => ι' i) ii') (Sigma.snd.{u2, u3} ι (fun (i : ι) => ι' i) ii')))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : ι -> Type.{u2}} [_inst_1 : Nonempty.{succ u3} ι] {l : ι -> (Filter.{u1} α)} (s : forall (i : ι), (ι' i) -> (Set.{u1} α)) (p : forall (i : ι), (ι' i) -> Prop), (forall (i : ι), Filter.HasBasis.{u1, succ u2} α (ι' i) (l i) (p i) (s i)) -> (Directed.{u1, succ u3} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Bases._hyg.5721 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Bases._hyg.5723 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Bases._hyg.5721 x._@.Mathlib.Order.Filter.Bases._hyg.5723) l) -> (Filter.HasBasis.{u1, max (succ u3) (succ u2)} α (Sigma.{u3, u2} ι (fun (i : ι) => ι' i)) (infᵢ.{u1, succ u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => l i)) (fun (ii' : Sigma.{u3, u2} ι (fun (i : ι) => ι' i)) => p (Sigma.fst.{u3, u2} ι (fun (i : ι) => ι' i) ii') (Sigma.snd.{u3, u2} ι (fun (i : ι) => ι' i) ii')) (fun (ii' : Sigma.{u3, u2} ι (fun (i : ι) => ι' i)) => s (Sigma.fst.{u3, u2} ι (fun (i : ι) => ι' i) ii') (Sigma.snd.{u3, u2} ι (fun (i : ι) => ι' i) ii')))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_infi_of_directed' Filter.hasBasis_infᵢ_of_directed'ₓ'. -/
theorem hasBasis_infᵢ_of_directed' {ι : Type _} {ι' : ι → Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : Σi, ι' i => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 :=
  by
  refine' ⟨fun t => _⟩
  rw [mem_infi_of_directed h, Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff
#align filter.has_basis_infi_of_directed' Filter.hasBasis_infᵢ_of_directed'

/- warning: filter.has_basis_infi_of_directed -> Filter.hasBasis_infᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : Nonempty.{succ u2} ι] {l : ι -> (Filter.{u1} α)} (s : ι -> ι' -> (Set.{u1} α)) (p : ι -> ι' -> Prop), (forall (i : ι), Filter.HasBasis.{u1, succ u3} α ι' (l i) (p i) (s i)) -> (Directed.{u1, succ u2} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) l) -> (Filter.HasBasis.{u1, max (succ u2) (succ u3)} α (Prod.{u2, u3} ι ι') (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => l i)) (fun (ii' : Prod.{u2, u3} ι ι') => p (Prod.fst.{u2, u3} ι ι' ii') (Prod.snd.{u2, u3} ι ι' ii')) (fun (ii' : Prod.{u2, u3} ι ι') => s (Prod.fst.{u2, u3} ι ι' ii') (Prod.snd.{u2, u3} ι ι' ii')))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : Type.{u2}} [_inst_1 : Nonempty.{succ u3} ι] {l : ι -> (Filter.{u1} α)} (s : ι -> ι' -> (Set.{u1} α)) (p : ι -> ι' -> Prop), (forall (i : ι), Filter.HasBasis.{u1, succ u2} α ι' (l i) (p i) (s i)) -> (Directed.{u1, succ u3} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Bases._hyg.5898 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Bases._hyg.5900 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Bases._hyg.5898 x._@.Mathlib.Order.Filter.Bases._hyg.5900) l) -> (Filter.HasBasis.{u1, max (succ u3) (succ u2)} α (Prod.{u3, u2} ι ι') (infᵢ.{u1, succ u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => l i)) (fun (ii' : Prod.{u3, u2} ι ι') => p (Prod.fst.{u3, u2} ι ι' ii') (Prod.snd.{u3, u2} ι ι' ii')) (fun (ii' : Prod.{u3, u2} ι ι') => s (Prod.fst.{u3, u2} ι ι' ii') (Prod.snd.{u3, u2} ι ι' ii')))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_infi_of_directed Filter.hasBasis_infᵢ_of_directedₓ'. -/
theorem hasBasis_infᵢ_of_directed {ι : Type _} {ι' : Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ι → ι' → Set α) (p : ι → ι' → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : ι × ι' => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 :=
  by
  refine' ⟨fun t => _⟩
  rw [mem_infi_of_directed h, Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff
#align filter.has_basis_infi_of_directed Filter.hasBasis_infᵢ_of_directed

/- warning: filter.has_basis_binfi_of_directed' -> Filter.hasBasis_binfᵢ_of_directed' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : ι -> Type.{u3}} {dom : Set.{u2} ι}, (Set.Nonempty.{u2} ι dom) -> (forall {l : ι -> (Filter.{u1} α)} (s : forall (i : ι), (ι' i) -> (Set.{u1} α)) (p : forall (i : ι), (ι' i) -> Prop), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i dom) -> (Filter.HasBasis.{u1, succ u3} α (ι' i) (l i) (p i) (s i))) -> (DirectedOn.{u2} ι (Order.Preimage.{succ u2, succ u1} ι (Filter.{u1} α) l (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))))) dom) -> (Filter.HasBasis.{u1, max (succ u2) (succ u3)} α (Sigma.{u2, u3} ι (fun (i : ι) => ι' i)) (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i dom) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i dom) => l i))) (fun (ii' : Sigma.{u2, u3} ι (fun (i : ι) => ι' i)) => And (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) (Sigma.fst.{u2, u3} ι (fun (i : ι) => ι' i) ii') dom) (p (Sigma.fst.{u2, u3} ι (fun (i : ι) => ι' i) ii') (Sigma.snd.{u2, u3} ι (fun (i : ι) => ι' i) ii'))) (fun (ii' : Sigma.{u2, u3} ι (fun (i : ι) => ι' i)) => s (Sigma.fst.{u2, u3} ι (fun (i : ι) => ι' i) ii') (Sigma.snd.{u2, u3} ι (fun (i : ι) => ι' i) ii'))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : ι -> Type.{u2}} {dom : Set.{u3} ι}, (Set.Nonempty.{u3} ι dom) -> (forall {l : ι -> (Filter.{u1} α)} (s : forall (i : ι), (ι' i) -> (Set.{u1} α)) (p : forall (i : ι), (ι' i) -> Prop), (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i dom) -> (Filter.HasBasis.{u1, succ u2} α (ι' i) (l i) (p i) (s i))) -> (DirectedOn.{u3} ι (Order.Preimage.{succ u3, succ u1} ι (Filter.{u1} α) l (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))))) dom) -> (Filter.HasBasis.{u1, max (succ u3) (succ u2)} α (Sigma.{u3, u2} ι (fun (i : ι) => ι' i)) (infᵢ.{u1, succ u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i dom) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i dom) => l i))) (fun (ii' : Sigma.{u3, u2} ι (fun (i : ι) => ι' i)) => And (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) (Sigma.fst.{u3, u2} ι (fun (i : ι) => ι' i) ii') dom) (p (Sigma.fst.{u3, u2} ι (fun (i : ι) => ι' i) ii') (Sigma.snd.{u3, u2} ι (fun (i : ι) => ι' i) ii'))) (fun (ii' : Sigma.{u3, u2} ι (fun (i : ι) => ι' i)) => s (Sigma.fst.{u3, u2} ι (fun (i : ι) => ι' i) ii') (Sigma.snd.{u3, u2} ι (fun (i : ι) => ι' i) ii'))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_binfi_of_directed' Filter.hasBasis_binfᵢ_of_directed'ₓ'. -/
theorem hasBasis_binfᵢ_of_directed' {ι : Type _} {ι' : ι → Sort _} {dom : Set ι}
    (hdom : dom.Nonempty) {l : ι → Filter α} (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : Σi, ι' i => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 :=
  by
  refine' ⟨fun t => _⟩
  rw [mem_binfi_of_directed h hdom, Sigma.exists]
  refine' exists_congr fun i => ⟨_, _⟩
  · rintro ⟨hi, hti⟩
    rcases(hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩
#align filter.has_basis_binfi_of_directed' Filter.hasBasis_binfᵢ_of_directed'

/- warning: filter.has_basis_binfi_of_directed -> Filter.hasBasis_binfᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} {dom : Set.{u2} ι}, (Set.Nonempty.{u2} ι dom) -> (forall {l : ι -> (Filter.{u1} α)} (s : ι -> ι' -> (Set.{u1} α)) (p : ι -> ι' -> Prop), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i dom) -> (Filter.HasBasis.{u1, succ u3} α ι' (l i) (p i) (s i))) -> (DirectedOn.{u2} ι (Order.Preimage.{succ u2, succ u1} ι (Filter.{u1} α) l (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))))) dom) -> (Filter.HasBasis.{u1, max (succ u2) (succ u3)} α (Prod.{u2, u3} ι ι') (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i dom) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i dom) => l i))) (fun (ii' : Prod.{u2, u3} ι ι') => And (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) (Prod.fst.{u2, u3} ι ι' ii') dom) (p (Prod.fst.{u2, u3} ι ι' ii') (Prod.snd.{u2, u3} ι ι' ii'))) (fun (ii' : Prod.{u2, u3} ι ι') => s (Prod.fst.{u2, u3} ι ι' ii') (Prod.snd.{u2, u3} ι ι' ii'))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : Type.{u2}} {dom : Set.{u3} ι}, (Set.Nonempty.{u3} ι dom) -> (forall {l : ι -> (Filter.{u1} α)} (s : ι -> ι' -> (Set.{u1} α)) (p : ι -> ι' -> Prop), (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i dom) -> (Filter.HasBasis.{u1, succ u2} α ι' (l i) (p i) (s i))) -> (DirectedOn.{u3} ι (Order.Preimage.{succ u3, succ u1} ι (Filter.{u1} α) l (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))))) dom) -> (Filter.HasBasis.{u1, max (succ u3) (succ u2)} α (Prod.{u3, u2} ι ι') (infᵢ.{u1, succ u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i dom) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i dom) => l i))) (fun (ii' : Prod.{u3, u2} ι ι') => And (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) (Prod.fst.{u3, u2} ι ι' ii') dom) (p (Prod.fst.{u3, u2} ι ι' ii') (Prod.snd.{u3, u2} ι ι' ii'))) (fun (ii' : Prod.{u3, u2} ι ι') => s (Prod.fst.{u3, u2} ι ι' ii') (Prod.snd.{u3, u2} ι ι' ii'))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_binfi_of_directed Filter.hasBasis_binfᵢ_of_directedₓ'. -/
theorem hasBasis_binfᵢ_of_directed {ι : Type _} {ι' : Sort _} {dom : Set ι} (hdom : dom.Nonempty)
    {l : ι → Filter α} (s : ι → ι' → Set α) (p : ι → ι' → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : ι × ι' => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 :=
  by
  refine' ⟨fun t => _⟩
  rw [mem_binfi_of_directed h hdom, Prod.exists]
  refine' exists_congr fun i => ⟨_, _⟩
  · rintro ⟨hi, hti⟩
    rcases(hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩
#align filter.has_basis_binfi_of_directed Filter.hasBasis_binfᵢ_of_directed

#print Filter.hasBasis_principal /-
theorem hasBasis_principal (t : Set α) : (𝓟 t).HasBasis (fun i : Unit => True) fun i => t :=
  ⟨fun U => by simp⟩
#align filter.has_basis_principal Filter.hasBasis_principal
-/

#print Filter.hasBasis_pure /-
theorem hasBasis_pure (x : α) : (pure x : Filter α).HasBasis (fun i : Unit => True) fun i => {x} :=
  by simp only [← principal_singleton, has_basis_principal]
#align filter.has_basis_pure Filter.hasBasis_pure
-/

/- warning: filter.has_basis.sup' -> Filter.HasBasis.sup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Filter.HasBasis.{u1, u3} α ι' l' p' s') -> (Filter.HasBasis.{u1, max 1 u2 u3} α (PProd.{u2, u3} ι ι') (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l l') (fun (i : PProd.{u2, u3} ι ι') => And (p (PProd.fst.{u2, u3} ι ι' i)) (p' (PProd.snd.{u2, u3} ι ι' i))) (fun (i : PProd.{u2, u3} ι ι') => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s (PProd.fst.{u2, u3} ι ι' i)) (s' (PProd.snd.{u2, u3} ι ι' i))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} {l : Filter.{u3} α} {l' : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u3} α)}, (Filter.HasBasis.{u3, u2} α ι l p s) -> (Filter.HasBasis.{u3, u1} α ι' l' p' s') -> (Filter.HasBasis.{u3, max (max 1 u2) u1} α (PProd.{u2, u1} ι ι') (HasSup.sup.{u3} (Filter.{u3} α) (SemilatticeSup.toHasSup.{u3} (Filter.{u3} α) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} α) (CompleteLattice.toLattice.{u3} (Filter.{u3} α) (Filter.instCompleteLatticeFilter.{u3} α)))) l l') (fun (i : PProd.{u2, u1} ι ι') => And (p (PProd.fst.{u2, u1} ι ι' i)) (p' (PProd.snd.{u2, u1} ι ι' i))) (fun (i : PProd.{u2, u1} ι ι') => Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) (s (PProd.fst.{u2, u1} ι ι' i)) (s' (PProd.snd.{u2, u1} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.sup' Filter.HasBasis.sup'ₓ'. -/
theorem HasBasis.sup' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  ⟨by
    intro t
    simp only [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff, exists_prop,
      and_assoc', exists_and_left]
    simp only [← and_assoc', exists_and_right, and_comm']⟩
#align filter.has_basis.sup' Filter.HasBasis.sup'

/- warning: filter.has_basis.sup -> Filter.HasBasis.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {ι : Type.{u2}} {ι' : Type.{u3}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, succ u2} α ι l p s) -> (Filter.HasBasis.{u1, succ u3} α ι' l' p' s') -> (Filter.HasBasis.{u1, max (succ u2) (succ u3)} α (Prod.{u2, u3} ι ι') (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l l') (fun (i : Prod.{u2, u3} ι ι') => And (p (Prod.fst.{u2, u3} ι ι' i)) (p' (Prod.snd.{u2, u3} ι ι' i))) (fun (i : Prod.{u2, u3} ι ι') => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s (Prod.fst.{u2, u3} ι ι' i)) (s' (Prod.snd.{u2, u3} ι ι' i))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {ι : Type.{u3}} {ι' : Type.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, succ u3} α ι l p s) -> (Filter.HasBasis.{u1, succ u2} α ι' l' p' s') -> (Filter.HasBasis.{u1, max (succ u3) (succ u2)} α (Prod.{u3, u2} ι ι') (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) l l') (fun (i : Prod.{u3, u2} ι ι') => And (p (Prod.fst.{u3, u2} ι ι' i)) (p' (Prod.snd.{u3, u2} ι ι' i))) (fun (i : Prod.{u3, u2} ι ι') => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (s (Prod.fst.{u3, u2} ι ι' i)) (s' (Prod.snd.{u3, u2} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.sup Filter.HasBasis.supₓ'. -/
theorem HasBasis.sup {ι ι' : Type _} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  (hl.sup' hl').to_hasBasis (fun i hi => ⟨⟨i.1, i.2⟩, hi, Subset.rfl⟩) fun i hi =>
    ⟨⟨i.1, i.2⟩, hi, Subset.rfl⟩
#align filter.has_basis.sup Filter.HasBasis.sup

/- warning: filter.has_basis_supr -> Filter.hasBasis_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : ι -> Type.{u3}} {l : ι -> (Filter.{u1} α)} {p : forall (i : ι), (ι' i) -> Prop} {s : forall (i : ι), (ι' i) -> (Set.{u1} α)}, (forall (i : ι), Filter.HasBasis.{u1, succ u3} α (ι' i) (l i) (p i) (s i)) -> (Filter.HasBasis.{u1, max u2 (succ u3)} α (forall (i : ι), ι' i) (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => l i)) (fun (f : forall (i : ι), ι' i) => forall (i : ι), p i (f i)) (fun (f : forall (i : ι), ι' i) => Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i (f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : ι -> Type.{u2}} {l : ι -> (Filter.{u1} α)} {p : forall (i : ι), (ι' i) -> Prop} {s : forall (i : ι), (ι' i) -> (Set.{u1} α)}, (forall (i : ι), Filter.HasBasis.{u1, succ u2} α (ι' i) (l i) (p i) (s i)) -> (Filter.HasBasis.{u1, max u3 (succ u2)} α (forall (i : ι), ι' i) (supᵢ.{u1, u3} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => l i)) (fun (f : forall (i : ι), ι' i) => forall (i : ι), p i (f i)) (fun (f : forall (i : ι), ι' i) => Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i (f i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_supr Filter.hasBasis_supᵢₓ'. -/
theorem hasBasis_supᵢ {ι : Sort _} {ι' : ι → Type _} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨆ i, l i).HasBasis (fun f : ∀ i, ι' i => ∀ i, p i (f i)) fun f : ∀ i, ι' i => ⋃ i, s i (f i) :=
  hasBasis_iff.mpr fun t => by
    simp only [has_basis_iff, (hl _).mem_iff, Classical.skolem, forall_and, Union_subset_iff,
      mem_supr]
#align filter.has_basis_supr Filter.hasBasis_supᵢ

/- warning: filter.has_basis.sup_principal -> Filter.HasBasis.sup_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall (t : Set.{u1} α), Filter.HasBasis.{u1, u2} α ι (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l (Filter.principal.{u1} α t)) p (fun (i : ι) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall (t : Set.{u2} α), Filter.HasBasis.{u2, u1} α ι (HasSup.sup.{u2} (Filter.{u2} α) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} α) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} α) (CompleteLattice.toLattice.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)))) l (Filter.principal.{u2} α t)) p (fun (i : ι) => Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (s i) t))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.sup_principal Filter.HasBasis.sup_principalₓ'. -/
theorem HasBasis.sup_principal (hl : l.HasBasis p s) (t : Set α) :
    (l ⊔ 𝓟 t).HasBasis p fun i => s i ∪ t :=
  ⟨fun u => by
    simp only [(hl.sup' (has_basis_principal t)).mem_iff, PProd.exists, exists_prop, and_true_iff,
      Unique.exists_iff]⟩
#align filter.has_basis.sup_principal Filter.HasBasis.sup_principal

/- warning: filter.has_basis.sup_pure -> Filter.HasBasis.sup_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall (x : α), Filter.HasBasis.{u1, u2} α ι (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α x)) p (fun (i : ι) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s i) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall (x : α), Filter.HasBasis.{u2, u1} α ι (HasSup.sup.{u2} (Filter.{u2} α) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} α) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} α) (CompleteLattice.toLattice.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)))) l (Pure.pure.{u2, u2} Filter.{u2} Filter.instPureFilter.{u2} α x)) p (fun (i : ι) => Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (s i) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.sup_pure Filter.HasBasis.sup_pureₓ'. -/
theorem HasBasis.sup_pure (hl : l.HasBasis p s) (x : α) :
    (l ⊔ pure x).HasBasis p fun i => s i ∪ {x} := by
  simp only [← principal_singleton, hl.sup_principal]
#align filter.has_basis.sup_pure Filter.HasBasis.sup_pure

/- warning: filter.has_basis.inf_principal -> Filter.HasBasis.inf_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall (s' : Set.{u1} α), Filter.HasBasis.{u1, u2} α ι (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l (Filter.principal.{u1} α s')) p (fun (i : ι) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s i) s'))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall (s' : Set.{u2} α), Filter.HasBasis.{u2, u1} α ι (HasInf.inf.{u2} (Filter.{u2} α) (Filter.instHasInfFilter.{u2} α) l (Filter.principal.{u2} α s')) p (fun (i : ι) => Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (s i) s'))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.inf_principal Filter.HasBasis.inf_principalₓ'. -/
theorem HasBasis.inf_principal (hl : l.HasBasis p s) (s' : Set α) :
    (l ⊓ 𝓟 s').HasBasis p fun i => s i ∩ s' :=
  ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_set_of_eq, mem_inter_iff, and_imp]⟩
#align filter.has_basis.inf_principal Filter.HasBasis.inf_principal

/- warning: filter.has_basis.principal_inf -> Filter.HasBasis.principal_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall (s' : Set.{u1} α), Filter.HasBasis.{u1, u2} α ι (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (Filter.principal.{u1} α s') l) p (fun (i : ι) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall (s' : Set.{u2} α), Filter.HasBasis.{u2, u1} α ι (HasInf.inf.{u2} (Filter.{u2} α) (Filter.instHasInfFilter.{u2} α) (Filter.principal.{u2} α s') l) p (fun (i : ι) => Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s' (s i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.principal_inf Filter.HasBasis.principal_infₓ'. -/
theorem HasBasis.principal_inf (hl : l.HasBasis p s) (s' : Set α) :
    (𝓟 s' ⊓ l).HasBasis p fun i => s' ∩ s i := by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'
#align filter.has_basis.principal_inf Filter.HasBasis.principal_inf

/- warning: filter.has_basis.inf_basis_ne_bot_iff -> Filter.HasBasis.inf_basis_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Filter.HasBasis.{u1, u3} α ι' l' p' s') -> (Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l l')) (forall {{i : ι}}, (p i) -> (forall {{i' : ι'}}, (p' i') -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s i) (s' i'))))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} {l : Filter.{u3} α} {l' : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} {p' : ι' -> Prop} {s' : ι' -> (Set.{u3} α)}, (Filter.HasBasis.{u3, u2} α ι l p s) -> (Filter.HasBasis.{u3, u1} α ι' l' p' s') -> (Iff (Filter.NeBot.{u3} α (HasInf.inf.{u3} (Filter.{u3} α) (Filter.instHasInfFilter.{u3} α) l l')) (forall {{i : ι}}, (p i) -> (forall {{i' : ι'}}, (p' i') -> (Set.Nonempty.{u3} α (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (s i) (s' i'))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.inf_basis_ne_bot_iff Filter.HasBasis.inf_basis_neBot_iffₓ'. -/
theorem HasBasis.inf_basis_neBot_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄ (hi : p i) ⦃i'⦄ (hi' : p' i'), (s i ∩ s' i').Nonempty :=
  (hl.inf' hl').neBot_iff.trans <| by simp [@forall_swap _ ι']
#align filter.has_basis.inf_basis_ne_bot_iff Filter.HasBasis.inf_basis_neBot_iff

/- warning: filter.has_basis.inf_ne_bot_iff -> Filter.HasBasis.inf_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l l')) (forall {{i : ι}}, (p i) -> (forall {{s' : Set.{u1} α}}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s' l') -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s i) s')))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {l' : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Iff (Filter.NeBot.{u2} α (HasInf.inf.{u2} (Filter.{u2} α) (Filter.instHasInfFilter.{u2} α) l l')) (forall {{i : ι}}, (p i) -> (forall {{s' : Set.{u2} α}}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s' l') -> (Set.Nonempty.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (s i) s')))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.inf_ne_bot_iff Filter.HasBasis.inf_neBot_iffₓ'. -/
theorem HasBasis.inf_neBot_iff (hl : l.HasBasis p s) :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄ (hi : p i) ⦃s'⦄ (hs' : s' ∈ l'), (s i ∩ s').Nonempty :=
  hl.inf_basis_neBot_iff l'.basis_sets
#align filter.has_basis.inf_ne_bot_iff Filter.HasBasis.inf_neBot_iff

/- warning: filter.has_basis.inf_principal_ne_bot_iff -> Filter.HasBasis.inf_principal_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {t : Set.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l (Filter.principal.{u1} α t))) (forall {{i : ι}}, (p i) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s i) t))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall {t : Set.{u2} α}, Iff (Filter.NeBot.{u2} α (HasInf.inf.{u2} (Filter.{u2} α) (Filter.instHasInfFilter.{u2} α) l (Filter.principal.{u2} α t))) (forall {{i : ι}}, (p i) -> (Set.Nonempty.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (s i) t))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.inf_principal_ne_bot_iff Filter.HasBasis.inf_principal_neBot_iffₓ'. -/
theorem HasBasis.inf_principal_neBot_iff (hl : l.HasBasis p s) {t : Set α} :
    NeBot (l ⊓ 𝓟 t) ↔ ∀ ⦃i⦄ (hi : p i), (s i ∩ t).Nonempty :=
  (hl.inf_principal t).neBot_iff
#align filter.has_basis.inf_principal_ne_bot_iff Filter.HasBasis.inf_principal_neBot_iff

theorem HasBasis.disjoint_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    Disjoint l l' ↔ ∃ (i : _)(hi : p i)(i' : _)(hi' : p' i'), Disjoint (s i) (s' i') :=
  not_iff_not.mp <| by
    simp only [disjoint_iff, ← Ne.def, ← ne_bot_iff, hl.inf_basis_ne_bot_iff hl', not_exists,
      bot_eq_empty, ← nonempty_iff_ne_empty, inf_eq_inter]
#align filter.has_basis.disjoint_iff Filter.HasBasis.disjoint_iffₓ

theorem Disjoint.exists_mem_filter_basis (h : Disjoint l l') (hl : l.HasBasis p s)
    (hl' : l'.HasBasis p' s') : ∃ (i : _)(hi : p i)(i' : _)(hi' : p' i'), Disjoint (s i) (s' i') :=
  (hl.disjoint_iff hl').1 h
#align disjoint.exists_mem_filter_basis Disjoint.exists_mem_filter_basisₓ

/- warning: pairwise.exists_mem_filter_basis_of_disjoint -> Pairwise.exists_mem_filter_basis_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {I : Type.{u2}} [_inst_1 : Finite.{succ u2} I] {l : I -> (Filter.{u1} α)} {ι : I -> Sort.{u3}} {p : forall (i : I), (ι i) -> Prop} {s : forall (i : I), (ι i) -> (Set.{u1} α)}, (Pairwise.{u2} I (Function.onFun.{succ u2, succ u1, 1} I (Filter.{u1} α) Prop (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) l)) -> (forall (i : I), Filter.HasBasis.{u1, u3} α (ι i) (l i) (p i) (s i)) -> (Exists.{imax (succ u2) u3} (forall (i : I), ι i) (fun (ind : forall (i : I), ι i) => And (forall (i : I), p i (ind i)) (Pairwise.{u2} I (Function.onFun.{succ u2, succ u1, 1} I (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) (fun (i : I) => s i (ind i))))))
but is expected to have type
  forall {α : Type.{u2}} {I : Type.{u3}} [_inst_1 : Finite.{succ u3} I] {l : I -> (Filter.{u2} α)} {ι : I -> Sort.{u1}} {p : forall (i : I), (ι i) -> Prop} {s : forall (i : I), (ι i) -> (Set.{u2} α)}, (Pairwise.{u3} I (Function.onFun.{succ u3, succ u2, 1} I (Filter.{u2} α) Prop (Disjoint.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)))) l)) -> (forall (i : I), Filter.HasBasis.{u2, u1} α (ι i) (l i) (p i) (s i)) -> (Exists.{imax (succ u3) u1} (forall (i : I), ι i) (fun (ind : forall (i : I), ι i) => And (forall (i : I), p i (ind i)) (Pairwise.{u3} I (Function.onFun.{succ u3, succ u2, 1} I (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (fun (i : I) => s i (ind i))))))
Case conversion may be inaccurate. Consider using '#align pairwise.exists_mem_filter_basis_of_disjoint Pairwise.exists_mem_filter_basis_of_disjointₓ'. -/
theorem Pairwise.exists_mem_filter_basis_of_disjoint {I : Type _} [Finite I] {l : I → Filter α}
    {ι : I → Sort _} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} (hd : Pairwise (Disjoint on l))
    (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ Pairwise (Disjoint on fun i => s i (ind i)) :=
  by
  rcases hd.exists_mem_filter_of_disjoint with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono fun i j hij => hij.mono (ht _) (ht _)⟩
#align pairwise.exists_mem_filter_basis_of_disjoint Pairwise.exists_mem_filter_basis_of_disjoint

/- warning: set.pairwise_disjoint.exists_mem_filter_basis -> Set.PairwiseDisjoint.exists_mem_filter_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {I : Type.{u2}} {l : I -> (Filter.{u1} α)} {ι : I -> Sort.{u3}} {p : forall (i : I), (ι i) -> Prop} {s : forall (i : I), (ι i) -> (Set.{u1} α)} {S : Set.{u2} I}, (Set.PairwiseDisjoint.{u1, u2} (Filter.{u1} α) I (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) S l) -> (Set.Finite.{u2} I S) -> (forall (i : I), Filter.HasBasis.{u1, u3} α (ι i) (l i) (p i) (s i)) -> (Exists.{imax (succ u2) u3} (forall (i : I), ι i) (fun (ind : forall (i : I), ι i) => And (forall (i : I), p i (ind i)) (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) I (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) S (fun (i : I) => s i (ind i)))))
but is expected to have type
  forall {α : Type.{u2}} {I : Type.{u3}} {l : I -> (Filter.{u2} α)} {ι : I -> Sort.{u1}} {p : forall (i : I), (ι i) -> Prop} {s : forall (i : I), (ι i) -> (Set.{u2} α)} {S : Set.{u3} I}, (Set.PairwiseDisjoint.{u2, u3} (Filter.{u2} α) I (Filter.instPartialOrderFilter.{u2} α) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) S l) -> (Set.Finite.{u3} I S) -> (forall (i : I), Filter.HasBasis.{u2, u1} α (ι i) (l i) (p i) (s i)) -> (Exists.{imax (succ u3) u1} (forall (i : I), ι i) (fun (ind : forall (i : I), ι i) => And (forall (i : I), p i (ind i)) (Set.PairwiseDisjoint.{u2, u3} (Set.{u2} α) I (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) S (fun (i : I) => s i (ind i)))))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.exists_mem_filter_basis Set.PairwiseDisjoint.exists_mem_filter_basisₓ'. -/
theorem Set.PairwiseDisjoint.exists_mem_filter_basis {I : Type _} {l : I → Filter α}
    {ι : I → Sort _} {p : ∀ i, ι i → Prop} {s : ∀ i, ι i → Set α} {S : Set I}
    (hd : S.PairwiseDisjoint l) (hS : S.Finite) (h : ∀ i, (l i).HasBasis (p i) (s i)) :
    ∃ ind : ∀ i, ι i, (∀ i, p i (ind i)) ∧ S.PairwiseDisjoint fun i => s i (ind i) :=
  by
  rcases hd.exists_mem_filter hS with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono ht⟩
#align set.pairwise_disjoint.exists_mem_filter_basis Set.PairwiseDisjoint.exists_mem_filter_basis

/- warning: filter.inf_ne_bot_iff -> Filter.inf_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {l' : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l l')) (forall {{s : Set.{u1} α}}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) -> (forall {{s' : Set.{u1} α}}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s' l') -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s'))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {l' : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l l')) (forall {{s : Set.{u1} α}}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) -> (forall {{s' : Set.{u1} α}}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s' l') -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s s'))))
Case conversion may be inaccurate. Consider using '#align filter.inf_ne_bot_iff Filter.inf_neBot_iffₓ'. -/
theorem inf_neBot_iff :
    NeBot (l ⊓ l') ↔ ∀ ⦃s : Set α⦄ (hs : s ∈ l) ⦃s'⦄ (hs' : s' ∈ l'), (s ∩ s').Nonempty :=
  l.basis_sets.inf_neBot_iff
#align filter.inf_ne_bot_iff Filter.inf_neBot_iff

/- warning: filter.inf_principal_ne_bot_iff -> Filter.inf_principal_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {s : Set.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l (Filter.principal.{u1} α s))) (forall (U : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U l) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U s)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {s : Set.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l (Filter.principal.{u1} α s))) (forall (U : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U l) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U s)))
Case conversion may be inaccurate. Consider using '#align filter.inf_principal_ne_bot_iff Filter.inf_principal_neBot_iffₓ'. -/
theorem inf_principal_neBot_iff {s : Set α} : NeBot (l ⊓ 𝓟 s) ↔ ∀ U ∈ l, (U ∩ s).Nonempty :=
  l.basis_sets.inf_principal_neBot_iff
#align filter.inf_principal_ne_bot_iff Filter.inf_principal_neBot_iff

/- warning: filter.mem_iff_inf_principal_compl -> Filter.mem_iff_inf_principal_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.mem_iff_inf_principal_compl Filter.mem_iff_inf_principal_complₓ'. -/
theorem mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∈ f ↔ f ⊓ 𝓟 (sᶜ) = ⊥ :=
  by
  refine' not_iff_not.1 ((inf_principal_ne_bot_iff.trans _).symm.trans ne_bot_iff)
  exact
    ⟨fun h hs => by simpa [not_nonempty_empty] using h s hs, fun hs t ht =>
      inter_compl_nonempty_iff.2 fun hts => hs <| mem_of_superset ht hts⟩
#align filter.mem_iff_inf_principal_compl Filter.mem_iff_inf_principal_compl

/- warning: filter.not_mem_iff_inf_principal_compl -> Filter.not_mem_iff_inf_principal_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Not (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f)) (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Not (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f)) (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))))
Case conversion may be inaccurate. Consider using '#align filter.not_mem_iff_inf_principal_compl Filter.not_mem_iff_inf_principal_complₓ'. -/
theorem not_mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∉ f ↔ NeBot (f ⊓ 𝓟 (sᶜ)) :=
  (not_congr mem_iff_inf_principal_compl).trans neBot_iff.symm
#align filter.not_mem_iff_inf_principal_compl Filter.not_mem_iff_inf_principal_compl

/- warning: filter.disjoint_principal_right -> Filter.disjoint_principal_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) f (Filter.principal.{u1} α s)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) f (Filter.principal.{u1} α s)) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) f)
Case conversion may be inaccurate. Consider using '#align filter.disjoint_principal_right Filter.disjoint_principal_rightₓ'. -/
@[simp]
theorem disjoint_principal_right {f : Filter α} {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ ∈ f := by
  rw [mem_iff_inf_principal_compl, compl_compl, disjoint_iff]
#align filter.disjoint_principal_right Filter.disjoint_principal_right

/- warning: filter.disjoint_principal_left -> Filter.disjoint_principal_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Filter.principal.{u1} α s) f) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Filter.principal.{u1} α s) f) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) f)
Case conversion may be inaccurate. Consider using '#align filter.disjoint_principal_left Filter.disjoint_principal_leftₓ'. -/
@[simp]
theorem disjoint_principal_left {f : Filter α} {s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ ∈ f := by
  rw [disjoint_comm, disjoint_principal_right]
#align filter.disjoint_principal_left Filter.disjoint_principal_left

/- warning: filter.disjoint_principal_principal -> Filter.disjoint_principal_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t)) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t)) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t)
Case conversion may be inaccurate. Consider using '#align filter.disjoint_principal_principal Filter.disjoint_principal_principalₓ'. -/
@[simp]
theorem disjoint_principal_principal {s t : Set α} : Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t := by
  simp [← subset_compl_iff_disjoint_left]
#align filter.disjoint_principal_principal Filter.disjoint_principal_principal

/- warning: disjoint.filter_principal -> Disjoint.filter_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t))
Case conversion may be inaccurate. Consider using '#align disjoint.filter_principal Disjoint.filter_principalₓ'. -/
alias disjoint_principal_principal ↔ _ _root_.disjoint.filter_principal
#align disjoint.filter_principal Disjoint.filter_principal

/- warning: filter.disjoint_pure_pure -> Filter.disjoint_pure_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {y : α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α x) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α y)) (Ne.{succ u1} α x y)
but is expected to have type
  forall {α : Type.{u1}} {x : α} {y : α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α x) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α y)) (Ne.{succ u1} α x y)
Case conversion may be inaccurate. Consider using '#align filter.disjoint_pure_pure Filter.disjoint_pure_pureₓ'. -/
@[simp]
theorem disjoint_pure_pure {x y : α} : Disjoint (pure x : Filter α) (pure y) ↔ x ≠ y := by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]
#align filter.disjoint_pure_pure Filter.disjoint_pure_pure

/- warning: filter.compl_diagonal_mem_prod -> Filter.compl_diagonal_mem_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) (HasCompl.compl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.booleanAlgebra.{u1} (Prod.{u1, u1} α α))) (Set.diagonal.{u1} α)) (Filter.prod.{u1, u1} α α l₁ l₂)) (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) l₁ l₂)
but is expected to have type
  forall {α : Type.{u1}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) (HasCompl.compl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α))) (Set.diagonal.{u1} α)) (Filter.prod.{u1, u1} α α l₁ l₂)) (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align filter.compl_diagonal_mem_prod Filter.compl_diagonal_mem_prodₓ'. -/
@[simp]
theorem compl_diagonal_mem_prod {l₁ l₂ : Filter α} : diagonal αᶜ ∈ l₁ ×ᶠ l₂ ↔ Disjoint l₁ l₂ := by
  simp only [mem_prod_iff, Filter.disjoint_iff, prod_subset_compl_diagonal_iff_disjoint]
#align filter.compl_diagonal_mem_prod Filter.compl_diagonal_mem_prod

theorem HasBasis.disjoint_iff_left (h : l.HasBasis p s) :
    Disjoint l l' ↔ ∃ (i : _)(hi : p i), s iᶜ ∈ l' := by
  simp only [h.disjoint_iff l'.basis_sets, exists_prop, id, ← disjoint_principal_left,
    (has_basis_principal _).disjoint_iff l'.basis_sets, Unique.exists_iff]
#align filter.has_basis.disjoint_iff_left Filter.HasBasis.disjoint_iff_leftₓ

theorem HasBasis.disjoint_iff_right (h : l.HasBasis p s) :
    Disjoint l' l ↔ ∃ (i : _)(hi : p i), s iᶜ ∈ l' :=
  disjoint_comm.trans h.disjoint_iff_leftₓ
#align filter.has_basis.disjoint_iff_right Filter.HasBasis.disjoint_iff_rightₓ

/- warning: filter.le_iff_forall_inf_principal_compl -> Filter.le_iff_forall_inf_principal_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g) (forall (V : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) V g) -> (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) V))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g) (forall (V : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) V g) -> (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) V))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align filter.le_iff_forall_inf_principal_compl Filter.le_iff_forall_inf_principal_complₓ'. -/
theorem le_iff_forall_inf_principal_compl {f g : Filter α} : f ≤ g ↔ ∀ V ∈ g, f ⊓ 𝓟 (Vᶜ) = ⊥ :=
  forall₂_congr fun _ _ => mem_iff_inf_principal_compl
#align filter.le_iff_forall_inf_principal_compl Filter.le_iff_forall_inf_principal_compl

/- warning: filter.inf_ne_bot_iff_frequently_left -> Filter.inf_neBot_iff_frequently_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) (forall {p : α -> Prop}, (Filter.Eventually.{u1} α (fun (x : α) => p x) f) -> (Filter.Frequently.{u1} α (fun (x : α) => p x) g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) (forall {p : α -> Prop}, (Filter.Eventually.{u1} α (fun (x : α) => p x) f) -> (Filter.Frequently.{u1} α (fun (x : α) => p x) g))
Case conversion may be inaccurate. Consider using '#align filter.inf_ne_bot_iff_frequently_left Filter.inf_neBot_iff_frequently_leftₓ'. -/
theorem inf_neBot_iff_frequently_left {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in f, p x) → ∃ᶠ x in g, p x := by
  simpa only [inf_ne_bot_iff, frequently_iff, exists_prop, and_comm']
#align filter.inf_ne_bot_iff_frequently_left Filter.inf_neBot_iff_frequently_left

/- warning: filter.inf_ne_bot_iff_frequently_right -> Filter.inf_neBot_iff_frequently_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) (forall {p : α -> Prop}, (Filter.Eventually.{u1} α (fun (x : α) => p x) g) -> (Filter.Frequently.{u1} α (fun (x : α) => p x) f))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) (forall {p : α -> Prop}, (Filter.Eventually.{u1} α (fun (x : α) => p x) g) -> (Filter.Frequently.{u1} α (fun (x : α) => p x) f))
Case conversion may be inaccurate. Consider using '#align filter.inf_ne_bot_iff_frequently_right Filter.inf_neBot_iff_frequently_rightₓ'. -/
theorem inf_neBot_iff_frequently_right {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in g, p x) → ∃ᶠ x in f, p x :=
  by
  rw [inf_comm]
  exact inf_ne_bot_iff_frequently_left
#align filter.inf_ne_bot_iff_frequently_right Filter.inf_neBot_iff_frequently_right

/- warning: filter.has_basis.eq_binfi -> Filter.HasBasis.eq_binfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Eq.{succ u1} (Filter.{u1} α) l (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (p i) (fun (_x : p i) => Filter.principal.{u1} α (s i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Eq.{succ u2} (Filter.{u2} α) l (infᵢ.{u2, u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => infᵢ.{u2, 0} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) (p i) (fun (_x : p i) => Filter.principal.{u2} α (s i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.eq_binfi Filter.HasBasis.eq_binfᵢₓ'. -/
theorem HasBasis.eq_binfᵢ (h : l.HasBasis p s) : l = ⨅ (i) (_ : p i), 𝓟 (s i) :=
  eq_binfᵢ_of_mem_iff_exists_mem fun t => by simp only [h.mem_iff, mem_principal]
#align filter.has_basis.eq_binfi Filter.HasBasis.eq_binfᵢ

/- warning: filter.has_basis.eq_infi -> Filter.HasBasis.eq_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l (fun (_x : ι) => True) s) -> (Eq.{succ u1} (Filter.{u1} α) l (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => Filter.principal.{u1} α (s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l (fun (_x : ι) => True) s) -> (Eq.{succ u2} (Filter.{u2} α) l (infᵢ.{u2, u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => Filter.principal.{u2} α (s i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.eq_infi Filter.HasBasis.eq_infᵢₓ'. -/
theorem HasBasis.eq_infᵢ (h : l.HasBasis (fun _ => True) s) : l = ⨅ i, 𝓟 (s i) := by
  simpa only [infᵢ_true] using h.eq_binfi
#align filter.has_basis.eq_infi Filter.HasBasis.eq_infᵢ

/- warning: filter.has_basis_infi_principal -> Filter.hasBasis_infᵢ_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, (Directed.{u1, u2} (Set.{u1} α) ι (GE.ge.{u1} (Set.{u1} α) (Set.hasLe.{u1} α)) s) -> (forall [_inst_1 : Nonempty.{u2} ι], Filter.HasBasis.{u1, u2} α ι (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => Filter.principal.{u1} α (s i))) (fun (_x : ι) => True) s)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)}, (Directed.{u2, u1} (Set.{u2} α) ι (fun (x._@.Mathlib.Order.Filter.Bases._hyg.9263 : Set.{u2} α) (x._@.Mathlib.Order.Filter.Bases._hyg.9265 : Set.{u2} α) => GE.ge.{u2} (Set.{u2} α) (Set.instLESet.{u2} α) x._@.Mathlib.Order.Filter.Bases._hyg.9263 x._@.Mathlib.Order.Filter.Bases._hyg.9265) s) -> (forall [_inst_1 : Nonempty.{u1} ι], Filter.HasBasis.{u2, u1} α ι (infᵢ.{u2, u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => Filter.principal.{u2} α (s i))) (fun (_x : ι) => True) s)
Case conversion may be inaccurate. Consider using '#align filter.has_basis_infi_principal Filter.hasBasis_infᵢ_principalₓ'. -/
theorem hasBasis_infᵢ_principal {s : ι → Set α} (h : Directed (· ≥ ·) s) [Nonempty ι] :
    (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True) s :=
  ⟨by
    refine' fun t =>
      (mem_infi_of_directed (h.mono_comp _ _) t).trans <| by
        simp only [exists_prop, true_and_iff, mem_principal]
    exact fun _ _ => principal_mono.2⟩
#align filter.has_basis_infi_principal Filter.hasBasis_infᵢ_principal

/- warning: filter.has_basis_infi_principal_finite -> Filter.hasBasis_infᵢ_principal_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : ι -> (Set.{u1} α)), Filter.HasBasis.{u1, succ u2} α (Set.{u2} ι) (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => Filter.principal.{u1} α (s i))) (fun (t : Set.{u2} ι) => Set.Finite.{u2} ι t) (fun (t : Set.{u2} ι) => Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => s i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : ι -> (Set.{u1} α)), Filter.HasBasis.{u1, succ u2} α (Set.{u2} ι) (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => Filter.principal.{u1} α (s i))) (fun (t : Set.{u2} ι) => Set.Finite.{u2} ι t) (fun (t : Set.{u2} ι) => Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) => s i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis_infi_principal_finite Filter.hasBasis_infᵢ_principal_finiteₓ'. -/
/-- If `s : ι → set α` is an indexed family of sets, then finite intersections of `s i` form a basis
of `⨅ i, 𝓟 (s i)`.  -/
theorem hasBasis_infᵢ_principal_finite {ι : Type _} (s : ι → Set α) :
    (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite) fun t => ⋂ i ∈ t, s i :=
  by
  refine' ⟨fun U => (mem_infi_finite _).trans _⟩
  simp only [infi_principal_finset, mem_Union, mem_principal, exists_prop, exists_finite_iff_finset,
    Finset.set_binterᵢ_coe]
#align filter.has_basis_infi_principal_finite Filter.hasBasis_infᵢ_principal_finite

/- warning: filter.has_basis_binfi_principal -> Filter.hasBasis_binfᵢ_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : β -> (Set.{u1} α)} {S : Set.{u2} β}, (DirectedOn.{u2} β (Order.Preimage.{succ u2, succ u1} β (Set.{u1} α) s (GE.ge.{u1} (Set.{u1} α) (Set.hasLe.{u1} α))) S) -> (Set.Nonempty.{u2} β S) -> (Filter.HasBasis.{u1, succ u2} α β (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) β (fun (i : β) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i S) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i S) => Filter.principal.{u1} α (s i)))) (fun (i : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i S) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : β -> (Set.{u2} α)} {S : Set.{u1} β}, (DirectedOn.{u1} β (Order.Preimage.{succ u1, succ u2} β (Set.{u2} α) s (fun (x._@.Mathlib.Order.Filter.Bases._hyg.9496 : Set.{u2} α) (x._@.Mathlib.Order.Filter.Bases._hyg.9498 : Set.{u2} α) => GE.ge.{u2} (Set.{u2} α) (Set.instLESet.{u2} α) x._@.Mathlib.Order.Filter.Bases._hyg.9496 x._@.Mathlib.Order.Filter.Bases._hyg.9498)) S) -> (Set.Nonempty.{u1} β S) -> (Filter.HasBasis.{u2, succ u1} α β (infᵢ.{u2, succ u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) β (fun (i : β) => infᵢ.{u2, 0} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) i S) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) i S) => Filter.principal.{u2} α (s i)))) (fun (i : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) i S) s)
Case conversion may be inaccurate. Consider using '#align filter.has_basis_binfi_principal Filter.hasBasis_binfᵢ_principalₓ'. -/
theorem hasBasis_binfᵢ_principal {s : β → Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· ≥ ·)) S)
    (ne : S.Nonempty) : (⨅ i ∈ S, 𝓟 (s i)).HasBasis (fun i => i ∈ S) s :=
  ⟨by
    refine' fun t => (mem_binfi_of_directed _ Ne).trans <| by simp only [mem_principal]
    rw [directedOn_iff_directed, ← directed_comp, (· ∘ ·)] at h⊢
    apply h.mono_comp _ _
    exact fun _ _ => principal_mono.2⟩
#align filter.has_basis_binfi_principal Filter.hasBasis_binfᵢ_principal

/- warning: filter.has_basis_binfi_principal' -> Filter.hasBasis_binfᵢ_principal' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (forall (i : ι), (p i) -> (forall (j : ι), (p j) -> (Exists.{succ u2} ι (fun (k : ι) => Exists.{0} (p k) (fun (h : p k) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s k) (s i)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s k) (s j))))))) -> (Exists.{succ u2} ι (fun (i : ι) => p i)) -> (Filter.HasBasis.{u1, succ u2} α ι (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (p i) (fun (h : p i) => Filter.principal.{u1} α (s i)))) p s)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (forall (i : ι), (p i) -> (forall (j : ι), (p j) -> (Exists.{succ u2} ι (fun (k : ι) => And (p k) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (s k) (s i)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (s k) (s j))))))) -> (Exists.{succ u2} ι (fun (i : ι) => p i)) -> (Filter.HasBasis.{u1, succ u2} α ι (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (p i) (fun (h : p i) => Filter.principal.{u1} α (s i)))) p s)
Case conversion may be inaccurate. Consider using '#align filter.has_basis_binfi_principal' Filter.hasBasis_binfᵢ_principal'ₓ'. -/
theorem hasBasis_binfᵢ_principal' {ι : Type _} {p : ι → Prop} {s : ι → Set α}
    (h : ∀ i, p i → ∀ j, p j → ∃ (k : _)(h : p k), s k ⊆ s i ∧ s k ⊆ s j) (ne : ∃ i, p i) :
    (⨅ (i) (h : p i), 𝓟 (s i)).HasBasis p s :=
  Filter.hasBasis_binfᵢ_principal h Ne
#align filter.has_basis_binfi_principal' Filter.hasBasis_binfᵢ_principal'

/- warning: filter.has_basis.map -> Filter.HasBasis.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} (f : α -> β), (Filter.HasBasis.{u1, u3} α ι l p s) -> (Filter.HasBasis.{u2, u3} β ι (Filter.map.{u1, u2} α β f l) p (fun (i : ι) => Set.image.{u1, u2} α β f (s i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} (f : α -> β), (Filter.HasBasis.{u3, u2} α ι l p s) -> (Filter.HasBasis.{u1, u2} β ι (Filter.map.{u3, u1} α β f l) p (fun (i : ι) => Set.image.{u3, u1} α β f (s i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.map Filter.HasBasis.mapₓ'. -/
theorem HasBasis.map (f : α → β) (hl : l.HasBasis p s) : (l.map f).HasBasis p fun i => f '' s i :=
  ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩
#align filter.has_basis.map Filter.HasBasis.map

/- warning: filter.has_basis.comap -> Filter.HasBasis.comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} (f : β -> α), (Filter.HasBasis.{u1, u3} α ι l p s) -> (Filter.HasBasis.{u2, u3} β ι (Filter.comap.{u2, u1} β α f l) p (fun (i : ι) => Set.preimage.{u2, u1} β α f (s i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} (f : β -> α), (Filter.HasBasis.{u3, u2} α ι l p s) -> (Filter.HasBasis.{u1, u2} β ι (Filter.comap.{u1, u3} β α f l) p (fun (i : ι) => Set.preimage.{u1, u3} β α f (s i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.comap Filter.HasBasis.comapₓ'. -/
theorem HasBasis.comap (f : β → α) (hl : l.HasBasis p s) :
    (l.comap f).HasBasis p fun i => f ⁻¹' s i :=
  ⟨by
    intro t
    simp only [mem_comap, exists_prop, hl.mem_iff]
    constructor
    · rintro ⟨t', ⟨i, hi, ht'⟩, H⟩
      exact ⟨i, hi, subset.trans (preimage_mono ht') H⟩
    · rintro ⟨i, hi, H⟩
      exact ⟨s i, ⟨i, hi, subset.refl _⟩, H⟩⟩
#align filter.has_basis.comap Filter.HasBasis.comap

#print Filter.comap_hasBasis /-
theorem comap_hasBasis (f : α → β) (l : Filter β) :
    HasBasis (comap f l) (fun s : Set β => s ∈ l) fun s => f ⁻¹' s :=
  ⟨fun t => mem_comap⟩
#align filter.comap_has_basis Filter.comap_hasBasis
-/

/- warning: filter.has_basis.forall_mem_mem -> Filter.HasBasis.forall_mem_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (forall {x : α}, Iff (forall (t : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)) (forall (i : ι), (p i) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (forall {x : α}, Iff (forall (t : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t l) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t)) (forall (i : ι), (p i) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.forall_mem_mem Filter.HasBasis.forall_mem_memₓ'. -/
theorem HasBasis.forall_mem_mem (h : HasBasis l p s) {x : α} :
    (∀ t ∈ l, x ∈ t) ↔ ∀ i, p i → x ∈ s i :=
  by
  simp only [h.mem_iff, exists_imp]
  exact ⟨fun h i hi => h (s i) i hi subset.rfl, fun h t i hi ht => ht (h i hi)⟩
#align filter.has_basis.forall_mem_mem Filter.HasBasis.forall_mem_mem

/- warning: filter.has_basis.binfi_mem -> Filter.HasBasis.binfᵢ_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} [_inst_1 : CompleteLattice.{u2} β] {f : (Set.{u1} α) -> β}, (Filter.HasBasis.{u1, u3} α ι l p s) -> (Monotone.{u1, u2} (Set.{u1} α) β (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1))) f) -> (Eq.{succ u2} β (infᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toHasInf.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_1)) (Set.{u1} α) (fun (t : Set.{u1} α) => infᵢ.{u2, 0} β (ConditionallyCompleteLattice.toHasInf.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_1)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l) => f t))) (infᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_1)) ι (fun (i : ι) => infᵢ.{u2, 0} β (ConditionallyCompleteLattice.toHasInf.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_1)) (p i) (fun (hi : p i) => f (s i)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)} [_inst_1 : CompleteLattice.{u3} β] {f : (Set.{u2} α) -> β}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Monotone.{u2, u3} (Set.{u2} α) β (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_1))) f) -> (Eq.{succ u3} β (infᵢ.{u3, succ u2} β (CompleteLattice.toInfSet.{u3} β _inst_1) (Set.{u2} α) (fun (t : Set.{u2} α) => infᵢ.{u3, 0} β (CompleteLattice.toInfSet.{u3} β _inst_1) (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t l) (fun (H : Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t l) => f t))) (infᵢ.{u3, u1} β (CompleteLattice.toInfSet.{u3} β _inst_1) ι (fun (i : ι) => infᵢ.{u3, 0} β (CompleteLattice.toInfSet.{u3} β _inst_1) (p i) (fun (hi : p i) => f (s i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.binfi_mem Filter.HasBasis.binfᵢ_memₓ'. -/
protected theorem HasBasis.binfᵢ_mem [CompleteLattice β] {f : Set α → β} (h : HasBasis l p s)
    (hf : Monotone f) : (⨅ t ∈ l, f t) = ⨅ (i) (hi : p i), f (s i) :=
  le_antisymm (le_infᵢ₂ fun i hi => infᵢ₂_le (s i) (h.mem_of_mem hi)) <|
    le_infᵢ₂ fun t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      infᵢ₂_le_of_le i hpi (hf hi)
#align filter.has_basis.binfi_mem Filter.HasBasis.binfᵢ_mem

/- warning: filter.has_basis.bInter_mem -> Filter.HasBasis.binterᵢ_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {f : (Set.{u1} α) -> (Set.{u2} β)}, (Filter.HasBasis.{u1, u3} α ι l p s) -> (Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) f) -> (Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β (Set.{u1} α) (fun (t : Set.{u1} α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t l) => f t))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, 0} β (p i) (fun (hi : p i) => f (s i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u3} α} {p : ι -> Prop} {s : ι -> (Set.{u3} α)} {f : (Set.{u3} α) -> (Set.{u2} β)}, (Filter.HasBasis.{u3, u1} α ι l p s) -> (Monotone.{u3, u2} (Set.{u3} α) (Set.{u2} β) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) f) -> (Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u3} β (Set.{u3} α) (fun (t : Set.{u3} α) => Set.interᵢ.{u2, 0} β (Membership.mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (instMembershipSetFilter.{u3} α) t l) (fun (H : Membership.mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (instMembershipSetFilter.{u3} α) t l) => f t))) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => Set.interᵢ.{u2, 0} β (p i) (fun (hi : p i) => f (s i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.bInter_mem Filter.HasBasis.binterᵢ_memₓ'. -/
protected theorem HasBasis.binterᵢ_mem {f : Set α → Set β} (h : HasBasis l p s) (hf : Monotone f) :
    (⋂ t ∈ l, f t) = ⋂ (i) (hi : p i), f (s i) :=
  h.binfᵢ_mem hf
#align filter.has_basis.bInter_mem Filter.HasBasis.binterᵢ_mem

/- warning: filter.has_basis.sInter_sets -> Filter.HasBasis.interₛ_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {l : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι l p s) -> (Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (Filter.sets.{u1} α l)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (p i) (fun (hi : p i) => s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {l : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι l p s) -> (Eq.{succ u2} (Set.{u2} α) (Set.interₛ.{u2} α (Filter.sets.{u2} α l)) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (p i) (fun (hi : p i) => s i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.sInter_sets Filter.HasBasis.interₛ_setsₓ'. -/
theorem HasBasis.interₛ_sets (h : HasBasis l p s) : ⋂₀ l.sets = ⋂ (i) (hi : p i), s i :=
  by
  rw [sInter_eq_bInter]
  exact h.bInter_mem monotone_id
#align filter.has_basis.sInter_sets Filter.HasBasis.interₛ_sets

variable {ι'' : Type _} [Preorder ι''] (l) (s'' : ι'' → Set α)

#print Filter.IsAntitoneBasis /-
/-- `is_antitone_basis s` means the image of `s` is a filter basis such that `s` is decreasing. -/
@[protect_proj]
structure IsAntitoneBasis extends IsBasis (fun _ => True) s'' : Prop where
  Antitone : Antitone s''
#align filter.is_antitone_basis Filter.IsAntitoneBasis
-/

#print Filter.HasAntitoneBasis /-
/-- We say that a filter `l` has an antitone basis `s : ι → set α`, if `t ∈ l` if and only if `t`
includes `s i` for some `i`, and `s` is decreasing. -/
@[protect_proj]
structure HasAntitoneBasis (l : Filter α) (s : ι'' → Set α) extends HasBasis l (fun _ => True) s :
  Prop where
  Antitone : Antitone s
#align filter.has_antitone_basis Filter.HasAntitoneBasis
-/

/- warning: filter.has_antitone_basis.map -> Filter.HasAntitoneBasis.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι'' : Type.{u3}} [_inst_1 : Preorder.{u3} ι''] {l : Filter.{u1} α} {s : ι'' -> (Set.{u1} α)} {m : α -> β}, (Filter.HasAntitoneBasis.{u1, u3} α ι'' _inst_1 l s) -> (Filter.HasAntitoneBasis.{u2, u3} β ι'' _inst_1 (Filter.map.{u1, u2} α β m l) (fun (n : ι'') => Set.image.{u1, u2} α β m (s n)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {ι'' : Type.{u2}} [_inst_1 : Preorder.{u2} ι''] {l : Filter.{u3} α} {s : ι'' -> (Set.{u3} α)} {m : α -> β}, (Filter.HasAntitoneBasis.{u3, u2} α ι'' _inst_1 l s) -> (Filter.HasAntitoneBasis.{u1, u2} β ι'' _inst_1 (Filter.map.{u3, u1} α β m l) (fun (n : ι'') => Set.image.{u3, u1} α β m (s n)))
Case conversion may be inaccurate. Consider using '#align filter.has_antitone_basis.map Filter.HasAntitoneBasis.mapₓ'. -/
theorem HasAntitoneBasis.map {l : Filter α} {s : ι'' → Set α} {m : α → β}
    (hf : HasAntitoneBasis l s) : HasAntitoneBasis (map m l) fun n => m '' s n :=
  ⟨HasBasis.map _ hf.to_hasBasis, fun i j hij => image_subset _ <| hf.2 hij⟩
#align filter.has_antitone_basis.map Filter.HasAntitoneBasis.map

end SameType

section TwoTypes

variable {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β} {pb : ι' → Prop}
  {sb : ι' → Set β} {f : α → β}

theorem HasBasis.tendsto_left_iff (hla : la.HasBasis pa sa) :
    Tendsto f la lb ↔ ∀ t ∈ lb, ∃ (i : _)(hi : pa i), MapsTo f (sa i) t :=
  by
  simp only [tendsto, (hla.map f).le_iffₓ, image_subset_iff]
  rfl
#align filter.has_basis.tendsto_left_iff Filter.HasBasis.tendsto_left_iffₓ

/- warning: filter.has_basis.tendsto_right_iff -> Filter.HasBasis.tendsto_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι' : Sort.{u3}} {la : Filter.{u1} α} {lb : Filter.{u2} β} {pb : ι' -> Prop} {sb : ι' -> (Set.{u2} β)} {f : α -> β}, (Filter.HasBasis.{u2, u3} β ι' lb pb sb) -> (Iff (Filter.Tendsto.{u1, u2} α β f la lb) (forall (i : ι'), (pb i) -> (Filter.Eventually.{u1} α (fun (x : α) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) (sb i)) la)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {ι' : Sort.{u2}} {la : Filter.{u1} α} {lb : Filter.{u3} β} {pb : ι' -> Prop} {sb : ι' -> (Set.{u3} β)} {f : α -> β}, (Filter.HasBasis.{u3, u2} β ι' lb pb sb) -> (Iff (Filter.Tendsto.{u1, u3} α β f la lb) (forall (i : ι'), (pb i) -> (Filter.Eventually.{u1} α (fun (x : α) => Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) (f x) (sb i)) la)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.tendsto_right_iff Filter.HasBasis.tendsto_right_iffₓ'. -/
theorem HasBasis.tendsto_right_iff (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ (i) (hi : pb i), ∀ᶠ x in la, f x ∈ sb i := by
  simpa only [tendsto, hlb.ge_iff, mem_map, Filter.Eventually]
#align filter.has_basis.tendsto_right_iff Filter.HasBasis.tendsto_right_iff

theorem HasBasis.tendsto_iff (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ (ib) (hib : pb ib), ∃ (ia : _)(hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib := by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]
#align filter.has_basis.tendsto_iff Filter.HasBasis.tendsto_iffₓ

theorem Tendsto.basis_left (H : Tendsto f la lb) (hla : la.HasBasis pa sa) :
    ∀ t ∈ lb, ∃ (i : _)(hi : pa i), MapsTo f (sa i) t :=
  hla.tendsto_left_iffₓ.1 H
#align filter.tendsto.basis_left Filter.Tendsto.basis_leftₓ

/- warning: filter.tendsto.basis_right -> Filter.Tendsto.basis_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι' : Sort.{u3}} {la : Filter.{u1} α} {lb : Filter.{u2} β} {pb : ι' -> Prop} {sb : ι' -> (Set.{u2} β)} {f : α -> β}, (Filter.Tendsto.{u1, u2} α β f la lb) -> (Filter.HasBasis.{u2, u3} β ι' lb pb sb) -> (forall (i : ι'), (pb i) -> (Filter.Eventually.{u1} α (fun (x : α) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) (sb i)) la))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι' : Sort.{u1}} {la : Filter.{u3} α} {lb : Filter.{u2} β} {pb : ι' -> Prop} {sb : ι' -> (Set.{u2} β)} {f : α -> β}, (Filter.Tendsto.{u3, u2} α β f la lb) -> (Filter.HasBasis.{u2, u1} β ι' lb pb sb) -> (forall (i : ι'), (pb i) -> (Filter.Eventually.{u3} α (fun (x : α) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (f x) (sb i)) la))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.basis_right Filter.Tendsto.basis_rightₓ'. -/
theorem Tendsto.basis_right (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb) :
    ∀ (i) (hi : pb i), ∀ᶠ x in la, f x ∈ sb i :=
  hlb.tendsto_right_iff.1 H
#align filter.tendsto.basis_right Filter.Tendsto.basis_right

theorem Tendsto.basis_both (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
    (hlb : lb.HasBasis pb sb) :
    ∀ (ib) (hib : pb ib), ∃ (ia : _)(hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib :=
  (hla.tendsto_iffₓ hlb).1 H
#align filter.tendsto.basis_both Filter.Tendsto.basis_bothₓ

/- warning: filter.has_basis.prod_pprod -> Filter.HasBasis.prod_pprod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {ι' : Sort.{u4}} {la : Filter.{u1} α} {pa : ι -> Prop} {sa : ι -> (Set.{u1} α)} {lb : Filter.{u2} β} {pb : ι' -> Prop} {sb : ι' -> (Set.{u2} β)}, (Filter.HasBasis.{u1, u3} α ι la pa sa) -> (Filter.HasBasis.{u2, u4} β ι' lb pb sb) -> (Filter.HasBasis.{max u1 u2, max 1 u3 u4} (Prod.{u1, u2} α β) (PProd.{u3, u4} ι ι') (Filter.prod.{u1, u2} α β la lb) (fun (i : PProd.{u3, u4} ι ι') => And (pa (PProd.fst.{u3, u4} ι ι' i)) (pb (PProd.snd.{u3, u4} ι ι' i))) (fun (i : PProd.{u3, u4} ι ι') => Set.prod.{u1, u2} α β (sa (PProd.fst.{u3, u4} ι ι' i)) (sb (PProd.snd.{u3, u4} ι ι' i))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {ι : Sort.{u3}} {ι' : Sort.{u1}} {la : Filter.{u4} α} {pa : ι -> Prop} {sa : ι -> (Set.{u4} α)} {lb : Filter.{u2} β} {pb : ι' -> Prop} {sb : ι' -> (Set.{u2} β)}, (Filter.HasBasis.{u4, u3} α ι la pa sa) -> (Filter.HasBasis.{u2, u1} β ι' lb pb sb) -> (Filter.HasBasis.{max u4 u2, max (max 1 u3) u1} (Prod.{u4, u2} α β) (PProd.{u3, u1} ι ι') (Filter.prod.{u4, u2} α β la lb) (fun (i : PProd.{u3, u1} ι ι') => And (pa (PProd.fst.{u3, u1} ι ι' i)) (pb (PProd.snd.{u3, u1} ι ι' i))) (fun (i : PProd.{u3, u1} ι ι') => Set.prod.{u4, u2} α β (sa (PProd.fst.{u3, u1} ι ι' i)) (sb (PProd.snd.{u3, u1} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.prod_pprod Filter.HasBasis.prod_pprodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_pprod (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ᶠ lb).HasBasis (fun i : PProd ι ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)
#align filter.has_basis.prod_pprod Filter.HasBasis.prod_pprod

/- warning: filter.has_basis.prod -> Filter.HasBasis.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {la : Filter.{u1} α} {lb : Filter.{u2} β} {ι : Type.{u3}} {ι' : Type.{u4}} {pa : ι -> Prop} {sa : ι -> (Set.{u1} α)} {pb : ι' -> Prop} {sb : ι' -> (Set.{u2} β)}, (Filter.HasBasis.{u1, succ u3} α ι la pa sa) -> (Filter.HasBasis.{u2, succ u4} β ι' lb pb sb) -> (Filter.HasBasis.{max u1 u2, max (succ u3) (succ u4)} (Prod.{u1, u2} α β) (Prod.{u3, u4} ι ι') (Filter.prod.{u1, u2} α β la lb) (fun (i : Prod.{u3, u4} ι ι') => And (pa (Prod.fst.{u3, u4} ι ι' i)) (pb (Prod.snd.{u3, u4} ι ι' i))) (fun (i : Prod.{u3, u4} ι ι') => Set.prod.{u1, u2} α β (sa (Prod.fst.{u3, u4} ι ι' i)) (sb (Prod.snd.{u3, u4} ι ι' i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {la : Filter.{u2} α} {lb : Filter.{u1} β} {ι : Type.{u4}} {ι' : Type.{u3}} {pa : ι -> Prop} {sa : ι -> (Set.{u2} α)} {pb : ι' -> Prop} {sb : ι' -> (Set.{u1} β)}, (Filter.HasBasis.{u2, succ u4} α ι la pa sa) -> (Filter.HasBasis.{u1, succ u3} β ι' lb pb sb) -> (Filter.HasBasis.{max u2 u1, max (succ u4) (succ u3)} (Prod.{u2, u1} α β) (Prod.{u4, u3} ι ι') (Filter.prod.{u2, u1} α β la lb) (fun (i : Prod.{u4, u3} ι ι') => And (pa (Prod.fst.{u4, u3} ι ι' i)) (pb (Prod.snd.{u4, u3} ι ι' i))) (fun (i : Prod.{u4, u3} ι ι') => Set.prod.{u2, u1} α β (sa (Prod.fst.{u4, u3} ι ι' i)) (sb (Prod.snd.{u4, u3} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.prod Filter.HasBasis.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod {ι ι' : Type _} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ᶠ lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf (hlb.comap Prod.snd)
#align filter.has_basis.prod Filter.HasBasis.prod

/- warning: filter.has_basis.prod_same_index -> Filter.HasBasis.prod_same_index is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {la : Filter.{u1} α} {sa : ι -> (Set.{u1} α)} {lb : Filter.{u2} β} {p : ι -> Prop} {sb : ι -> (Set.{u2} β)}, (Filter.HasBasis.{u1, u3} α ι la p sa) -> (Filter.HasBasis.{u2, u3} β ι lb p sb) -> (forall {i : ι} {j : ι}, (p i) -> (p j) -> (Exists.{u3} ι (fun (k : ι) => And (p k) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (sa k) (sa i)) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (sb k) (sb j)))))) -> (Filter.HasBasis.{max u1 u2, u3} (Prod.{u1, u2} α β) ι (Filter.prod.{u1, u2} α β la lb) p (fun (i : ι) => Set.prod.{u1, u2} α β (sa i) (sb i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {la : Filter.{u2} α} {sa : ι -> (Set.{u2} α)} {lb : Filter.{u3} β} {p : ι -> Prop} {sb : ι -> (Set.{u3} β)}, (Filter.HasBasis.{u2, u1} α ι la p sa) -> (Filter.HasBasis.{u3, u1} β ι lb p sb) -> (forall {i : ι} {j : ι}, (p i) -> (p j) -> (Exists.{u1} ι (fun (k : ι) => And (p k) (And (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (sa k) (sa i)) (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (sb k) (sb j)))))) -> (Filter.HasBasis.{max u2 u3, u1} (Prod.{u2, u3} α β) ι (Filter.prod.{u2, u3} α β la lb) p (fun (i : ι) => Set.prod.{u2, u3} α β (sa i) (sb i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.prod_same_index Filter.HasBasis.prod_same_indexₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_same_index {p : ι → Prop} {sb : ι → Set β} (hla : la.HasBasis p sa)
    (hlb : lb.HasBasis p sb) (h_dir : ∀ {i j}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j) :
    (la ×ᶠ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  by
  simp only [has_basis_iff, (hla.prod_pprod hlb).mem_iff]
  refine' fun t => ⟨_, _⟩
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : sa i ×ˢ sb j ⊆ t⟩
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩
    exact ⟨k, hk, (Set.prod_mono ki kj).trans hsub⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩
#align filter.has_basis.prod_same_index Filter.HasBasis.prod_same_index

/- warning: filter.has_basis.prod_same_index_mono -> Filter.HasBasis.prod_same_index_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {la : Filter.{u1} α} {lb : Filter.{u2} β} {ι : Type.{u3}} [_inst_1 : LinearOrder.{u3} ι] {p : ι -> Prop} {sa : ι -> (Set.{u1} α)} {sb : ι -> (Set.{u2} β)}, (Filter.HasBasis.{u1, succ u3} α ι la p sa) -> (Filter.HasBasis.{u2, succ u3} β ι lb p sb) -> (MonotoneOn.{u3, u1} ι (Set.{u1} α) (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (LinearOrder.toLattice.{u3} ι _inst_1)))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) sa (setOf.{u3} ι (fun (i : ι) => p i))) -> (MonotoneOn.{u3, u2} ι (Set.{u2} β) (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (LinearOrder.toLattice.{u3} ι _inst_1)))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) sb (setOf.{u3} ι (fun (i : ι) => p i))) -> (Filter.HasBasis.{max u1 u2, succ u3} (Prod.{u1, u2} α β) ι (Filter.prod.{u1, u2} α β la lb) p (fun (i : ι) => Set.prod.{u1, u2} α β (sa i) (sb i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {la : Filter.{u2} α} {lb : Filter.{u1} β} {ι : Type.{u3}} [_inst_1 : LinearOrder.{u3} ι] {p : ι -> Prop} {sa : ι -> (Set.{u2} α)} {sb : ι -> (Set.{u1} β)}, (Filter.HasBasis.{u2, succ u3} α ι la p sa) -> (Filter.HasBasis.{u1, succ u3} β ι lb p sb) -> (MonotoneOn.{u3, u2} ι (Set.{u2} α) (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_1))))) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) sa (setOf.{u3} ι (fun (i : ι) => p i))) -> (MonotoneOn.{u3, u1} ι (Set.{u1} β) (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_1))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) sb (setOf.{u3} ι (fun (i : ι) => p i))) -> (Filter.HasBasis.{max u2 u1, succ u3} (Prod.{u2, u1} α β) ι (Filter.prod.{u2, u1} α β la lb) p (fun (i : ι) => Set.prod.{u2, u1} α β (sa i) (sb i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.prod_same_index_mono Filter.HasBasis.prod_same_index_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_same_index_mono {ι : Type _} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : MonotoneOn sa { i | p i }) (hsb : MonotoneOn sb { i | p i }) :
    (la ×ᶠ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  hla.prod_same_index hlb fun i j hi hj =>
    have : p (min i j) := min_rec' _ hi hj
    ⟨min i j, this, hsa this hi <| min_le_left _ _, hsb this hj <| min_le_right _ _⟩
#align filter.has_basis.prod_same_index_mono Filter.HasBasis.prod_same_index_mono

/- warning: filter.has_basis.prod_same_index_anti -> Filter.HasBasis.prod_same_index_anti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {la : Filter.{u1} α} {lb : Filter.{u2} β} {ι : Type.{u3}} [_inst_1 : LinearOrder.{u3} ι] {p : ι -> Prop} {sa : ι -> (Set.{u1} α)} {sb : ι -> (Set.{u2} β)}, (Filter.HasBasis.{u1, succ u3} α ι la p sa) -> (Filter.HasBasis.{u2, succ u3} β ι lb p sb) -> (AntitoneOn.{u3, u1} ι (Set.{u1} α) (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (LinearOrder.toLattice.{u3} ι _inst_1)))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) sa (setOf.{u3} ι (fun (i : ι) => p i))) -> (AntitoneOn.{u3, u2} ι (Set.{u2} β) (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (LinearOrder.toLattice.{u3} ι _inst_1)))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) sb (setOf.{u3} ι (fun (i : ι) => p i))) -> (Filter.HasBasis.{max u1 u2, succ u3} (Prod.{u1, u2} α β) ι (Filter.prod.{u1, u2} α β la lb) p (fun (i : ι) => Set.prod.{u1, u2} α β (sa i) (sb i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {la : Filter.{u2} α} {lb : Filter.{u1} β} {ι : Type.{u3}} [_inst_1 : LinearOrder.{u3} ι] {p : ι -> Prop} {sa : ι -> (Set.{u2} α)} {sb : ι -> (Set.{u1} β)}, (Filter.HasBasis.{u2, succ u3} α ι la p sa) -> (Filter.HasBasis.{u1, succ u3} β ι lb p sb) -> (AntitoneOn.{u3, u2} ι (Set.{u2} α) (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_1))))) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) sa (setOf.{u3} ι (fun (i : ι) => p i))) -> (AntitoneOn.{u3, u1} ι (Set.{u1} β) (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_1))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) sb (setOf.{u3} ι (fun (i : ι) => p i))) -> (Filter.HasBasis.{max u2 u1, succ u3} (Prod.{u2, u1} α β) ι (Filter.prod.{u2, u1} α β la lb) p (fun (i : ι) => Set.prod.{u2, u1} α β (sa i) (sb i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.prod_same_index_anti Filter.HasBasis.prod_same_index_antiₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_same_index_anti {ι : Type _} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : AntitoneOn sa { i | p i }) (hsb : AntitoneOn sb { i | p i }) :
    (la ×ᶠ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left
#align filter.has_basis.prod_same_index_anti Filter.HasBasis.prod_same_index_anti

/- warning: filter.has_basis.prod_self -> Filter.HasBasis.prod_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {la : Filter.{u1} α} {pa : ι -> Prop} {sa : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι la pa sa) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (Filter.prod.{u1, u1} α α la la) pa (fun (i : ι) => Set.prod.{u1, u1} α α (sa i) (sa i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {la : Filter.{u2} α} {pa : ι -> Prop} {sa : ι -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι la pa sa) -> (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (Filter.prod.{u2, u2} α α la la) pa (fun (i : ι) => Set.prod.{u2, u2} α α (sa i) (sa i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.prod_self Filter.HasBasis.prod_selfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasBasis.prod_self (hl : la.HasBasis pa sa) :
    (la ×ᶠ la).HasBasis pa fun i => sa i ×ˢ sa i :=
  hl.prod_same_index hl fun i j hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))
#align filter.has_basis.prod_self Filter.HasBasis.prod_self

/- warning: filter.mem_prod_self_iff -> Filter.mem_prod_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {la : Filter.{u1} α} {s : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (Filter.prod.{u1, u1} α α la la)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t la) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t la) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α t t) s)))
but is expected to have type
  forall {α : Type.{u1}} {la : Filter.{u1} α} {s : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (Filter.prod.{u1, u1} α α la la)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t la) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α t t) s)))
Case conversion may be inaccurate. Consider using '#align filter.mem_prod_self_iff Filter.mem_prod_self_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_prod_self_iff {s} : s ∈ la ×ᶠ la ↔ ∃ t ∈ la, t ×ˢ t ⊆ s :=
  la.basis_sets.prod_self.mem_iff
#align filter.mem_prod_self_iff Filter.mem_prod_self_iff

/- warning: filter.has_antitone_basis.prod -> Filter.HasAntitoneBasis.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : LinearOrder.{u3} ι] {f : Filter.{u1} α} {g : Filter.{u2} β} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u2} β)}, (Filter.HasAntitoneBasis.{u1, u3} α ι (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (LinearOrder.toLattice.{u3} ι _inst_1)))) f s) -> (Filter.HasAntitoneBasis.{u2, u3} β ι (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (LinearOrder.toLattice.{u3} ι _inst_1)))) g t) -> (Filter.HasAntitoneBasis.{max u1 u2, u3} (Prod.{u1, u2} α β) ι (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (LinearOrder.toLattice.{u3} ι _inst_1)))) (Filter.prod.{u1, u2} α β f g) (fun (n : ι) => Set.prod.{u1, u2} α β (s n) (t n)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Type.{u3}} [_inst_1 : LinearOrder.{u3} ι] {f : Filter.{u2} α} {g : Filter.{u1} β} {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u1} β)}, (Filter.HasAntitoneBasis.{u2, u3} α ι (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_1))))) f s) -> (Filter.HasAntitoneBasis.{u1, u3} β ι (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_1))))) g t) -> (Filter.HasAntitoneBasis.{max u1 u2, u3} (Prod.{u2, u1} α β) ι (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_1))))) (Filter.prod.{u2, u1} α β f g) (fun (n : ι) => Set.prod.{u2, u1} α β (s n) (t n)))
Case conversion may be inaccurate. Consider using '#align filter.has_antitone_basis.prod Filter.HasAntitoneBasis.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem HasAntitoneBasis.prod {ι : Type _} [LinearOrder ι] {f : Filter α} {g : Filter β}
    {s : ι → Set α} {t : ι → Set β} (hf : HasAntitoneBasis f s) (hg : HasAntitoneBasis g t) :
    HasAntitoneBasis (f ×ᶠ g) fun n => s n ×ˢ t n :=
  ⟨hf.1.prod_same_index_anti hg.1 (hf.2.AntitoneOn _) (hg.2.AntitoneOn _), hf.2.set_prod hg.2⟩
#align filter.has_antitone_basis.prod Filter.HasAntitoneBasis.prod

/- warning: filter.has_basis.coprod -> Filter.HasBasis.coprod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {la : Filter.{u1} α} {lb : Filter.{u2} β} {ι : Type.{u3}} {ι' : Type.{u4}} {pa : ι -> Prop} {sa : ι -> (Set.{u1} α)} {pb : ι' -> Prop} {sb : ι' -> (Set.{u2} β)}, (Filter.HasBasis.{u1, succ u3} α ι la pa sa) -> (Filter.HasBasis.{u2, succ u4} β ι' lb pb sb) -> (Filter.HasBasis.{max u1 u2, max (succ u3) (succ u4)} (Prod.{u1, u2} α β) (Prod.{u3, u4} ι ι') (Filter.coprod.{u1, u2} α β la lb) (fun (i : Prod.{u3, u4} ι ι') => And (pa (Prod.fst.{u3, u4} ι ι' i)) (pb (Prod.snd.{u3, u4} ι ι' i))) (fun (i : Prod.{u3, u4} ι ι') => Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Prod.{u1, u2} α β)) (Set.preimage.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (sa (Prod.fst.{u3, u4} ι ι' i))) (Set.preimage.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (sb (Prod.snd.{u3, u4} ι ι' i)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {la : Filter.{u2} α} {lb : Filter.{u1} β} {ι : Type.{u4}} {ι' : Type.{u3}} {pa : ι -> Prop} {sa : ι -> (Set.{u2} α)} {pb : ι' -> Prop} {sb : ι' -> (Set.{u1} β)}, (Filter.HasBasis.{u2, succ u4} α ι la pa sa) -> (Filter.HasBasis.{u1, succ u3} β ι' lb pb sb) -> (Filter.HasBasis.{max u2 u1, max (succ u4) (succ u3)} (Prod.{u2, u1} α β) (Prod.{u4, u3} ι ι') (Filter.coprod.{u2, u1} α β la lb) (fun (i : Prod.{u4, u3} ι ι') => And (pa (Prod.fst.{u4, u3} ι ι' i)) (pb (Prod.snd.{u4, u3} ι ι' i))) (fun (i : Prod.{u4, u3} ι ι') => Union.union.{max u2 u1} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (Set.instUnionSet.{max u2 u1} (Prod.{u2, u1} α β)) (Set.preimage.{max u2 u1, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) (sa (Prod.fst.{u4, u3} ι ι' i))) (Set.preimage.{max u2 u1, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) (sb (Prod.snd.{u4, u3} ι ι' i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.coprod Filter.HasBasis.coprodₓ'. -/
theorem HasBasis.coprod {ι ι' : Type _} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la.coprod lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i =>
      Prod.fst ⁻¹' sa i.1 ∪ Prod.snd ⁻¹' sb i.2 :=
  (hla.comap Prod.fst).sup (hlb.comap Prod.snd)
#align filter.has_basis.coprod Filter.HasBasis.coprod

end TwoTypes

/- warning: filter.map_sigma_mk_comap -> Filter.map_sigma_mk_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {π : α -> Type.{u3}} {π' : β -> Type.{u4}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (g : forall (a : α), (π a) -> (π' (f a))) (a : α) (l : Filter.{u4} (π' (f a))), Eq.{succ (max u1 u3)} (Filter.{max u1 u3} (Sigma.{u1, u3} α (fun (a : α) => π a))) (Filter.map.{u3, max u1 u3} (π a) (Sigma.{u1, u3} α (fun (a : α) => π a)) (Sigma.mk.{u1, u3} α (fun (a : α) => π a) a) (Filter.comap.{u3, u4} (π a) (π' (f a)) (g a) l)) (Filter.comap.{max u1 u3, max u2 u4} (Sigma.{u1, u3} α (fun (a : α) => π a)) (Sigma.{u2, u4} β π') (Sigma.map.{u1, u2, u3, u4} α β (fun (a : α) => π a) π' f g) (Filter.map.{u4, max u2 u4} (π' (f a)) (Sigma.{u2, u4} β π') (Sigma.mk.{u2, u4} β π' (f a)) l)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {π : α -> Type.{u4}} {π' : β -> Type.{u3}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (g : forall (a : α), (π a) -> (π' (f a))) (a : α) (l : Filter.{u3} (π' (f a))), Eq.{max (succ u2) (succ u4)} (Filter.{max u2 u4} (Sigma.{u2, u4} α π)) (Filter.map.{u4, max u2 u4} (π a) (Sigma.{u2, u4} α π) (Sigma.mk.{u2, u4} α π a) (Filter.comap.{u4, u3} (π a) (π' (f a)) (g a) l)) (Filter.comap.{max u4 u2, max u3 u1} (Sigma.{u2, u4} α (fun (a : α) => π a)) (Sigma.{u1, u3} β π') (Sigma.map.{u2, u1, u4, u3} α β (fun (a : α) => π a) π' f g) (Filter.map.{u3, max u1 u3} (π' (f a)) (Sigma.{u1, u3} β π') (Sigma.mk.{u1, u3} β π' (f a)) l)))
Case conversion may be inaccurate. Consider using '#align filter.map_sigma_mk_comap Filter.map_sigma_mk_comapₓ'. -/
theorem map_sigma_mk_comap {π : α → Type _} {π' : β → Type _} {f : α → β}
    (hf : Function.Injective f) (g : ∀ a, π a → π' (f a)) (a : α) (l : Filter (π' (f a))) :
    map (Sigma.mk a) (comap (g a) l) = comap (Sigma.map f g) (map (Sigma.mk (f a)) l) :=
  by
  refine' (((basis_sets _).comap _).map _).eq_of_same_basis _
  convert ((basis_sets _).map _).comap _
  ext1 s
  apply image_sigma_mk_preimage_sigma_map hf
#align filter.map_sigma_mk_comap Filter.map_sigma_mk_comap

end Filter

end Sort

namespace Filter

variable {α β γ ι : Type _} {ι' : Sort _}

#print Filter.IsCountablyGenerated /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`out] [] -/
/-- `is_countably_generated f` means `f = generate s` for some countable `s`. -/
class IsCountablyGenerated (f : Filter α) : Prop where
  out : ∃ s : Set (Set α), s.Countable ∧ f = generate s
#align filter.is_countably_generated Filter.IsCountablyGenerated
-/

#print Filter.IsCountableBasis /-
/-- `is_countable_basis p s` means the image of `s` bounded by `p` is a countable filter basis. -/
structure IsCountableBasis (p : ι → Prop) (s : ι → Set α) extends IsBasis p s : Prop where
  Countable : (setOf p).Countable
#align filter.is_countable_basis Filter.IsCountableBasis
-/

#print Filter.HasCountableBasis /-
/-- We say that a filter `l` has a countable basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`, and the set
defined by `p` is countable. -/
structure HasCountableBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) extends HasBasis l p s :
  Prop where
  Countable : (setOf p).Countable
#align filter.has_countable_basis Filter.HasCountableBasis
-/

#print Filter.CountableFilterBasis /-
/-- A countable filter basis `B` on a type `α` is a nonempty countable collection of sets of `α`
such that the intersection of two elements of this collection contains some element
of the collection. -/
structure CountableFilterBasis (α : Type _) extends FilterBasis α where
  Countable : sets.Countable
#align filter.countable_filter_basis Filter.CountableFilterBasis
-/

#print Filter.Nat.inhabitedCountableFilterBasis /-
-- For illustration purposes, the countable filter basis defining (at_top : filter ℕ)
instance Nat.inhabitedCountableFilterBasis : Inhabited (CountableFilterBasis ℕ) :=
  ⟨{ (default : FilterBasis ℕ) with Countable := countable_range fun n => Ici n }⟩
#align filter.nat.inhabited_countable_filter_basis Filter.Nat.inhabitedCountableFilterBasis
-/

/- warning: filter.has_countable_basis.is_countably_generated -> Filter.HasCountableBasis.isCountablyGenerated is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : Filter.{u1} α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasCountableBasis.{u1, u2} α ι f p s) -> (Filter.IsCountablyGenerated.{u1} α f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {f : Filter.{u2} α} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, (Filter.HasCountableBasis.{u2, u1} α ι f p s) -> (Filter.IsCountablyGenerated.{u2} α f)
Case conversion may be inaccurate. Consider using '#align filter.has_countable_basis.is_countably_generated Filter.HasCountableBasis.isCountablyGeneratedₓ'. -/
theorem HasCountableBasis.isCountablyGenerated {f : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : f.HasCountableBasis p s) : f.IsCountablyGenerated :=
  ⟨⟨{ t | ∃ i, p i ∧ s i = t }, h.Countable.image s, h.to_hasBasis.eq_generate⟩⟩
#align filter.has_countable_basis.is_countably_generated Filter.HasCountableBasis.isCountablyGenerated

/- warning: filter.antitone_seq_of_seq -> Filter.antitone_seq_of_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Nat -> (Set.{u1} α)), Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => And (Antitone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) t) (Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, 1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) Nat (fun (i : Nat) => Filter.principal.{u1} α (s i))) (infᵢ.{u1, 1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) Nat (fun (i : Nat) => Filter.principal.{u1} α (t i)))))
but is expected to have type
  forall {α : Type.{u1}} (s : Nat -> (Set.{u1} α)), Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => And (Antitone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) t) (Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, 1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) Nat (fun (i : Nat) => Filter.principal.{u1} α (s i))) (infᵢ.{u1, 1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) Nat (fun (i : Nat) => Filter.principal.{u1} α (t i)))))
Case conversion may be inaccurate. Consider using '#align filter.antitone_seq_of_seq Filter.antitone_seq_of_seqₓ'. -/
theorem antitone_seq_of_seq (s : ℕ → Set α) :
    ∃ t : ℕ → Set α, Antitone t ∧ (⨅ i, 𝓟 <| s i) = ⨅ i, 𝓟 (t i) :=
  by
  use fun n => ⋂ m ≤ n, s m; constructor
  · exact fun i j hij => bInter_mono (Iic_subset_Iic.2 hij) fun n hn => subset.refl _
  apply le_antisymm <;> rw [le_infᵢ_iff] <;> intro i
  · rw [le_principal_iff]
    refine' (bInter_mem (finite_le_nat _)).2 fun j hji => _
    rw [← le_principal_iff]
    apply infᵢ_le_of_le j _
    exact le_rfl
  · apply infᵢ_le_of_le i _
    rw [principal_mono]
    intro a
    simp
    intro h
    apply h
    rfl
#align filter.antitone_seq_of_seq Filter.antitone_seq_of_seq

/- warning: filter.countable_binfi_eq_infi_seq -> Filter.countable_binfᵢ_eq_infᵢ_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {B : Set.{u2} ι}, (Set.Countable.{u2} ι B) -> (Set.Nonempty.{u2} ι B) -> (forall (f : ι -> α), Exists.{succ u2} (Nat -> ι) (fun (x : Nat -> ι) => Eq.{succ u1} α (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (t : ι) => infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t B) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t B) => f t))) (infᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => f (x i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {B : Set.{u1} ι}, (Set.Countable.{u1} ι B) -> (Set.Nonempty.{u1} ι B) -> (forall (f : ι -> α), Exists.{succ u1} (Nat -> ι) (fun (x : Nat -> ι) => Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (t : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) t B) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) t B) => f t))) (infᵢ.{u2, 1} α (CompleteLattice.toInfSet.{u2} α _inst_1) Nat (fun (i : Nat) => f (x i)))))
Case conversion may be inaccurate. Consider using '#align filter.countable_binfi_eq_infi_seq Filter.countable_binfᵢ_eq_infᵢ_seqₓ'. -/
theorem countable_binfᵢ_eq_infᵢ_seq [CompleteLattice α] {B : Set ι} (Bcbl : B.Countable)
    (Bne : B.Nonempty) (f : ι → α) : ∃ x : ℕ → ι, (⨅ t ∈ B, f t) = ⨅ i, f (x i) :=
  let ⟨g, hg⟩ := Bcbl.exists_eq_range Bne
  ⟨g, hg.symm ▸ infᵢ_range⟩
#align filter.countable_binfi_eq_infi_seq Filter.countable_binfᵢ_eq_infᵢ_seq

/- warning: filter.countable_binfi_eq_infi_seq' -> Filter.countable_binfᵢ_eq_infᵢ_seq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {B : Set.{u2} ι}, (Set.Countable.{u2} ι B) -> (forall (f : ι -> α) {i₀ : ι}, (Eq.{succ u1} α (f i₀) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) -> (Exists.{succ u2} (Nat -> ι) (fun (x : Nat -> ι) => Eq.{succ u1} α (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (t : ι) => infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t B) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t B) => f t))) (infᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => f (x i))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {B : Set.{u1} ι}, (Set.Countable.{u1} ι B) -> (forall (f : ι -> α) {i₀ : ι}, (Eq.{succ u2} α (f i₀) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))) -> (Exists.{succ u1} (Nat -> ι) (fun (x : Nat -> ι) => Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (t : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) t B) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) t B) => f t))) (infᵢ.{u2, 1} α (CompleteLattice.toInfSet.{u2} α _inst_1) Nat (fun (i : Nat) => f (x i))))))
Case conversion may be inaccurate. Consider using '#align filter.countable_binfi_eq_infi_seq' Filter.countable_binfᵢ_eq_infᵢ_seq'ₓ'. -/
theorem countable_binfᵢ_eq_infᵢ_seq' [CompleteLattice α] {B : Set ι} (Bcbl : B.Countable)
    (f : ι → α) {i₀ : ι} (h : f i₀ = ⊤) : ∃ x : ℕ → ι, (⨅ t ∈ B, f t) = ⨅ i, f (x i) :=
  by
  cases' B.eq_empty_or_nonempty with hB Bnonempty
  · rw [hB, infᵢ_emptyset]
    use fun n => i₀
    simp [h]
  · exact countable_binfi_eq_infi_seq Bcbl Bnonempty f
#align filter.countable_binfi_eq_infi_seq' Filter.countable_binfᵢ_eq_infᵢ_seq'

/- warning: filter.countable_binfi_principal_eq_seq_infi -> Filter.countable_binfᵢ_principal_eq_seq_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {B : Set.{u1} (Set.{u1} α)}, (Set.Countable.{u1} (Set.{u1} α) B) -> (Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (x : Nat -> (Set.{u1} α)) => Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Set.{u1} α) (fun (t : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t B) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t B) => Filter.principal.{u1} α t))) (infᵢ.{u1, 1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) Nat (fun (i : Nat) => Filter.principal.{u1} α (x i)))))
but is expected to have type
  forall {α : Type.{u1}} {B : Set.{u1} (Set.{u1} α)}, (Set.Countable.{u1} (Set.{u1} α) B) -> (Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (x : Nat -> (Set.{u1} α)) => Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, succ u1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Set.{u1} α) (fun (t : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t B) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t B) => Filter.principal.{u1} α t))) (infᵢ.{u1, 1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) Nat (fun (i : Nat) => Filter.principal.{u1} α (x i)))))
Case conversion may be inaccurate. Consider using '#align filter.countable_binfi_principal_eq_seq_infi Filter.countable_binfᵢ_principal_eq_seq_infᵢₓ'. -/
theorem countable_binfᵢ_principal_eq_seq_infᵢ {B : Set (Set α)} (Bcbl : B.Countable) :
    ∃ x : ℕ → Set α, (⨅ t ∈ B, 𝓟 t) = ⨅ i, 𝓟 (x i) :=
  countable_binfᵢ_eq_infᵢ_seq' Bcbl 𝓟 principal_univ
#align filter.countable_binfi_principal_eq_seq_infi Filter.countable_binfᵢ_principal_eq_seq_infᵢ

section IsCountablyGenerated

#print Filter.HasAntitoneBasis.mem_iff /-
protected theorem HasAntitoneBasis.mem_iff [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hs : l.HasAntitoneBasis s) {t : Set α} : t ∈ l ↔ ∃ i, s i ⊆ t :=
  hs.to_hasBasis.mem_iff.trans <| by simp only [exists_prop, true_and_iff]
#align filter.has_antitone_basis.mem_iff Filter.HasAntitoneBasis.mem_iff
-/

#print Filter.HasAntitoneBasis.mem /-
protected theorem HasAntitoneBasis.mem [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hs : l.HasAntitoneBasis s) (i : ι) : s i ∈ l :=
  hs.to_hasBasis.mem_of_mem trivial
#align filter.has_antitone_basis.mem Filter.HasAntitoneBasis.mem
-/

#print Filter.HasAntitoneBasis.hasBasis_ge /-
theorem HasAntitoneBasis.hasBasis_ge [Preorder ι] [IsDirected ι (· ≤ ·)] {l : Filter α}
    {s : ι → Set α} (hs : l.HasAntitoneBasis s) (i : ι) : l.HasBasis (fun j => i ≤ j) s :=
  hs.1.to_hasBasis (fun j _ => (exists_ge_ge i j).imp fun k hk => ⟨hk.1, hs.2 hk.2⟩) fun j hj =>
    ⟨j, trivial, Subset.rfl⟩
#align filter.has_antitone_basis.has_basis_ge Filter.HasAntitoneBasis.hasBasis_ge
-/

/- warning: filter.has_basis.exists_antitone_subbasis -> Filter.HasBasis.exists_antitone_subbasis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι' : Sort.{u2}} {f : Filter.{u1} α} [h : Filter.IsCountablyGenerated.{u1} α f] {p : ι' -> Prop} {s : ι' -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι' f p s) -> (Exists.{imax 1 u2} (Nat -> ι') (fun (x : Nat -> ι') => And (forall (i : Nat), p (x i)) (Filter.HasAntitoneBasis.{u1, 0} α Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) f (fun (i : Nat) => s (x i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι' : Sort.{u1}} {f : Filter.{u2} α} [h : Filter.IsCountablyGenerated.{u2} α f] {p : ι' -> Prop} {s : ι' -> (Set.{u2} α)}, (Filter.HasBasis.{u2, u1} α ι' f p s) -> (Exists.{imax 1 u1} (Nat -> ι') (fun (x : Nat -> ι') => And (forall (i : Nat), p (x i)) (Filter.HasAntitoneBasis.{u2, 0} α Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) f (fun (i : Nat) => s (x i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.exists_antitone_subbasis Filter.HasBasis.exists_antitone_subbasisₓ'. -/
/-- If `f` is countably generated and `f.has_basis p s`, then `f` admits a decreasing basis
enumerated by natural numbers such that all sets have the form `s i`. More precisely, there is a
sequence `i n` such that `p (i n)` for all `n` and `s (i n)` is a decreasing sequence of sets which
forms a basis of `f`-/
theorem HasBasis.exists_antitone_subbasis {f : Filter α} [h : f.IsCountablyGenerated]
    {p : ι' → Prop} {s : ι' → Set α} (hs : f.HasBasis p s) :
    ∃ x : ℕ → ι', (∀ i, p (x i)) ∧ f.HasAntitoneBasis fun i => s (x i) :=
  by
  obtain ⟨x', hx'⟩ : ∃ x : ℕ → Set α, f = ⨅ i, 𝓟 (x i) :=
    by
    rcases h with ⟨s, hsc, rfl⟩
    rw [generate_eq_binfi]
    exact countable_binfi_principal_eq_seq_infi hsc
  have : ∀ i, x' i ∈ f := fun i => hx'.symm ▸ (infᵢ_le (fun i => 𝓟 (x' i)) i) (mem_principal_self _)
  let x : ℕ → { i : ι' // p i } := fun n =>
    Nat.recOn n (hs.index _ <| this 0) fun n xn =>
      hs.index _ <| inter_mem (this <| n + 1) (hs.mem_of_mem xn.2)
  have x_mono : Antitone fun i => s (x i) :=
    by
    refine' antitone_nat_of_succ_le fun i => _
    exact (hs.set_index_subset _).trans (inter_subset_right _ _)
  have x_subset : ∀ i, s (x i) ⊆ x' i := by
    rintro (_ | i)
    exacts[hs.set_index_subset _, subset.trans (hs.set_index_subset _) (inter_subset_left _ _)]
  refine' ⟨fun i => x i, fun i => (x i).2, _⟩
  have : (⨅ i, 𝓟 (s (x i))).HasAntitoneBasis fun i => s (x i) :=
    ⟨has_basis_infi_principal (directed_of_sup x_mono), x_mono⟩
  convert this
  exact
    le_antisymm (le_infᵢ fun i => le_principal_iff.2 <| by cases i <;> apply hs.set_index_mem)
      (hx'.symm ▸
        le_infᵢ fun i => le_principal_iff.2 <| this.to_has_basis.mem_iff.2 ⟨i, trivial, x_subset i⟩)
#align filter.has_basis.exists_antitone_subbasis Filter.HasBasis.exists_antitone_subbasis

#print Filter.exists_antitone_basis /-
/-- A countably generated filter admits a basis formed by an antitone sequence of sets. -/
theorem exists_antitone_basis (f : Filter α) [f.IsCountablyGenerated] :
    ∃ x : ℕ → Set α, f.HasAntitoneBasis x :=
  let ⟨x, hxf, hx⟩ := f.basis_sets.exists_antitone_subbasis
  ⟨x, hx⟩
#align filter.exists_antitone_basis Filter.exists_antitone_basis
-/

/- warning: filter.exists_antitone_seq -> Filter.exists_antitone_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Filter.{u1} α) [_inst_1 : Filter.IsCountablyGenerated.{u1} α f], Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (x : Nat -> (Set.{u1} α)) => And (Antitone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) x) (forall {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (Exists.{1} Nat (fun (i : Nat) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (x i) s))))
but is expected to have type
  forall {α : Type.{u1}} (f : Filter.{u1} α) [_inst_1 : Filter.IsCountablyGenerated.{u1} α f], Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (x : Nat -> (Set.{u1} α)) => And (Antitone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) x) (forall {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (Exists.{1} Nat (fun (i : Nat) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (x i) s))))
Case conversion may be inaccurate. Consider using '#align filter.exists_antitone_seq Filter.exists_antitone_seqₓ'. -/
theorem exists_antitone_seq (f : Filter α) [f.IsCountablyGenerated] :
    ∃ x : ℕ → Set α, Antitone x ∧ ∀ {s}, s ∈ f ↔ ∃ i, x i ⊆ s :=
  let ⟨x, hx⟩ := f.exists_antitone_basis
  ⟨x, hx.Antitone, fun s => by simp [hx.to_has_basis.mem_iff]⟩
#align filter.exists_antitone_seq Filter.exists_antitone_seq

/- warning: filter.inf.is_countably_generated -> Filter.Inf.isCountablyGenerated is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Filter.{u1} α) (g : Filter.{u1} α) [_inst_1 : Filter.IsCountablyGenerated.{u1} α f] [_inst_2 : Filter.IsCountablyGenerated.{u1} α g], Filter.IsCountablyGenerated.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)
but is expected to have type
  forall {α : Type.{u1}} (f : Filter.{u1} α) (g : Filter.{u1} α) [_inst_1 : Filter.IsCountablyGenerated.{u1} α f] [_inst_2 : Filter.IsCountablyGenerated.{u1} α g], Filter.IsCountablyGenerated.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)
Case conversion may be inaccurate. Consider using '#align filter.inf.is_countably_generated Filter.Inf.isCountablyGeneratedₓ'. -/
instance Inf.isCountablyGenerated (f g : Filter α) [IsCountablyGenerated f]
    [IsCountablyGenerated g] : IsCountablyGenerated (f ⊓ g) :=
  by
  rcases f.exists_antitone_basis with ⟨s, hs⟩
  rcases g.exists_antitone_basis with ⟨t, ht⟩
  exact
    has_countable_basis.is_countably_generated
      ⟨hs.to_has_basis.inf ht.to_has_basis, Set.to_countable _⟩
#align filter.inf.is_countably_generated Filter.Inf.isCountablyGenerated

#print Filter.map.isCountablyGenerated /-
instance map.isCountablyGenerated (l : Filter α) [l.IsCountablyGenerated] (f : α → β) :
    (map f l).IsCountablyGenerated :=
  let ⟨x, hxl⟩ := l.exists_antitone_basis
  HasCountableBasis.isCountablyGenerated ⟨hxl.map.to_hasBasis, to_countable _⟩
#align filter.map.is_countably_generated Filter.map.isCountablyGenerated
-/

#print Filter.comap.isCountablyGenerated /-
instance comap.isCountablyGenerated (l : Filter β) [l.IsCountablyGenerated] (f : α → β) :
    (comap f l).IsCountablyGenerated :=
  let ⟨x, hxl⟩ := l.exists_antitone_basis
  HasCountableBasis.isCountablyGenerated ⟨hxl.to_hasBasis.comap _, to_countable _⟩
#align filter.comap.is_countably_generated Filter.comap.isCountablyGenerated
-/

/- warning: filter.sup.is_countably_generated -> Filter.Sup.isCountablyGenerated is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Filter.{u1} α) (g : Filter.{u1} α) [_inst_1 : Filter.IsCountablyGenerated.{u1} α f] [_inst_2 : Filter.IsCountablyGenerated.{u1} α g], Filter.IsCountablyGenerated.{u1} α (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g)
but is expected to have type
  forall {α : Type.{u1}} (f : Filter.{u1} α) (g : Filter.{u1} α) [_inst_1 : Filter.IsCountablyGenerated.{u1} α f] [_inst_2 : Filter.IsCountablyGenerated.{u1} α g], Filter.IsCountablyGenerated.{u1} α (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f g)
Case conversion may be inaccurate. Consider using '#align filter.sup.is_countably_generated Filter.Sup.isCountablyGeneratedₓ'. -/
instance Sup.isCountablyGenerated (f g : Filter α) [IsCountablyGenerated f]
    [IsCountablyGenerated g] : IsCountablyGenerated (f ⊔ g) :=
  by
  rcases f.exists_antitone_basis with ⟨s, hs⟩
  rcases g.exists_antitone_basis with ⟨t, ht⟩
  exact
    has_countable_basis.is_countably_generated
      ⟨hs.to_has_basis.sup ht.to_has_basis, Set.to_countable _⟩
#align filter.sup.is_countably_generated Filter.Sup.isCountablyGenerated

#print Filter.prod.isCountablyGenerated /-
instance prod.isCountablyGenerated (la : Filter α) (lb : Filter β) [IsCountablyGenerated la]
    [IsCountablyGenerated lb] : IsCountablyGenerated (la ×ᶠ lb) :=
  Filter.Inf.isCountablyGenerated _ _
#align filter.prod.is_countably_generated Filter.prod.isCountablyGenerated
-/

#print Filter.coprod.isCountablyGenerated /-
instance coprod.isCountablyGenerated (la : Filter α) (lb : Filter β) [IsCountablyGenerated la]
    [IsCountablyGenerated lb] : IsCountablyGenerated (la.coprod lb) :=
  Filter.Sup.isCountablyGenerated _ _
#align filter.coprod.is_countably_generated Filter.coprod.isCountablyGenerated
-/

end IsCountablyGenerated

/- warning: filter.is_countably_generated_seq -> Filter.isCountablyGenerated_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] (x : β -> (Set.{u1} α)), Filter.IsCountablyGenerated.{u1} α (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) β (fun (i : β) => Filter.principal.{u1} α (x i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] (x : β -> (Set.{u1} α)), Filter.IsCountablyGenerated.{u1} α (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) β (fun (i : β) => Filter.principal.{u1} α (x i)))
Case conversion may be inaccurate. Consider using '#align filter.is_countably_generated_seq Filter.isCountablyGenerated_seqₓ'. -/
theorem isCountablyGenerated_seq [Countable β] (x : β → Set α) :
    IsCountablyGenerated (⨅ i, 𝓟 <| x i) :=
  by
  use range x, countable_range x
  rw [generate_eq_binfi, infᵢ_range]
#align filter.is_countably_generated_seq Filter.isCountablyGenerated_seq

/- warning: filter.is_countably_generated_of_seq -> Filter.isCountablyGenerated_of_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α}, (Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (x : Nat -> (Set.{u1} α)) => Eq.{succ u1} (Filter.{u1} α) f (infᵢ.{u1, 1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) Nat (fun (i : Nat) => Filter.principal.{u1} α (x i))))) -> (Filter.IsCountablyGenerated.{u1} α f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α}, (Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (x : Nat -> (Set.{u1} α)) => Eq.{succ u1} (Filter.{u1} α) f (infᵢ.{u1, 1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) Nat (fun (i : Nat) => Filter.principal.{u1} α (x i))))) -> (Filter.IsCountablyGenerated.{u1} α f)
Case conversion may be inaccurate. Consider using '#align filter.is_countably_generated_of_seq Filter.isCountablyGenerated_of_seqₓ'. -/
theorem isCountablyGenerated_of_seq {f : Filter α} (h : ∃ x : ℕ → Set α, f = ⨅ i, 𝓟 <| x i) :
    f.IsCountablyGenerated := by
  let ⟨x, h⟩ := h
  rw [h] <;> apply is_countably_generated_seq
#align filter.is_countably_generated_of_seq Filter.isCountablyGenerated_of_seq

/- warning: filter.is_countably_generated_binfi_principal -> Filter.isCountablyGenerated_binfᵢ_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {B : Set.{u1} (Set.{u1} α)}, (Set.Countable.{u1} (Set.{u1} α) B) -> (Filter.IsCountablyGenerated.{u1} α (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s B) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s B) => Filter.principal.{u1} α s))))
but is expected to have type
  forall {α : Type.{u1}} {B : Set.{u1} (Set.{u1} α)}, (Set.Countable.{u1} (Set.{u1} α) B) -> (Filter.IsCountablyGenerated.{u1} α (infᵢ.{u1, succ u1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s B) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s B) => Filter.principal.{u1} α s))))
Case conversion may be inaccurate. Consider using '#align filter.is_countably_generated_binfi_principal Filter.isCountablyGenerated_binfᵢ_principalₓ'. -/
theorem isCountablyGenerated_binfᵢ_principal {B : Set <| Set α} (h : B.Countable) :
    IsCountablyGenerated (⨅ s ∈ B, 𝓟 s) :=
  isCountablyGenerated_of_seq (countable_binfᵢ_principal_eq_seq_infᵢ h)
#align filter.is_countably_generated_binfi_principal Filter.isCountablyGenerated_binfᵢ_principal

#print Filter.isCountablyGenerated_iff_exists_antitone_basis /-
theorem isCountablyGenerated_iff_exists_antitone_basis {f : Filter α} :
    IsCountablyGenerated f ↔ ∃ x : ℕ → Set α, f.HasAntitoneBasis x :=
  by
  constructor
  · intro h
    exact f.exists_antitone_basis
  · rintro ⟨x, h⟩
    rw [h.to_has_basis.eq_infi]
    exact is_countably_generated_seq x
#align filter.is_countably_generated_iff_exists_antitone_basis Filter.isCountablyGenerated_iff_exists_antitone_basis
-/

#print Filter.isCountablyGenerated_principal /-
@[instance]
theorem isCountablyGenerated_principal (s : Set α) : IsCountablyGenerated (𝓟 s) :=
  isCountablyGenerated_of_seq ⟨fun _ => s, infᵢ_const.symm⟩
#align filter.is_countably_generated_principal Filter.isCountablyGenerated_principal
-/

#print Filter.isCountablyGenerated_pure /-
@[instance]
theorem isCountablyGenerated_pure (a : α) : IsCountablyGenerated (pure a) :=
  by
  rw [← principal_singleton]
  exact is_countably_generated_principal _
#align filter.is_countably_generated_pure Filter.isCountablyGenerated_pure
-/

/- warning: filter.is_countably_generated_bot -> Filter.isCountablyGenerated_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Filter.IsCountablyGenerated.{u1} α (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Filter.IsCountablyGenerated.{u1} α (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.is_countably_generated_bot Filter.isCountablyGenerated_botₓ'. -/
@[instance]
theorem isCountablyGenerated_bot : IsCountablyGenerated (⊥ : Filter α) :=
  @principal_empty α ▸ isCountablyGenerated_principal _
#align filter.is_countably_generated_bot Filter.isCountablyGenerated_bot

/- warning: filter.is_countably_generated_top -> Filter.isCountablyGenerated_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Filter.IsCountablyGenerated.{u1} α (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Filter.IsCountablyGenerated.{u1} α (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))
Case conversion may be inaccurate. Consider using '#align filter.is_countably_generated_top Filter.isCountablyGenerated_topₓ'. -/
@[instance]
theorem isCountablyGenerated_top : IsCountablyGenerated (⊤ : Filter α) :=
  @principal_univ α ▸ isCountablyGenerated_principal _
#align filter.is_countably_generated_top Filter.isCountablyGenerated_top

/- warning: filter.infi.is_countably_generated -> Filter.infᵢ.isCountablyGenerated is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Countable.{u2} ι] (f : ι -> (Filter.{u1} α)) [_inst_2 : forall (i : ι), Filter.IsCountablyGenerated.{u1} α (f i)], Filter.IsCountablyGenerated.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Sort.{u1}} {ι : Type.{u2}} [_inst_1 : Countable.{u1} α] (f : α -> (Filter.{u2} ι)) [_inst_2 : forall (i : α), Filter.IsCountablyGenerated.{u2} ι (f i)], Filter.IsCountablyGenerated.{u2} ι (infᵢ.{u2, u1} (Filter.{u2} ι) (CompleteLattice.toInfSet.{u2} (Filter.{u2} ι) (Filter.instCompleteLatticeFilter.{u2} ι)) α (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align filter.infi.is_countably_generated Filter.infᵢ.isCountablyGeneratedₓ'. -/
instance infᵢ.isCountablyGenerated {ι : Sort _} [Countable ι] (f : ι → Filter α)
    [∀ i, IsCountablyGenerated (f i)] : IsCountablyGenerated (⨅ i, f i) :=
  by
  choose s hs using fun i => exists_antitone_basis (f i)
  rw [← plift.down_surjective.infi_comp]
  refine' has_countable_basis.is_countably_generated ⟨has_basis_infi fun n => (hs _).to_hasBasis, _⟩
  refine' (countable_range <| Sigma.map (coe : Finset (PLift ι) → Set (PLift ι)) fun _ => id).mono _
  rintro ⟨I, f⟩ ⟨hI, -⟩
  lift I to Finset (PLift ι) using hI
  exact ⟨⟨I, f⟩, rfl⟩
#align filter.infi.is_countably_generated Filter.infᵢ.isCountablyGenerated

end Filter

