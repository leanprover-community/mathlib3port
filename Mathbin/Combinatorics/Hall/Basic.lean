/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import Combinatorics.Hall.Finite
import CategoryTheory.CofilteredSystem
import Data.Rel

#align_import combinatorics.hall.basic from "leanprover-community/mathlib"@"2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe"

/-!
# Hall's Marriage Theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a list of finite subsets $X_1, X_2, \dots, X_n$ of some given set
$S$, P. Hall in [Hall1935] gave a necessary and sufficient condition for
there to be a list of distinct elements $x_1, x_2, \dots, x_n$ with
$x_i\in X_i$ for each $i$: it is when for each $k$, the union of every
$k$ of these subsets has at least $k$ elements.

Rather than a list of finite subsets, one may consider indexed families
`t : ι → finset α` of finite subsets with `ι` a `fintype`, and then the list
of distinct representatives is given by an injective function `f : ι → α`
such that `∀ i, f i ∈ t i`, called a *matching*.
This version is formalized as `finset.all_card_le_bUnion_card_iff_exists_injective'`
in a separate module.

The theorem can be generalized to remove the constraint that `ι` be a `fintype`.
As observed in [Halpern1966], one may use the constrained version of the theorem
in a compactness argument to remove this constraint.
The formulation of compactness we use is that inverse limits of nonempty finite sets
are nonempty (`nonempty_sections_of_finite_inverse_system`), which uses the
Tychonoff theorem.
The core of this module is constructing the inverse system: for every finite subset `ι'` of
`ι`, we can consider the matchings on the restriction of the indexed family `t` to `ι'`.

## Main statements

* `finset.all_card_le_bUnion_card_iff_exists_injective` is in terms of `t : ι → finset α`.
* `fintype.all_card_le_rel_image_card_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` such that `rel.image r {a}` is a finite set for all `a : α`.
* `fintype.all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Todo

* The statement of the theorem in terms of bipartite graphs is in preparation.

## Tags

Hall's Marriage Theorem, indexed families
-/


open Finset

universe u v

#print hallMatchingsOn /-
/-- The set of matchings for `t` when restricted to a `finset` of `ι`. -/
def hallMatchingsOn {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :=
  {f : ι' → α | Function.Injective f ∧ ∀ x, f x ∈ t x}
#align hall_matchings_on hallMatchingsOn
-/

#print hallMatchingsOn.restrict /-
/-- Given a matching on a finset, construct the restriction of that matching to a subset. -/
def hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι → Finset α) {ι' ι'' : Finset ι}
    (h : ι' ⊆ ι'') (f : hallMatchingsOn t ι'') : hallMatchingsOn t ι' :=
  by
  refine' ⟨fun i => f.val ⟨i, h i.property⟩, _⟩
  cases' f.property with hinj hc
  refine' ⟨_, fun i => hc ⟨i, h i.property⟩⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  simpa only [Subtype.mk_eq_mk] using hinj hh
#align hall_matchings_on.restrict hallMatchingsOn.restrict
-/

#print hallMatchingsOn.nonempty /-
/-- When the Hall condition is satisfied, the set of matchings on a finite set is nonempty.
This is where `finset.all_card_le_bUnion_card_iff_exists_injective'` comes into the argument. -/
theorem hallMatchingsOn.nonempty {ι : Type u} {α : Type v} [DecidableEq α] (t : ι → Finset α)
    (h : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) (ι' : Finset ι) :
    Nonempty (hallMatchingsOn t ι') := by classical
#align hall_matchings_on.nonempty hallMatchingsOn.nonempty
-/

#print hallMatchingsFunctor /-
-- TODO: This takes a long time to elaborate for an unknown reason.
/-- This is the `hall_matchings_on` sets assembled into a directed system.
-/
def hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι → Finset α) : (Finset ι)ᵒᵖ ⥤ Type max u v
    where
  obj ι' := hallMatchingsOn t ι'.unop
  map ι' ι'' g f := hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop) f
#align hall_matchings_functor hallMatchingsFunctor
-/

#print hallMatchingsOn.finite /-
instance hallMatchingsOn.finite {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :
    Finite (hallMatchingsOn t ι') := by classical
#align hall_matchings_on.finite hallMatchingsOn.finite
-/

#print Finset.all_card_le_biUnion_card_iff_exists_injective /-
/-- This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `s.bUnion t` is the union of all the sets `t i` for `i ∈ s`.

This theorem is bootstrapped from `finset.all_card_le_bUnion_card_iff_exists_injective'`,
which has the additional constraint that `ι` is a `fintype`.
-/
theorem Finset.all_card_le_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v}
    [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  by
  constructor
  · intro h
    -- Set up the functor
    haveI : ∀ ι' : (Finset ι)ᵒᵖ, Nonempty ((hallMatchingsFunctor t).obj ι') := fun ι' =>
      hallMatchingsOn.nonempty t h ι'.unop
    classical
  -- Apply the compactness argument 
  -- Interpret the resulting section of the inverse limit 
  -- Build the matching function from the section 
  -- Show that it is injective 
  -- Show that it maps each index to the corresponding finite set
  · -- The reverse direction is a straightforward cardinality argument
    rintro ⟨f, hf₁, hf₂⟩ s
    rw [← Finset.card_image_of_injective s hf₁]
    apply Finset.card_le_card
    intro
    rw [Finset.mem_image, Finset.mem_biUnion]
    rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hf₂ x⟩
#align finset.all_card_le_bUnion_card_iff_exists_injective Finset.all_card_le_biUnion_card_iff_exists_injective
-/

/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α : Type u} {β : Type v} [DecidableEq β] (r : α → β → Prop)
    [∀ a : α, Fintype (Rel.image r {a})] (A : Finset α) : Fintype (Rel.image r A) :=
  by
  have h : Rel.image r A = (A.bUnion fun a => (Rel.image r {a}).toFinset : Set β) := by ext;
    simp [Rel.image]
  rw [h]
  apply FinsetCoe.fintype

#print Fintype.all_card_le_rel_image_card_iff_exists_injective /-
/-- This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite; see
`fintype.all_card_le_filter_rel_iff_exists_injective`).  There is
a transversal of the relation (an injective function `α → β` whose graph is
a subrelation of the relation) iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

Note: if `[fintype β]`, then there exist instances for `[∀ (a : α), fintype (rel.image r {a})]`.
-/
theorem Fintype.all_card_le_rel_image_card_iff_exists_injective {α : Type u} {β : Type v}
    [DecidableEq β] (r : α → β → Prop) [∀ a : α, Fintype (Rel.image r {a})] :
    (∀ A : Finset α, A.card ≤ Fintype.card (Rel.image r A)) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, r x (f x) :=
  by
  let r' a := (Rel.image r {a}).toFinset
  have h : ∀ A : Finset α, Fintype.card (Rel.image r A) = (A.biUnion r').card :=
    by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    simp [Rel.image]
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp [Rel.image]
  simp only [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
#align fintype.all_card_le_rel_image_card_iff_exists_injective Fintype.all_card_le_rel_image_card_iff_exists_injective
-/

#print Fintype.all_card_le_filter_rel_iff_exists_injective /-
-- TODO: decidable_pred makes Yael sad. When an appropriate decidable_rel-like exists, fix it.
/-- This is a version of **Hall's Marriage Theorem** in terms of a relation to a finite type.
There is a transversal of the relation (an injective function `α → β` whose graph is a subrelation
of the relation) iff every subset of `k` terms of `α` is related to at least `k` terms of `β`.

It is like `fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `finset.filter`
rather than `rel.image`.
-/
theorem Fintype.all_card_le_filter_rel_iff_exists_injective {α : Type u} {β : Type v} [Fintype β]
    (r : α → β → Prop) [∀ a, DecidablePred (r a)] :
    (∀ A : Finset α, A.card ≤ (univ.filterₓ fun b : β => ∃ a ∈ A, r a b).card) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, r x (f x) :=
  by
  haveI := Classical.decEq β
  let r' a := univ.filter fun b => r a b
  have h : ∀ A : Finset α, (univ.filter fun b : β => ∃ a ∈ A, r a b) = A.biUnion r' :=
    by
    intro A
    ext b
    simp
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp
  simp_rw [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
#align fintype.all_card_le_filter_rel_iff_exists_injective Fintype.all_card_le_filter_rel_iff_exists_injective
-/

