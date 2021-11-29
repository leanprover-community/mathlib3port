import Mathbin.Combinatorics.Hall.Finite 
import Mathbin.Topology.Category.Top.Limits

/-!
# Hall's Marriage Theorem

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
are nonempty (`nonempty_sections_of_fintype_inverse_system`), which uses the
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

/-- The sup directed order on finsets.

TODO: remove when #9200 is merged.  There are two ways `finset α` can
get a `small_category` instance (used in
`hall_matchings_functor`). The first is from the preorder on `finset
α` and the second is from this `directed_order`. These categories
should be the same, but there is a defeq issue. -/
def hallFinsetDirectedOrder (α : Type u) : DirectedOrder (Finset α) :=
  ⟨fun s t =>
      by 
        classical 
        exact ⟨s ∪ t, subset_union_left s t, subset_union_right s t⟩⟩

attribute [local instance] hallFinsetDirectedOrder

/-- The set of matchings for `t` when restricted to a `finset` of `ι`. -/
def HallMatchingsOn {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :=
  { f:ι' → α | Function.Injective f ∧ ∀ x, f x ∈ t x }

/-- Given a matching on a finset, construct the restriction of that matching to a subset. -/
def HallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι → Finset α) {ι' ι'' : Finset ι} (h : ι' ⊆ ι'')
  (f : HallMatchingsOn t ι'') : HallMatchingsOn t ι' :=
  by 
    refine' ⟨fun i => f.val ⟨i, h i.property⟩, _⟩
    cases' f.property with hinj hc 
    refine' ⟨_, fun i => hc ⟨i, h i.property⟩⟩
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hh 
    simpa only [Subtype.mk_eq_mk] using hinj hh

-- error in Combinatorics.Hall.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- When the Hall condition is satisfied, the set of matchings on a finite set is nonempty.
This is where `finset.all_card_le_bUnion_card_iff_exists_injective'` comes into the argument. -/
theorem hall_matchings_on.nonempty
{ι : Type u}
{α : Type v}
[decidable_eq α]
(t : ι → finset α)
(h : ∀ s : finset ι, «expr ≤ »(s.card, (s.bUnion t).card))
(ι' : finset ι) : nonempty (hall_matchings_on t ι') :=
begin
  classical,
  refine [expr ⟨classical.indefinite_description _ _⟩],
  apply [expr (all_card_le_bUnion_card_iff_exists_injective' (λ i : ι', t i)).mp],
  intro [ident s'],
  convert [] [expr h (s'.image coe)] ["using", 1],
  simp [] [] ["only"] ["[", expr card_image_of_injective s' subtype.coe_injective, "]"] [] [],
  rw [expr image_bUnion] [],
  congr
end

/--
This is the `hall_matchings_on` sets assembled into a directed system.
-/
def hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι → Finset α) : «expr ᵒᵖ» (Finset ι) ⥤ Type max u v :=
  { obj := fun ι' => HallMatchingsOn t ι'.unop,
    map := fun ι' ι'' g f => HallMatchingsOn.restrict t (CategoryTheory.le_of_hom g.unop) f }

noncomputable instance HallMatchingsOn.fintype {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :
  Fintype (HallMatchingsOn t ι') :=
  by 
    classical 
    rw [HallMatchingsOn]
    let g : HallMatchingsOn t ι' → ι' → ι'.bUnion t
    ·
      rintro f i 
      refine' ⟨f.val i, _⟩
      rw [mem_bUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Fintype.ofInjective g 
    intro f f' h 
    simp only [g, Function.funext_iffₓ, Subtype.val_eq_coe] at h 
    ext a 
    exact h a

-- error in Combinatorics.Hall.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `s.bUnion t` is the union of all the sets `t i` for `i ∈ s`.

This theorem is bootstrapped from `finset.all_card_le_bUnion_card_iff_exists_injective'`,
which has the additional constraint that `ι` is a `fintype`.
-/
theorem finset.all_card_le_bUnion_card_iff_exists_injective
{ι : Type u}
{α : Type v}
[decidable_eq α]
(t : ι → finset α) : «expr ↔ »(∀
 s : finset ι, «expr ≤ »(s.card, (s.bUnion t).card), «expr∃ , »((f : ι → α), «expr ∧ »(function.injective f, ∀
   x, «expr ∈ »(f x, t x)))) :=
begin
  split,
  { intro [ident h],
    haveI [] [":", expr ∀
     ι' : «expr ᵒᵖ»(finset ι), nonempty ((hall_matchings_functor t).obj ι')] [":=", expr λ
     ι', hall_matchings_on.nonempty t h ι'.unop],
    classical,
    haveI [] [":", expr ∀
     ι' : «expr ᵒᵖ»(finset ι), fintype ((hall_matchings_functor t).obj ι')] [":=", expr begin
       intro [ident ι'],
       rw ["[", expr hall_matchings_functor, "]"] [],
       apply_instance
     end],
    obtain ["⟨", ident u, ",", ident hu, "⟩", ":=", expr nonempty_sections_of_fintype_inverse_system (hall_matchings_functor t)],
    refine [expr ⟨_, _, _⟩],
    { exact [expr λ
       i, (u (opposite.op ({i} : finset ι))).val ⟨i, by simp [] [] ["only"] ["[", expr opposite.unop_op, ",", expr mem_singleton, "]"] [] []⟩] },
    { intros [ident i, ident i'],
      have [ident subi] [":", expr «expr ⊆ »(({i} : finset ι), {i, i'})] [":=", expr by simp [] [] [] [] [] []],
      have [ident subi'] [":", expr «expr ⊆ »(({i'} : finset ι), {i, i'})] [":=", expr by simp [] [] [] [] [] []],
      have [ident le] [":", expr ∀ {s t : finset ι}, «expr ⊆ »(s, t) → «expr ≤ »(s, t)] [":=", expr λ _ _ h, h],
      rw ["[", "<-", expr hu (category_theory.hom_of_le (le subi)).op, ",", "<-", expr hu (category_theory.hom_of_le (le subi')).op, "]"] [],
      let [ident uii'] [] [":=", expr u (opposite.op ({i, i'} : finset ι))],
      exact [expr λ h, subtype.mk_eq_mk.mp (uii'.property.1 h)] },
    { intro [ident i],
      apply [expr (u (opposite.op ({i} : finset ι))).property.2] } },
  { rintro ["⟨", ident f, ",", ident hf₁, ",", ident hf₂, "⟩", ident s],
    rw ["<-", expr finset.card_image_of_injective s hf₁] [],
    apply [expr finset.card_le_of_subset],
    intro ["_"],
    rw ["[", expr finset.mem_image, ",", expr finset.mem_bUnion, "]"] [],
    rintros ["⟨", ident x, ",", ident hx, ",", ident rfl, "⟩"],
    exact [expr ⟨x, hx, hf₂ x⟩] }
end

-- error in Combinatorics.Hall.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance
{α : Type u}
{β : Type v}
[decidable_eq β]
(r : α → β → exprProp())
[∀ a : α, fintype (rel.image r {a})]
(A : finset α) : fintype (rel.image r A) :=
begin
  have [ident h] [":", expr «expr = »(rel.image r A, (A.bUnion (λ a, (rel.image r {a}).to_finset) : set β))] [],
  { ext [] [] [],
    simp [] [] [] ["[", expr rel.image, "]"] [] [] },
  rw ["[", expr h, "]"] [],
  apply [expr finset_coe.fintype]
end

-- error in Combinatorics.Hall.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite; see
`fintype.all_card_le_filter_rel_iff_exists_injective`).  There is
a transversal of the relation (an injective function `α → β` whose graph is
a subrelation of the relation) iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

Note: if `[fintype β]`, then there exist instances for `[∀ (a : α), fintype (rel.image r {a})]`.
-/
theorem fintype.all_card_le_rel_image_card_iff_exists_injective
{α : Type u}
{β : Type v}
[decidable_eq β]
(r : α → β → exprProp())
[∀
 a : α, fintype (rel.image r {a})] : «expr ↔ »(∀
 A : finset α, «expr ≤ »(A.card, fintype.card (rel.image r A)), «expr∃ , »((f : α → β), «expr ∧ »(function.injective f, ∀
   x, r x (f x)))) :=
begin
  let [ident r'] [] [":=", expr λ a, (rel.image r {a}).to_finset],
  have [ident h] [":", expr ∀ A : finset α, «expr = »(fintype.card (rel.image r A), (A.bUnion r').card)] [],
  { intro [ident A],
    rw ["<-", expr set.to_finset_card] [],
    apply [expr congr_arg],
    ext [] [ident b] [],
    simp [] [] [] ["[", expr rel.image, "]"] [] [] },
  have [ident h'] [":", expr ∀ (f : α → β) (x), «expr ↔ »(r x (f x), «expr ∈ »(f x, r' x))] [],
  { simp [] [] [] ["[", expr rel.image, "]"] [] [] },
  simp [] [] ["only"] ["[", expr h, ",", expr h', "]"] [] [],
  apply [expr finset.all_card_le_bUnion_card_iff_exists_injective]
end

-- error in Combinatorics.Hall.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
This is a version of **Hall's Marriage Theorem** in terms of a relation to a finite type.
There is a transversal of the relation (an injective function `α → β` whose graph is a subrelation
of the relation) iff every subset of `k` terms of `α` is related to at least `k` terms of `β`.

It is like `fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `finset.filter`
rather than `rel.image`.
-/
theorem fintype.all_card_le_filter_rel_iff_exists_injective
{α : Type u}
{β : Type v}
[fintype β]
(r : α → β → exprProp())
[∀
 a, decidable_pred (r a)] : «expr ↔ »(∀
 A : finset α, «expr ≤ »(A.card, (univ.filter (λ
    b : β, «expr∃ , »((a «expr ∈ » A), r a b))).card), «expr∃ , »((f : α → β), «expr ∧ »(function.injective f, ∀
   x, r x (f x)))) :=
begin
  haveI [] [] [":=", expr classical.dec_eq β],
  let [ident r'] [] [":=", expr λ a, univ.filter (λ b, r a b)],
  have [ident h] [":", expr ∀
   A : finset α, «expr = »(univ.filter (λ b : β, «expr∃ , »((a «expr ∈ » A), r a b)), A.bUnion r')] [],
  { intro [ident A],
    ext [] [ident b] [],
    simp [] [] [] [] [] [] },
  have [ident h'] [":", expr ∀ (f : α → β) (x), «expr ↔ »(r x (f x), «expr ∈ »(f x, r' x))] [],
  { simp [] [] [] [] [] [] },
  simp_rw ["[", expr h, ",", expr h', "]"] [],
  apply [expr finset.all_card_le_bUnion_card_iff_exists_injective]
end

