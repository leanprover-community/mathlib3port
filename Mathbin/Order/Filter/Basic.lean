/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad

! This file was ported from Lean 3 source module order.filter.basic
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Traversable.Instances
import Mathbin.Data.Set.Finite
import Mathbin.Order.Copy
import Mathbin.Tactic.Monotonicity.Default

/-!
# Theory of filters on sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `filter` : filters on a set;
* `at_top`, `at_bot`, `cofinite`, `principal` : specific filters;
* `map`, `comap` : operations on filters;
* `tendsto` : limit with respect to filters;
* `eventually` : `f.eventually p` means `{x | p x} ∈ f`;
* `frequently` : `f.frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` : takes a list of proofs `hᵢ : sᵢ ∈ f`, and replaces a goal `s ∈ f`
  with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `ne_bot f` : an utility class stating that `f` is a non-trivial filter.

Filters on a type `X` are sets of sets of `X` satisfying three conditions. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

In this file, we define the type `filter X` of filters on `X`, and endow it with a complete lattice
structure. This structure is lifted from the lattice structure on `set (set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `filter` is a monadic functor, with a push-forward operation
`filter.map` and a pull-back operation `filter.comap` that form a Galois connections for the
order on filters.

The examples of filters appearing in the description of the two motivating ideas are:
* `(at_top : filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in topology.uniform_space.basic)
* `μ.ae` : made of sets whose complement has zero measure with respect to `μ` (defined in
  `measure_theory.measure_space`)

The general notion of limit of a map with respect to filters on the source and target types
is `filter.tendsto`. It is defined in terms of the order and the push-forward operation.
The predicate "happening eventually" is `filter.eventually`, and "happening often" is
`filter.frequently`, whose definitions are immediate after `filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

For instance, anticipating on topology.basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `tendsto u at_top (𝓝 x) → (∀ᶠ n in at_top, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from topology.basic.

## Notations

* `∀ᶠ x in f, p x` : `f.eventually p`;
* `∃ᶠ x in f, p x` : `f.frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `principal s`, localized in `filter`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[ne_bot f]` in a number of lemmas and definitions.
-/


open Function Set Order

universe u v w x y

open Classical

#print Filter /-
/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure Filter (α : Type _) where
  sets : Set (Set α)
  univ_sets : Set.univ ∈ sets
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
#align filter Filter
-/

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can write `U ∈ F` as on paper. -/
instance {α : Type _} : Membership (Set α) (Filter α) :=
  ⟨fun U F => U ∈ F.sets⟩

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

/- warning: filter.mem_mk -> Filter.mem_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} (Set.{u1} α)} {h₁ : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Set.univ.{u1} α) t} {h₂ : forall {x : Set.{u1} α} {y : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) x y) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) y t)} {h₃ : forall {x : Set.{u1} α} {y : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x t) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) y t) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) x y) t)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (Filter.mk.{u1} α t h₁ h₂ h₃)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} (Set.{u1} α)} {h₁ : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Set.univ.{u1} α) t} {h₂ : forall {x : Set.{u1} α} {y : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) x t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) x y) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) y t)} {h₃ : forall {x : Set.{u1} α} {y : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) x t) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) y t) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) x y) t)}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (Filter.mk.{u1} α t h₁ h₂ h₃)) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s t)
Case conversion may be inaccurate. Consider using '#align filter.mem_mk Filter.mem_mkₓ'. -/
@[simp]
protected theorem mem_mk {t : Set (Set α)} {h₁ h₂ h₃} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t :=
  Iff.rfl
#align filter.mem_mk Filter.mem_mk

#print Filter.mem_sets /-
@[simp]
protected theorem mem_sets : s ∈ f.sets ↔ s ∈ f :=
  Iff.rfl
#align filter.mem_sets Filter.mem_sets
-/

#print Filter.inhabitedMem /-
instance inhabitedMem : Inhabited { s : Set α // s ∈ f } :=
  ⟨⟨univ, f.univ_sets⟩⟩
#align filter.inhabited_mem Filter.inhabitedMem
-/

#print Filter.filter_eq /-
theorem filter_eq : ∀ {f g : Filter α}, f.sets = g.sets → f = g
  | ⟨a, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
#align filter.filter_eq Filter.filter_eq
-/

#print Filter.filter_eq_iff /-
theorem filter_eq_iff : f = g ↔ f.sets = g.sets :=
  ⟨congr_arg _, filter_eq⟩
#align filter.filter_eq_iff Filter.filter_eq_iff
-/

#print Filter.ext_iff /-
protected theorem ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g := by
  simp only [filter_eq_iff, ext_iff, Filter.mem_sets]
#align filter.ext_iff Filter.ext_iff
-/

#print Filter.ext /-
@[ext]
protected theorem ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
  Filter.ext_iff.2
#align filter.ext Filter.ext
-/

/- warning: filter.coext -> Filter.coext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, (forall (s : Set.{u1} α), Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) g)) -> (Eq.{succ u1} (Filter.{u1} α) f g)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, (forall (s : Set.{u1} α), Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) f) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) g)) -> (Eq.{succ u1} (Filter.{u1} α) f g)
Case conversion may be inaccurate. Consider using '#align filter.coext Filter.coextₓ'. -/
/-- An extensionality lemma that is useful for filters with good lemmas about `sᶜ ∈ f` (e.g.,
`filter.comap`, `filter.coprod`, `filter.Coprod`, `filter.cofinite`). -/
protected theorem coext (h : ∀ s, sᶜ ∈ f ↔ sᶜ ∈ g) : f = g :=
  Filter.ext <| compl_surjective.forall.2 h
#align filter.coext Filter.coext

#print Filter.univ_mem /-
@[simp]
theorem univ_mem : univ ∈ f :=
  f.univ_sets
#align filter.univ_mem Filter.univ_mem
-/

#print Filter.mem_of_superset /-
theorem mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy
#align filter.mem_of_superset Filter.mem_of_superset
-/

/- warning: filter.inter_mem -> Filter.inter_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) f)
Case conversion may be inaccurate. Consider using '#align filter.inter_mem Filter.inter_memₓ'. -/
theorem inter_mem {s t : Set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
  f.inter_sets hs ht
#align filter.inter_mem Filter.inter_mem

/- warning: filter.inter_mem_iff -> Filter.inter_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) f) (And (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) f) (And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f))
Case conversion may be inaccurate. Consider using '#align filter.inter_mem_iff Filter.inter_mem_iffₓ'. -/
@[simp]
theorem inter_mem_iff {s t : Set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f :=
  ⟨fun h => ⟨mem_of_superset h (inter_subset_left s t), mem_of_superset h (inter_subset_right s t)⟩,
    and_imp.2 inter_mem⟩
#align filter.inter_mem_iff Filter.inter_mem_iff

/- warning: filter.diff_mem -> Filter.diff_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t) f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t) f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) f)
Case conversion may be inaccurate. Consider using '#align filter.diff_mem Filter.diff_memₓ'. -/
theorem diff_mem {s t : Set α} (hs : s ∈ f) (ht : tᶜ ∈ f) : s \ t ∈ f :=
  inter_mem hs ht
#align filter.diff_mem Filter.diff_mem

#print Filter.univ_mem' /-
theorem univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
  mem_of_superset univ_mem fun x _ => h x
#align filter.univ_mem' Filter.univ_mem'
-/

#print Filter.mp_mem /-
theorem mp_mem (hs : s ∈ f) (h : { x | x ∈ s → x ∈ t } ∈ f) : t ∈ f :=
  mem_of_superset (inter_mem hs h) fun x ⟨h₁, h₂⟩ => h₂ h₁
#align filter.mp_mem Filter.mp_mem
-/

#print Filter.congr_sets /-
theorem congr_sets (h : { x | x ∈ s ↔ x ∈ t } ∈ f) : s ∈ f ↔ t ∈ f :=
  ⟨fun hs => mp_mem hs (mem_of_superset h fun x => Iff.mp), fun hs =>
    mp_mem hs (mem_of_superset h fun x => Iff.mpr)⟩
#align filter.congr_sets Filter.congr_sets
-/

#print Filter.binterᵢ_mem /-
@[simp]
theorem binterᵢ_mem {β : Type v} {s : β → Set α} {is : Set β} (hf : is.Finite) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
  Finite.induction_on hf (by simp) fun i s hi _ hs => by simp [hs]
#align filter.bInter_mem Filter.binterᵢ_mem
-/

#print Filter.binterᵢ_finset_mem /-
@[simp]
theorem binterᵢ_finset_mem {β : Type v} {s : β → Set α} (is : Finset β) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
  binterᵢ_mem is.finite_toSet
#align filter.bInter_finset_mem Filter.binterᵢ_finset_mem
-/

alias bInter_finset_mem ← _root_.finset.Inter_mem_sets
#align finset.Inter_mem_sets Finset.interᵢ_mem_sets

attribute [protected] Finset.interᵢ_mem_sets

#print Filter.interₛ_mem /-
@[simp]
theorem interₛ_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s ∈ f ↔ ∀ U ∈ s, U ∈ f := by
  rw [sInter_eq_bInter, bInter_mem hfin]
#align filter.sInter_mem Filter.interₛ_mem
-/

#print Filter.interᵢ_mem /-
@[simp]
theorem interᵢ_mem {β : Type v} {s : β → Set α} [Finite β] : (⋂ i, s i) ∈ f ↔ ∀ i, s i ∈ f := by
  simpa using bInter_mem finite_univ
#align filter.Inter_mem Filter.interᵢ_mem
-/

/- warning: filter.exists_mem_subset_iff -> Filter.exists_mem_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s))) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f)
Case conversion may be inaccurate. Consider using '#align filter.exists_mem_subset_iff Filter.exists_mem_subset_iffₓ'. -/
theorem exists_mem_subset_iff : (∃ t ∈ f, t ⊆ s) ↔ s ∈ f :=
  ⟨fun ⟨t, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩
#align filter.exists_mem_subset_iff Filter.exists_mem_subset_iff

/- warning: filter.monotone_mem -> Filter.monotone_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Monotone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (s : Set.{u1} α) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Monotone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (s : Set.{u1} α) => Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f)
Case conversion may be inaccurate. Consider using '#align filter.monotone_mem Filter.monotone_memₓ'. -/
theorem monotone_mem {f : Filter α} : Monotone fun s => s ∈ f := fun s t hst h =>
  mem_of_superset h hst
#align filter.monotone_mem Filter.monotone_mem

/- warning: filter.exists_mem_and_iff -> Filter.exists_mem_and_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {P : (Set.{u1} α) -> Prop} {Q : (Set.{u1} α) -> Prop}, (Antitone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) P) -> (Antitone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) Q) -> (Iff (And (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u f) => P u))) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u f) => Q u)))) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u f) => And (P u) (Q u)))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {P : (Set.{u1} α) -> Prop} {Q : (Set.{u1} α) -> Prop}, (Antitone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) P) -> (Antitone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) Q) -> (Iff (And (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u f) (P u))) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u f) (Q u)))) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u f) (And (P u) (Q u)))))
Case conversion may be inaccurate. Consider using '#align filter.exists_mem_and_iff Filter.exists_mem_and_iffₓ'. -/
theorem exists_mem_and_iff {P : Set α → Prop} {Q : Set α → Prop} (hP : Antitone P)
    (hQ : Antitone Q) : ((∃ u ∈ f, P u) ∧ ∃ u ∈ f, Q u) ↔ ∃ u ∈ f, P u ∧ Q u :=
  by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact
      ⟨u ∩ v, inter_mem huf hvf, hP (inter_subset_left _ _) hPu, hQ (inter_subset_right _ _) hQv⟩
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩
#align filter.exists_mem_and_iff Filter.exists_mem_and_iff

/- warning: filter.forall_in_swap -> Filter.forall_in_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {β : Type.{u2}} {p : (Set.{u1} α) -> β -> Prop}, Iff (forall (a : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) a f) -> (forall (b : β), p a b)) (forall (b : β) (a : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) a f) -> (p a b))
but is expected to have type
  forall {α : Type.{u2}} {f : Filter.{u2} α} {β : Type.{u1}} {p : (Set.{u2} α) -> β -> Prop}, Iff (forall (a : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) a f) -> (forall (b : β), p a b)) (forall (b : β) (a : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) a f) -> (p a b))
Case conversion may be inaccurate. Consider using '#align filter.forall_in_swap Filter.forall_in_swapₓ'. -/
theorem forall_in_swap {β : Type _} {p : Set α → β → Prop} :
    (∀ a ∈ f, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ f, p a b :=
  Set.forall_in_swap
#align filter.forall_in_swap Filter.forall_in_swap

end Filter

namespace Tactic.Interactive

open Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- `filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/
unsafe def filter_upwards (s : parse types.pexpr_list ?) (wth : parse with_ident_list ?)
    (tgt : parse (tk "using" *> texpr)?) : tactic Unit := do
  (s []).reverse.mapM fun e => eapplyc `filter.mp_mem >> eapply e
  eapplyc `filter.univ_mem'
  sorry
  let wth := wth.getD []
  if ¬wth then intros wth else skip
  match tgt with
    | some e => exact e
    | none => skip
#align tactic.interactive.filter_upwards tactic.interactive.filter_upwards

add_tactic_doc
  { Name := "filter_upwards"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.filter_upwards]
    tags := ["goal management", "lemma application"] }

end Tactic.Interactive

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type _} {ι : Sort x}

section Principal

#print Filter.principal /-
/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset x y hx := Subset.trans hx
  inter_sets x y := subset_inter
#align filter.principal Filter.principal
-/

-- mathport name: filter.principal
scoped notation "𝓟" => Filter.principal

#print Filter.mem_principal /-
@[simp]
theorem mem_principal {s t : Set α} : s ∈ 𝓟 t ↔ t ⊆ s :=
  Iff.rfl
#align filter.mem_principal Filter.mem_principal
-/

#print Filter.mem_principal_self /-
theorem mem_principal_self (s : Set α) : s ∈ 𝓟 s :=
  Subset.rfl
#align filter.mem_principal_self Filter.mem_principal_self
-/

end Principal

open Filter

section Join

#print Filter.join /-
/-- The join of a filter of filters is defined by the relation `s ∈ join f ↔ {t | s ∈ t} ∈ f`. -/
def join (f : Filter (Filter α)) : Filter α
    where
  sets := { s | { t : Filter α | s ∈ t } ∈ f }
  univ_sets := by simp only [mem_set_of_eq, univ_sets, ← Filter.mem_sets, set_of_true]
  sets_of_superset x y hx xy := mem_of_superset hx fun f h => mem_of_superset h xy
  inter_sets x y hx hy := mem_of_superset (inter_mem hx hy) fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂
#align filter.join Filter.join
-/

#print Filter.mem_join /-
@[simp]
theorem mem_join {s : Set α} {f : Filter (Filter α)} : s ∈ join f ↔ { t | s ∈ t } ∈ f :=
  Iff.rfl
#align filter.mem_join Filter.mem_join
-/

end Join

section Lattice

variable {f g : Filter α} {s t : Set α}

instance : PartialOrder (Filter α)
    where
  le f g := ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm a b h₁ h₂ := filter_eq <| Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

/- warning: filter.le_def -> Filter.le_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g) (forall (x : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) x g) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) x f))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g) (forall (x : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) x g) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) x f))
Case conversion may be inaccurate. Consider using '#align filter.le_def Filter.le_defₓ'. -/
theorem le_def : f ≤ g ↔ ∀ x ∈ g, x ∈ f :=
  Iff.rfl
#align filter.le_def Filter.le_def

/- warning: filter.not_le -> Filter.not_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Not (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s g) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s g) => Not (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Not (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s g) (Not (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f))))
Case conversion may be inaccurate. Consider using '#align filter.not_le Filter.not_leₓ'. -/
protected theorem not_le : ¬f ≤ g ↔ ∃ s ∈ g, s ∉ f := by simp_rw [le_def, not_forall]
#align filter.not_le Filter.not_le

#print Filter.GenerateSets /-
/-- `generate_sets g s`: `s` is in the filter closure of `g`. -/
inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → generate_sets s
  | univ : generate_sets univ
  | Superset {s t : Set α} : generate_sets s → s ⊆ t → generate_sets t
  | inter {s t : Set α} : generate_sets s → generate_sets t → generate_sets (s ∩ t)
#align filter.generate_sets Filter.GenerateSets
-/

#print Filter.generate /-
/-- `generate g` is the largest filter containing the sets `g`. -/
def generate (g : Set (Set α)) : Filter α
    where
  sets := GenerateSets g
  univ_sets := GenerateSets.univ
  sets_of_superset x y := GenerateSets.superset
  inter_sets s t := GenerateSets.inter
#align filter.generate Filter.generate
-/

/- warning: filter.sets_iff_generate -> Filter.le_generate_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (Set.{u1} α)} {f : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (Filter.generate.{u1} α s)) (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) s (Filter.sets.{u1} α f))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (Set.{u1} α)} {f : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (Filter.generate.{u1} α s)) (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) s (Filter.sets.{u1} α f))
Case conversion may be inaccurate. Consider using '#align filter.sets_iff_generate Filter.le_generate_iffₓ'. -/
theorem le_generate_iff {s : Set (Set α)} {f : Filter α} : f ≤ Filter.generate s ↔ s ⊆ f.sets :=
  Iff.intro (fun h u hu => h <| GenerateSets.basic <| hu) fun h u hu =>
    hu.recOn h univ_mem (fun x y _ hxy hx => mem_of_superset hx hxy) fun x y _ _ hx hy =>
      inter_mem hx hy
#align filter.sets_iff_generate Filter.le_generate_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print Filter.mem_generate_iff /-
theorem mem_generate_iff {s : Set <| Set α} {U : Set α} :
    U ∈ generate s ↔ ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ ⋂₀ t ⊆ U :=
  by
  constructor <;> intro h
  · induction h
    case basic V V_in =>
      exact ⟨{V}, singleton_subset_iff.2 V_in, finite_singleton _, (sInter_singleton _).Subset⟩
    case univ => exact ⟨∅, empty_subset _, finite_empty, subset_univ _⟩
    case superset V W hV' hVW hV =>
      rcases hV with ⟨t, hts, ht, htV⟩
      exact ⟨t, hts, ht, htV.trans hVW⟩
    case
      inter V W hV' hW' hV hW =>
      rcases hV, hW with ⟨⟨t, hts, ht, htV⟩, u, hus, hu, huW⟩
      exact
        ⟨t ∪ u, union_subset hts hus, ht.union hu,
          (sInter_union _ _).Subset.trans <| inter_subset_inter htV huW⟩
  · rcases h with ⟨t, hts, tfin, h⟩
    exact mem_of_superset ((sInter_mem tfin).2 fun V hV => generate_sets.basic <| hts hV) h
#align filter.mem_generate_iff Filter.mem_generate_iff
-/

#print Filter.mkOfClosure /-
/-- `mk_of_closure s hs` constructs a filter on `α` whose elements set is exactly
`s : set (set α)`, provided one gives the assumption `hs : (generate s).sets = s`. -/
protected def mkOfClosure (s : Set (Set α)) (hs : (generate s).sets = s) : Filter α
    where
  sets := s
  univ_sets := hs ▸ (univ_mem : univ ∈ generate s)
  sets_of_superset x y := hs ▸ (mem_of_superset : x ∈ generate s → x ⊆ y → y ∈ generate s)
  inter_sets x y := hs ▸ (inter_mem : x ∈ generate s → y ∈ generate s → x ∩ y ∈ generate s)
#align filter.mk_of_closure Filter.mkOfClosure
-/

#print Filter.mkOfClosure_sets /-
theorem mkOfClosure_sets {s : Set (Set α)} {hs : (generate s).sets = s} :
    Filter.mkOfClosure s hs = generate s :=
  Filter.ext fun u =>
    show u ∈ (Filter.mkOfClosure s hs).sets ↔ u ∈ (generate s).sets from hs.symm ▸ Iff.rfl
#align filter.mk_of_closure_sets Filter.mkOfClosure_sets
-/

/- warning: filter.gi_generate -> Filter.giGenerate is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), GaloisInsertion.{u1, u1} (Set.{u1} (Set.{u1} α)) (OrderDual.{u1} (Filter.{u1} α)) (PartialOrder.toPreorder.{u1} (Set.{u1} (Set.{u1} α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Set.{u1} α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Set.{u1} α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Set.{u1} α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Set.{u1} α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Set.{u1} α)) (Set.completeBooleanAlgebra.{u1} (Set.{u1} α)))))))) (OrderDual.preorder.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.generate.{u1} α) (Filter.sets.{u1} α)
but is expected to have type
  forall (α : Type.{u1}), GaloisInsertion.{u1, u1} (Set.{u1} (Set.{u1} α)) (OrderDual.{u1} (Filter.{u1} α)) (PartialOrder.toPreorder.{u1} (Set.{u1} (Set.{u1} α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Set.{u1} α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Set.{u1} α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Set.{u1} α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Set.{u1} α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Set.{u1} α)) (Set.instCompleteBooleanAlgebraSet.{u1} (Set.{u1} α)))))))) (OrderDual.preorder.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.generate.{u1} α) (Filter.sets.{u1} α)
Case conversion may be inaccurate. Consider using '#align filter.gi_generate Filter.giGenerateₓ'. -/
/-- Galois insertion from sets of sets into filters. -/
def giGenerate (α : Type _) :
    @GaloisInsertion (Set (Set α)) (Filter α)ᵒᵈ _ _ Filter.generate Filter.sets
    where
  gc s f := le_generate_iff
  le_l_u f u h := GenerateSets.basic h
  choice s hs := Filter.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| le_rfl)
  choice_eq s hs := mkOfClosure_sets
#align filter.gi_generate Filter.giGenerate

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters. -/
instance : HasInf (Filter α) :=
  ⟨fun f g : Filter α =>
    { sets := { s | ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b }
      univ_sets := ⟨_, univ_mem, _, univ_mem, by simp⟩
      sets_of_superset := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ xy
        refine'
          ⟨a ∪ y, mem_of_superset ha (subset_union_left a y), b ∪ y,
            mem_of_superset hb (subset_union_left b y), _⟩
        rw [← inter_union_distrib_right, union_eq_self_of_subset_left xy]
      inter_sets := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine' ⟨a ∩ c, inter_mem ha hc, b ∩ d, inter_mem hb hd, _⟩
        ac_rfl }⟩

/- warning: filter.mem_inf_iff -> Filter.mem_inf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) (Exists.{succ u1} (Set.{u1} α) (fun (t₁ : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t₁ f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t₁ f) => Exists.{succ u1} (Set.{u1} α) (fun (t₂ : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t₂ g) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t₂ g) => Eq.{succ u1} (Set.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t₁ t₂))))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) (Exists.{succ u1} (Set.{u1} α) (fun (t₁ : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t₁ f) (Exists.{succ u1} (Set.{u1} α) (fun (t₂ : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t₂ g) (Eq.{succ u1} (Set.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t₁ t₂))))))
Case conversion may be inaccurate. Consider using '#align filter.mem_inf_iff Filter.mem_inf_iffₓ'. -/
theorem mem_inf_iff {f g : Filter α} {s : Set α} : s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂ :=
  Iff.rfl
#align filter.mem_inf_iff Filter.mem_inf_iff

/- warning: filter.mem_inf_of_left -> Filter.mem_inf_of_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g))
Case conversion may be inaccurate. Consider using '#align filter.mem_inf_of_left Filter.mem_inf_of_leftₓ'. -/
theorem mem_inf_of_left {f g : Filter α} {s : Set α} (h : s ∈ f) : s ∈ f ⊓ g :=
  ⟨s, h, univ, univ_mem, (inter_univ s).symm⟩
#align filter.mem_inf_of_left Filter.mem_inf_of_left

/- warning: filter.mem_inf_of_right -> Filter.mem_inf_of_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s g) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s g) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g))
Case conversion may be inaccurate. Consider using '#align filter.mem_inf_of_right Filter.mem_inf_of_rightₓ'. -/
theorem mem_inf_of_right {f g : Filter α} {s : Set α} (h : s ∈ g) : s ∈ f ⊓ g :=
  ⟨univ, univ_mem, s, h, (univ_inter s).symm⟩
#align filter.mem_inf_of_right Filter.mem_inf_of_right

/- warning: filter.inter_mem_inf -> Filter.inter_mem_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g))
Case conversion may be inaccurate. Consider using '#align filter.inter_mem_inf Filter.inter_mem_infₓ'. -/
theorem inter_mem_inf {α : Type u} {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) :
    s ∩ t ∈ f ⊓ g :=
  ⟨s, hs, t, ht, rfl⟩
#align filter.inter_mem_inf Filter.inter_mem_inf

/- warning: filter.mem_inf_of_inter -> Filter.mem_inf_of_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) u) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) u) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g))
Case conversion may be inaccurate. Consider using '#align filter.mem_inf_of_inter Filter.mem_inf_of_interₓ'. -/
theorem mem_inf_of_inter {f g : Filter α} {s t u : Set α} (hs : s ∈ f) (ht : t ∈ g)
    (h : s ∩ t ⊆ u) : u ∈ f ⊓ g :=
  mem_of_superset (inter_mem_inf hs ht) h
#align filter.mem_inf_of_inter Filter.mem_inf_of_inter

/- warning: filter.mem_inf_iff_superset -> Filter.mem_inf_iff_superset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) (Exists.{succ u1} (Set.{u1} α) (fun (t₁ : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t₁ f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t₁ f) => Exists.{succ u1} (Set.{u1} α) (fun (t₂ : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t₂ g) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t₂ g) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t₁ t₂) s)))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) (Exists.{succ u1} (Set.{u1} α) (fun (t₁ : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t₁ f) (Exists.{succ u1} (Set.{u1} α) (fun (t₂ : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t₂ g) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t₁ t₂) s)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_inf_iff_superset Filter.mem_inf_iff_supersetₓ'. -/
theorem mem_inf_iff_superset {f g : Filter α} {s : Set α} :
    s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ∩ t₂ ⊆ s :=
  ⟨fun ⟨t₁, h₁, t₂, h₂, Eq⟩ => ⟨t₁, h₁, t₂, h₂, Eq ▸ Subset.rfl⟩, fun ⟨t₁, h₁, t₂, h₂, sub⟩ =>
    mem_inf_of_inter h₁ h₂ sub⟩
#align filter.mem_inf_iff_superset Filter.mem_inf_iff_superset

instance : Top (Filter α) :=
  ⟨{  sets := { s | ∀ x, x ∈ s }
      univ_sets := fun x => mem_univ x
      sets_of_superset := fun x y hx hxy a => hxy (hx a)
      inter_sets := fun x y hx hy a => mem_inter (hx _) (hy _) }⟩

/- warning: filter.mem_top_iff_forall -> Filter.mem_top_iff_forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (forall (x : α), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (forall (x : α), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)
Case conversion may be inaccurate. Consider using '#align filter.mem_top_iff_forall Filter.mem_top_iff_forallₓ'. -/
theorem mem_top_iff_forall {s : Set α} : s ∈ (⊤ : Filter α) ↔ ∀ x, x ∈ s :=
  Iff.rfl
#align filter.mem_top_iff_forall Filter.mem_top_iff_forall

/- warning: filter.mem_top -> Filter.mem_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (Eq.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (Eq.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align filter.mem_top Filter.mem_topₓ'. -/
@[simp]
theorem mem_top {s : Set α} : s ∈ (⊤ : Filter α) ↔ s = univ := by
  rw [mem_top_iff_forall, eq_univ_iff_forall]
#align filter.mem_top Filter.mem_top

section CompleteLattice

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for the lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/
private def original_complete_lattice : CompleteLattice (Filter α) :=
  @OrderDual.completeLattice _ (giGenerate α).liftCompleteLattice
#align filter.original_complete_lattice filter.original_complete_lattice

attribute [local instance] original_complete_lattice

instance : CompleteLattice (Filter α) :=
  originalCompleteLattice.copy-- le
      Filter.partialOrder.le
    rfl-- top
      Filter.hasTop.1
    (top_unique fun s hs => by simp [mem_top.1 hs])-- bot
    _
    rfl-- sup
    _
    rfl-- inf
      Filter.hasInf.1
    (by
      ext (f g) : 2
      exact
        le_antisymm (le_inf (fun s => mem_inf_of_left) fun s => mem_inf_of_right)
          (by
            rintro s ⟨a, ha, b, hb, rfl⟩
            exact
              inter_sets _ (@inf_le_left (Filter α) _ _ _ _ ha)
                (@inf_le_right (Filter α) _ _ _ _ hb)))
    (-- Sup
      join ∘
      𝓟)
    (by
      ext (s x)
      exact mem_Inter₂.symm.trans (Set.ext_iff.1 (sInter_image _ _) x).symm)-- Inf
    _
    rfl

instance : Inhabited (Filter α) :=
  ⟨⊥⟩

end CompleteLattice

#print Filter.NeBot /-
/-- A filter is `ne_bot` if it is not equal to `⊥`, or equivalently the empty set
does not belong to the filter. Bourbaki include this assumption in the definition
of a filter but we prefer to have a `complete_lattice` structure on filter, so
we use a typeclass argument in lemmas instead. -/
class NeBot (f : Filter α) : Prop where
  ne' : f ≠ ⊥
#align filter.ne_bot Filter.NeBot
-/

/- warning: filter.ne_bot_iff -> Filter.neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α f) (Ne.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α f) (Ne.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.ne_bot_iff Filter.neBot_iffₓ'. -/
theorem neBot_iff {f : Filter α} : NeBot f ↔ f ≠ ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align filter.ne_bot_iff Filter.neBot_iff

/- warning: filter.ne_bot.ne -> Filter.NeBot.ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α}, (Filter.NeBot.{u1} α f) -> (Ne.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α}, (Filter.NeBot.{u1} α f) -> (Ne.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.ne_bot.ne Filter.NeBot.neₓ'. -/
theorem NeBot.ne {f : Filter α} (hf : NeBot f) : f ≠ ⊥ :=
  NeBot.ne'
#align filter.ne_bot.ne Filter.NeBot.ne

/- warning: filter.not_ne_bot -> Filter.not_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Not (Filter.NeBot.{u1} α f)) (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Not (Filter.NeBot.{u1} α f)) (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.not_ne_bot Filter.not_neBotₓ'. -/
@[simp]
theorem not_neBot {α : Type _} {f : Filter α} : ¬f.ne_bot ↔ f = ⊥ :=
  not_iff_comm.1 neBot_iff.symm
#align filter.not_ne_bot Filter.not_neBot

/- warning: filter.ne_bot.mono -> Filter.NeBot.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, (Filter.NeBot.{u1} α f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g) -> (Filter.NeBot.{u1} α g)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, (Filter.NeBot.{u1} α f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g) -> (Filter.NeBot.{u1} α g)
Case conversion may be inaccurate. Consider using '#align filter.ne_bot.mono Filter.NeBot.monoₓ'. -/
theorem NeBot.mono {f g : Filter α} (hf : NeBot f) (hg : f ≤ g) : NeBot g :=
  ⟨ne_bot_of_le_ne_bot hf.1 hg⟩
#align filter.ne_bot.mono Filter.NeBot.mono

/- warning: filter.ne_bot_of_le -> Filter.neBot_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} [hf : Filter.NeBot.{u1} α f], (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g) -> (Filter.NeBot.{u1} α g)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} [hf : Filter.NeBot.{u1} α f], (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g) -> (Filter.NeBot.{u1} α g)
Case conversion may be inaccurate. Consider using '#align filter.ne_bot_of_le Filter.neBot_of_leₓ'. -/
theorem neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f ≤ g) : NeBot g :=
  hf.mono hg
#align filter.ne_bot_of_le Filter.neBot_of_le

/- warning: filter.sup_ne_bot -> Filter.sup_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g)) (Or (Filter.NeBot.{u1} α f) (Filter.NeBot.{u1} α g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.NeBot.{u1} α (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f g)) (Or (Filter.NeBot.{u1} α f) (Filter.NeBot.{u1} α g))
Case conversion may be inaccurate. Consider using '#align filter.sup_ne_bot Filter.sup_neBotₓ'. -/
@[simp]
theorem sup_neBot {f g : Filter α} : NeBot (f ⊔ g) ↔ NeBot f ∨ NeBot g := by
  simp [ne_bot_iff, not_and_or]
#align filter.sup_ne_bot Filter.sup_neBot

/- warning: filter.not_disjoint_self_iff -> Filter.not_disjoint_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Not (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) f f)) (Filter.NeBot.{u1} α f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Not (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) f f)) (Filter.NeBot.{u1} α f)
Case conversion may be inaccurate. Consider using '#align filter.not_disjoint_self_iff Filter.not_disjoint_self_iffₓ'. -/
theorem not_disjoint_self_iff : ¬Disjoint f f ↔ f.ne_bot := by rw [disjoint_self, ne_bot_iff]
#align filter.not_disjoint_self_iff Filter.not_disjoint_self_iff

/- warning: filter.bot_sets_eq -> Filter.bot_sets_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Set.univ.{u1} (Set.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Set.univ.{u1} (Set.{u1} α))
Case conversion may be inaccurate. Consider using '#align filter.bot_sets_eq Filter.bot_sets_eqₓ'. -/
theorem bot_sets_eq : (⊥ : Filter α).sets = univ :=
  rfl
#align filter.bot_sets_eq Filter.bot_sets_eq

/- warning: filter.sup_sets_eq -> Filter.sup_sets_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g)) (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasInter.{u1} (Set.{u1} α)) (Filter.sets.{u1} α f) (Filter.sets.{u1} α g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f g)) (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.instInterSet.{u1} (Set.{u1} α)) (Filter.sets.{u1} α f) (Filter.sets.{u1} α g))
Case conversion may be inaccurate. Consider using '#align filter.sup_sets_eq Filter.sup_sets_eqₓ'. -/
theorem sup_sets_eq {f g : Filter α} : (f ⊔ g).sets = f.sets ∩ g.sets :=
  (giGenerate α).gc.u_inf
#align filter.sup_sets_eq Filter.sup_sets_eq

/- warning: filter.Sup_sets_eq -> Filter.supₛ_sets_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (Filter.{u1} α)}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (SupSet.supₛ.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) s)) (Set.interᵢ.{u1, succ u1} (Set.{u1} α) (Filter.{u1} α) (fun (f : Filter.{u1} α) => Set.interᵢ.{u1, 0} (Set.{u1} α) (Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) f s) (fun (H : Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) f s) => Filter.sets.{u1} α f)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (Filter.{u1} α)}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (SupSet.supₛ.{u1} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) s)) (Set.interᵢ.{u1, succ u1} (Set.{u1} α) (Filter.{u1} α) (fun (f : Filter.{u1} α) => Set.interᵢ.{u1, 0} (Set.{u1} α) (Membership.mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.instMembershipSet.{u1} (Filter.{u1} α)) f s) (fun (H : Membership.mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.instMembershipSet.{u1} (Filter.{u1} α)) f s) => Filter.sets.{u1} α f)))
Case conversion may be inaccurate. Consider using '#align filter.Sup_sets_eq Filter.supₛ_sets_eqₓ'. -/
theorem supₛ_sets_eq {s : Set (Filter α)} : (supₛ s).sets = ⋂ f ∈ s, (f : Filter α).sets :=
  (giGenerate α).gc.u_infₛ
#align filter.Sup_sets_eq Filter.supₛ_sets_eq

/- warning: filter.supr_sets_eq -> Filter.supᵢ_sets_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (Set.interᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => Filter.sets.{u1} α (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (supᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (Set.interᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => Filter.sets.{u1} α (f i)))
Case conversion may be inaccurate. Consider using '#align filter.supr_sets_eq Filter.supᵢ_sets_eqₓ'. -/
theorem supᵢ_sets_eq {f : ι → Filter α} : (supᵢ f).sets = ⋂ i, (f i).sets :=
  (giGenerate α).gc.u_infᵢ
#align filter.supr_sets_eq Filter.supᵢ_sets_eq

/- warning: filter.generate_empty -> Filter.generate_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasEmptyc.{u1} (Set.{u1} α)))) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Set.{u1} α)) (Set.instEmptyCollectionSet.{u1} (Set.{u1} α)))) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))
Case conversion may be inaccurate. Consider using '#align filter.generate_empty Filter.generate_emptyₓ'. -/
theorem generate_empty : Filter.generate ∅ = (⊤ : Filter α) :=
  (giGenerate α).gc.l_bot
#align filter.generate_empty Filter.generate_empty

/- warning: filter.generate_univ -> Filter.generate_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α (Set.univ.{u1} (Set.{u1} α))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α (Set.univ.{u1} (Set.{u1} α))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.generate_univ Filter.generate_univₓ'. -/
theorem generate_univ : Filter.generate univ = (⊥ : Filter α) :=
  mkOfClosure_sets.symm
#align filter.generate_univ Filter.generate_univ

/- warning: filter.generate_union -> Filter.generate_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (Set.{u1} α)} {t : Set.{u1} (Set.{u1} α)}, Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasUnion.{u1} (Set.{u1} α)) s t)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (Filter.generate.{u1} α s) (Filter.generate.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (Set.{u1} α)} {t : Set.{u1} (Set.{u1} α)}, Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.instUnionSet.{u1} (Set.{u1} α)) s t)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (Filter.generate.{u1} α s) (Filter.generate.{u1} α t))
Case conversion may be inaccurate. Consider using '#align filter.generate_union Filter.generate_unionₓ'. -/
theorem generate_union {s t : Set (Set α)} :
    Filter.generate (s ∪ t) = Filter.generate s ⊓ Filter.generate t :=
  (giGenerate α).gc.l_sup
#align filter.generate_union Filter.generate_union

/- warning: filter.generate_Union -> Filter.generate_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} (Set.{u1} α))}, Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α (Set.unionᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => s i))) (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => Filter.generate.{u1} α (s i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} (Set.{u1} α))}, Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α (Set.unionᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => s i))) (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => Filter.generate.{u1} α (s i)))
Case conversion may be inaccurate. Consider using '#align filter.generate_Union Filter.generate_unionᵢₓ'. -/
theorem generate_unionᵢ {s : ι → Set (Set α)} :
    Filter.generate (⋃ i, s i) = ⨅ i, Filter.generate (s i) :=
  (giGenerate α).gc.l_supᵢ
#align filter.generate_Union Filter.generate_unionᵢ

/- warning: filter.mem_bot -> Filter.mem_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.mem_bot Filter.mem_botₓ'. -/
@[simp]
theorem mem_bot {s : Set α} : s ∈ (⊥ : Filter α) :=
  trivial
#align filter.mem_bot Filter.mem_bot

/- warning: filter.mem_sup -> Filter.mem_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g)) (And (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f g)) (And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s g))
Case conversion may be inaccurate. Consider using '#align filter.mem_sup Filter.mem_supₓ'. -/
@[simp]
theorem mem_sup {f g : Filter α} {s : Set α} : s ∈ f ⊔ g ↔ s ∈ f ∧ s ∈ g :=
  Iff.rfl
#align filter.mem_sup Filter.mem_sup

/- warning: filter.union_mem_sup -> Filter.union_mem_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f g))
Case conversion may be inaccurate. Consider using '#align filter.union_mem_sup Filter.union_mem_supₓ'. -/
theorem union_mem_sup {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : s ∪ t ∈ f ⊔ g :=
  ⟨mem_of_superset hs (subset_union_left s t), mem_of_superset ht (subset_union_right s t)⟩
#align filter.union_mem_sup Filter.union_mem_sup

/- warning: filter.mem_Sup -> Filter.mem_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : Set.{u1} α} {s : Set.{u1} (Filter.{u1} α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) x (SupSet.supₛ.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) s)) (forall (f : Filter.{u1} α), (Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) f s) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) x f))
but is expected to have type
  forall {α : Type.{u1}} {x : Set.{u1} α} {s : Set.{u1} (Filter.{u1} α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) x (SupSet.supₛ.{u1} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) s)) (forall (f : Filter.{u1} α), (Membership.mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.instMembershipSet.{u1} (Filter.{u1} α)) f s) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) x f))
Case conversion may be inaccurate. Consider using '#align filter.mem_Sup Filter.mem_supₛₓ'. -/
@[simp]
theorem mem_supₛ {x : Set α} {s : Set (Filter α)} : x ∈ supₛ s ↔ ∀ f ∈ s, x ∈ (f : Filter α) :=
  Iff.rfl
#align filter.mem_Sup Filter.mem_supₛ

/- warning: filter.mem_supr -> Filter.mem_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {x : Set.{u1} α} {f : ι -> (Filter.{u1} α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) x (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (forall (i : ι), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) x (f i))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {x : Set.{u1} α} {f : ι -> (Filter.{u1} α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) x (supᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (forall (i : ι), Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) x (f i))
Case conversion may be inaccurate. Consider using '#align filter.mem_supr Filter.mem_supᵢₓ'. -/
@[simp]
theorem mem_supᵢ {x : Set α} {f : ι → Filter α} : x ∈ supᵢ f ↔ ∀ i, x ∈ f i := by
  simp only [← Filter.mem_sets, supr_sets_eq, iff_self_iff, mem_Inter]
#align filter.mem_supr Filter.mem_supᵢ

/- warning: filter.supr_ne_bot -> Filter.supᵢ_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)}, Iff (Filter.NeBot.{u1} α (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => f i))) (Exists.{u2} ι (fun (i : ι) => Filter.NeBot.{u1} α (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)}, Iff (Filter.NeBot.{u1} α (supᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => f i))) (Exists.{u2} ι (fun (i : ι) => Filter.NeBot.{u1} α (f i)))
Case conversion may be inaccurate. Consider using '#align filter.supr_ne_bot Filter.supᵢ_neBotₓ'. -/
@[simp]
theorem supᵢ_neBot {f : ι → Filter α} : (⨆ i, f i).ne_bot ↔ ∃ i, (f i).ne_bot := by
  simp [ne_bot_iff]
#align filter.supr_ne_bot Filter.supᵢ_neBot

/- warning: filter.infi_eq_generate -> Filter.infᵢ_eq_generate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Filter.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι s) (Filter.generate.{u1} α (Set.unionᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => Filter.sets.{u1} α (s i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Filter.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι s) (Filter.generate.{u1} α (Set.unionᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => Filter.sets.{u1} α (s i))))
Case conversion may be inaccurate. Consider using '#align filter.infi_eq_generate Filter.infᵢ_eq_generateₓ'. -/
theorem infᵢ_eq_generate (s : ι → Filter α) : infᵢ s = generate (⋃ i, (s i).sets) :=
  show generate _ = generate _ from congr_arg _ <| congr_arg supₛ <| (range_comp _ _).symm
#align filter.infi_eq_generate Filter.infᵢ_eq_generate

/- warning: filter.mem_infi_of_mem -> Filter.mem_infᵢ_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} (i : ι) {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (f i)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} (i : ι) {s : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (f i)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi_of_mem Filter.mem_infᵢ_of_memₓ'. -/
theorem mem_infᵢ_of_mem {f : ι → Filter α} (i : ι) : ∀ {s}, s ∈ f i → s ∈ ⨅ i, f i :=
  show (⨅ i, f i) ≤ f i from infᵢ_le _ _
#align filter.mem_infi_of_mem Filter.mem_infᵢ_of_mem

/- warning: filter.mem_infi_of_Inter -> Filter.mem_infᵢ_of_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : ι -> (Filter.{u1} α)} {U : Set.{u1} α} {I : Set.{u2} ι}, (Set.Finite.{u2} ι I) -> (forall {V : (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) -> (Set.{u1} α)}, (forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (V i) (s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) => V i)) U) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : ι -> (Filter.{u2} α)} {U : Set.{u2} α} {I : Set.{u1} ι}, (Set.Finite.{u1} ι I) -> (forall {V : (Set.Elem.{u1} ι I) -> (Set.{u2} α)}, (forall (i : Set.Elem.{u1} ι I), Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (V i) (s (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x I) i))) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.interᵢ.{u2, succ u1} α (Set.Elem.{u1} ι I) (fun (i : Set.Elem.{u1} ι I) => V i)) U) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) U (infᵢ.{u2, succ u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => s i))))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi_of_Inter Filter.mem_infᵢ_of_interᵢₓ'. -/
theorem mem_infᵢ_of_interᵢ {ι} {s : ι → Filter α} {U : Set α} {I : Set ι} (I_fin : I.Finite)
    {V : I → Set α} (hV : ∀ i, V i ∈ s i) (hU : (⋂ i, V i) ⊆ U) : U ∈ ⨅ i, s i :=
  by
  haveI := I_fin.fintype
  refine' mem_of_superset (Inter_mem.2 fun i => _) hU
  exact mem_infi_of_mem i (hV _)
#align filter.mem_infi_of_Inter Filter.mem_infᵢ_of_interᵢ

/- warning: filter.mem_infi -> Filter.mem_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : ι -> (Filter.{u1} α)} {U : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => s i))) (Exists.{succ u2} (Set.{u2} ι) (fun (I : Set.{u2} ι) => And (Set.Finite.{u2} ι I) (Exists.{max (succ u2) (succ u1)} ((coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) -> (Set.{u1} α)) (fun (V : (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) -> (Set.{u1} α)) => And (forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (V i) (s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I))))) i))) (Eq.{succ u1} (Set.{u1} α) U (Set.interᵢ.{u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) I) => V i)))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : ι -> (Filter.{u2} α)} {U : Set.{u2} α}, Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) U (infᵢ.{u2, succ u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => s i))) (Exists.{succ u1} (Set.{u1} ι) (fun (I : Set.{u1} ι) => And (Set.Finite.{u1} ι I) (Exists.{max (succ u2) (succ u1)} ((Set.Elem.{u1} ι I) -> (Set.{u2} α)) (fun (V : (Set.Elem.{u1} ι I) -> (Set.{u2} α)) => And (forall (i : Set.Elem.{u1} ι I), Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (V i) (s (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x I) i))) (Eq.{succ u2} (Set.{u2} α) U (Set.interᵢ.{u2, succ u1} α (Set.Elem.{u1} ι I) (fun (i : Set.Elem.{u1} ι I) => V i)))))))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi Filter.mem_infᵢₓ'. -/
theorem mem_infᵢ {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔ ∃ I : Set ι, I.Finite ∧ ∃ V : I → Set α, (∀ i, V i ∈ s i) ∧ U = ⋂ i, V i :=
  by
  constructor
  · rw [infi_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_Union_of_finite_subset_Union tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_Union] at tinter
    set V := fun i => U ∪ ⋂₀ σ i with hV
    have V_in : ∀ i, V i ∈ s i := by
      rintro i
      have : ⋂₀ σ i ∈ s i := by
        rw [sInter_mem (σfin _)]
        apply σsub
      exact mem_of_superset this (subset_union_right _ _)
    refine' ⟨I, Ifin, V, V_in, _⟩
    rwa [hV, ← union_Inter, union_eq_self_of_subset_right]
  · rintro ⟨I, Ifin, V, V_in, rfl⟩
    exact mem_infi_of_Inter Ifin V_in subset.rfl
#align filter.mem_infi Filter.mem_infᵢ

/- warning: filter.mem_infi' -> Filter.mem_infᵢ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : ι -> (Filter.{u1} α)} {U : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => s i))) (Exists.{succ u2} (Set.{u2} ι) (fun (I : Set.{u2} ι) => And (Set.Finite.{u2} ι I) (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u1} α)) (fun (V : ι -> (Set.{u1} α)) => And (forall (i : ι), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (V i) (s i)) (And (forall (i : ι), (Not (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I)) -> (Eq.{succ u1} (Set.{u1} α) (V i) (Set.univ.{u1} α))) (And (Eq.{succ u1} (Set.{u1} α) U (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) => V i)))) (Eq.{succ u1} (Set.{u1} α) U (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => V i)))))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : ι -> (Filter.{u2} α)} {U : Set.{u2} α}, Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) U (infᵢ.{u2, succ u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => s i))) (Exists.{succ u1} (Set.{u1} ι) (fun (I : Set.{u1} ι) => And (Set.Finite.{u1} ι I) (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u2} α)) (fun (V : ι -> (Set.{u2} α)) => And (forall (i : ι), Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (V i) (s i)) (And (forall (i : ι), (Not (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I)) -> (Eq.{succ u2} (Set.{u2} α) (V i) (Set.univ.{u2} α))) (And (Eq.{succ u2} (Set.{u2} α) U (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) => V i)))) (Eq.{succ u2} (Set.{u2} α) U (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => V i)))))))))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi' Filter.mem_infᵢ'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (i «expr ∉ » I) -/
theorem mem_infᵢ' {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔
      ∃ I : Set ι,
        I.Finite ∧
          ∃ V : ι → Set α,
            (∀ i, V i ∈ s i) ∧
              (∀ (i) (_ : i ∉ I), V i = univ) ∧ (U = ⋂ i ∈ I, V i) ∧ U = ⋂ i, V i :=
  by
  simp only [mem_infi, SetCoe.forall', bInter_eq_Inter]
  refine' ⟨_, fun ⟨I, If, V, hVs, _, hVU, _⟩ => ⟨I, If, fun i => V i, fun i => hVs i, hVU⟩⟩
  rintro ⟨I, If, V, hV, rfl⟩
  refine' ⟨I, If, fun i => if hi : i ∈ I then V ⟨i, hi⟩ else univ, fun i => _, fun i hi => _, _⟩
  · split_ifs
    exacts[hV _, univ_mem]
  · exact dif_neg hi
  ·
    simp only [Inter_dite, bInter_eq_Inter, dif_pos (Subtype.coe_prop _), Subtype.coe_eta,
      Inter_univ, inter_univ, eq_self_iff_true, true_and_iff]
#align filter.mem_infi' Filter.mem_infᵢ'

/- warning: filter.exists_Inter_of_mem_infi -> Filter.exists_interᵢ_of_mem_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {f : ι -> (Filter.{u2} α)} {s : Set.{u2} α}, (Membership.Mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (Filter.hasMem.{u2} α) s (infᵢ.{u2, succ u1} (Filter.{u2} α) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} α) (Filter.completeLattice.{u2} α))) ι (fun (i : ι) => f i))) -> (Exists.{max (succ u1) (succ u2)} (ι -> (Set.{u2} α)) (fun (t : ι -> (Set.{u2} α)) => And (forall (i : ι), Membership.Mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (Filter.hasMem.{u2} α) (t i) (f i)) (Eq.{succ u2} (Set.{u2} α) s (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => t i)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {f : ι -> (Filter.{u1} α)} {s : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => f i))) -> (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u1} α)) (fun (t : ι -> (Set.{u1} α)) => And (forall (i : ι), Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (t i) (f i)) (Eq.{succ u1} (Set.{u1} α) s (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => t i)))))
Case conversion may be inaccurate. Consider using '#align filter.exists_Inter_of_mem_infi Filter.exists_interᵢ_of_mem_infᵢₓ'. -/
theorem exists_interᵢ_of_mem_infᵢ {ι : Type _} {α : Type _} {f : ι → Filter α} {s}
    (hs : s ∈ ⨅ i, f i) : ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i :=
  let ⟨I, If, V, hVs, hV', hVU, hVU'⟩ := mem_infᵢ'.1 hs
  ⟨V, hVs, hVU'⟩
#align filter.exists_Inter_of_mem_infi Filter.exists_interᵢ_of_mem_infᵢ

/- warning: filter.mem_infi_of_finite -> Filter.mem_infᵢ_of_finite is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {α : Type.{u2}} {f : ι -> (Filter.{u2} α)} (s : Set.{u2} α), Iff (Membership.Mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (Filter.hasMem.{u2} α) s (infᵢ.{u2, succ u1} (Filter.{u2} α) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} α) (Filter.completeLattice.{u2} α))) ι (fun (i : ι) => f i))) (Exists.{max (succ u1) (succ u2)} (ι -> (Set.{u2} α)) (fun (t : ι -> (Set.{u2} α)) => And (forall (i : ι), Membership.Mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (Filter.hasMem.{u2} α) (t i) (f i)) (Eq.{succ u2} (Set.{u2} α) s (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => t i)))))
but is expected to have type
  forall {ι : Type.{u2}} [_inst_1 : Finite.{succ u2} ι] {α : Type.{u1}} {f : ι -> (Filter.{u1} α)} (s : Set.{u1} α), Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => f i))) (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u1} α)) (fun (t : ι -> (Set.{u1} α)) => And (forall (i : ι), Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (t i) (f i)) (Eq.{succ u1} (Set.{u1} α) s (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => t i)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi_of_finite Filter.mem_infᵢ_of_finiteₓ'. -/
theorem mem_infᵢ_of_finite {ι : Type _} [Finite ι] {α : Type _} {f : ι → Filter α} (s) :
    (s ∈ ⨅ i, f i) ↔ ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i :=
  by
  refine' ⟨exists_Inter_of_mem_infi, _⟩
  rintro ⟨t, ht, rfl⟩
  exact Inter_mem.2 fun i => mem_infi_of_mem i (ht i)
#align filter.mem_infi_of_finite Filter.mem_infᵢ_of_finite

/- warning: filter.le_principal_iff -> Filter.le_principal_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {f : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (Filter.principal.{u1} α s)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {f : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (Filter.principal.{u1} α s)) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f)
Case conversion may be inaccurate. Consider using '#align filter.le_principal_iff Filter.le_principal_iffₓ'. -/
@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  show (∀ {t}, s ⊆ t → t ∈ f) ↔ s ∈ f from
    ⟨fun h => h (Subset.refl s), fun hs t ht => mem_of_superset hs ht⟩
#align filter.le_principal_iff Filter.le_principal_iff

/- warning: filter.Iic_principal -> Filter.Iic_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Filter.{u1} α)) (Set.Iic.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)) (Filter.principal.{u1} α s)) (setOf.{u1} (Filter.{u1} α) (fun (l : Filter.{u1} α) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Filter.{u1} α)) (Set.Iic.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α)) (Filter.principal.{u1} α s)) (setOf.{u1} (Filter.{u1} α) (fun (l : Filter.{u1} α) => Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l))
Case conversion may be inaccurate. Consider using '#align filter.Iic_principal Filter.Iic_principalₓ'. -/
theorem Iic_principal (s : Set α) : Iic (𝓟 s) = { l | s ∈ l } :=
  Set.ext fun x => le_principal_iff
#align filter.Iic_principal Filter.Iic_principal

/- warning: filter.principal_mono -> Filter.principal_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align filter.principal_mono Filter.principal_monoₓ'. -/
theorem principal_mono {s t : Set α} : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  simp only [le_principal_iff, iff_self_iff, mem_principal]
#align filter.principal_mono Filter.principal_mono

/- warning: filter.monotone_principal -> Filter.monotone_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Monotone.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)) (Filter.principal.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, Monotone.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α)) (Filter.principal.{u1} α)
Case conversion may be inaccurate. Consider using '#align filter.monotone_principal Filter.monotone_principalₓ'. -/
@[mono]
theorem monotone_principal : Monotone (𝓟 : Set α → Filter α) := fun _ _ => principal_mono.2
#align filter.monotone_principal Filter.monotone_principal

#print Filter.principal_eq_iff_eq /-
@[simp]
theorem principal_eq_iff_eq {s t : Set α} : 𝓟 s = 𝓟 t ↔ s = t := by
  simp only [le_antisymm_iff, le_principal_iff, mem_principal] <;> rfl
#align filter.principal_eq_iff_eq Filter.principal_eq_iff_eq
-/

/- warning: filter.join_principal_eq_Sup -> Filter.join_principal_eq_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (Filter.{u1} α)}, Eq.{succ u1} (Filter.{u1} α) (Filter.join.{u1} α (Filter.principal.{u1} (Filter.{u1} α) s)) (SupSet.supₛ.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (Filter.{u1} α)}, Eq.{succ u1} (Filter.{u1} α) (Filter.join.{u1} α (Filter.principal.{u1} (Filter.{u1} α) s)) (SupSet.supₛ.{u1} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) s)
Case conversion may be inaccurate. Consider using '#align filter.join_principal_eq_Sup Filter.join_principal_eq_supₛₓ'. -/
@[simp]
theorem join_principal_eq_supₛ {s : Set (Filter α)} : join (𝓟 s) = supₛ s :=
  rfl
#align filter.join_principal_eq_Sup Filter.join_principal_eq_supₛ

/- warning: filter.principal_univ -> Filter.principal_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Filter.{u1} α) (Filter.principal.{u1} α (Set.univ.{u1} α)) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Filter.{u1} α) (Filter.principal.{u1} α (Set.univ.{u1} α)) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))
Case conversion may be inaccurate. Consider using '#align filter.principal_univ Filter.principal_univₓ'. -/
@[simp]
theorem principal_univ : 𝓟 (univ : Set α) = ⊤ :=
  top_unique <| by simp only [le_principal_iff, mem_top, eq_self_iff_true]
#align filter.principal_univ Filter.principal_univ

/- warning: filter.principal_empty -> Filter.principal_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Filter.{u1} α) (Filter.principal.{u1} α (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Filter.{u1} α) (Filter.principal.{u1} α (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.principal_empty Filter.principal_emptyₓ'. -/
@[simp]
theorem principal_empty : 𝓟 (∅ : Set α) = ⊥ :=
  bot_unique fun s _ => empty_subset _
#align filter.principal_empty Filter.principal_empty

/- warning: filter.generate_eq_binfi -> Filter.generate_eq_binfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α S) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) => Filter.principal.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (Filter.generate.{u1} α S) (infᵢ.{u1, succ u1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s S) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s S) => Filter.principal.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align filter.generate_eq_binfi Filter.generate_eq_binfᵢₓ'. -/
theorem generate_eq_binfᵢ (S : Set (Set α)) : generate S = ⨅ s ∈ S, 𝓟 s :=
  eq_of_forall_le_iff fun f => by simp [sets_iff_generate, le_principal_iff, subset_def]
#align filter.generate_eq_binfi Filter.generate_eq_binfᵢ

/-! ### Lattice equations -/


/- warning: filter.empty_mem_iff_bot -> Filter.empty_mem_iff_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) f) (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) f) (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.empty_mem_iff_bot Filter.empty_mem_iff_botₓ'. -/
theorem empty_mem_iff_bot {f : Filter α} : ∅ ∈ f ↔ f = ⊥ :=
  ⟨fun h => bot_unique fun s _ => mem_of_superset h (empty_subset s), fun h => h.symm ▸ mem_bot⟩
#align filter.empty_mem_iff_bot Filter.empty_mem_iff_bot

#print Filter.nonempty_of_mem /-
theorem nonempty_of_mem {f : Filter α} [hf : NeBot f] {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun h => absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id
#align filter.nonempty_of_mem Filter.nonempty_of_mem
-/

#print Filter.NeBot.nonempty_of_mem /-
theorem NeBot.nonempty_of_mem {f : Filter α} (hf : NeBot f) {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  @nonempty_of_mem α f hf s hs
#align filter.ne_bot.nonempty_of_mem Filter.NeBot.nonempty_of_mem
-/

#print Filter.empty_not_mem /-
@[simp]
theorem empty_not_mem (f : Filter α) [NeBot f] : ¬∅ ∈ f := fun h => (nonempty_of_mem h).ne_empty rfl
#align filter.empty_not_mem Filter.empty_not_mem
-/

#print Filter.nonempty_of_neBot /-
theorem nonempty_of_neBot (f : Filter α) [NeBot f] : Nonempty α :=
  nonempty_of_exists <| nonempty_of_mem (univ_mem : univ ∈ f)
#align filter.nonempty_of_ne_bot Filter.nonempty_of_neBot
-/

/- warning: filter.compl_not_mem -> Filter.compl_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} [_inst_1 : Filter.NeBot.{u1} α f], (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Not (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} [_inst_1 : Filter.NeBot.{u1} α f], (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Not (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) f))
Case conversion may be inaccurate. Consider using '#align filter.compl_not_mem Filter.compl_not_memₓ'. -/
theorem compl_not_mem {f : Filter α} {s : Set α} [NeBot f] (h : s ∈ f) : sᶜ ∉ f := fun hsc =>
  (nonempty_of_mem (inter_mem h hsc)).ne_empty <| inter_compl_self s
#align filter.compl_not_mem Filter.compl_not_mem

/- warning: filter.filter_eq_bot_of_is_empty -> Filter.filter_eq_bot_of_isEmpty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IsEmpty.{succ u1} α] (f : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IsEmpty.{succ u1} α] (f : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.filter_eq_bot_of_is_empty Filter.filter_eq_bot_of_isEmptyₓ'. -/
theorem filter_eq_bot_of_isEmpty [IsEmpty α] (f : Filter α) : f = ⊥ :=
  empty_mem_iff_bot.mp <| univ_mem' isEmptyElim
#align filter.filter_eq_bot_of_is_empty Filter.filter_eq_bot_of_isEmpty

/- warning: filter.disjoint_iff -> Filter.disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) f g) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) => Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) f g) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t)))))
Case conversion may be inaccurate. Consider using '#align filter.disjoint_iff Filter.disjoint_iffₓ'. -/
protected theorem disjoint_iff {f g : Filter α} : Disjoint f g ↔ ∃ s ∈ f, ∃ t ∈ g, Disjoint s t :=
  by
  simp only [disjoint_iff, ← empty_mem_iff_bot, mem_inf_iff, inf_eq_inter, bot_eq_empty,
    @eq_comm _ ∅]
#align filter.disjoint_iff Filter.disjoint_iff

/- warning: filter.disjoint_of_disjoint_of_mem -> Filter.disjoint_of_disjoint_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) -> (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) f g)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) -> (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) f g)
Case conversion may be inaccurate. Consider using '#align filter.disjoint_of_disjoint_of_mem Filter.disjoint_of_disjoint_of_memₓ'. -/
theorem disjoint_of_disjoint_of_mem {f g : Filter α} {s t : Set α} (h : Disjoint s t) (hs : s ∈ f)
    (ht : t ∈ g) : Disjoint f g :=
  Filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩
#align filter.disjoint_of_disjoint_of_mem Filter.disjoint_of_disjoint_of_mem

/- warning: filter.ne_bot.not_disjoint -> Filter.NeBot.not_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.NeBot.{u1} α f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) -> (Not (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.NeBot.{u1} α f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) -> (Not (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t))
Case conversion may be inaccurate. Consider using '#align filter.ne_bot.not_disjoint Filter.NeBot.not_disjointₓ'. -/
theorem NeBot.not_disjoint (hf : f.ne_bot) (hs : s ∈ f) (ht : t ∈ f) : ¬Disjoint s t := fun h =>
  not_disjoint_self_iff.2 hf <| Filter.disjoint_iff.2 ⟨s, hs, t, ht, h⟩
#align filter.ne_bot.not_disjoint Filter.NeBot.not_disjoint

/- warning: filter.inf_eq_bot_iff -> Filter.inf_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U f) => Exists.{succ u1} (Set.{u1} α) (fun (V : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) V g) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) V g) => Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U V) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U f) (Exists.{succ u1} (Set.{u1} α) (fun (V : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) V g) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U V) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align filter.inf_eq_bot_iff Filter.inf_eq_bot_iffₓ'. -/
theorem inf_eq_bot_iff {f g : Filter α} : f ⊓ g = ⊥ ↔ ∃ U ∈ f, ∃ V ∈ g, U ∩ V = ∅ := by
  simpa only [← disjoint_iff, Set.disjoint_iff_inter_eq_empty] using Filter.disjoint_iff
#align filter.inf_eq_bot_iff Filter.inf_eq_bot_iff

/- warning: pairwise.exists_mem_filter_of_disjoint -> Pairwise.exists_mem_filter_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Finite.{succ u2} ι] {l : ι -> (Filter.{u1} α)}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Filter.{u1} α) Prop (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) l)) -> (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u1} α)) (fun (s : ι -> (Set.{u1} α)) => And (forall (i : ι), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (s i) (l i)) (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) s))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {l : ι -> (Filter.{u2} α)}, (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Filter.{u2} α) Prop (Disjoint.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)))) l)) -> (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u2} α)) (fun (s : ι -> (Set.{u2} α)) => And (forall (i : ι), Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (s i) (l i)) (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) s))))
Case conversion may be inaccurate. Consider using '#align pairwise.exists_mem_filter_of_disjoint Pairwise.exists_mem_filter_of_disjointₓ'. -/
theorem Pairwise.exists_mem_filter_of_disjoint {ι : Type _} [Finite ι] {l : ι → Filter α}
    (hd : Pairwise (Disjoint on l)) :
    ∃ s : ι → Set α, (∀ i, s i ∈ l i) ∧ Pairwise (Disjoint on s) :=
  by
  simp only [Pairwise, Function.onFun, Filter.disjoint_iff, Subtype.exists'] at hd
  choose! s t hst using hd
  refine' ⟨fun i => ⋂ j, @s i j ∩ @t j i, fun i => _, fun i j hij => _⟩
  exacts[Inter_mem.2 fun j => inter_mem (@s i j).2 (@t j i).2,
    (hst hij).mono ((Inter_subset _ j).trans (inter_subset_left _ _))
      ((Inter_subset _ i).trans (inter_subset_right _ _))]
#align pairwise.exists_mem_filter_of_disjoint Pairwise.exists_mem_filter_of_disjoint

/- warning: set.pairwise_disjoint.exists_mem_filter -> Set.PairwiseDisjoint.exists_mem_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {l : ι -> (Filter.{u1} α)} {t : Set.{u2} ι}, (Set.PairwiseDisjoint.{u1, u2} (Filter.{u1} α) ι (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) t l) -> (Set.Finite.{u2} ι t) -> (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u1} α)) (fun (s : ι -> (Set.{u1} α)) => And (forall (i : ι), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (s i) (l i)) (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t s)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {l : ι -> (Filter.{u2} α)} {t : Set.{u1} ι}, (Set.PairwiseDisjoint.{u2, u1} (Filter.{u2} α) ι (Filter.instPartialOrderFilter.{u2} α) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) t l) -> (Set.Finite.{u1} ι t) -> (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u2} α)) (fun (s : ι -> (Set.{u2} α)) => And (forall (i : ι), Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (s i) (l i)) (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) t s)))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.exists_mem_filter Set.PairwiseDisjoint.exists_mem_filterₓ'. -/
theorem Set.PairwiseDisjoint.exists_mem_filter {ι : Type _} {l : ι → Filter α} {t : Set ι}
    (hd : t.PairwiseDisjoint l) (ht : t.Finite) :
    ∃ s : ι → Set α, (∀ i, s i ∈ l i) ∧ t.PairwiseDisjoint s :=
  by
  cases ht
  obtain ⟨s, hd⟩ :
    ∃ s : ∀ i : t, { s : Set α // s ∈ l i }, Pairwise (Disjoint on fun i => (s i : Set α)) :=
    by
    rcases(hd.subtype _ _).exists_mem_filter_of_disjoint with ⟨s, hsl, hsd⟩
    exact ⟨fun i => ⟨s i, hsl i⟩, hsd⟩
  -- TODO: Lean fails to find `can_lift` instance and fails to use an instance supplied by `letI`
  rcases@Subtype.exists_pi_extension ι (fun i => { s // s ∈ l i }) _ _ s with ⟨s, rfl⟩
  exact ⟨fun i => s i, fun i => (s i).2, Pairwise.set_of_subtype _ _ hd⟩
#align set.pairwise_disjoint.exists_mem_filter Set.PairwiseDisjoint.exists_mem_filter

#print Filter.unique /-
/-- There is exactly one filter on an empty type. -/
instance unique [IsEmpty α] : Unique (Filter α)
    where
  toInhabited := Filter.inhabited
  uniq := filter_eq_bot_of_isEmpty
#align filter.unique Filter.unique
-/

/- warning: filter.eq_top_of_ne_bot -> Filter.eq_top_of_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Subsingleton.{succ u1} α] (l : Filter.{u1} α) [_inst_2 : Filter.NeBot.{u1} α l], Eq.{succ u1} (Filter.{u1} α) l (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Subsingleton.{succ u1} α] (l : Filter.{u1} α) [_inst_2 : Filter.NeBot.{u1} α l], Eq.{succ u1} (Filter.{u1} α) l (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))
Case conversion may be inaccurate. Consider using '#align filter.eq_top_of_ne_bot Filter.eq_top_of_neBotₓ'. -/
/-- There are only two filters on a `subsingleton`: `⊥` and `⊤`. If the type is empty, then they are
equal. -/
theorem eq_top_of_neBot [Subsingleton α] (l : Filter α) [NeBot l] : l = ⊤ :=
  by
  refine' top_unique fun s hs => _
  obtain rfl : s = univ; exact Subsingleton.eq_univ_of_nonempty (nonempty_of_mem hs)
  exact univ_mem
#align filter.eq_top_of_ne_bot Filter.eq_top_of_neBot

#print Filter.forall_mem_nonempty_iff_neBot /-
theorem forall_mem_nonempty_iff_neBot {f : Filter α} :
    (∀ s : Set α, s ∈ f → s.Nonempty) ↔ NeBot f :=
  ⟨fun h => ⟨fun hf => not_nonempty_empty (h ∅ <| hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩
#align filter.forall_mem_nonempty_iff_ne_bot Filter.forall_mem_nonempty_iff_neBot
-/

instance [Nonempty α] : Nontrivial (Filter α) :=
  ⟨⟨⊤, ⊥,
      NeBot.ne <|
        forall_mem_nonempty_iff_neBot.1 fun s hs => by
          rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]⟩⟩

#print Filter.nontrivial_iff_nonempty /-
theorem nontrivial_iff_nonempty : Nontrivial (Filter α) ↔ Nonempty α :=
  ⟨fun h =>
    by_contra fun h' =>
      haveI := not_nonempty_iff.1 h'
      not_subsingleton (Filter α) inferInstance,
    @Filter.nontrivial α⟩
#align filter.nontrivial_iff_nonempty Filter.nontrivial_iff_nonempty
-/

/- warning: filter.eq_Inf_of_mem_iff_exists_mem -> Filter.eq_infₛ_of_mem_iff_exists_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {S : Set.{u1} (Filter.{u1} α)} {l : Filter.{u1} α}, (forall {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) (Exists.{succ u1} (Filter.{u1} α) (fun (f : Filter.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) f S) (fun (H : Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) f S) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f)))) -> (Eq.{succ u1} (Filter.{u1} α) l (InfSet.infₛ.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) S))
but is expected to have type
  forall {α : Type.{u1}} {S : Set.{u1} (Filter.{u1} α)} {l : Filter.{u1} α}, (forall {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) (Exists.{succ u1} (Filter.{u1} α) (fun (f : Filter.{u1} α) => And (Membership.mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.instMembershipSet.{u1} (Filter.{u1} α)) f S) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f)))) -> (Eq.{succ u1} (Filter.{u1} α) l (InfSet.infₛ.{u1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) S))
Case conversion may be inaccurate. Consider using '#align filter.eq_Inf_of_mem_iff_exists_mem Filter.eq_infₛ_of_mem_iff_exists_memₓ'. -/
theorem eq_infₛ_of_mem_iff_exists_mem {S : Set (Filter α)} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) : l = infₛ S :=
  le_antisymm (le_infₛ fun f hf s hs => h.2 ⟨f, hf, hs⟩) fun s hs =>
    let ⟨f, hf, hs⟩ := h.1 hs
    (infₛ_le hf : infₛ S ≤ f) hs
#align filter.eq_Inf_of_mem_iff_exists_mem Filter.eq_infₛ_of_mem_iff_exists_mem

/- warning: filter.eq_infi_of_mem_iff_exists_mem -> Filter.eq_infᵢ_of_mem_iff_exists_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} {l : Filter.{u1} α}, (forall {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) (Exists.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (f i)))) -> (Eq.{succ u1} (Filter.{u1} α) l (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} {l : Filter.{u1} α}, (forall {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) (Exists.{u2} ι (fun (i : ι) => Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (f i)))) -> (Eq.{succ u1} (Filter.{u1} α) l (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f))
Case conversion may be inaccurate. Consider using '#align filter.eq_infi_of_mem_iff_exists_mem Filter.eq_infᵢ_of_mem_iff_exists_memₓ'. -/
theorem eq_infᵢ_of_mem_iff_exists_mem {f : ι → Filter α} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ i, s ∈ f i) : l = infᵢ f :=
  eq_infₛ_of_mem_iff_exists_mem fun s => h.trans exists_range_iff.symm
#align filter.eq_infi_of_mem_iff_exists_mem Filter.eq_infᵢ_of_mem_iff_exists_mem

theorem eq_binfᵢ_of_mem_iff_exists_mem {f : ι → Filter α} {p : ι → Prop} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ (i : _)(_ : p i), s ∈ f i) : l = ⨅ (i) (_ : p i), f i :=
  by
  rw [infᵢ_subtype']
  apply eq_infi_of_mem_iff_exists_mem
  intro s
  exact h.trans ⟨fun ⟨i, pi, si⟩ => ⟨⟨i, pi⟩, si⟩, fun ⟨⟨i, pi⟩, si⟩ => ⟨i, pi, si⟩⟩
#align filter.eq_binfi_of_mem_iff_exists_mem Filter.eq_binfᵢ_of_mem_iff_exists_memₓ

/- warning: filter.infi_sets_eq -> Filter.infᵢ_sets_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)}, (Directed.{u1, u2} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) f) -> (forall [ne : Nonempty.{u2} ι], Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (Set.unionᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => Filter.sets.{u1} α (f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)}, (Directed.{u1, u2} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Basic._hyg.10324 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.10326 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.10324 x._@.Mathlib.Order.Filter.Basic._hyg.10326) f) -> (forall [ne : Nonempty.{u2} ι], Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (Set.unionᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => Filter.sets.{u1} α (f i))))
Case conversion may be inaccurate. Consider using '#align filter.infi_sets_eq Filter.infᵢ_sets_eqₓ'. -/
theorem infᵢ_sets_eq {f : ι → Filter α} (h : Directed (· ≥ ·) f) [ne : Nonempty ι] :
    (infᵢ f).sets = ⋃ i, (f i).sets :=
  let ⟨i⟩ := Ne
  let u :=
    { sets := ⋃ i, (f i).sets
      univ_sets := by simp only [mem_Union] <;> exact ⟨i, univ_mem⟩
      sets_of_superset := by
        simp only [mem_Union, exists_imp] <;> intro x y i hx hxy <;>
          exact ⟨i, mem_of_superset hx hxy⟩
      inter_sets := by
        simp only [mem_Union, exists_imp]
        intro x y a hx b hy
        rcases h a b with ⟨c, ha, hb⟩
        exact ⟨c, inter_mem (ha hx) (hb hy)⟩ }
  have : u = infᵢ f :=
    eq_infᵢ_of_mem_iff_exists_mem fun s => by simp only [Filter.mem_mk, mem_Union, Filter.mem_sets]
  congr_arg Filter.sets this.symm
#align filter.infi_sets_eq Filter.infᵢ_sets_eq

/- warning: filter.mem_infi_of_directed -> Filter.mem_infᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)}, (Directed.{u1, u2} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) f) -> (forall [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} α), Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (Exists.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)}, (Directed.{u1, u2} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Basic._hyg.10519 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.10521 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.10519 x._@.Mathlib.Order.Filter.Basic._hyg.10521) f) -> (forall [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} α), Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (Exists.{u2} ι (fun (i : ι) => Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (f i))))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi_of_directed Filter.mem_infᵢ_of_directedₓ'. -/
theorem mem_infᵢ_of_directed {f : ι → Filter α} (h : Directed (· ≥ ·) f) [Nonempty ι] (s) :
    s ∈ infᵢ f ↔ ∃ i, s ∈ f i := by simp only [← Filter.mem_sets, infi_sets_eq h, mem_Union]
#align filter.mem_infi_of_directed Filter.mem_infᵢ_of_directed

/- warning: filter.mem_binfi_of_directed -> Filter.mem_binfᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : β -> (Filter.{u1} α)} {s : Set.{u2} β}, (DirectedOn.{u2} β (Order.Preimage.{succ u2, succ u1} β (Filter.{u1} α) f (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))))) s) -> (Set.Nonempty.{u2} β s) -> (forall {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) β (fun (i : β) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) => f i)))) (Exists.{succ u2} β (fun (i : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : β -> (Filter.{u1} α)} {s : Set.{u2} β}, (DirectedOn.{u2} β (Order.Preimage.{succ u2, succ u1} β (Filter.{u1} α) f (fun (x._@.Mathlib.Order.Filter.Basic._hyg.10594 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.10596 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.10594 x._@.Mathlib.Order.Filter.Basic._hyg.10596)) s) -> (Set.Nonempty.{u2} β s) -> (forall {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) β (fun (i : β) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) => f i)))) (Exists.{succ u2} β (fun (i : β) => And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (f i)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_binfi_of_directed Filter.mem_binfᵢ_of_directedₓ'. -/
theorem mem_binfᵢ_of_directed {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s)
    (ne : s.Nonempty) {t : Set α} : (t ∈ ⨅ i ∈ s, f i) ↔ ∃ i ∈ s, t ∈ f i := by
  haveI : Nonempty { x // x ∈ s } := ne.to_subtype <;>
      erw [infᵢ_subtype', mem_infi_of_directed h.directed_coe, Subtype.exists] <;>
    rfl
#align filter.mem_binfi_of_directed Filter.mem_binfᵢ_of_directed

/- warning: filter.binfi_sets_eq -> Filter.binfᵢ_sets_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : β -> (Filter.{u1} α)} {s : Set.{u2} β}, (DirectedOn.{u2} β (Order.Preimage.{succ u2, succ u1} β (Filter.{u1} α) f (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))))) s) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) β (fun (i : β) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) => f i)))) (Set.unionᵢ.{u1, succ u2} (Set.{u1} α) β (fun (i : β) => Set.unionᵢ.{u1, 0} (Set.{u1} α) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) => Filter.sets.{u1} α (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : β -> (Filter.{u1} α)} {s : Set.{u2} β}, (DirectedOn.{u2} β (Order.Preimage.{succ u2, succ u1} β (Filter.{u1} α) f (fun (x._@.Mathlib.Order.Filter.Basic._hyg.10737 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.10739 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.10737 x._@.Mathlib.Order.Filter.Basic._hyg.10739)) s) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) β (fun (i : β) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) => f i)))) (Set.unionᵢ.{u1, succ u2} (Set.{u1} α) β (fun (i : β) => Set.unionᵢ.{u1, 0} (Set.{u1} α) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) => Filter.sets.{u1} α (f i)))))
Case conversion may be inaccurate. Consider using '#align filter.binfi_sets_eq Filter.binfᵢ_sets_eqₓ'. -/
theorem binfᵢ_sets_eq {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s)
    (ne : s.Nonempty) : (⨅ i ∈ s, f i).sets = ⋃ i ∈ s, (f i).sets :=
  ext fun t => by simp [mem_binfi_of_directed h Ne]
#align filter.binfi_sets_eq Filter.binfᵢ_sets_eq

/- warning: filter.infi_sets_eq_finite -> Filter.infᵢ_sets_eq_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (f : ι -> (Filter.{u1} α)), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => f i))) (Set.unionᵢ.{u1, succ u2} (Set.{u1} α) (Finset.{u2} ι) (fun (t : Finset.{u2} ι) => Filter.sets.{u1} α (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (f : ι -> (Filter.{u2} α)), Eq.{succ u2} (Set.{u2} (Set.{u2} α)) (Filter.sets.{u2} α (infᵢ.{u2, succ u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => f i))) (Set.unionᵢ.{u2, succ u1} (Set.{u2} α) (Finset.{u1} ι) (fun (t : Finset.{u1} ι) => Filter.sets.{u2} α (infᵢ.{u2, succ u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => infᵢ.{u2, 0} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align filter.infi_sets_eq_finite Filter.infᵢ_sets_eq_finiteₓ'. -/
theorem infᵢ_sets_eq_finite {ι : Type _} (f : ι → Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset ι, (⨅ i ∈ t, f i).sets :=
  by
  rw [infᵢ_eq_infᵢ_finset, infi_sets_eq]
  exact directed_of_sup fun s₁ s₂ => binfᵢ_mono
#align filter.infi_sets_eq_finite Filter.infᵢ_sets_eq_finite

/- warning: filter.infi_sets_eq_finite' -> Filter.infᵢ_sets_eq_finite' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Filter.{u1} α)), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => f i))) (Set.unionᵢ.{u1, succ u2} (Set.{u1} α) (Finset.{u2} (PLift.{u2} ι)) (fun (t : Finset.{u2} (PLift.{u2} ι)) => Filter.sets.{u1} α (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} (PLift.{u2} ι) (Finset.{u2} (PLift.{u2} ι)) (Finset.hasMem.{u2} (PLift.{u2} ι)) i t) (fun (H : Membership.Mem.{u2, u2} (PLift.{u2} ι) (Finset.{u2} (PLift.{u2} ι)) (Finset.hasMem.{u2} (PLift.{u2} ι)) i t) => f (PLift.down.{u2} ι i))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Filter.{u1} α)), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Filter.sets.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => f i))) (Set.unionᵢ.{u1, succ u2} (Set.{u1} α) (Finset.{u2} (PLift.{u2} ι)) (fun (t : Finset.{u2} (PLift.{u2} ι)) => Filter.sets.{u1} α (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u2, u2} (PLift.{u2} ι) (Finset.{u2} (PLift.{u2} ι)) (Finset.instMembershipFinset.{u2} (PLift.{u2} ι)) i t) (fun (H : Membership.mem.{u2, u2} (PLift.{u2} ι) (Finset.{u2} (PLift.{u2} ι)) (Finset.instMembershipFinset.{u2} (PLift.{u2} ι)) i t) => f (PLift.down.{u2} ι i))))))
Case conversion may be inaccurate. Consider using '#align filter.infi_sets_eq_finite' Filter.infᵢ_sets_eq_finite'ₓ'. -/
theorem infᵢ_sets_eq_finite' (f : ι → Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset (PLift ι), (⨅ i ∈ t, f (PLift.down i)).sets :=
  by
  rw [← infi_sets_eq_finite, ← equiv.plift.surjective.infi_comp]
  rfl
#align filter.infi_sets_eq_finite' Filter.infᵢ_sets_eq_finite'

/- warning: filter.mem_infi_finite -> Filter.mem_infᵢ_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Filter.{u1} α)} (s : Set.{u1} α), Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (Exists.{succ u2} (Finset.{u2} ι) (fun (t : Finset.{u2} ι) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {f : ι -> (Filter.{u2} α)} (s : Set.{u2} α), Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (infᵢ.{u2, succ u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι f)) (Exists.{succ u1} (Finset.{u1} ι) (fun (t : Finset.{u1} ι) => Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (infᵢ.{u2, succ u1} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => infᵢ.{u2, 0} (Filter.{u2} α) (CompleteLattice.toInfSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi_finite Filter.mem_infᵢ_finiteₓ'. -/
theorem mem_infᵢ_finite {ι : Type _} {f : ι → Filter α} (s) :
    s ∈ infᵢ f ↔ ∃ t : Finset ι, s ∈ ⨅ i ∈ t, f i :=
  (Set.ext_iff.1 (infᵢ_sets_eq_finite f) s).trans mem_unionᵢ
#align filter.mem_infi_finite Filter.mem_infᵢ_finite

/- warning: filter.mem_infi_finite' -> Filter.mem_infᵢ_finite' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} (s : Set.{u1} α), Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (Exists.{succ u2} (Finset.{u2} (PLift.{u2} ι)) (fun (t : Finset.{u2} (PLift.{u2} ι)) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} (PLift.{u2} ι) (Finset.{u2} (PLift.{u2} ι)) (Finset.hasMem.{u2} (PLift.{u2} ι)) i t) (fun (H : Membership.Mem.{u2, u2} (PLift.{u2} ι) (Finset.{u2} (PLift.{u2} ι)) (Finset.hasMem.{u2} (PLift.{u2} ι)) i t) => f (PLift.down.{u2} ι i))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} (s : Set.{u1} α), Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (Exists.{succ u2} (Finset.{u2} (PLift.{u2} ι)) (fun (t : Finset.{u2} (PLift.{u2} ι)) => Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u2, u2} (PLift.{u2} ι) (Finset.{u2} (PLift.{u2} ι)) (Finset.instMembershipFinset.{u2} (PLift.{u2} ι)) i t) (fun (H : Membership.mem.{u2, u2} (PLift.{u2} ι) (Finset.{u2} (PLift.{u2} ι)) (Finset.instMembershipFinset.{u2} (PLift.{u2} ι)) i t) => f (PLift.down.{u2} ι i))))))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi_finite' Filter.mem_infᵢ_finite'ₓ'. -/
theorem mem_infᵢ_finite' {f : ι → Filter α} (s) :
    s ∈ infᵢ f ↔ ∃ t : Finset (PLift ι), s ∈ ⨅ i ∈ t, f (PLift.down i) :=
  (Set.ext_iff.1 (infᵢ_sets_eq_finite' f) s).trans mem_unionᵢ
#align filter.mem_infi_finite' Filter.mem_infᵢ_finite'

/- warning: filter.sup_join -> Filter.sup_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f₁ : Filter.{u1} (Filter.{u1} α)} {f₂ : Filter.{u1} (Filter.{u1} α)}, Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (Filter.join.{u1} α f₁) (Filter.join.{u1} α f₂)) (Filter.join.{u1} α (HasSup.sup.{u1} (Filter.{u1} (Filter.{u1} α)) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} (Filter.{u1} α)) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} (Filter.{u1} α)) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} (Filter.{u1} α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Filter.{u1} α)) (Filter.completeLattice.{u1} (Filter.{u1} α)))))) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {f₁ : Filter.{u1} (Filter.{u1} α)} {f₂ : Filter.{u1} (Filter.{u1} α)}, Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Filter.join.{u1} α f₁) (Filter.join.{u1} α f₂)) (Filter.join.{u1} α (HasSup.sup.{u1} (Filter.{u1} (Filter.{u1} α)) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} (Filter.{u1} α)) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} (Filter.{u1} α)) (CompleteLattice.toLattice.{u1} (Filter.{u1} (Filter.{u1} α)) (Filter.instCompleteLatticeFilter.{u1} (Filter.{u1} α))))) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align filter.sup_join Filter.sup_joinₓ'. -/
@[simp]
theorem sup_join {f₁ f₂ : Filter (Filter α)} : join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂) :=
  Filter.ext fun x => by simp only [mem_sup, mem_join]
#align filter.sup_join Filter.sup_join

/- warning: filter.supr_join -> Filter.supᵢ_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} (Filter.{u1} α))}, Eq.{succ u1} (Filter.{u1} α) (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (x : ι) => Filter.join.{u1} α (f x))) (Filter.join.{u1} α (supᵢ.{u1, u2} (Filter.{u1} (Filter.{u1} α)) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} (Filter.{u1} α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Filter.{u1} α)) (Filter.completeLattice.{u1} (Filter.{u1} α)))) ι (fun (x : ι) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} (Filter.{u1} α))}, Eq.{succ u1} (Filter.{u1} α) (supᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (x : ι) => Filter.join.{u1} α (f x))) (Filter.join.{u1} α (supᵢ.{u1, u2} (Filter.{u1} (Filter.{u1} α)) (CompleteLattice.toSupSet.{u1} (Filter.{u1} (Filter.{u1} α)) (Filter.instCompleteLatticeFilter.{u1} (Filter.{u1} α))) ι (fun (x : ι) => f x)))
Case conversion may be inaccurate. Consider using '#align filter.supr_join Filter.supᵢ_joinₓ'. -/
@[simp]
theorem supᵢ_join {ι : Sort w} {f : ι → Filter (Filter α)} : (⨆ x, join (f x)) = join (⨆ x, f x) :=
  Filter.ext fun x => by simp only [mem_supr, mem_join]
#align filter.supr_join Filter.supᵢ_join

instance : DistribLattice (Filter α) :=
  { Filter.completeLattice with
    le_sup_inf := by
      intro x y z s
      simp only [and_assoc', mem_inf_iff, mem_sup, exists_prop, exists_imp, and_imp]
      rintro hs t₁ ht₁ t₂ ht₂ rfl
      exact
        ⟨t₁, x.sets_of_superset hs (inter_subset_left t₁ t₂), ht₁, t₂,
          x.sets_of_superset hs (inter_subset_right t₁ t₂), ht₂, rfl⟩ }

-- The dual version does not hold! `filter α` is not a `complete_distrib_lattice`. -/
instance : Coframe (Filter α) :=
  { Filter.completeLattice with
    infₛ := infₛ
    infᵢ_sup_le_sup_inf := fun f s =>
      by
      rw [infₛ_eq_infᵢ', infᵢ_subtype']
      rintro t ⟨h₁, h₂⟩
      rw [infi_sets_eq_finite'] at h₂
      simp only [mem_Union, (Finset.inf_eq_infᵢ _ _).symm] at h₂
      obtain ⟨u, hu⟩ := h₂
      suffices (⨅ i, f ⊔ ↑i) ≤ f ⊔ u.inf fun i => ↑i.down by exact this ⟨h₁, hu⟩
      refine' Finset.induction_on u (le_sup_of_le_right le_top) _
      rintro ⟨i⟩ u _ ih
      rw [Finset.inf_insert, sup_inf_left]
      exact le_inf (infᵢ_le _ _) ih }

/- warning: filter.mem_infi_finset -> Filter.mem_infᵢ_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {f : α -> (Filter.{u2} β)} {t : Set.{u2} β}, Iff (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (infᵢ.{u2, succ u1} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) α (fun (a : α) => infᵢ.{u2, 0} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => f a)))) (Exists.{max (succ u1) (succ u2)} (α -> (Set.{u2} β)) (fun (p : α -> (Set.{u2} β)) => And (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (p a) (f a))) (Eq.{succ u2} (Set.{u2} β) t (Set.interᵢ.{u2, succ u1} β α (fun (a : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => p a))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {f : α -> (Filter.{u2} β)} {t : Set.{u2} β}, Iff (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) t (infᵢ.{u2, succ u1} (Filter.{u2} β) (CompleteLattice.toInfSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) α (fun (a : α) => infᵢ.{u2, 0} (Filter.{u2} β) (CompleteLattice.toInfSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) => f a)))) (Exists.{max (succ u1) (succ u2)} (α -> (Set.{u2} β)) (fun (p : α -> (Set.{u2} β)) => And (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (p a) (f a))) (Eq.{succ u2} (Set.{u2} β) t (Set.interᵢ.{u2, succ u1} β α (fun (a : α) => Set.interᵢ.{u2, 0} β (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) => p a))))))
Case conversion may be inaccurate. Consider using '#align filter.mem_infi_finset Filter.mem_infᵢ_finsetₓ'. -/
theorem mem_infᵢ_finset {s : Finset α} {f : α → Filter β} {t : Set β} :
    (t ∈ ⨅ a ∈ s, f a) ↔ ∃ p : α → Set β, (∀ a ∈ s, p a ∈ f a) ∧ t = ⋂ a ∈ s, p a :=
  by
  simp only [← Finset.set_binterᵢ_coe, bInter_eq_Inter, infᵢ_subtype']
  refine' ⟨fun h => _, _⟩
  · rcases(mem_infi_of_finite _).1 h with ⟨p, hp, rfl⟩
    refine'
      ⟨fun a => if h : a ∈ s then p ⟨a, h⟩ else univ, fun a ha => by simpa [ha] using hp ⟨a, ha⟩, _⟩
    refine' Inter_congr_of_surjective id surjective_id _
    rintro ⟨a, ha⟩
    simp [ha]
  · rintro ⟨p, hpf, rfl⟩
    exact Inter_mem.2 fun a => mem_infi_of_mem a (hpf a a.2)
#align filter.mem_infi_finset Filter.mem_infᵢ_finset

/- warning: filter.infi_ne_bot_of_directed' -> Filter.infᵢ_neBot_of_directed' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} [_inst_1 : Nonempty.{u2} ι], (Directed.{u1, u2} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) f) -> (forall (i : ι), Filter.NeBot.{u1} α (f i)) -> (Filter.NeBot.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} [_inst_1 : Nonempty.{u2} ι], (Directed.{u1, u2} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Basic._hyg.11996 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.11998 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.11996 x._@.Mathlib.Order.Filter.Basic._hyg.11998) f) -> (forall (i : ι), Filter.NeBot.{u1} α (f i)) -> (Filter.NeBot.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f))
Case conversion may be inaccurate. Consider using '#align filter.infi_ne_bot_of_directed' Filter.infᵢ_neBot_of_directed'ₓ'. -/
/-- If `f : ι → filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed` for a version assuming `nonempty α` instead of `nonempty ι`. -/
theorem infᵢ_neBot_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f)
    (hb : ∀ i, NeBot (f i)) : NeBot (infᵢ f) :=
  ⟨by
    intro h
    have he : ∅ ∈ infᵢ f := h.symm ▸ (mem_bot : ∅ ∈ (⊥ : Filter α))
    obtain ⟨i, hi⟩ : ∃ i, ∅ ∈ f i
    exact (mem_infi_of_directed hd ∅).1 he
    exact (hb i).Ne (empty_mem_iff_bot.1 hi)⟩
#align filter.infi_ne_bot_of_directed' Filter.infᵢ_neBot_of_directed'

/- warning: filter.infi_ne_bot_of_directed -> Filter.infᵢ_neBot_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} [hn : Nonempty.{succ u1} α], (Directed.{u1, u2} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) f) -> (forall (i : ι), Filter.NeBot.{u1} α (f i)) -> (Filter.NeBot.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} [hn : Nonempty.{succ u1} α], (Directed.{u1, u2} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Basic._hyg.12063 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.12065 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.12063 x._@.Mathlib.Order.Filter.Basic._hyg.12065) f) -> (forall (i : ι), Filter.NeBot.{u1} α (f i)) -> (Filter.NeBot.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f))
Case conversion may be inaccurate. Consider using '#align filter.infi_ne_bot_of_directed Filter.infᵢ_neBot_of_directedₓ'. -/
/-- If `f : ι → filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed'` for a version assuming `nonempty ι` instead of `nonempty α`. -/
theorem infᵢ_neBot_of_directed {f : ι → Filter α} [hn : Nonempty α] (hd : Directed (· ≥ ·) f)
    (hb : ∀ i, NeBot (f i)) : NeBot (infᵢ f) :=
  by
  cases isEmpty_or_nonempty ι
  · constructor
    simp [infᵢ_of_empty f, top_ne_bot]
  · exact infi_ne_bot_of_directed' hd hb
#align filter.infi_ne_bot_of_directed Filter.infᵢ_neBot_of_directed

/- warning: filter.Inf_ne_bot_of_directed' -> Filter.infₛ_neBot_of_directed' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (Filter.{u1} α)}, (Set.Nonempty.{u1} (Filter.{u1} α) s) -> (DirectedOn.{u1} (Filter.{u1} α) (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) s) -> (Not (Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) s)) -> (Filter.NeBot.{u1} α (InfSet.infₛ.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (Filter.{u1} α)}, (Set.Nonempty.{u1} (Filter.{u1} α) s) -> (DirectedOn.{u1} (Filter.{u1} α) (fun (x._@.Mathlib.Order.Filter.Basic._hyg.12138 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.12140 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.12138 x._@.Mathlib.Order.Filter.Basic._hyg.12140) s) -> (Not (Membership.mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.instMembershipSet.{u1} (Filter.{u1} α)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) s)) -> (Filter.NeBot.{u1} α (InfSet.infₛ.{u1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align filter.Inf_ne_bot_of_directed' Filter.infₛ_neBot_of_directed'ₓ'. -/
theorem infₛ_neBot_of_directed' {s : Set (Filter α)} (hne : s.Nonempty) (hd : DirectedOn (· ≥ ·) s)
    (hbot : ⊥ ∉ s) : NeBot (infₛ s) :=
  (infₛ_eq_infᵢ' s).symm ▸
    @infᵢ_neBot_of_directed' _ _ _ hne.to_subtype hd.directed_val fun ⟨f, hf⟩ =>
      ⟨ne_of_mem_of_not_mem hf hbot⟩
#align filter.Inf_ne_bot_of_directed' Filter.infₛ_neBot_of_directed'

/- warning: filter.Inf_ne_bot_of_directed -> Filter.infₛ_neBot_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Nonempty.{succ u1} α] {s : Set.{u1} (Filter.{u1} α)}, (DirectedOn.{u1} (Filter.{u1} α) (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) s) -> (Not (Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) s)) -> (Filter.NeBot.{u1} α (InfSet.infₛ.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Nonempty.{succ u1} α] {s : Set.{u1} (Filter.{u1} α)}, (DirectedOn.{u1} (Filter.{u1} α) (fun (x._@.Mathlib.Order.Filter.Basic._hyg.12238 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.12240 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.12238 x._@.Mathlib.Order.Filter.Basic._hyg.12240) s) -> (Not (Membership.mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.instMembershipSet.{u1} (Filter.{u1} α)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) s)) -> (Filter.NeBot.{u1} α (InfSet.infₛ.{u1} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align filter.Inf_ne_bot_of_directed Filter.infₛ_neBot_of_directedₓ'. -/
theorem infₛ_neBot_of_directed [Nonempty α] {s : Set (Filter α)} (hd : DirectedOn (· ≥ ·) s)
    (hbot : ⊥ ∉ s) : NeBot (infₛ s) :=
  (infₛ_eq_infᵢ' s).symm ▸
    infᵢ_neBot_of_directed hd.directed_val fun ⟨f, hf⟩ => ⟨ne_of_mem_of_not_mem hf hbot⟩
#align filter.Inf_ne_bot_of_directed Filter.infₛ_neBot_of_directed

/- warning: filter.infi_ne_bot_iff_of_directed' -> Filter.infᵢ_neBot_iff_of_directed' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} [_inst_1 : Nonempty.{u2} ι], (Directed.{u1, u2} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) f) -> (Iff (Filter.NeBot.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (forall (i : ι), Filter.NeBot.{u1} α (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} [_inst_1 : Nonempty.{u2} ι], (Directed.{u1, u2} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Basic._hyg.12333 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.12335 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.12333 x._@.Mathlib.Order.Filter.Basic._hyg.12335) f) -> (Iff (Filter.NeBot.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (forall (i : ι), Filter.NeBot.{u1} α (f i)))
Case conversion may be inaccurate. Consider using '#align filter.infi_ne_bot_iff_of_directed' Filter.infᵢ_neBot_iff_of_directed'ₓ'. -/
theorem infᵢ_neBot_iff_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    NeBot (infᵢ f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (infᵢ_le _ i), infᵢ_neBot_of_directed' hd⟩
#align filter.infi_ne_bot_iff_of_directed' Filter.infᵢ_neBot_iff_of_directed'

/- warning: filter.infi_ne_bot_iff_of_directed -> Filter.infᵢ_neBot_iff_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} [_inst_1 : Nonempty.{succ u1} α], (Directed.{u1, u2} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) f) -> (Iff (Filter.NeBot.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (forall (i : ι), Filter.NeBot.{u1} α (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} [_inst_1 : Nonempty.{succ u1} α], (Directed.{u1, u2} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Basic._hyg.12402 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.12404 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.12402 x._@.Mathlib.Order.Filter.Basic._hyg.12404) f) -> (Iff (Filter.NeBot.{u1} α (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (forall (i : ι), Filter.NeBot.{u1} α (f i)))
Case conversion may be inaccurate. Consider using '#align filter.infi_ne_bot_iff_of_directed Filter.infᵢ_neBot_iff_of_directedₓ'. -/
theorem infᵢ_neBot_iff_of_directed {f : ι → Filter α} [Nonempty α] (hd : Directed (· ≥ ·) f) :
    NeBot (infᵢ f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (infᵢ_le _ i), infᵢ_neBot_of_directed hd⟩
#align filter.infi_ne_bot_iff_of_directed Filter.infᵢ_neBot_iff_of_directed

/- warning: filter.infi_sets_induct -> Filter.infᵢ_sets_induct is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (infᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) -> (forall {p : (Set.{u1} α) -> Prop}, (p (Set.univ.{u1} α)) -> (forall {i : ι} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s₁ (f i)) -> (p s₂) -> (p (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂))) -> (p s))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Filter.{u1} α)} {s : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (infᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) -> (forall {p : (Set.{u1} α) -> Prop}, (p (Set.univ.{u1} α)) -> (forall {i : ι} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s₁ (f i)) -> (p s₂) -> (p (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂))) -> (p s))
Case conversion may be inaccurate. Consider using '#align filter.infi_sets_induct Filter.infᵢ_sets_inductₓ'. -/
@[elab_as_elim]
theorem infᵢ_sets_induct {f : ι → Filter α} {s : Set α} (hs : s ∈ infᵢ f) {p : Set α → Prop}
    (uni : p univ) (ins : ∀ {i s₁ s₂}, s₁ ∈ f i → p s₂ → p (s₁ ∩ s₂)) : p s :=
  by
  rw [mem_infi_finite'] at hs
  simp only [← Finset.inf_eq_infᵢ] at hs
  rcases hs with ⟨is, his⟩
  revert s
  refine' Finset.induction_on is _ _
  · intro s hs
    rwa [mem_top.1 hs]
  · rintro ⟨i⟩ js his ih s hs
    rw [Finset.inf_insert, mem_inf_iff] at hs
    rcases hs with ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    exact ins hs₁ (ih hs₂)
#align filter.infi_sets_induct Filter.infᵢ_sets_induct

/-! #### `principal` equations -/


/- warning: filter.inf_principal -> Filter.inf_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t)) (Filter.principal.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t)) (Filter.principal.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align filter.inf_principal Filter.inf_principalₓ'. -/
@[simp]
theorem inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t) :=
  le_antisymm
    (by simp only [le_principal_iff, mem_inf_iff] <;> exact ⟨s, subset.rfl, t, subset.rfl, rfl⟩)
    (by simp [le_inf_iff, inter_subset_left, inter_subset_right])
#align filter.inf_principal Filter.inf_principal

/- warning: filter.sup_principal -> Filter.sup_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t)) (Filter.principal.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Filter.{u1} α) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Filter.principal.{u1} α s) (Filter.principal.{u1} α t)) (Filter.principal.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align filter.sup_principal Filter.sup_principalₓ'. -/
@[simp]
theorem sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t) :=
  Filter.ext fun u => by simp only [union_subset_iff, mem_sup, mem_principal]
#align filter.sup_principal Filter.sup_principal

/- warning: filter.supr_principal -> Filter.supᵢ_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Eq.{succ u1} (Filter.{u1} α) (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (x : ι) => Filter.principal.{u1} α (s x))) (Filter.principal.{u1} α (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Eq.{succ u1} (Filter.{u1} α) (supᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (x : ι) => Filter.principal.{u1} α (s x))) (Filter.principal.{u1} α (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)))
Case conversion may be inaccurate. Consider using '#align filter.supr_principal Filter.supᵢ_principalₓ'. -/
@[simp]
theorem supᵢ_principal {ι : Sort w} {s : ι → Set α} : (⨆ x, 𝓟 (s x)) = 𝓟 (⋃ i, s i) :=
  Filter.ext fun x => by simp only [mem_supr, mem_principal, Union_subset_iff]
#align filter.supr_principal Filter.supᵢ_principal

/- warning: filter.principal_eq_bot_iff -> Filter.principal_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (Filter.principal.{u1} α s) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (Filter.principal.{u1} α s) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.principal_eq_bot_iff Filter.principal_eq_bot_iffₓ'. -/
@[simp]
theorem principal_eq_bot_iff {s : Set α} : 𝓟 s = ⊥ ↔ s = ∅ :=
  empty_mem_iff_bot.symm.trans <| mem_principal.trans subset_empty_iff
#align filter.principal_eq_bot_iff Filter.principal_eq_bot_iff

#print Filter.principal_neBot_iff /-
@[simp]
theorem principal_neBot_iff {s : Set α} : NeBot (𝓟 s) ↔ s.Nonempty :=
  neBot_iff.trans <| (not_congr principal_eq_bot_iff).trans nonempty_iff_ne_empty.symm
#align filter.principal_ne_bot_iff Filter.principal_neBot_iff
-/

alias principal_ne_bot_iff ↔ _ _root_.set.nonempty.principal_ne_bot
#align set.nonempty.principal_ne_bot Set.Nonempty.principal_neBot

/- warning: filter.is_compl_principal -> Filter.isCompl_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), IsCompl.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)) (Filter.principal.{u1} α s) (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), IsCompl.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Filter.principal.{u1} α s) (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align filter.is_compl_principal Filter.isCompl_principalₓ'. -/
theorem isCompl_principal (s : Set α) : IsCompl (𝓟 s) (𝓟 (sᶜ)) :=
  IsCompl.of_eq (by rw [inf_principal, inter_compl_self, principal_empty]) <| by
    rw [sup_principal, union_compl_self, principal_univ]
#align filter.is_compl_principal Filter.isCompl_principal

/- warning: filter.mem_inf_principal' -> Filter.mem_inf_principal' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α t))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t) s) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α t))) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t) s) f)
Case conversion may be inaccurate. Consider using '#align filter.mem_inf_principal' Filter.mem_inf_principal'ₓ'. -/
theorem mem_inf_principal' {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ tᶜ ∪ s ∈ f := by
  simp only [← le_principal_iff, (is_compl_principal s).le_left_iff, disjoint_assoc, inf_principal,
    ← (is_compl_principal (t ∩ sᶜ)).le_right_iff, compl_inter, compl_compl]
#align filter.mem_inf_principal' Filter.mem_inf_principal'

/- warning: filter.mem_inf_principal -> Filter.mem_inf_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α t))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (setOf.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α t))) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (setOf.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) f)
Case conversion may be inaccurate. Consider using '#align filter.mem_inf_principal Filter.mem_inf_principalₓ'. -/
theorem mem_inf_principal {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ { x | x ∈ t → x ∈ s } ∈ f :=
  by
  simp only [mem_inf_principal', imp_iff_not_or]
  rfl
#align filter.mem_inf_principal Filter.mem_inf_principal

/- warning: filter.supr_inf_principal -> Filter.supᵢ_inf_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Filter.{u1} α)) (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (f i) (Filter.principal.{u1} α s))) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => f i)) (Filter.principal.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Filter.{u1} α)) (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (supᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (f i) (Filter.principal.{u1} α s))) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (supᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => f i)) (Filter.principal.{u1} α s))
Case conversion may be inaccurate. Consider using '#align filter.supr_inf_principal Filter.supᵢ_inf_principalₓ'. -/
theorem supᵢ_inf_principal (f : ι → Filter α) (s : Set α) : (⨆ i, f i ⊓ 𝓟 s) = (⨆ i, f i) ⊓ 𝓟 s :=
  by
  ext
  simp only [mem_supr, mem_inf_principal]
#align filter.supr_inf_principal Filter.supᵢ_inf_principal

/- warning: filter.inf_principal_eq_bot -> Filter.inf_principal_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α s)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α s)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) f)
Case conversion may be inaccurate. Consider using '#align filter.inf_principal_eq_bot Filter.inf_principal_eq_botₓ'. -/
theorem inf_principal_eq_bot {f : Filter α} {s : Set α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ ∈ f :=
  by
  rw [← empty_mem_iff_bot, mem_inf_principal]
  rfl
#align filter.inf_principal_eq_bot Filter.inf_principal_eq_bot

/- warning: filter.mem_of_eq_bot -> Filter.mem_of_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f)
Case conversion may be inaccurate. Consider using '#align filter.mem_of_eq_bot Filter.mem_of_eq_botₓ'. -/
theorem mem_of_eq_bot {f : Filter α} {s : Set α} (h : f ⊓ 𝓟 (sᶜ) = ⊥) : s ∈ f := by
  rwa [inf_principal_eq_bot, compl_compl] at h
#align filter.mem_of_eq_bot Filter.mem_of_eq_bot

/- warning: filter.diff_mem_inf_principal_compl -> Filter.diff_mem_inf_principal_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (forall (t : Set.{u1} α), Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (forall (t : Set.{u1} α), Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))))
Case conversion may be inaccurate. Consider using '#align filter.diff_mem_inf_principal_compl Filter.diff_mem_inf_principal_complₓ'. -/
theorem diff_mem_inf_principal_compl {f : Filter α} {s : Set α} (hs : s ∈ f) (t : Set α) :
    s \ t ∈ f ⊓ 𝓟 (tᶜ) :=
  inter_mem_inf hs <| mem_principal_self (tᶜ)
#align filter.diff_mem_inf_principal_compl Filter.diff_mem_inf_principal_compl

/- warning: filter.principal_le_iff -> Filter.principal_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {f : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.principal.{u1} α s) f) (forall (V : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) V f) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s V))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {f : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.principal.{u1} α s) f) (forall (V : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) V f) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s V))
Case conversion may be inaccurate. Consider using '#align filter.principal_le_iff Filter.principal_le_iffₓ'. -/
theorem principal_le_iff {s : Set α} {f : Filter α} : 𝓟 s ≤ f ↔ ∀ V ∈ f, s ⊆ V :=
  by
  change (∀ V, V ∈ f → V ∈ _) ↔ _
  simp_rw [mem_principal]
#align filter.principal_le_iff Filter.principal_le_iff

/- warning: filter.infi_principal_finset -> Filter.infᵢ_principal_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => Filter.principal.{u1} α (f i)))) (Filter.principal.{u1} α (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => Filter.principal.{u1} α (f i)))) (Filter.principal.{u1} α (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align filter.infi_principal_finset Filter.infᵢ_principal_finsetₓ'. -/
@[simp]
theorem infᵢ_principal_finset {ι : Type w} (s : Finset ι) (f : ι → Set α) :
    (⨅ i ∈ s, 𝓟 (f i)) = 𝓟 (⋂ i ∈ s, f i) :=
  by
  induction' s using Finset.induction_on with i s hi hs
  · simp
  · rw [Finset.infᵢ_insert, Finset.set_binterᵢ_insert, hs, inf_principal]
#align filter.infi_principal_finset Filter.infᵢ_principal_finset

/- warning: filter.infi_principal -> Filter.infᵢ_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Finite.{succ u2} ι] (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => Filter.principal.{u1} α (f i))) (Filter.principal.{u1} α (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Finite.{succ u2} ι] (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => Filter.principal.{u1} α (f i))) (Filter.principal.{u1} α (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align filter.infi_principal Filter.infᵢ_principalₓ'. -/
@[simp]
theorem infᵢ_principal {ι : Type w} [Finite ι] (f : ι → Set α) : (⨅ i, 𝓟 (f i)) = 𝓟 (⋂ i, f i) :=
  by
  cases nonempty_fintype ι
  simpa using infi_principal_finset Finset.univ f
#align filter.infi_principal Filter.infᵢ_principal

/- warning: filter.infi_principal_finite -> Filter.infᵢ_principal_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι}, (Set.Finite.{u2} ι s) -> (forall (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => Filter.principal.{u1} α (f i)))) (Filter.principal.{u1} α (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι}, (Set.Finite.{u2} ι s) -> (forall (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Filter.{u1} α) (infᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => Filter.principal.{u1} α (f i)))) (Filter.principal.{u1} α (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i)))))
Case conversion may be inaccurate. Consider using '#align filter.infi_principal_finite Filter.infᵢ_principal_finiteₓ'. -/
theorem infᵢ_principal_finite {ι : Type w} {s : Set ι} (hs : s.Finite) (f : ι → Set α) :
    (⨅ i ∈ s, 𝓟 (f i)) = 𝓟 (⋂ i ∈ s, f i) :=
  by
  lift s to Finset ι using hs
  exact_mod_cast infi_principal_finset s f
#align filter.infi_principal_finite Filter.infᵢ_principal_finite

end Lattice

/- warning: filter.join_mono -> Filter.join_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f₁ : Filter.{u1} (Filter.{u1} α)} {f₂ : Filter.{u1} (Filter.{u1} α)}, (LE.le.{u1} (Filter.{u1} (Filter.{u1} α)) (Preorder.toLE.{u1} (Filter.{u1} (Filter.{u1} α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Filter.{u1} α)) (Filter.partialOrder.{u1} (Filter.{u1} α)))) f₁ f₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.join.{u1} α f₁) (Filter.join.{u1} α f₂))
but is expected to have type
  forall {α : Type.{u1}} {f₁ : Filter.{u1} (Filter.{u1} α)} {f₂ : Filter.{u1} (Filter.{u1} α)}, (LE.le.{u1} (Filter.{u1} (Filter.{u1} α)) (Preorder.toLE.{u1} (Filter.{u1} (Filter.{u1} α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Filter.{u1} α)) (Filter.instPartialOrderFilter.{u1} (Filter.{u1} α)))) f₁ f₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.join.{u1} α f₁) (Filter.join.{u1} α f₂))
Case conversion may be inaccurate. Consider using '#align filter.join_mono Filter.join_monoₓ'. -/
@[mono]
theorem join_mono {f₁ f₂ : Filter (Filter α)} (h : f₁ ≤ f₂) : join f₁ ≤ join f₂ := fun s hs => h hs
#align filter.join_mono Filter.join_mono

/-! ### Eventually -/


#print Filter.Eventually /-
/-- `f.eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in at_top, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f
#align filter.eventually Filter.Eventually
-/

-- mathport name: «expr∀ᶠ in , »
notation3"∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r

#print Filter.eventually_iff /-
theorem eventually_iff {f : Filter α} {P : α → Prop} : (∀ᶠ x in f, P x) ↔ { x | P x } ∈ f :=
  Iff.rfl
#align filter.eventually_iff Filter.eventually_iff
-/

#print Filter.eventually_mem_set /-
@[simp]
theorem eventually_mem_set {s : Set α} {l : Filter α} : (∀ᶠ x in l, x ∈ s) ↔ s ∈ l :=
  Iff.rfl
#align filter.eventually_mem_set Filter.eventually_mem_set
-/

#print Filter.ext' /-
protected theorem ext' {f₁ f₂ : Filter α}
    (h : ∀ p : α → Prop, (∀ᶠ x in f₁, p x) ↔ ∀ᶠ x in f₂, p x) : f₁ = f₂ :=
  Filter.ext h
#align filter.ext' Filter.ext'
-/

/- warning: filter.eventually.filter_mono -> Filter.Eventually.filter_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f₁ f₂) -> (forall {p : α -> Prop}, (Filter.Eventually.{u1} α (fun (x : α) => p x) f₂) -> (Filter.Eventually.{u1} α (fun (x : α) => p x) f₁))
but is expected to have type
  forall {α : Type.{u1}} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f₁ f₂) -> (forall {p : α -> Prop}, (Filter.Eventually.{u1} α (fun (x : α) => p x) f₂) -> (Filter.Eventually.{u1} α (fun (x : α) => p x) f₁))
Case conversion may be inaccurate. Consider using '#align filter.eventually.filter_mono Filter.Eventually.filter_monoₓ'. -/
theorem Eventually.filter_mono {f₁ f₂ : Filter α} (h : f₁ ≤ f₂) {p : α → Prop}
    (hp : ∀ᶠ x in f₂, p x) : ∀ᶠ x in f₁, p x :=
  h hp
#align filter.eventually.filter_mono Filter.Eventually.filter_mono

#print Filter.eventually_of_mem /-
theorem eventually_of_mem {f : Filter α} {P : α → Prop} {U : Set α} (hU : U ∈ f)
    (h : ∀ x ∈ U, P x) : ∀ᶠ x in f, P x :=
  mem_of_superset hU h
#align filter.eventually_of_mem Filter.eventually_of_mem
-/

#print Filter.Eventually.and /-
protected theorem Eventually.and {p q : α → Prop} {f : Filter α} :
    f.Eventually p → f.Eventually q → ∀ᶠ x in f, p x ∧ q x :=
  inter_mem
#align filter.eventually.and Filter.Eventually.and
-/

#print Filter.eventually_true /-
@[simp]
theorem eventually_true (f : Filter α) : ∀ᶠ x in f, True :=
  univ_mem
#align filter.eventually_true Filter.eventually_true
-/

#print Filter.eventually_of_forall /-
theorem eventually_of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
  univ_mem' hp
#align filter.eventually_of_forall Filter.eventually_of_forall
-/

#print Filter.forall_eventually_of_eventually_forall /-
theorem forall_eventually_of_eventually_forall {f : Filter α} {p : α → β → Prop}
    (h : ∀ᶠ x in f, ∀ y, p x y) : ∀ y, ∀ᶠ x in f, p x y :=
  by
  intro y
  filter_upwards [h]
  tauto
#align filter.forall_eventually_of_eventually_forall Filter.forall_eventually_of_eventually_forall
-/

/- warning: filter.eventually_false_iff_eq_bot -> Filter.eventually_false_iff_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Filter.Eventually.{u1} α (fun (x : α) => False) f) (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α}, Iff (Filter.Eventually.{u1} α (fun (x : α) => False) f) (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.eventually_false_iff_eq_bot Filter.eventually_false_iff_eq_botₓ'. -/
@[simp]
theorem eventually_false_iff_eq_bot {f : Filter α} : (∀ᶠ x in f, False) ↔ f = ⊥ :=
  empty_mem_iff_bot
#align filter.eventually_false_iff_eq_bot Filter.eventually_false_iff_eq_bot

#print Filter.eventually_const /-
@[simp]
theorem eventually_const {f : Filter α} [t : NeBot f] {p : Prop} : (∀ᶠ x in f, p) ↔ p :=
  by_cases (fun h : p => by simp [h]) fun h => by simpa [h] using t.ne
#align filter.eventually_const Filter.eventually_const
-/

/- warning: filter.eventually_iff_exists_mem -> Filter.eventually_iff_exists_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) f) (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) v f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) v f) => forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y v) -> (p y))))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) f) (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) v f) (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y v) -> (p y))))
Case conversion may be inaccurate. Consider using '#align filter.eventually_iff_exists_mem Filter.eventually_iff_exists_memₓ'. -/
theorem eventually_iff_exists_mem {p : α → Prop} {f : Filter α} :
    (∀ᶠ x in f, p x) ↔ ∃ v ∈ f, ∀ y ∈ v, p y :=
  exists_mem_subset_iff.symm
#align filter.eventually_iff_exists_mem Filter.eventually_iff_exists_mem

/- warning: filter.eventually.exists_mem -> Filter.Eventually.exists_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (x : α) => p x) f) -> (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) v f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) v f) => forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y v) -> (p y))))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (x : α) => p x) f) -> (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) v f) (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y v) -> (p y))))
Case conversion may be inaccurate. Consider using '#align filter.eventually.exists_mem Filter.Eventually.exists_memₓ'. -/
theorem Eventually.exists_mem {p : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x) :
    ∃ v ∈ f, ∀ y ∈ v, p y :=
  eventually_iff_exists_mem.1 hp
#align filter.eventually.exists_mem Filter.Eventually.exists_mem

#print Filter.Eventually.mp /-
theorem Eventually.mp {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∀ᶠ x in f, p x → q x) : ∀ᶠ x in f, q x :=
  mp_mem hp hq
#align filter.eventually.mp Filter.Eventually.mp
-/

#print Filter.Eventually.mono /-
theorem Eventually.mono {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∀ x, p x → q x) : ∀ᶠ x in f, q x :=
  hp.mp (eventually_of_forall hq)
#align filter.eventually.mono Filter.Eventually.mono
-/

#print Filter.eventually_and /-
@[simp]
theorem eventually_and {p q : α → Prop} {f : Filter α} :
    (∀ᶠ x in f, p x ∧ q x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in f, q x :=
  inter_mem_iff
#align filter.eventually_and Filter.eventually_and
-/

#print Filter.Eventually.congr /-
theorem Eventually.congr {f : Filter α} {p q : α → Prop} (h' : ∀ᶠ x in f, p x)
    (h : ∀ᶠ x in f, p x ↔ q x) : ∀ᶠ x in f, q x :=
  h'.mp (h.mono fun x hx => hx.mp)
#align filter.eventually.congr Filter.Eventually.congr
-/

#print Filter.eventually_congr /-
theorem eventually_congr {f : Filter α} {p q : α → Prop} (h : ∀ᶠ x in f, p x ↔ q x) :
    (∀ᶠ x in f, p x) ↔ ∀ᶠ x in f, q x :=
  ⟨fun hp => hp.congr h, fun hq => hq.congr <| by simpa only [Iff.comm] using h⟩
#align filter.eventually_congr Filter.eventually_congr
-/

/- warning: filter.eventually_all -> Filter.eventually_all is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Finite.{succ u2} ι] {l : Filter.{u1} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => forall (i : ι), p i x) l) (forall (i : ι), Filter.Eventually.{u1} α (fun (x : α) => p i x) l)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {l : Filter.{u2} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u2} α (fun (x : α) => forall (i : ι), p i x) l) (forall (i : ι), Filter.Eventually.{u2} α (fun (x : α) => p i x) l)
Case conversion may be inaccurate. Consider using '#align filter.eventually_all Filter.eventually_allₓ'. -/
@[simp]
theorem eventually_all {ι : Type _} [Finite ι] {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x :=
  by
  cases nonempty_fintype ι
  simpa only [Filter.Eventually, set_of_forall] using Inter_mem
#align filter.eventually_all Filter.eventually_all

/- warning: filter.eventually_all_finite -> Filter.eventually_all_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {I : Set.{u2} ι}, (Set.Finite.{u2} ι I) -> (forall {l : Filter.{u1} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) -> (p i x)) l) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) -> (Filter.Eventually.{u1} α (fun (x : α) => p i x) l)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {I : Set.{u1} ι}, (Set.Finite.{u1} ι I) -> (forall {l : Filter.{u2} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u2} α (fun (x : α) => forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) -> (p i x)) l) (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) -> (Filter.Eventually.{u2} α (fun (x : α) => p i x) l)))
Case conversion may be inaccurate. Consider using '#align filter.eventually_all_finite Filter.eventually_all_finiteₓ'. -/
@[simp]
theorem eventually_all_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, set_of_forall] using bInter_mem hI
#align filter.eventually_all_finite Filter.eventually_all_finite

/- warning: set.finite.eventually_all -> Set.Finite.eventually_all is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {I : Set.{u2} ι}, (Set.Finite.{u2} ι I) -> (forall {l : Filter.{u1} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) -> (p i x)) l) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) -> (Filter.Eventually.{u1} α (fun (x : α) => p i x) l)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {I : Set.{u1} ι}, (Set.Finite.{u1} ι I) -> (forall {l : Filter.{u2} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u2} α (fun (x : α) => forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) -> (p i x)) l) (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) -> (Filter.Eventually.{u2} α (fun (x : α) => p i x) l)))
Case conversion may be inaccurate. Consider using '#align set.finite.eventually_all Set.Finite.eventually_allₓ'. -/
alias eventually_all_finite ← _root_.set.finite.eventually_all
#align set.finite.eventually_all Set.Finite.eventually_all

attribute [protected] Set.Finite.eventually_all

/- warning: filter.eventually_all_finset -> Filter.eventually_all_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (I : Finset.{u2} ι) {l : Filter.{u1} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i I) -> (p i x)) l) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i I) -> (Filter.Eventually.{u1} α (fun (x : α) => p i x) l))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (I : Finset.{u1} ι) {l : Filter.{u2} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u2} α (fun (x : α) => forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i I) -> (p i x)) l) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i I) -> (Filter.Eventually.{u2} α (fun (x : α) => p i x) l))
Case conversion may be inaccurate. Consider using '#align filter.eventually_all_finset Filter.eventually_all_finsetₓ'. -/
@[simp]
theorem eventually_all_finset {ι} (I : Finset ι) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x :=
  I.finite_toSet.eventually_all
#align filter.eventually_all_finset Filter.eventually_all_finset

/- warning: finset.eventually_all -> Finset.eventually_all is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (I : Finset.{u2} ι) {l : Filter.{u1} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i I) -> (p i x)) l) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i I) -> (Filter.Eventually.{u1} α (fun (x : α) => p i x) l))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (I : Finset.{u1} ι) {l : Filter.{u2} α} {p : ι -> α -> Prop}, Iff (Filter.Eventually.{u2} α (fun (x : α) => forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i I) -> (p i x)) l) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i I) -> (Filter.Eventually.{u2} α (fun (x : α) => p i x) l))
Case conversion may be inaccurate. Consider using '#align finset.eventually_all Finset.eventually_allₓ'. -/
alias eventually_all_finset ← _root_.finset.eventually_all
#align finset.eventually_all Finset.eventually_all

attribute [protected] Finset.eventually_all

#print Filter.eventually_or_distrib_left /-
@[simp]
theorem eventually_or_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p ∨ q x) ↔ p ∨ ∀ᶠ x in f, q x :=
  by_cases (fun h : p => by simp [h]) fun h => by simp [h]
#align filter.eventually_or_distrib_left Filter.eventually_or_distrib_left
-/

#print Filter.eventually_or_distrib_right /-
@[simp]
theorem eventually_or_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x ∨ q) ↔ (∀ᶠ x in f, p x) ∨ q := by
  simp only [or_comm' _ q, eventually_or_distrib_left]
#align filter.eventually_or_distrib_right Filter.eventually_or_distrib_right
-/

#print Filter.eventually_imp_distrib_left /-
@[simp]
theorem eventually_imp_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p → q x) ↔ p → ∀ᶠ x in f, q x := by
  simp only [imp_iff_not_or, eventually_or_distrib_left]
#align filter.eventually_imp_distrib_left Filter.eventually_imp_distrib_left
-/

/- warning: filter.eventually_bot -> Filter.eventually_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop}, Filter.Eventually.{u1} α (fun (x : α) => p x) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop}, Filter.Eventually.{u1} α (fun (x : α) => p x) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.eventually_bot Filter.eventually_botₓ'. -/
@[simp]
theorem eventually_bot {p : α → Prop} : ∀ᶠ x in ⊥, p x :=
  ⟨⟩
#align filter.eventually_bot Filter.eventually_bot

/- warning: filter.eventually_top -> Filter.eventually_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (forall (x : α), p x)
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (forall (x : α), p x)
Case conversion may be inaccurate. Consider using '#align filter.eventually_top Filter.eventually_topₓ'. -/
@[simp]
theorem eventually_top {p : α → Prop} : (∀ᶠ x in ⊤, p x) ↔ ∀ x, p x :=
  Iff.rfl
#align filter.eventually_top Filter.eventually_top

/- warning: filter.eventually_sup -> Filter.eventually_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g)) (And (Filter.Eventually.{u1} α (fun (x : α) => p x) f) (Filter.Eventually.{u1} α (fun (x : α) => p x) g))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f g)) (And (Filter.Eventually.{u1} α (fun (x : α) => p x) f) (Filter.Eventually.{u1} α (fun (x : α) => p x) g))
Case conversion may be inaccurate. Consider using '#align filter.eventually_sup Filter.eventually_supₓ'. -/
@[simp]
theorem eventually_sup {p : α → Prop} {f g : Filter α} :
    (∀ᶠ x in f ⊔ g, p x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in g, p x :=
  Iff.rfl
#align filter.eventually_sup Filter.eventually_sup

/- warning: filter.eventually_Sup -> Filter.eventually_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {fs : Set.{u1} (Filter.{u1} α)}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (SupSet.supₛ.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) fs)) (forall (f : Filter.{u1} α), (Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) f fs) -> (Filter.Eventually.{u1} α (fun (x : α) => p x) f))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {fs : Set.{u1} (Filter.{u1} α)}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (SupSet.supₛ.{u1} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) fs)) (forall (f : Filter.{u1} α), (Membership.mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.instMembershipSet.{u1} (Filter.{u1} α)) f fs) -> (Filter.Eventually.{u1} α (fun (x : α) => p x) f))
Case conversion may be inaccurate. Consider using '#align filter.eventually_Sup Filter.eventually_supₛₓ'. -/
@[simp]
theorem eventually_supₛ {p : α → Prop} {fs : Set (Filter α)} :
    (∀ᶠ x in supₛ fs, p x) ↔ ∀ f ∈ fs, ∀ᶠ x in f, p x :=
  Iff.rfl
#align filter.eventually_Sup Filter.eventually_supₛ

/- warning: filter.eventually_supr -> Filter.eventually_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {p : α -> Prop} {fs : ι -> (Filter.{u1} α)}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (supᵢ.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (b : ι) => fs b))) (forall (b : ι), Filter.Eventually.{u1} α (fun (x : α) => p x) (fs b))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {p : α -> Prop} {fs : ι -> (Filter.{u1} α)}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (supᵢ.{u1, u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (b : ι) => fs b))) (forall (b : ι), Filter.Eventually.{u1} α (fun (x : α) => p x) (fs b))
Case conversion may be inaccurate. Consider using '#align filter.eventually_supr Filter.eventually_supᵢₓ'. -/
@[simp]
theorem eventually_supᵢ {p : α → Prop} {fs : ι → Filter α} :
    (∀ᶠ x in ⨆ b, fs b, p x) ↔ ∀ b, ∀ᶠ x in fs b, p x :=
  mem_supᵢ
#align filter.eventually_supr Filter.eventually_supᵢ

#print Filter.eventually_principal /-
@[simp]
theorem eventually_principal {a : Set α} {p : α → Prop} : (∀ᶠ x in 𝓟 a, p x) ↔ ∀ x ∈ a, p x :=
  Iff.rfl
#align filter.eventually_principal Filter.eventually_principal
-/

/- warning: filter.eventually_inf -> Filter.eventually_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (p x))))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {g : Filter.{u1} α} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (p x))))))
Case conversion may be inaccurate. Consider using '#align filter.eventually_inf Filter.eventually_infₓ'. -/
theorem eventually_inf {f g : Filter α} {p : α → Prop} :
    (∀ᶠ x in f ⊓ g, p x) ↔ ∃ s ∈ f, ∃ t ∈ g, ∀ x ∈ s ∩ t, p x :=
  mem_inf_iff_superset
#align filter.eventually_inf Filter.eventually_inf

/- warning: filter.eventually_inf_principal -> Filter.eventually_inf_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {p : α -> Prop} {s : Set.{u1} α}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α s))) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (p x)) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {p : α -> Prop} {s : Set.{u1} α}, Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α s))) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (p x)) f)
Case conversion may be inaccurate. Consider using '#align filter.eventually_inf_principal Filter.eventually_inf_principalₓ'. -/
theorem eventually_inf_principal {f : Filter α} {p : α → Prop} {s : Set α} :
    (∀ᶠ x in f ⊓ 𝓟 s, p x) ↔ ∀ᶠ x in f, x ∈ s → p x :=
  mem_inf_principal
#align filter.eventually_inf_principal Filter.eventually_inf_principal

/-! ### Frequently -/


#print Filter.Frequently /-
/-- `f.frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in at_top, p x`
means that there exist arbitrarily large `x` for which `p` holds true. -/
protected def Frequently (p : α → Prop) (f : Filter α) : Prop :=
  ¬∀ᶠ x in f, ¬p x
#align filter.frequently Filter.Frequently
-/

-- mathport name: «expr∃ᶠ in , »
notation3"∃ᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r

#print Filter.Eventually.frequently /-
theorem Eventually.frequently {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ᶠ x in f, p x) :
    ∃ᶠ x in f, p x :=
  compl_not_mem h
#align filter.eventually.frequently Filter.Eventually.frequently
-/

#print Filter.frequently_of_forall /-
theorem frequently_of_forall {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ x, p x) :
    ∃ᶠ x in f, p x :=
  Eventually.frequently (eventually_of_forall h)
#align filter.frequently_of_forall Filter.frequently_of_forall
-/

#print Filter.Frequently.mp /-
theorem Frequently.mp {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
    (hpq : ∀ᶠ x in f, p x → q x) : ∃ᶠ x in f, q x :=
  mt (fun hq => hq.mp <| hpq.mono fun x => mt) h
#align filter.frequently.mp Filter.Frequently.mp
-/

/- warning: filter.frequently.filter_mono -> Filter.Frequently.filter_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, (Filter.Frequently.{u1} α (fun (x : α) => p x) f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g) -> (Filter.Frequently.{u1} α (fun (x : α) => p x) g)
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, (Filter.Frequently.{u1} α (fun (x : α) => p x) f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g) -> (Filter.Frequently.{u1} α (fun (x : α) => p x) g)
Case conversion may be inaccurate. Consider using '#align filter.frequently.filter_mono Filter.Frequently.filter_monoₓ'. -/
theorem Frequently.filter_mono {p : α → Prop} {f g : Filter α} (h : ∃ᶠ x in f, p x) (hle : f ≤ g) :
    ∃ᶠ x in g, p x :=
  mt (fun h' => h'.filter_mono hle) h
#align filter.frequently.filter_mono Filter.Frequently.filter_mono

#print Filter.Frequently.mono /-
theorem Frequently.mono {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
    (hpq : ∀ x, p x → q x) : ∃ᶠ x in f, q x :=
  h.mp (eventually_of_forall hpq)
#align filter.frequently.mono Filter.Frequently.mono
-/

#print Filter.Frequently.and_eventually /-
theorem Frequently.and_eventually {p q : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x)
    (hq : ∀ᶠ x in f, q x) : ∃ᶠ x in f, p x ∧ q x :=
  by
  refine' mt (fun h => hq.mp <| h.mono _) hp
  exact fun x hpq hq hp => hpq ⟨hp, hq⟩
#align filter.frequently.and_eventually Filter.Frequently.and_eventually
-/

#print Filter.Eventually.and_frequently /-
theorem Eventually.and_frequently {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∃ᶠ x in f, q x) : ∃ᶠ x in f, p x ∧ q x := by
  simpa only [and_comm] using hq.and_eventually hp
#align filter.eventually.and_frequently Filter.Eventually.and_frequently
-/

#print Filter.Frequently.exists /-
theorem Frequently.exists {p : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x) : ∃ x, p x :=
  by
  by_contra H
  replace H : ∀ᶠ x in f, ¬p x; exact eventually_of_forall (not_exists.1 H)
  exact hp H
#align filter.frequently.exists Filter.Frequently.exists
-/

#print Filter.Eventually.exists /-
theorem Eventually.exists {p : α → Prop} {f : Filter α} [NeBot f] (hp : ∀ᶠ x in f, p x) :
    ∃ x, p x :=
  hp.Frequently.exists
#align filter.eventually.exists Filter.Eventually.exists
-/

#print Filter.frequently_iff_forall_eventually_exists_and /-
theorem frequently_iff_forall_eventually_exists_and {p : α → Prop} {f : Filter α} :
    (∃ᶠ x in f, p x) ↔ ∀ {q : α → Prop}, (∀ᶠ x in f, q x) → ∃ x, p x ∧ q x :=
  ⟨fun hp q hq => (hp.and_eventually hq).exists, fun H hp => by
    simpa only [and_not_self_iff, exists_false] using H hp⟩
#align filter.frequently_iff_forall_eventually_exists_and Filter.frequently_iff_forall_eventually_exists_and
-/

/- warning: filter.frequently_iff -> Filter.frequently_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {P : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (x : α) => P x) f) (forall {U : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U f) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x U) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x U) => P x))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {P : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (x : α) => P x) f) (forall {U : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U f) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x U) (P x))))
Case conversion may be inaccurate. Consider using '#align filter.frequently_iff Filter.frequently_iffₓ'. -/
theorem frequently_iff {f : Filter α} {P : α → Prop} :
    (∃ᶠ x in f, P x) ↔ ∀ {U}, U ∈ f → ∃ x ∈ U, P x :=
  by
  simp only [frequently_iff_forall_eventually_exists_and, exists_prop, and_comm' (P _)]
  rfl
#align filter.frequently_iff Filter.frequently_iff

#print Filter.not_eventually /-
@[simp]
theorem not_eventually {p : α → Prop} {f : Filter α} : (¬∀ᶠ x in f, p x) ↔ ∃ᶠ x in f, ¬p x := by
  simp [Filter.Frequently]
#align filter.not_eventually Filter.not_eventually
-/

#print Filter.not_frequently /-
@[simp]
theorem not_frequently {p : α → Prop} {f : Filter α} : (¬∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, ¬p x := by
  simp only [Filter.Frequently, Classical.not_not]
#align filter.not_frequently Filter.not_frequently
-/

#print Filter.frequently_true_iff_neBot /-
@[simp]
theorem frequently_true_iff_neBot (f : Filter α) : (∃ᶠ x in f, True) ↔ NeBot f := by
  simp [Filter.Frequently, -not_eventually, eventually_false_iff_eq_bot, ne_bot_iff]
#align filter.frequently_true_iff_ne_bot Filter.frequently_true_iff_neBot
-/

#print Filter.frequently_false /-
@[simp]
theorem frequently_false (f : Filter α) : ¬∃ᶠ x in f, False := by simp
#align filter.frequently_false Filter.frequently_false
-/

#print Filter.frequently_const /-
@[simp]
theorem frequently_const {f : Filter α} [NeBot f] {p : Prop} : (∃ᶠ x in f, p) ↔ p :=
  by_cases (fun h : p => by simpa [h] ) fun h => by simp [h]
#align filter.frequently_const Filter.frequently_const
-/

#print Filter.frequently_or_distrib /-
@[simp]
theorem frequently_or_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x ∨ q x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in f, q x := by
  simp only [Filter.Frequently, ← not_and_or, not_or, eventually_and]
#align filter.frequently_or_distrib Filter.frequently_or_distrib
-/

#print Filter.frequently_or_distrib_left /-
theorem frequently_or_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∨ q x) ↔ p ∨ ∃ᶠ x in f, q x := by simp
#align filter.frequently_or_distrib_left Filter.frequently_or_distrib_left
-/

#print Filter.frequently_or_distrib_right /-
theorem frequently_or_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∨ q) ↔ (∃ᶠ x in f, p x) ∨ q := by simp
#align filter.frequently_or_distrib_right Filter.frequently_or_distrib_right
-/

#print Filter.frequently_imp_distrib /-
@[simp]
theorem frequently_imp_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∃ᶠ x in f, q x := by
  simp [imp_iff_not_or, not_eventually, frequently_or_distrib]
#align filter.frequently_imp_distrib Filter.frequently_imp_distrib
-/

#print Filter.frequently_imp_distrib_left /-
theorem frequently_imp_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p → q x) ↔ p → ∃ᶠ x in f, q x := by simp
#align filter.frequently_imp_distrib_left Filter.frequently_imp_distrib_left
-/

#print Filter.frequently_imp_distrib_right /-
theorem frequently_imp_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x → q) ↔ (∀ᶠ x in f, p x) → q := by simp
#align filter.frequently_imp_distrib_right Filter.frequently_imp_distrib_right
-/

#print Filter.eventually_imp_distrib_right /-
@[simp]
theorem eventually_imp_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x → q) ↔ (∃ᶠ x in f, p x) → q := by
  simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]
#align filter.eventually_imp_distrib_right Filter.eventually_imp_distrib_right
-/

#print Filter.frequently_and_distrib_left /-
@[simp]
theorem frequently_and_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∧ q x) ↔ p ∧ ∃ᶠ x in f, q x := by
  simp only [Filter.Frequently, not_and, eventually_imp_distrib_left, not_imp]
#align filter.frequently_and_distrib_left Filter.frequently_and_distrib_left
-/

#print Filter.frequently_and_distrib_right /-
@[simp]
theorem frequently_and_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∧ q) ↔ (∃ᶠ x in f, p x) ∧ q := by
  simp only [and_comm' _ q, frequently_and_distrib_left]
#align filter.frequently_and_distrib_right Filter.frequently_and_distrib_right
-/

/- warning: filter.frequently_bot -> Filter.frequently_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop}, Not (Filter.Frequently.{u1} α (fun (x : α) => p x) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop}, Not (Filter.Frequently.{u1} α (fun (x : α) => p x) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.frequently_bot Filter.frequently_botₓ'. -/
@[simp]
theorem frequently_bot {p : α → Prop} : ¬∃ᶠ x in ⊥, p x := by simp
#align filter.frequently_bot Filter.frequently_bot

/- warning: filter.frequently_top -> Filter.frequently_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (Exists.{succ u1} α (fun (x : α) => p x))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (Exists.{succ u1} α (fun (x : α) => p x))
Case conversion may be inaccurate. Consider using '#align filter.frequently_top Filter.frequently_topₓ'. -/
@[simp]
theorem frequently_top {p : α → Prop} : (∃ᶠ x in ⊤, p x) ↔ ∃ x, p x := by simp [Filter.Frequently]
#align filter.frequently_top Filter.frequently_top

/- warning: filter.frequently_principal -> Filter.frequently_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : Set.{u1} α} {p : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (Filter.principal.{u1} α a)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) => p x)))
but is expected to have type
  forall {α : Type.{u1}} {a : Set.{u1} α} {p : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (Filter.principal.{u1} α a)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x a) (p x)))
Case conversion may be inaccurate. Consider using '#align filter.frequently_principal Filter.frequently_principalₓ'. -/
@[simp]
theorem frequently_principal {a : Set α} {p : α → Prop} : (∃ᶠ x in 𝓟 a, p x) ↔ ∃ x ∈ a, p x := by
  simp [Filter.Frequently, not_forall]
#align filter.frequently_principal Filter.frequently_principal

/- warning: filter.frequently_sup -> Filter.frequently_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g)) (Or (Filter.Frequently.{u1} α (fun (x : α) => p x) f) (Filter.Frequently.{u1} α (fun (x : α) => p x) g))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f g)) (Or (Filter.Frequently.{u1} α (fun (x : α) => p x) f) (Filter.Frequently.{u1} α (fun (x : α) => p x) g))
Case conversion may be inaccurate. Consider using '#align filter.frequently_sup Filter.frequently_supₓ'. -/
theorem frequently_sup {p : α → Prop} {f g : Filter α} :
    (∃ᶠ x in f ⊔ g, p x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in g, p x := by
  simp only [Filter.Frequently, eventually_sup, not_and_or]
#align filter.frequently_sup Filter.frequently_sup

/- warning: filter.frequently_Sup -> Filter.frequently_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {fs : Set.{u1} (Filter.{u1} α)}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (SupSet.supₛ.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) fs)) (Exists.{succ u1} (Filter.{u1} α) (fun (f : Filter.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) f fs) (fun (H : Membership.Mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.hasMem.{u1} (Filter.{u1} α)) f fs) => Filter.Frequently.{u1} α (fun (x : α) => p x) f)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {fs : Set.{u1} (Filter.{u1} α)}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (SupSet.supₛ.{u1} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) fs)) (Exists.{succ u1} (Filter.{u1} α) (fun (f : Filter.{u1} α) => And (Membership.mem.{u1, u1} (Filter.{u1} α) (Set.{u1} (Filter.{u1} α)) (Set.instMembershipSet.{u1} (Filter.{u1} α)) f fs) (Filter.Frequently.{u1} α (fun (x : α) => p x) f)))
Case conversion may be inaccurate. Consider using '#align filter.frequently_Sup Filter.frequently_supₛₓ'. -/
@[simp]
theorem frequently_supₛ {p : α → Prop} {fs : Set (Filter α)} :
    (∃ᶠ x in supₛ fs, p x) ↔ ∃ f ∈ fs, ∃ᶠ x in f, p x := by
  simp [Filter.Frequently, -not_eventually, not_forall]
#align filter.frequently_Sup Filter.frequently_supₛ

/- warning: filter.frequently_supr -> Filter.frequently_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} {fs : β -> (Filter.{u1} α)}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (supᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) β (fun (b : β) => fs b))) (Exists.{succ u2} β (fun (b : β) => Filter.Frequently.{u1} α (fun (x : α) => p x) (fs b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} {fs : β -> (Filter.{u1} α)}, Iff (Filter.Frequently.{u1} α (fun (x : α) => p x) (supᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) β (fun (b : β) => fs b))) (Exists.{succ u2} β (fun (b : β) => Filter.Frequently.{u1} α (fun (x : α) => p x) (fs b)))
Case conversion may be inaccurate. Consider using '#align filter.frequently_supr Filter.frequently_supᵢₓ'. -/
@[simp]
theorem frequently_supᵢ {p : α → Prop} {fs : β → Filter α} :
    (∃ᶠ x in ⨆ b, fs b, p x) ↔ ∃ b, ∃ᶠ x in fs b, p x := by
  simp [Filter.Frequently, -not_eventually, not_forall]
#align filter.frequently_supr Filter.frequently_supᵢ

#print Filter.Eventually.choice /-
theorem Eventually.choice {r : α → β → Prop} {l : Filter α} [l.ne_bot] (h : ∀ᶠ x in l, ∃ y, r x y) :
    ∃ f : α → β, ∀ᶠ x in l, r x (f x) := by
  classical
    use fun x =>
      if hx : ∃ y, r x y then Classical.choose hx
      else Classical.choose (Classical.choose_spec h.exists)
    filter_upwards [h]
    intro x hx
    rw [dif_pos hx]
    exact Classical.choose_spec hx
#align filter.eventually.choice Filter.Eventually.choice
-/

/-!
### Relation “eventually equal”
-/


#print Filter.EventuallyEq /-
/-- Two functions `f` and `g` are *eventually equal* along a filter `l` if the set of `x` such that
`f x = g x` belongs to `l`. -/
def EventuallyEq (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x = g x
#align filter.eventually_eq Filter.EventuallyEq
-/

-- mathport name: «expr =ᶠ[ ] »
notation:50 f " =ᶠ[" l:50 "] " g:50 => EventuallyEq l f g

#print Filter.EventuallyEq.eventually /-
theorem EventuallyEq.eventually {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) :
    ∀ᶠ x in l, f x = g x :=
  h
#align filter.eventually_eq.eventually Filter.EventuallyEq.eventually
-/

#print Filter.EventuallyEq.rw /-
theorem EventuallyEq.rw {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (p : α → β → Prop)
    (hf : ∀ᶠ x in l, p x (f x)) : ∀ᶠ x in l, p x (g x) :=
  hf.congr <| h.mono fun x hx => hx ▸ Iff.rfl
#align filter.eventually_eq.rw Filter.EventuallyEq.rw
-/

#print Filter.eventuallyEq_set /-
theorem eventuallyEq_set {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ s ↔ x ∈ t :=
  eventually_congr <| eventually_of_forall fun x => ⟨Eq.to_iff, Iff.to_eq⟩
#align filter.eventually_eq_set Filter.eventuallyEq_set
-/

alias eventually_eq_set ↔ eventually_eq.mem_iff eventually.set_eq
#align filter.eventually_eq.mem_iff Filter.EventuallyEq.mem_iff
#align filter.eventually.set_eq Filter.Eventually.set_eq

#print Filter.eventuallyEq_univ /-
@[simp]
theorem eventuallyEq_univ {s : Set α} {l : Filter α} : s =ᶠ[l] univ ↔ s ∈ l := by
  simp [eventually_eq_set]
#align filter.eventually_eq_univ Filter.eventuallyEq_univ
-/

/- warning: filter.eventually_eq.exists_mem -> Filter.EventuallyEq.exists_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u1, u2} α β l f g) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) => Set.EqOn.{u1, u2} α β f g s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u1, u2} α β l f g) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) (Set.EqOn.{u1, u2} α β f g s)))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.exists_mem Filter.EventuallyEq.exists_memₓ'. -/
theorem EventuallyEq.exists_mem {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) :
    ∃ s ∈ l, EqOn f g s :=
  h.exists_mem
#align filter.eventually_eq.exists_mem Filter.EventuallyEq.exists_mem

#print Filter.eventuallyEq_of_mem /-
theorem eventuallyEq_of_mem {l : Filter α} {f g : α → β} {s : Set α} (hs : s ∈ l) (h : EqOn f g s) :
    f =ᶠ[l] g :=
  eventually_of_mem hs h
#align filter.eventually_eq_of_mem Filter.eventuallyEq_of_mem
-/

/- warning: filter.eventually_eq_iff_exists_mem -> Filter.eventuallyEq_iff_exists_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, Iff (Filter.EventuallyEq.{u1, u2} α β l f g) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) => Set.EqOn.{u1, u2} α β f g s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, Iff (Filter.EventuallyEq.{u1, u2} α β l f g) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) (Set.EqOn.{u1, u2} α β f g s)))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq_iff_exists_mem Filter.eventuallyEq_iff_exists_memₓ'. -/
theorem eventuallyEq_iff_exists_mem {l : Filter α} {f g : α → β} :
    f =ᶠ[l] g ↔ ∃ s ∈ l, EqOn f g s :=
  eventually_iff_exists_mem
#align filter.eventually_eq_iff_exists_mem Filter.eventuallyEq_iff_exists_mem

/- warning: filter.eventually_eq.filter_mono -> Filter.EventuallyEq.filter_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u1, u2} α β l f g) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l' l) -> (Filter.EventuallyEq.{u1, u2} α β l' f g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {l' : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u1, u2} α β l f g) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l' l) -> (Filter.EventuallyEq.{u1, u2} α β l' f g)
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.filter_mono Filter.EventuallyEq.filter_monoₓ'. -/
theorem EventuallyEq.filter_mono {l l' : Filter α} {f g : α → β} (h₁ : f =ᶠ[l] g) (h₂ : l' ≤ l) :
    f =ᶠ[l'] g :=
  h₂ h₁
#align filter.eventually_eq.filter_mono Filter.EventuallyEq.filter_mono

#print Filter.EventuallyEq.refl /-
@[refl]
theorem EventuallyEq.refl (l : Filter α) (f : α → β) : f =ᶠ[l] f :=
  eventually_of_forall fun x => rfl
#align filter.eventually_eq.refl Filter.EventuallyEq.refl
-/

#print Filter.EventuallyEq.rfl /-
theorem EventuallyEq.rfl {l : Filter α} {f : α → β} : f =ᶠ[l] f :=
  EventuallyEq.refl l f
#align filter.eventually_eq.rfl Filter.EventuallyEq.rfl
-/

#print Filter.EventuallyEq.symm /-
@[symm]
theorem EventuallyEq.symm {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) : g =ᶠ[l] f :=
  H.mono fun _ => Eq.symm
#align filter.eventually_eq.symm Filter.EventuallyEq.symm
-/

#print Filter.EventuallyEq.trans /-
@[trans]
theorem EventuallyEq.trans {l : Filter α} {f g h : α → β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h) :
    f =ᶠ[l] h :=
  H₂.rw (fun x y => f x = y) H₁
#align filter.eventually_eq.trans Filter.EventuallyEq.trans
-/

#print Filter.EventuallyEq.prod_mk /-
theorem EventuallyEq.prod_mk {l} {f f' : α → β} (hf : f =ᶠ[l] f') {g g' : α → γ} (hg : g =ᶠ[l] g') :
    (fun x => (f x, g x)) =ᶠ[l] fun x => (f' x, g' x) :=
  hf.mp <|
    hg.mono <| by
      intros
      simp only [*]
#align filter.eventually_eq.prod_mk Filter.EventuallyEq.prod_mk
-/

#print Filter.EventuallyEq.fun_comp /-
theorem EventuallyEq.fun_comp {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) (h : β → γ) :
    h ∘ f =ᶠ[l] h ∘ g :=
  H.mono fun x hx => congr_arg h hx
#align filter.eventually_eq.fun_comp Filter.EventuallyEq.fun_comp
-/

/- warning: filter.eventually_eq.comp₂ -> Filter.EventuallyEq.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {f : α -> β} {f' : α -> β} {g : α -> γ} {g' : α -> γ} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, u2} α β l f f') -> (forall (h : β -> γ -> δ), (Filter.EventuallyEq.{u1, u3} α γ l g g') -> (Filter.EventuallyEq.{u1, u4} α δ l (fun (x : α) => h (f x) (g x)) (fun (x : α) => h (f' x) (g' x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u1}} {f : α -> β} {f' : α -> β} {g : α -> γ} {g' : α -> γ} {l : Filter.{u2} α}, (Filter.EventuallyEq.{u2, u3} α β l f f') -> (forall (h : β -> γ -> δ), (Filter.EventuallyEq.{u2, u4} α γ l g g') -> (Filter.EventuallyEq.{u2, u1} α δ l (fun (x : α) => h (f x) (g x)) (fun (x : α) => h (f' x) (g' x))))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.comp₂ Filter.EventuallyEq.comp₂ₓ'. -/
theorem EventuallyEq.comp₂ {δ} {f f' : α → β} {g g' : α → γ} {l} (Hf : f =ᶠ[l] f') (h : β → γ → δ)
    (Hg : g =ᶠ[l] g') : (fun x => h (f x) (g x)) =ᶠ[l] fun x => h (f' x) (g' x) :=
  (Hf.prod_mk Hg).fun_comp (uncurry h)
#align filter.eventually_eq.comp₂ Filter.EventuallyEq.comp₂

#print Filter.EventuallyEq.mul /-
@[to_additive]
theorem EventuallyEq.mul [Mul β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : (fun x => f x * f' x) =ᶠ[l] fun x => g x * g' x :=
  h.comp₂ (· * ·) h'
#align filter.eventually_eq.mul Filter.EventuallyEq.mul
#align filter.eventually_eq.add Filter.EventuallyEq.add
-/

#print Filter.EventuallyEq.inv /-
@[to_additive]
theorem EventuallyEq.inv [Inv β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    (fun x => (f x)⁻¹) =ᶠ[l] fun x => (g x)⁻¹ :=
  h.fun_comp Inv.inv
#align filter.eventually_eq.inv Filter.EventuallyEq.inv
#align filter.eventually_eq.neg Filter.EventuallyEq.neg
-/

#print Filter.EventuallyEq.div /-
@[to_additive]
theorem EventuallyEq.div [Div β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : (fun x => f x / f' x) =ᶠ[l] fun x => g x / g' x :=
  h.comp₂ (· / ·) h'
#align filter.eventually_eq.div Filter.EventuallyEq.div
#align filter.eventually_eq.sub Filter.EventuallyEq.sub
-/

/- warning: filter.eventually_eq.const_smul -> Filter.EventuallyEq.const_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {𝕜 : Type.{u3}} [_inst_1 : SMul.{u3, u2} 𝕜 β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u1, u2} α β l f g) -> (forall (c : 𝕜), Filter.EventuallyEq.{u1, u2} α β l (fun (x : α) => SMul.smul.{u3, u2} 𝕜 β _inst_1 c (f x)) (fun (x : α) => SMul.smul.{u3, u2} 𝕜 β _inst_1 c (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {𝕜 : Type.{u1}} [_inst_1 : SMul.{u1, u3} 𝕜 β] {l : Filter.{u2} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u2, u3} α β l f g) -> (forall (c : 𝕜), Filter.EventuallyEq.{u2, u3} α β l (fun (x : α) => HSMul.hSMul.{u1, u3, u3} 𝕜 β β (instHSMul.{u1, u3} 𝕜 β _inst_1) c (f x)) (fun (x : α) => HSMul.hSMul.{u1, u3, u3} 𝕜 β β (instHSMul.{u1, u3} 𝕜 β _inst_1) c (g x)))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.const_smul Filter.EventuallyEq.const_smulₓ'. -/
@[to_additive]
theorem EventuallyEq.const_smul {𝕜} [SMul 𝕜 β] {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g)
    (c : 𝕜) : (fun x => c • f x) =ᶠ[l] fun x => c • g x :=
  h.fun_comp fun x => c • x
#align filter.eventually_eq.const_smul Filter.EventuallyEq.const_smul
#align filter.eventually_eq.const_vadd Filter.EventuallyEq.const_vadd

/- warning: filter.eventually_eq.smul -> Filter.EventuallyEq.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {𝕜 : Type.{u3}} [_inst_1 : SMul.{u3, u2} 𝕜 β] {l : Filter.{u1} α} {f : α -> 𝕜} {f' : α -> 𝕜} {g : α -> β} {g' : α -> β}, (Filter.EventuallyEq.{u1, u3} α 𝕜 l f f') -> (Filter.EventuallyEq.{u1, u2} α β l g g') -> (Filter.EventuallyEq.{u1, u2} α β l (fun (x : α) => SMul.smul.{u3, u2} 𝕜 β _inst_1 (f x) (g x)) (fun (x : α) => SMul.smul.{u3, u2} 𝕜 β _inst_1 (f' x) (g' x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {𝕜 : Type.{u1}} [_inst_1 : SMul.{u1, u3} 𝕜 β] {l : Filter.{u2} α} {f : α -> 𝕜} {f' : α -> 𝕜} {g : α -> β} {g' : α -> β}, (Filter.EventuallyEq.{u2, u1} α 𝕜 l f f') -> (Filter.EventuallyEq.{u2, u3} α β l g g') -> (Filter.EventuallyEq.{u2, u3} α β l (fun (x : α) => HSMul.hSMul.{u1, u3, u3} 𝕜 β β (instHSMul.{u1, u3} 𝕜 β _inst_1) (f x) (g x)) (fun (x : α) => HSMul.hSMul.{u1, u3, u3} 𝕜 β β (instHSMul.{u1, u3} 𝕜 β _inst_1) (f' x) (g' x)))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.smul Filter.EventuallyEq.smulₓ'. -/
@[to_additive]
theorem EventuallyEq.smul {𝕜} [SMul 𝕜 β] {l : Filter α} {f f' : α → 𝕜} {g g' : α → β}
    (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') : (fun x => f x • g x) =ᶠ[l] fun x => f' x • g' x :=
  hf.comp₂ (· • ·) hg
#align filter.eventually_eq.smul Filter.EventuallyEq.smul
#align filter.eventually_eq.vadd Filter.EventuallyEq.vadd

#print Filter.EventuallyEq.sup /-
theorem EventuallyEq.sup [HasSup β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : (fun x => f x ⊔ g x) =ᶠ[l] fun x => f' x ⊔ g' x :=
  hf.comp₂ (· ⊔ ·) hg
#align filter.eventually_eq.sup Filter.EventuallyEq.sup
-/

#print Filter.EventuallyEq.inf /-
theorem EventuallyEq.inf [HasInf β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : (fun x => f x ⊓ g x) =ᶠ[l] fun x => f' x ⊓ g' x :=
  hf.comp₂ (· ⊓ ·) hg
#align filter.eventually_eq.inf Filter.EventuallyEq.inf
-/

#print Filter.EventuallyEq.preimage /-
theorem EventuallyEq.preimage {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (s : Set β) :
    f ⁻¹' s =ᶠ[l] g ⁻¹' s :=
  h.fun_comp s
#align filter.eventually_eq.preimage Filter.EventuallyEq.preimage
-/

/- warning: filter.eventually_eq.inter -> Filter.EventuallyEq.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, 0} α Prop l s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop l (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t t'))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, 0} α Prop l s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop l (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s s') (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.inter Filter.EventuallyEq.interₓ'. -/
theorem EventuallyEq.inter {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∩ s' : Set α) =ᶠ[l] (t ∩ t' : Set α) :=
  h.comp₂ (· ∧ ·) h'
#align filter.eventually_eq.inter Filter.EventuallyEq.inter

/- warning: filter.eventually_eq.union -> Filter.EventuallyEq.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, 0} α Prop l s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop l (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s s') (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t t'))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, 0} α Prop l s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop l (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s s') (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.union Filter.EventuallyEq.unionₓ'. -/
theorem EventuallyEq.union {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∪ s' : Set α) =ᶠ[l] (t ∪ t' : Set α) :=
  h.comp₂ (· ∨ ·) h'
#align filter.eventually_eq.union Filter.EventuallyEq.union

/- warning: filter.eventually_eq.compl -> Filter.EventuallyEq.compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, 0} α Prop l (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, 0} α Prop l (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.compl Filter.EventuallyEq.complₓ'. -/
theorem EventuallyEq.compl {s t : Set α} {l : Filter α} (h : s =ᶠ[l] t) :
    (sᶜ : Set α) =ᶠ[l] (tᶜ : Set α) :=
  h.fun_comp Not
#align filter.eventually_eq.compl Filter.EventuallyEq.compl

/- warning: filter.eventually_eq.diff -> Filter.EventuallyEq.diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, 0} α Prop l s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop l (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s s') (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t t'))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, 0} α Prop l s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop l (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s s') (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.diff Filter.EventuallyEq.diffₓ'. -/
theorem EventuallyEq.diff {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s \ s' : Set α) =ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl
#align filter.eventually_eq.diff Filter.EventuallyEq.diff

#print Filter.eventuallyEq_empty /-
theorem eventuallyEq_empty {s : Set α} {l : Filter α} : s =ᶠ[l] (∅ : Set α) ↔ ∀ᶠ x in l, x ∉ s :=
  eventuallyEq_set.trans <| by simp
#align filter.eventually_eq_empty Filter.eventuallyEq_empty
-/

/- warning: filter.inter_eventually_eq_left -> Filter.inter_eventuallyEq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop l (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) s) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)) l)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop l (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) s) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)) l)
Case conversion may be inaccurate. Consider using '#align filter.inter_eventually_eq_left Filter.inter_eventuallyEq_leftₓ'. -/
theorem inter_eventuallyEq_left {s t : Set α} {l : Filter α} :
    (s ∩ t : Set α) =ᶠ[l] s ↔ ∀ᶠ x in l, x ∈ s → x ∈ t := by
  simp only [eventually_eq_set, mem_inter_iff, and_iff_left_iff_imp]
#align filter.inter_eventually_eq_left Filter.inter_eventuallyEq_left

/- warning: filter.inter_eventually_eq_right -> Filter.inter_eventuallyEq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop l (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) t) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) l)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop l (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) t) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) l)
Case conversion may be inaccurate. Consider using '#align filter.inter_eventually_eq_right Filter.inter_eventuallyEq_rightₓ'. -/
theorem inter_eventuallyEq_right {s t : Set α} {l : Filter α} :
    (s ∩ t : Set α) =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ t → x ∈ s := by
  rw [inter_comm, inter_eventually_eq_left]
#align filter.inter_eventually_eq_right Filter.inter_eventuallyEq_right

#print Filter.eventuallyEq_principal /-
@[simp]
theorem eventuallyEq_principal {s : Set α} {f g : α → β} : f =ᶠ[𝓟 s] g ↔ EqOn f g s :=
  Iff.rfl
#align filter.eventually_eq_principal Filter.eventuallyEq_principal
-/

/- warning: filter.eventually_eq_inf_principal_iff -> Filter.eventuallyEq_inf_principal_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {F : Filter.{u1} α} {s : Set.{u1} α} {f : α -> β} {g : α -> β}, Iff (Filter.EventuallyEq.{u1, u2} α β (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) F (Filter.principal.{u1} α s)) f g) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u2} β (f x) (g x))) F)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {F : Filter.{u1} α} {s : Set.{u1} α} {f : α -> β} {g : α -> β}, Iff (Filter.EventuallyEq.{u1, u2} α β (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) F (Filter.principal.{u1} α s)) f g) (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Eq.{succ u2} β (f x) (g x))) F)
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq_inf_principal_iff Filter.eventuallyEq_inf_principal_iffₓ'. -/
theorem eventuallyEq_inf_principal_iff {F : Filter α} {s : Set α} {f g : α → β} :
    f =ᶠ[F ⊓ 𝓟 s] g ↔ ∀ᶠ x in F, x ∈ s → f x = g x :=
  eventually_inf_principal
#align filter.eventually_eq_inf_principal_iff Filter.eventuallyEq_inf_principal_iff

/- warning: filter.eventually_eq.sub_eq -> Filter.EventuallyEq.sub_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u2} β] {f : α -> β} {g : α -> β} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, u2} α β l f g) -> (Filter.EventuallyEq.{u1, u2} α β l (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_1)))) f g) (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u2} β] {f : α -> β} {g : α -> β} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, u2} α β l f g) -> (Filter.EventuallyEq.{u1, u2} α β l (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_1)))) f g) (OfNat.ofNat.{max u1 u2} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => β) (fun (i : α) => NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.sub_eq Filter.EventuallyEq.sub_eqₓ'. -/
theorem EventuallyEq.sub_eq [AddGroup β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    f - g =ᶠ[l] 0 := by simpa using (eventually_eq.sub (eventually_eq.refl l f) h).symm
#align filter.eventually_eq.sub_eq Filter.EventuallyEq.sub_eq

/- warning: filter.eventually_eq_iff_sub -> Filter.eventuallyEq_iff_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u2} β] {f : α -> β} {g : α -> β} {l : Filter.{u1} α}, Iff (Filter.EventuallyEq.{u1, u2} α β l f g) (Filter.EventuallyEq.{u1, u2} α β l (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_1)))) f g) (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u2} β] {f : α -> β} {g : α -> β} {l : Filter.{u1} α}, Iff (Filter.EventuallyEq.{u1, u2} α β l f g) (Filter.EventuallyEq.{u1, u2} α β l (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_1)))) f g) (OfNat.ofNat.{max u1 u2} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => β) (fun (i : α) => NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq_iff_sub Filter.eventuallyEq_iff_subₓ'. -/
theorem eventuallyEq_iff_sub [AddGroup β] {f g : α → β} {l : Filter α} :
    f =ᶠ[l] g ↔ f - g =ᶠ[l] 0 :=
  ⟨fun h => h.sub_eq, fun h => by simpa using h.add (eventually_eq.refl l g)⟩
#align filter.eventually_eq_iff_sub Filter.eventuallyEq_iff_sub

section LE

variable [LE β] {l : Filter α}

#print Filter.EventuallyLe /-
/-- A function `f` is eventually less than or equal to a function `g` at a filter `l`. -/
def EventuallyLe (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x ≤ g x
#align filter.eventually_le Filter.EventuallyLe
-/

-- mathport name: «expr ≤ᶠ[ ] »
notation:50 f " ≤ᶠ[" l:50 "] " g:50 => EventuallyLe l f g

#print Filter.EventuallyLe.congr /-
theorem EventuallyLe.congr {f f' g g' : α → β} (H : f ≤ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f' ≤ᶠ[l] g' :=
  H.mp <| hg.mp <| hf.mono fun x hf hg H => by rwa [hf, hg] at H
#align filter.eventually_le.congr Filter.EventuallyLe.congr
-/

#print Filter.eventuallyLe_congr /-
theorem eventuallyLe_congr {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f ≤ᶠ[l] g ↔ f' ≤ᶠ[l] g' :=
  ⟨fun H => H.congr hf hg, fun H => H.congr hf.symm hg.symm⟩
#align filter.eventually_le_congr Filter.eventuallyLe_congr
-/

end LE

section Preorder

variable [Preorder β] {l : Filter α} {f g h : α → β}

#print Filter.EventuallyEq.le /-
theorem EventuallyEq.le (h : f =ᶠ[l] g) : f ≤ᶠ[l] g :=
  h.mono fun x => le_of_eq
#align filter.eventually_eq.le Filter.EventuallyEq.le
-/

#print Filter.EventuallyLe.refl /-
@[refl]
theorem EventuallyLe.refl (l : Filter α) (f : α → β) : f ≤ᶠ[l] f :=
  EventuallyEq.rfl.le
#align filter.eventually_le.refl Filter.EventuallyLe.refl
-/

#print Filter.EventuallyLe.rfl /-
theorem EventuallyLe.rfl : f ≤ᶠ[l] f :=
  EventuallyLe.refl l f
#align filter.eventually_le.rfl Filter.EventuallyLe.rfl
-/

#print Filter.EventuallyLe.trans /-
@[trans]
theorem EventuallyLe.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₂.mp <| H₁.mono fun x => le_trans
#align filter.eventually_le.trans Filter.EventuallyLe.trans
-/

#print Filter.EventuallyEq.trans_le /-
@[trans]
theorem EventuallyEq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.le.trans H₂
#align filter.eventually_eq.trans_le Filter.EventuallyEq.trans_le
-/

#print Filter.EventuallyLe.trans_eq /-
@[trans]
theorem EventuallyLe.trans_eq (H₁ : f ≤ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.trans H₂.le
#align filter.eventually_le.trans_eq Filter.EventuallyLe.trans_eq
-/

end Preorder

#print Filter.EventuallyLe.antisymm /-
theorem EventuallyLe.antisymm [PartialOrder β] {l : Filter α} {f g : α → β} (h₁ : f ≤ᶠ[l] g)
    (h₂ : g ≤ᶠ[l] f) : f =ᶠ[l] g :=
  h₂.mp <| h₁.mono fun x => le_antisymm
#align filter.eventually_le.antisymm Filter.EventuallyLe.antisymm
-/

#print Filter.eventuallyLe_antisymm_iff /-
theorem eventuallyLe_antisymm_iff [PartialOrder β] {l : Filter α} {f g : α → β} :
    f =ᶠ[l] g ↔ f ≤ᶠ[l] g ∧ g ≤ᶠ[l] f := by
  simp only [eventually_eq, eventually_le, le_antisymm_iff, eventually_and]
#align filter.eventually_le_antisymm_iff Filter.eventuallyLe_antisymm_iff
-/

#print Filter.EventuallyLe.le_iff_eq /-
theorem EventuallyLe.le_iff_eq [PartialOrder β] {l : Filter α} {f g : α → β} (h : f ≤ᶠ[l] g) :
    g ≤ᶠ[l] f ↔ g =ᶠ[l] f :=
  ⟨fun h' => h'.antisymm h, EventuallyEq.le⟩
#align filter.eventually_le.le_iff_eq Filter.EventuallyLe.le_iff_eq
-/

#print Filter.Eventually.ne_of_lt /-
theorem Eventually.ne_of_lt [Preorder β] {l : Filter α} {f g : α → β} (h : ∀ᶠ x in l, f x < g x) :
    ∀ᶠ x in l, f x ≠ g x :=
  h.mono fun x hx => hx.Ne
#align filter.eventually.ne_of_lt Filter.Eventually.ne_of_lt
-/

/- warning: filter.eventually.ne_top_of_lt -> Filter.Eventually.ne_top_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u2} β] [_inst_2 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1))] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) (f x) (g x)) l) -> (Filter.Eventually.{u1} α (fun (x : α) => Ne.{succ u2} β (f x) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u2} β] [_inst_2 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1))] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) (f x) (g x)) l) -> (Filter.Eventually.{u1} α (fun (x : α) => Ne.{succ u2} β (f x) (Top.top.{u2} β (OrderTop.toTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l)
Case conversion may be inaccurate. Consider using '#align filter.eventually.ne_top_of_lt Filter.Eventually.ne_top_of_ltₓ'. -/
theorem Eventually.ne_top_of_lt [PartialOrder β] [OrderTop β] {l : Filter α} {f g : α → β}
    (h : ∀ᶠ x in l, f x < g x) : ∀ᶠ x in l, f x ≠ ⊤ :=
  h.mono fun x hx => hx.ne_top
#align filter.eventually.ne_top_of_lt Filter.Eventually.ne_top_of_lt

/- warning: filter.eventually.lt_top_of_ne -> Filter.Eventually.lt_top_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u2} β] [_inst_2 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1))] {l : Filter.{u1} α} {f : α -> β}, (Filter.Eventually.{u1} α (fun (x : α) => Ne.{succ u2} β (f x) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) (f x) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u2} β] [_inst_2 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1))] {l : Filter.{u1} α} {f : α -> β}, (Filter.Eventually.{u1} α (fun (x : α) => Ne.{succ u2} β (f x) (Top.top.{u2} β (OrderTop.toTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) (f x) (Top.top.{u2} β (OrderTop.toTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l)
Case conversion may be inaccurate. Consider using '#align filter.eventually.lt_top_of_ne Filter.Eventually.lt_top_of_neₓ'. -/
theorem Eventually.lt_top_of_ne [PartialOrder β] [OrderTop β] {l : Filter α} {f : α → β}
    (h : ∀ᶠ x in l, f x ≠ ⊤) : ∀ᶠ x in l, f x < ⊤ :=
  h.mono fun x hx => hx.lt_top
#align filter.eventually.lt_top_of_ne Filter.Eventually.lt_top_of_ne

/- warning: filter.eventually.lt_top_iff_ne_top -> Filter.Eventually.lt_top_iff_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u2} β] [_inst_2 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1))] {l : Filter.{u1} α} {f : α -> β}, Iff (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) (f x) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l) (Filter.Eventually.{u1} α (fun (x : α) => Ne.{succ u2} β (f x) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u2} β] [_inst_2 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1))] {l : Filter.{u1} α} {f : α -> β}, Iff (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) (f x) (Top.top.{u2} β (OrderTop.toTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l) (Filter.Eventually.{u1} α (fun (x : α) => Ne.{succ u2} β (f x) (Top.top.{u2} β (OrderTop.toTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) _inst_2))) l)
Case conversion may be inaccurate. Consider using '#align filter.eventually.lt_top_iff_ne_top Filter.Eventually.lt_top_iff_ne_topₓ'. -/
theorem Eventually.lt_top_iff_ne_top [PartialOrder β] [OrderTop β] {l : Filter α} {f : α → β} :
    (∀ᶠ x in l, f x < ⊤) ↔ ∀ᶠ x in l, f x ≠ ⊤ :=
  ⟨Eventually.ne_of_lt, Eventually.lt_top_of_ne⟩
#align filter.eventually.lt_top_iff_ne_top Filter.Eventually.lt_top_iff_ne_top

/- warning: filter.eventually_le.inter -> Filter.EventuallyLe.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s t) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s' t') -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t t'))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s t) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s' t') -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s s') (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align filter.eventually_le.inter Filter.EventuallyLe.interₓ'. -/
@[mono]
theorem EventuallyLe.inter {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∩ s' : Set α) ≤ᶠ[l] (t ∩ t' : Set α) :=
  h'.mp <| h.mono fun x => And.imp
#align filter.eventually_le.inter Filter.EventuallyLe.inter

/- warning: filter.eventually_le.union -> Filter.EventuallyLe.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s t) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s' t') -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s s') (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t t'))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s t) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s' t') -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s s') (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align filter.eventually_le.union Filter.EventuallyLe.unionₓ'. -/
@[mono]
theorem EventuallyLe.union {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∪ s' : Set α) ≤ᶠ[l] (t ∪ t' : Set α) :=
  h'.mp <| h.mono fun x => Or.imp
#align filter.eventually_le.union Filter.EventuallyLe.union

/- warning: filter.eventually_le.compl -> Filter.EventuallyLe.compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s t) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s t) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align filter.eventually_le.compl Filter.EventuallyLe.complₓ'. -/
@[mono]
theorem EventuallyLe.compl {s t : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) :
    (tᶜ : Set α) ≤ᶠ[l] (sᶜ : Set α) :=
  h.mono fun x => mt
#align filter.eventually_le.compl Filter.EventuallyLe.compl

/- warning: filter.eventually_le.diff -> Filter.EventuallyLe.diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s t) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l t' s') -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s s') (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t t'))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α} {l : Filter.{u1} α}, (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l s t) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l t' s') -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s s') (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align filter.eventually_le.diff Filter.EventuallyLe.diffₓ'. -/
@[mono]
theorem EventuallyLe.diff {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : t' ≤ᶠ[l] s') :
    (s \ s' : Set α) ≤ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl
#align filter.eventually_le.diff Filter.EventuallyLe.diff

/- warning: filter.eventually_le.mul_le_mul -> Filter.EventuallyLe.mul_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulZeroClass.{u2} β] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : PosMulMono.{u2} β (MulZeroClass.toHasMul.{u2} β _inst_1) (MulZeroClass.toHasZero.{u2} β _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)] [_inst_4 : MulPosMono.{u2} β (MulZeroClass.toHasMul.{u2} β _inst_1) (MulZeroClass.toHasZero.{u2} β _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)] {l : Filter.{u1} α} {f₁ : α -> β} {f₂ : α -> β} {g₁ : α -> β} {g₂ : α -> β}, (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l f₁ f₂) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l g₁ g₂) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasZero.{u2} β _inst_1))))) g₁) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasZero.{u2} β _inst_1))))) f₂) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasMul.{u2} β _inst_1))) f₁ g₁) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasMul.{u2} β _inst_1))) f₂ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulZeroClass.{u2} β] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : PosMulMono.{u2} β (MulZeroClass.toMul.{u2} β _inst_1) (MulZeroClass.toZero.{u2} β _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)] [_inst_4 : MulPosMono.{u2} β (MulZeroClass.toMul.{u2} β _inst_1) (MulZeroClass.toZero.{u2} β _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)] {l : Filter.{u1} α} {f₁ : α -> β} {f₂ : α -> β} {g₁ : α -> β} {g₂ : α -> β}, (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l f₁ f₂) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l g₁ g₂) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21857 : α) => β) (fun (i : α) => MulZeroClass.toZero.{u2} β _inst_1)))) g₁) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21857 : α) => β) (fun (i : α) => MulZeroClass.toZero.{u2} β _inst_1)))) f₂) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) l (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toMul.{u2} β _inst_1))) f₁ g₁) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toMul.{u2} β _inst_1))) f₂ g₂))
Case conversion may be inaccurate. Consider using '#align filter.eventually_le.mul_le_mul Filter.EventuallyLe.mul_le_mulₓ'. -/
theorem EventuallyLe.mul_le_mul [MulZeroClass β] [PartialOrder β] [PosMulMono β] [MulPosMono β]
    {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) (hg₀ : 0 ≤ᶠ[l] g₁)
    (hf₀ : 0 ≤ᶠ[l] f₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg, hg₀, hf₀]with x using mul_le_mul
#align filter.eventually_le.mul_le_mul Filter.EventuallyLe.mul_le_mul

#print Filter.EventuallyLe.mul_le_mul' /-
@[to_additive EventuallyLe.add_le_add]
theorem EventuallyLe.mul_le_mul' [Mul β] [Preorder β] [CovariantClass β β (· * ·) (· ≤ ·)]
    [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β}
    (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg]with x hfx hgx using mul_le_mul' hfx hgx
#align filter.eventually_le.mul_le_mul' Filter.EventuallyLe.mul_le_mul'
#align filter.eventually_le.add_le_add Filter.EventuallyLe.add_le_add
-/

/- warning: filter.eventually_le.mul_nonneg -> Filter.EventuallyLe.mul_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : OrderedSemiring.{u2} β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (OrderedSemiring.toOrderedAddCommMonoid.{u2} β _inst_1)))) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1))))))))) f) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (OrderedSemiring.toOrderedAddCommMonoid.{u2} β _inst_1)))) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1))))))))) g) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (OrderedSemiring.toOrderedAddCommMonoid.{u2} β _inst_1)))) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1))))))))) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1))))))) f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : OrderedSemiring.{u2} β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedSemiring.toPartialOrder.{u2} β _inst_1))) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21857 : α) => β) (fun (i : α) => MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1)))))) f) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedSemiring.toPartialOrder.{u2} β _inst_1))) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21857 : α) => β) (fun (i : α) => MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1)))))) g) -> (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedSemiring.toPartialOrder.{u2} β _inst_1))) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21857 : α) => β) (fun (i : α) => MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1)))))) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (OrderedSemiring.toSemiring.{u2} β _inst_1)))))) f g))
Case conversion may be inaccurate. Consider using '#align filter.eventually_le.mul_nonneg Filter.EventuallyLe.mul_nonnegₓ'. -/
theorem EventuallyLe.mul_nonneg [OrderedSemiring β] {l : Filter α} {f g : α → β} (hf : 0 ≤ᶠ[l] f)
    (hg : 0 ≤ᶠ[l] g) : 0 ≤ᶠ[l] f * g := by filter_upwards [hf, hg]with x using mul_nonneg
#align filter.eventually_le.mul_nonneg Filter.EventuallyLe.mul_nonneg

/- warning: filter.eventually_sub_nonneg -> Filter.eventually_sub_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : OrderedRing.{u2} β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, Iff (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β (OrderedRing.toOrderedAddCommGroup.{u2} β _inst_1)))) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β (OrderedRing.toRing.{u2} β _inst_1)))))))))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddGroupWithOne.toAddGroup.{u2} β (NonAssocRing.toAddGroupWithOne.{u2} β (Ring.toNonAssocRing.{u2} β (OrderedRing.toRing.{u2} β _inst_1)))))))) g f)) (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β (OrderedRing.toOrderedAddCommGroup.{u2} β _inst_1)))) l f g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : OrderedRing.{u2} β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, Iff (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedRing.toPartialOrder.{u2} β _inst_1))) l (OfNat.ofNat.{max u1 u2} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21857 : α) => β) (fun (i : α) => MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β (OrderedSemiring.toSemiring.{u2} β (OrderedRing.toOrderedSemiring.{u2} β _inst_1))))))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Ring.toSub.{u2} β (OrderedRing.toRing.{u2} β _inst_1)))) g f)) (Filter.EventuallyLe.{u1, u2} α β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedRing.toPartialOrder.{u2} β _inst_1))) l f g)
Case conversion may be inaccurate. Consider using '#align filter.eventually_sub_nonneg Filter.eventually_sub_nonnegₓ'. -/
theorem eventually_sub_nonneg [OrderedRing β] {l : Filter α} {f g : α → β} :
    0 ≤ᶠ[l] g - f ↔ f ≤ᶠ[l] g :=
  eventually_congr <| eventually_of_forall fun x => sub_nonneg
#align filter.eventually_sub_nonneg Filter.eventually_sub_nonneg

#print Filter.EventuallyLe.sup /-
theorem EventuallyLe.sup [SemilatticeSup β] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂)
    (hg : g₁ ≤ᶠ[l] g₂) : f₁ ⊔ g₁ ≤ᶠ[l] f₂ ⊔ g₂ := by
  filter_upwards [hf, hg]with x hfx hgx using sup_le_sup hfx hgx
#align filter.eventually_le.sup Filter.EventuallyLe.sup
-/

#print Filter.EventuallyLe.sup_le /-
theorem EventuallyLe.sup_le [SemilatticeSup β] {l : Filter α} {f g h : α → β} (hf : f ≤ᶠ[l] h)
    (hg : g ≤ᶠ[l] h) : f ⊔ g ≤ᶠ[l] h := by
  filter_upwards [hf, hg]with x hfx hgx using sup_le hfx hgx
#align filter.eventually_le.sup_le Filter.EventuallyLe.sup_le
-/

#print Filter.EventuallyLe.le_sup_of_le_left /-
theorem EventuallyLe.le_sup_of_le_left [SemilatticeSup β] {l : Filter α} {f g h : α → β}
    (hf : h ≤ᶠ[l] f) : h ≤ᶠ[l] f ⊔ g := by filter_upwards [hf]with x hfx using le_sup_of_le_left hfx
#align filter.eventually_le.le_sup_of_le_left Filter.EventuallyLe.le_sup_of_le_left
-/

#print Filter.EventuallyLe.le_sup_of_le_right /-
theorem EventuallyLe.le_sup_of_le_right [SemilatticeSup β] {l : Filter α} {f g h : α → β}
    (hg : h ≤ᶠ[l] g) : h ≤ᶠ[l] f ⊔ g := by
  filter_upwards [hg]with x hgx using le_sup_of_le_right hgx
#align filter.eventually_le.le_sup_of_le_right Filter.EventuallyLe.le_sup_of_le_right
-/

/- warning: filter.join_le -> Filter.join_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} (Filter.{u1} α)} {l : Filter.{u1} α}, (Filter.Eventually.{u1} (Filter.{u1} α) (fun (m : Filter.{u1} α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) m l) f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.join.{u1} α f) l)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} (Filter.{u1} α)} {l : Filter.{u1} α}, (Filter.Eventually.{u1} (Filter.{u1} α) (fun (m : Filter.{u1} α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) m l) f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.join.{u1} α f) l)
Case conversion may be inaccurate. Consider using '#align filter.join_le Filter.join_leₓ'. -/
theorem join_le {f : Filter (Filter α)} {l : Filter α} (h : ∀ᶠ m in f, m ≤ l) : join f ≤ l :=
  fun s hs => h.mono fun m hm => hm hs
#align filter.join_le Filter.join_le

/-! ### Push-forwards, pull-backs, and the monad structure -/


section Map

#print Filter.map /-
/-- The forward map of a filter -/
def map (m : α → β) (f : Filter α) : Filter β
    where
  sets := Preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset s t hs st := mem_of_superset hs <| preimage_mono st
  inter_sets s t hs ht := inter_mem hs ht
#align filter.map Filter.map
-/

#print Filter.map_principal /-
@[simp]
theorem map_principal {s : Set α} {f : α → β} : map f (𝓟 s) = 𝓟 (Set.image f s) :=
  Filter.ext fun a => image_subset_iff.symm
#align filter.map_principal Filter.map_principal
-/

variable {f : Filter α} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

#print Filter.eventually_map /-
@[simp]
theorem eventually_map {P : β → Prop} : (∀ᶠ b in map m f, P b) ↔ ∀ᶠ a in f, P (m a) :=
  Iff.rfl
#align filter.eventually_map Filter.eventually_map
-/

#print Filter.frequently_map /-
@[simp]
theorem frequently_map {P : β → Prop} : (∃ᶠ b in map m f, P b) ↔ ∃ᶠ a in f, P (m a) :=
  Iff.rfl
#align filter.frequently_map Filter.frequently_map
-/

#print Filter.mem_map /-
@[simp]
theorem mem_map : t ∈ map m f ↔ m ⁻¹' t ∈ f :=
  Iff.rfl
#align filter.mem_map Filter.mem_map
-/

#print Filter.mem_map' /-
theorem mem_map' : t ∈ map m f ↔ { x | m x ∈ t } ∈ f :=
  Iff.rfl
#align filter.mem_map' Filter.mem_map'
-/

#print Filter.image_mem_map /-
theorem image_mem_map (hs : s ∈ f) : m '' s ∈ map m f :=
  f.sets_of_superset hs <| subset_preimage_image m s
#align filter.image_mem_map Filter.image_mem_map
-/

#print Filter.image_mem_map_iff /-
theorem image_mem_map_iff (hf : Injective m) : m '' s ∈ map m f ↔ s ∈ f :=
  ⟨fun h => by rwa [← preimage_image_eq s hf], image_mem_map⟩
#align filter.image_mem_map_iff Filter.image_mem_map_iff
-/

#print Filter.range_mem_map /-
theorem range_mem_map : range m ∈ map m f :=
  by
  rw [← image_univ]
  exact image_mem_map univ_mem
#align filter.range_mem_map Filter.range_mem_map
-/

/- warning: filter.mem_map_iff_exists_image -> Filter.mem_map_iff_exists_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β} {t : Set.{u2} β}, Iff (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (Filter.map.{u1, u2} α β m f)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β m s) t)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β} {t : Set.{u2} β}, Iff (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) t (Filter.map.{u1, u2} α β m f)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Set.image.{u1, u2} α β m s) t)))
Case conversion may be inaccurate. Consider using '#align filter.mem_map_iff_exists_image Filter.mem_map_iff_exists_imageₓ'. -/
theorem mem_map_iff_exists_image : t ∈ map m f ↔ ∃ s ∈ f, m '' s ⊆ t :=
  ⟨fun ht => ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩, fun ⟨s, hs, ht⟩ =>
    mem_of_superset (image_mem_map hs) ht⟩
#align filter.mem_map_iff_exists_image Filter.mem_map_iff_exists_image

#print Filter.map_id /-
@[simp]
theorem map_id : Filter.map id f = f :=
  filter_eq <| rfl
#align filter.map_id Filter.map_id
-/

#print Filter.map_id' /-
@[simp]
theorem map_id' : Filter.map (fun x => x) f = f :=
  map_id
#align filter.map_id' Filter.map_id'
-/

#print Filter.map_compose /-
@[simp]
theorem map_compose : Filter.map m' ∘ Filter.map m = Filter.map (m' ∘ m) :=
  funext fun _ => filter_eq <| rfl
#align filter.map_compose Filter.map_compose
-/

#print Filter.map_map /-
@[simp]
theorem map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f :=
  congr_fun (@Filter.map_compose m m') f
#align filter.map_map Filter.map_map
-/

#print Filter.map_congr /-
/-- If functions `m₁` and `m₂` are eventually equal at a filter `f`, then
they map this filter to the same filter. -/
theorem map_congr {m₁ m₂ : α → β} {f : Filter α} (h : m₁ =ᶠ[f] m₂) : map m₁ f = map m₂ f :=
  Filter.ext' fun p => by
    simp only [eventually_map]
    exact eventually_congr (h.mono fun x hx => hx ▸ Iff.rfl)
#align filter.map_congr Filter.map_congr
-/

end Map

section Comap

#print Filter.comap /-
/-- The inverse map of a filter. A set `s` belongs to `filter.comap m f` if either of the following
equivalent conditions hold.

1. There exists a set `t ∈ f` such that `m ⁻¹' t ⊆ s`. This is used as a definition.
2. The set `{y | ∀ x, m x = y → x ∈ s}` belongs to `f`, see `filter.mem_comap'`.
3. The set `(m '' sᶜ)ᶜ` belongs to `f`, see `filter.mem_comap_iff_compl` and
`filter.compl_mem_comap`. -/
def comap (m : α → β) (f : Filter β) : Filter α
    where
  sets := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s }
  univ_sets := ⟨univ, univ_mem, by simp only [subset_univ, preimage_univ]⟩
  sets_of_superset := fun a b ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩
#align filter.comap Filter.comap
-/

variable {f : α → β} {l : Filter β} {p : α → Prop} {s : Set α}

#print Filter.mem_comap' /-
theorem mem_comap' : s ∈ comap f l ↔ { y | ∀ ⦃x⦄, f x = y → x ∈ s } ∈ l :=
  ⟨fun ⟨t, ht, hts⟩ => mem_of_superset ht fun y hy x hx => hts <| mem_preimage.2 <| by rwa [hx],
    fun h => ⟨_, h, fun x hx => hx rfl⟩⟩
#align filter.mem_comap' Filter.mem_comap'
-/

#print Filter.mem_comap_prod_mk /-
/-- RHS form is used, e.g., in the definition of `uniform_space`. -/
theorem mem_comap_prod_mk {x : α} {s : Set β} {F : Filter (α × β)} :
    s ∈ comap (Prod.mk x) F ↔ { p : α × β | p.fst = x → p.snd ∈ s } ∈ F := by
  simp_rw [mem_comap', Prod.ext_iff, and_imp, @forall_swap β (_ = _), forall_eq, eq_comm]
#align filter.mem_comap_prod_mk Filter.mem_comap_prod_mk
-/

#print Filter.eventually_comap /-
@[simp]
theorem eventually_comap : (∀ᶠ a in comap f l, p a) ↔ ∀ᶠ b in l, ∀ a, f a = b → p a :=
  mem_comap'
#align filter.eventually_comap Filter.eventually_comap
-/

#print Filter.frequently_comap /-
@[simp]
theorem frequently_comap : (∃ᶠ a in comap f l, p a) ↔ ∃ᶠ b in l, ∃ a, f a = b ∧ p a := by
  simp only [Filter.Frequently, eventually_comap, not_exists, not_and]
#align filter.frequently_comap Filter.frequently_comap
-/

/- warning: filter.mem_comap_iff_compl -> Filter.mem_comap_iff_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : Filter.{u2} β} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (Filter.comap.{u1, u2} α β f l)) (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : Filter.{u2} β} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (Filter.comap.{u1, u2} α β f l)) (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) l)
Case conversion may be inaccurate. Consider using '#align filter.mem_comap_iff_compl Filter.mem_comap_iff_complₓ'. -/
theorem mem_comap_iff_compl : s ∈ comap f l ↔ (f '' sᶜ)ᶜ ∈ l := by
  simp only [mem_comap', compl_def, mem_image, mem_set_of_eq, not_exists, not_and',
    Classical.not_not]
#align filter.mem_comap_iff_compl Filter.mem_comap_iff_compl

/- warning: filter.compl_mem_comap -> Filter.compl_mem_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : Filter.{u2} β} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (Filter.comap.{u1, u2} α β f l)) (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s)) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : Filter.{u2} β} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (Filter.comap.{u1, u2} α β f l)) (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.image.{u1, u2} α β f s)) l)
Case conversion may be inaccurate. Consider using '#align filter.compl_mem_comap Filter.compl_mem_comapₓ'. -/
theorem compl_mem_comap : sᶜ ∈ comap f l ↔ (f '' s)ᶜ ∈ l := by rw [mem_comap_iff_compl, compl_compl]
#align filter.compl_mem_comap Filter.compl_mem_comap

end Comap

#print Filter.bind /-
/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `filter.seq` for the
applicative instance. -/
def bind (f : Filter α) (m : α → Filter β) : Filter β :=
  join (map m f)
#align filter.bind Filter.bind
-/

#print Filter.seq /-
/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq (f : Filter (α → β)) (g : Filter α) : Filter β :=
  ⟨{ s | ∃ u ∈ f, ∃ t ∈ g, ∀ m ∈ u, ∀ x ∈ t, (m : α → β) x ∈ s },
    ⟨univ, univ_mem, univ, univ_mem, by simp only [forall_prop_of_true, mem_univ, forall_true_iff]⟩,
    fun s₀ s₁ ⟨t₀, t₁, h₀, h₁, h⟩ hst => ⟨t₀, t₁, h₀, h₁, fun x hx y hy => hst <| h _ hx _ hy⟩,
    fun s₀ s₁ ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩ =>
    ⟨t₀ ∩ u₀, inter_mem ht₀ hu₀, t₁ ∩ u₁, inter_mem ht₁ hu₁, fun x ⟨hx₀, hx₁⟩ x ⟨hy₀, hy₁⟩ =>
      ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩⟩
#align filter.seq Filter.seq
-/

/-- `pure x` is the set of sets that contain `x`. It is equal to `𝓟 {x}` but
with this definition we have `s ∈ pure a` defeq `a ∈ s`. -/
instance : Pure Filter :=
  ⟨fun (α : Type u) x =>
    { sets := { s | x ∈ s }
      inter_sets := fun s t => And.intro
      sets_of_superset := fun s t hs hst => hst hs
      univ_sets := trivial }⟩

instance : Bind Filter :=
  ⟨@Filter.bind⟩

instance : Seq Filter :=
  ⟨@Filter.seq⟩

instance : Functor Filter where map := @Filter.map

#print Filter.pure_sets /-
theorem pure_sets (a : α) : (pure a : Filter α).sets = { s | a ∈ s } :=
  rfl
#align filter.pure_sets Filter.pure_sets
-/

#print Filter.mem_pure /-
@[simp]
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Filter α) ↔ a ∈ s :=
  Iff.rfl
#align filter.mem_pure Filter.mem_pure
-/

#print Filter.eventually_pure /-
@[simp]
theorem eventually_pure {a : α} {p : α → Prop} : (∀ᶠ x in pure a, p x) ↔ p a :=
  Iff.rfl
#align filter.eventually_pure Filter.eventually_pure
-/

#print Filter.principal_singleton /-
@[simp]
theorem principal_singleton (a : α) : 𝓟 {a} = pure a :=
  Filter.ext fun s => by simp only [mem_pure, mem_principal, singleton_subset_iff]
#align filter.principal_singleton Filter.principal_singleton
-/

#print Filter.map_pure /-
@[simp]
theorem map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
  rfl
#align filter.map_pure Filter.map_pure
-/

#print Filter.join_pure /-
@[simp]
theorem join_pure (f : Filter α) : join (pure f) = f :=
  Filter.ext fun s => Iff.rfl
#align filter.join_pure Filter.join_pure
-/

#print Filter.pure_bind /-
@[simp]
theorem pure_bind (a : α) (m : α → Filter β) : bind (pure a) m = m a := by
  simp only [Bind.bind, bind, map_pure, join_pure]
#align filter.pure_bind Filter.pure_bind
-/

section

#print Filter.monad /-
-- this section needs to be before applicative, otherwise the wrong instance will be chosen
/-- The monad structure on filters. -/
protected def monad : Monad Filter where map := @Filter.map
#align filter.monad Filter.monad
-/

attribute [local instance] Filter.monad

#print Filter.lawfulMonad /-
protected theorem lawfulMonad : LawfulMonad Filter :=
  { id_map := fun α f => filter_eq rfl
    pure_bind := fun α β => pure_bind
    bind_assoc := fun α β γ f m₁ m₂ => filter_eq rfl
    bind_pure_comp_eq_map := fun α β f x =>
      Filter.ext fun s => by
        simp only [Bind.bind, bind, Functor.map, mem_map', mem_join, mem_set_of_eq, comp,
          mem_pure] }
#align filter.is_lawful_monad Filter.lawfulMonad
-/

end

instance : Applicative Filter where
  map := @Filter.map
  seq := @Filter.seq

instance : Alternative Filter where
  failure α := ⊥
  orelse α x y := x ⊔ y

#print Filter.map_def /-
@[simp]
theorem map_def {α β} (m : α → β) (f : Filter α) : m <$> f = map m f :=
  rfl
#align filter.map_def Filter.map_def
-/

#print Filter.bind_def /-
@[simp]
theorem bind_def {α β} (f : Filter α) (m : α → Filter β) : f >>= m = bind f m :=
  rfl
#align filter.bind_def Filter.bind_def
-/

/-! #### `map` and `comap` equations -/


section Map

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Filter β} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

/- warning: filter.mem_comap -> Filter.mem_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {m : α -> β} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (Filter.comap.{u1, u2} α β m g)) (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t g) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t g) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.preimage.{u1, u2} α β m t) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {m : α -> β} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (Filter.comap.{u1, u2} α β m g)) (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) t g) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.preimage.{u1, u2} α β m t) s)))
Case conversion may be inaccurate. Consider using '#align filter.mem_comap Filter.mem_comapₓ'. -/
@[simp]
theorem mem_comap : s ∈ comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s :=
  Iff.rfl
#align filter.mem_comap Filter.mem_comap

#print Filter.preimage_mem_comap /-
theorem preimage_mem_comap (ht : t ∈ g) : m ⁻¹' t ∈ comap m g :=
  ⟨t, ht, Subset.rfl⟩
#align filter.preimage_mem_comap Filter.preimage_mem_comap
-/

#print Filter.Eventually.comap /-
theorem Eventually.comap {p : β → Prop} (hf : ∀ᶠ b in g, p b) (f : α → β) :
    ∀ᶠ a in comap f g, p (f a) :=
  preimage_mem_comap hf
#align filter.eventually.comap Filter.Eventually.comap
-/

#print Filter.comap_id /-
theorem comap_id : comap id f = f :=
  le_antisymm (fun s => preimage_mem_comap) fun s ⟨t, ht, hst⟩ => mem_of_superset ht hst
#align filter.comap_id Filter.comap_id
-/

#print Filter.comap_id' /-
theorem comap_id' : comap (fun x => x) f = f :=
  comap_id
#align filter.comap_id' Filter.comap_id'
-/

/- warning: filter.comap_const_of_not_mem -> Filter.comap_const_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {t : Set.{u2} β} {x : β}, (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t g) -> (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t)) -> (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β (fun (y : α) => x) g) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {t : Set.{u2} β} {x : β}, (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) t g) -> (Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t)) -> (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β (fun (y : α) => x) g) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.comap_const_of_not_mem Filter.comap_const_of_not_memₓ'. -/
theorem comap_const_of_not_mem {x : β} (ht : t ∈ g) (hx : x ∉ t) : comap (fun y : α => x) g = ⊥ :=
  empty_mem_iff_bot.1 <| mem_comap'.2 <| mem_of_superset ht fun x' hx' y h => hx <| h.symm ▸ hx'
#align filter.comap_const_of_not_mem Filter.comap_const_of_not_mem

/- warning: filter.comap_const_of_mem -> Filter.comap_const_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {x : β}, (forall (t : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t g) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t)) -> (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β (fun (y : α) => x) g) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {x : β}, (forall (t : Set.{u2} β), (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) t g) -> (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t)) -> (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β (fun (y : α) => x) g) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.comap_const_of_mem Filter.comap_const_of_memₓ'. -/
theorem comap_const_of_mem {x : β} (h : ∀ t ∈ g, x ∈ t) : comap (fun y : α => x) g = ⊤ :=
  top_unique fun s hs => univ_mem' fun y => h _ (mem_comap'.1 hs) rfl
#align filter.comap_const_of_mem Filter.comap_const_of_mem

#print Filter.map_const /-
theorem map_const [NeBot f] {c : β} : (f.map fun x => c) = pure c :=
  by
  ext s
  by_cases h : c ∈ s <;> simp [h]
#align filter.map_const Filter.map_const
-/

#print Filter.comap_comap /-
theorem comap_comap {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
  Filter.coext fun s => by simp only [compl_mem_comap, image_image]
#align filter.comap_comap Filter.comap_comap
-/

section comm

/-!
The variables in the following lemmas are used as in this diagram:
```
    φ
  α → β
θ ↓   ↓ ψ
  γ → δ
    ρ
```
-/


variable {φ : α → β} {θ : α → γ} {ψ : β → δ} {ρ : γ → δ} (H : ψ ∘ φ = ρ ∘ θ)

include H

/- warning: filter.map_comm -> Filter.map_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {φ : α -> β} {θ : α -> γ} {ψ : β -> δ} {ρ : γ -> δ}, (Eq.{max (succ u1) (succ u4)} (α -> δ) (Function.comp.{succ u1, succ u2, succ u4} α β δ ψ φ) (Function.comp.{succ u1, succ u3, succ u4} α γ δ ρ θ)) -> (forall (F : Filter.{u1} α), Eq.{succ u4} (Filter.{u4} δ) (Filter.map.{u2, u4} β δ ψ (Filter.map.{u1, u2} α β φ F)) (Filter.map.{u3, u4} γ δ ρ (Filter.map.{u1, u3} α γ θ F)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u1}} {φ : α -> β} {θ : α -> γ} {ψ : β -> δ} {ρ : γ -> δ}, (Eq.{max (succ u2) (succ u1)} (α -> δ) (Function.comp.{succ u2, succ u3, succ u1} α β δ ψ φ) (Function.comp.{succ u2, succ u4, succ u1} α γ δ ρ θ)) -> (forall (F : Filter.{u2} α), Eq.{succ u1} (Filter.{u1} δ) (Filter.map.{u3, u1} β δ ψ (Filter.map.{u2, u3} α β φ F)) (Filter.map.{u4, u1} γ δ ρ (Filter.map.{u2, u4} α γ θ F)))
Case conversion may be inaccurate. Consider using '#align filter.map_comm Filter.map_commₓ'. -/
theorem map_comm (F : Filter α) : map ψ (map φ F) = map ρ (map θ F) := by
  rw [Filter.map_map, H, ← Filter.map_map]
#align filter.map_comm Filter.map_comm

/- warning: filter.comap_comm -> Filter.comap_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {φ : α -> β} {θ : α -> γ} {ψ : β -> δ} {ρ : γ -> δ}, (Eq.{max (succ u1) (succ u4)} (α -> δ) (Function.comp.{succ u1, succ u2, succ u4} α β δ ψ φ) (Function.comp.{succ u1, succ u3, succ u4} α γ δ ρ θ)) -> (forall (G : Filter.{u4} δ), Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β φ (Filter.comap.{u2, u4} β δ ψ G)) (Filter.comap.{u1, u3} α γ θ (Filter.comap.{u3, u4} γ δ ρ G)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u1}} {φ : α -> β} {θ : α -> γ} {ψ : β -> δ} {ρ : γ -> δ}, (Eq.{max (succ u2) (succ u1)} (α -> δ) (Function.comp.{succ u2, succ u3, succ u1} α β δ ψ φ) (Function.comp.{succ u2, succ u4, succ u1} α γ δ ρ θ)) -> (forall (G : Filter.{u1} δ), Eq.{succ u2} (Filter.{u2} α) (Filter.comap.{u2, u3} α β φ (Filter.comap.{u3, u1} β δ ψ G)) (Filter.comap.{u2, u4} α γ θ (Filter.comap.{u4, u1} γ δ ρ G)))
Case conversion may be inaccurate. Consider using '#align filter.comap_comm Filter.comap_commₓ'. -/
theorem comap_comm (G : Filter δ) : comap φ (comap ψ G) = comap θ (comap ρ G) := by
  rw [Filter.comap_comap, H, ← Filter.comap_comap]
#align filter.comap_comm Filter.comap_comm

end comm

#print Function.Semiconj.filter_map /-
theorem Function.Semiconj.filter_map {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) :=
  map_comm h.comp_eq
#align function.semiconj.filter_map Function.Semiconj.filter_map
-/

#print Function.Commute.filter_map /-
theorem Function.Commute.filter_map {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  h.filterMap
#align function.commute.filter_map Function.Commute.filter_map
-/

#print Function.Semiconj.filter_comap /-
theorem Function.Semiconj.filter_comap {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (comap f) (comap gb) (comap ga) :=
  comap_comm h.comp_eq.symm
#align function.semiconj.filter_comap Function.Semiconj.filter_comap
-/

#print Function.Commute.filter_comap /-
theorem Function.Commute.filter_comap {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (comap f) (comap g) :=
  h.filter_comap
#align function.commute.filter_comap Function.Commute.filter_comap
-/

#print Filter.comap_principal /-
@[simp]
theorem comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 (m ⁻¹' t) :=
  Filter.ext fun s =>
    ⟨fun ⟨u, (hu : t ⊆ u), (b : preimage m u ⊆ s)⟩ => (preimage_mono hu).trans b, fun h =>
      ⟨t, Subset.refl t, h⟩⟩
#align filter.comap_principal Filter.comap_principal
-/

#print Filter.comap_pure /-
@[simp]
theorem comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b}) := by
  rw [← principal_singleton, comap_principal]
#align filter.comap_pure Filter.comap_pure
-/

/- warning: filter.map_le_iff_le_comap -> Filter.map_le_iff_le_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u2} β} {m : α -> β}, Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.map.{u1, u2} α β m f) g) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (Filter.comap.{u1, u2} α β m g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u2} β} {m : α -> β}, Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.map.{u1, u2} α β m f) g) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (Filter.comap.{u1, u2} α β m g))
Case conversion may be inaccurate. Consider using '#align filter.map_le_iff_le_comap Filter.map_le_iff_le_comapₓ'. -/
theorem map_le_iff_le_comap : map m f ≤ g ↔ f ≤ comap m g :=
  ⟨fun h s ⟨t, ht, hts⟩ => mem_of_superset (h ht) hts, fun h s ht => h ⟨_, ht, Subset.rfl⟩⟩
#align filter.map_le_iff_le_comap Filter.map_le_iff_le_comap

/- warning: filter.gc_map_comap -> Filter.gc_map_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (m : α -> β), GaloisConnection.{u1, u2} (Filter.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) (Filter.map.{u1, u2} α β m) (Filter.comap.{u1, u2} α β m)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (m : α -> β), GaloisConnection.{u1, u2} (Filter.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α)) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) (Filter.map.{u1, u2} α β m) (Filter.comap.{u1, u2} α β m)
Case conversion may be inaccurate. Consider using '#align filter.gc_map_comap Filter.gc_map_comapₓ'. -/
theorem gc_map_comap (m : α → β) : GaloisConnection (map m) (comap m) := fun f g =>
  map_le_iff_le_comap
#align filter.gc_map_comap Filter.gc_map_comap

/- warning: filter.map_mono -> Filter.map_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Monotone.{u1, u2} (Filter.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) (Filter.map.{u1, u2} α β m)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Monotone.{u1, u2} (Filter.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α)) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) (Filter.map.{u1, u2} α β m)
Case conversion may be inaccurate. Consider using '#align filter.map_mono Filter.map_monoₓ'. -/
@[mono]
theorem map_mono : Monotone (map m) :=
  (gc_map_comap m).monotone_l
#align filter.map_mono Filter.map_mono

/- warning: filter.comap_mono -> Filter.comap_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Monotone.{u2, u1} (Filter.{u2} β) (Filter.{u1} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)) (Filter.comap.{u1, u2} α β m)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Monotone.{u2, u1} (Filter.{u2} β) (Filter.{u1} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α)) (Filter.comap.{u1, u2} α β m)
Case conversion may be inaccurate. Consider using '#align filter.comap_mono Filter.comap_monoₓ'. -/
@[mono]
theorem comap_mono : Monotone (comap m) :=
  (gc_map_comap m).monotone_u
#align filter.comap_mono Filter.comap_mono

/- warning: filter.map_bot -> Filter.map_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toHasBot.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toBot.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)))
Case conversion may be inaccurate. Consider using '#align filter.map_bot Filter.map_botₓ'. -/
@[simp]
theorem map_bot : map m ⊥ = ⊥ :=
  (gc_map_comap m).l_bot
#align filter.map_bot Filter.map_bot

/- warning: filter.map_sup -> Filter.map_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {m : α -> β}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f₁ f₂)) (HasSup.sup.{u2} (Filter.{u2} β) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} β) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))))) (Filter.map.{u1, u2} α β m f₁) (Filter.map.{u1, u2} α β m f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {m : α -> β}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f₁ f₂)) (HasSup.sup.{u2} (Filter.{u2} β) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} β) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} β) (CompleteLattice.toLattice.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)))) (Filter.map.{u1, u2} α β m f₁) (Filter.map.{u1, u2} α β m f₂))
Case conversion may be inaccurate. Consider using '#align filter.map_sup Filter.map_supₓ'. -/
@[simp]
theorem map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ :=
  (gc_map_comap m).l_sup
#align filter.map_sup Filter.map_sup

/- warning: filter.map_supr -> Filter.map_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {m : α -> β} {f : ι -> (Filter.{u1} α)}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (supᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => f i))) (supᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasSup.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.map.{u1, u2} α β m (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {m : α -> β} {f : ι -> (Filter.{u1} α)}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (supᵢ.{u1, u3} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => f i))) (supᵢ.{u2, u3} (Filter.{u2} β) (CompleteLattice.toSupSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) ι (fun (i : ι) => Filter.map.{u1, u2} α β m (f i)))
Case conversion may be inaccurate. Consider using '#align filter.map_supr Filter.map_supᵢₓ'. -/
@[simp]
theorem map_supᵢ {f : ι → Filter α} : map m (⨆ i, f i) = ⨆ i, map m (f i) :=
  (gc_map_comap m).l_supᵢ
#align filter.map_supr Filter.map_supᵢ

/- warning: filter.map_top -> Filter.map_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (Filter.principal.{u2} β (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (Filter.principal.{u2} β (Set.range.{u2, succ u1} β α f))
Case conversion may be inaccurate. Consider using '#align filter.map_top Filter.map_topₓ'. -/
@[simp]
theorem map_top (f : α → β) : map f ⊤ = 𝓟 (range f) := by
  rw [← principal_univ, map_principal, image_univ]
#align filter.map_top Filter.map_top

/- warning: filter.comap_top -> Filter.comap_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (Top.top.{u2} (Filter.{u2} β) (Filter.hasTop.{u2} β))) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (Top.top.{u2} (Filter.{u2} β) (Filter.instTopFilter.{u2} β))) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))
Case conversion may be inaccurate. Consider using '#align filter.comap_top Filter.comap_topₓ'. -/
@[simp]
theorem comap_top : comap m ⊤ = ⊤ :=
  (gc_map_comap m).u_top
#align filter.comap_top Filter.comap_top

/- warning: filter.comap_inf -> Filter.comap_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) g₁ g₂)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (Filter.comap.{u1, u2} α β m g₁) (Filter.comap.{u1, u2} α β m g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) g₁ g₂)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (Filter.comap.{u1, u2} α β m g₁) (Filter.comap.{u1, u2} α β m g₂))
Case conversion may be inaccurate. Consider using '#align filter.comap_inf Filter.comap_infₓ'. -/
@[simp]
theorem comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ :=
  (gc_map_comap m).u_inf
#align filter.comap_inf Filter.comap_inf

/- warning: filter.comap_infi -> Filter.comap_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {m : α -> β} {f : ι -> (Filter.{u2} β)}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => f i))) (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => Filter.comap.{u1, u2} α β m (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {m : α -> β} {f : ι -> (Filter.{u2} β)}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (infᵢ.{u2, u3} (Filter.{u2} β) (CompleteLattice.toInfSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) ι (fun (i : ι) => f i))) (infᵢ.{u1, u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => Filter.comap.{u1, u2} α β m (f i)))
Case conversion may be inaccurate. Consider using '#align filter.comap_infi Filter.comap_infᵢₓ'. -/
@[simp]
theorem comap_infᵢ {f : ι → Filter β} : comap m (⨅ i, f i) = ⨅ i, comap m (f i) :=
  (gc_map_comap m).u_infᵢ
#align filter.comap_infi Filter.comap_infᵢ

/- warning: filter.le_comap_top -> Filter.le_comap_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (l : Filter.{u1} α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l (Filter.comap.{u1, u2} α β f (Top.top.{u2} (Filter.{u2} β) (Filter.hasTop.{u2} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (l : Filter.{u1} α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l (Filter.comap.{u1, u2} α β f (Top.top.{u2} (Filter.{u2} β) (Filter.instTopFilter.{u2} β)))
Case conversion may be inaccurate. Consider using '#align filter.le_comap_top Filter.le_comap_topₓ'. -/
theorem le_comap_top (f : α → β) (l : Filter α) : l ≤ comap f ⊤ :=
  by
  rw [comap_top]
  exact le_top
#align filter.le_comap_top Filter.le_comap_top

/- warning: filter.map_comap_le -> Filter.map_comap_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {m : α -> β}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.map.{u1, u2} α β m (Filter.comap.{u1, u2} α β m g)) g
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {m : α -> β}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.map.{u1, u2} α β m (Filter.comap.{u1, u2} α β m g)) g
Case conversion may be inaccurate. Consider using '#align filter.map_comap_le Filter.map_comap_leₓ'. -/
theorem map_comap_le : map m (comap m g) ≤ g :=
  (gc_map_comap m).l_u_le _
#align filter.map_comap_le Filter.map_comap_le

/- warning: filter.le_comap_map -> Filter.le_comap_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β}, LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (Filter.comap.{u1, u2} α β m (Filter.map.{u1, u2} α β m f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β}, LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (Filter.comap.{u1, u2} α β m (Filter.map.{u1, u2} α β m f))
Case conversion may be inaccurate. Consider using '#align filter.le_comap_map Filter.le_comap_mapₓ'. -/
theorem le_comap_map : f ≤ comap m (map m f) :=
  (gc_map_comap m).le_u_l _
#align filter.le_comap_map Filter.le_comap_map

/- warning: filter.comap_bot -> Filter.comap_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toHasBot.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β)))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toBot.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.comap_bot Filter.comap_botₓ'. -/
@[simp]
theorem comap_bot : comap m ⊥ = ⊥ :=
  bot_unique fun s _ => ⟨∅, mem_bot, by simp only [empty_subset, preimage_empty]⟩
#align filter.comap_bot Filter.comap_bot

#print Filter.neBot_of_comap /-
theorem neBot_of_comap (h : (comap m g).ne_bot) : g.ne_bot :=
  by
  rw [ne_bot_iff] at *
  contrapose! h
  rw [h]
  exact comap_bot
#align filter.ne_bot_of_comap Filter.neBot_of_comap
-/

/- warning: filter.comap_inf_principal_range -> Filter.comap_inf_principal_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) g (Filter.principal.{u2} β (Set.range.{u2, succ u1} β α m)))) (Filter.comap.{u1, u2} α β m g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g : Filter.{u2} β} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) g (Filter.principal.{u2} β (Set.range.{u2, succ u1} β α m)))) (Filter.comap.{u1, u2} α β m g)
Case conversion may be inaccurate. Consider using '#align filter.comap_inf_principal_range Filter.comap_inf_principal_rangeₓ'. -/
theorem comap_inf_principal_range : comap m (g ⊓ 𝓟 (range m)) = comap m g := by simp
#align filter.comap_inf_principal_range Filter.comap_inf_principal_range

/- warning: filter.disjoint_comap -> Filter.disjoint_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β} {m : α -> β}, (Disjoint.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) g₁ g₂) -> (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Filter.comap.{u1, u2} α β m g₁) (Filter.comap.{u1, u2} α β m g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β} {m : α -> β}, (Disjoint.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) g₁ g₂) -> (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Filter.comap.{u1, u2} α β m g₁) (Filter.comap.{u1, u2} α β m g₂))
Case conversion may be inaccurate. Consider using '#align filter.disjoint_comap Filter.disjoint_comapₓ'. -/
theorem disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (comap m g₁) (comap m g₂) := by
  simp only [disjoint_iff, ← comap_inf, h.eq_bot, comap_bot]
#align filter.disjoint_comap Filter.disjoint_comap

/- warning: filter.comap_supr -> Filter.comap_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> (Filter.{u2} β)} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (supᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasSup.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι f)) (supᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => Filter.comap.{u1, u2} α β m (f i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : ι -> (Filter.{u3} β)} {m : α -> β}, Eq.{succ u2} (Filter.{u2} α) (Filter.comap.{u2, u3} α β m (supᵢ.{u3, u1} (Filter.{u3} β) (CompleteLattice.toSupSet.{u3} (Filter.{u3} β) (Filter.instCompleteLatticeFilter.{u3} β)) ι f)) (supᵢ.{u2, u1} (Filter.{u2} α) (CompleteLattice.toSupSet.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)) ι (fun (i : ι) => Filter.comap.{u2, u3} α β m (f i)))
Case conversion may be inaccurate. Consider using '#align filter.comap_supr Filter.comap_supᵢₓ'. -/
theorem comap_supᵢ {ι} {f : ι → Filter β} {m : α → β} : comap m (supᵢ f) = ⨆ i, comap m (f i) :=
  le_antisymm
    (fun s hs =>
      have : ∀ i, ∃ t, t ∈ f i ∧ m ⁻¹' t ⊆ s := by
        simpa only [mem_comap, exists_prop, mem_supr] using mem_supr.1 hs
      let ⟨t, ht⟩ := Classical.axiom_of_choice this
      ⟨⋃ i, t i, mem_supᵢ.2 fun i => (f i).sets_of_superset (ht i).1 (subset_unionᵢ _ _),
        by
        rw [preimage_Union, Union_subset_iff]
        exact fun i => (ht i).2⟩)
    (supᵢ_le fun i => comap_mono <| le_supᵢ _ _)
#align filter.comap_supr Filter.comap_supᵢ

/- warning: filter.comap_Sup -> Filter.comap_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u2} (Filter.{u2} β)} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (SupSet.supₛ.{u2} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasSup.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) s)) (supᵢ.{u1, succ u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Filter.{u2} β) (fun (f : Filter.{u2} β) => supᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u2, u2} (Filter.{u2} β) (Set.{u2} (Filter.{u2} β)) (Set.hasMem.{u2} (Filter.{u2} β)) f s) (fun (H : Membership.Mem.{u2, u2} (Filter.{u2} β) (Set.{u2} (Filter.{u2} β)) (Set.hasMem.{u2} (Filter.{u2} β)) f s) => Filter.comap.{u1, u2} α β m f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u2} (Filter.{u2} β)} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (SupSet.supₛ.{u2} (Filter.{u2} β) (CompleteLattice.toSupSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) s)) (supᵢ.{u1, succ u2} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Filter.{u2} β) (fun (f : Filter.{u2} β) => supᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (Membership.mem.{u2, u2} (Filter.{u2} β) (Set.{u2} (Filter.{u2} β)) (Set.instMembershipSet.{u2} (Filter.{u2} β)) f s) (fun (H : Membership.mem.{u2, u2} (Filter.{u2} β) (Set.{u2} (Filter.{u2} β)) (Set.instMembershipSet.{u2} (Filter.{u2} β)) f s) => Filter.comap.{u1, u2} α β m f)))
Case conversion may be inaccurate. Consider using '#align filter.comap_Sup Filter.comap_supₛₓ'. -/
theorem comap_supₛ {s : Set (Filter β)} {m : α → β} : comap m (supₛ s) = ⨆ f ∈ s, comap m f := by
  simp only [supₛ_eq_supᵢ, comap_supr, eq_self_iff_true]
#align filter.comap_Sup Filter.comap_supₛ

/- warning: filter.comap_sup -> Filter.comap_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (HasSup.sup.{u2} (Filter.{u2} β) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} β) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))))) g₁ g₂)) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (Filter.comap.{u1, u2} α β m g₁) (Filter.comap.{u1, u2} α β m g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β} {m : α -> β}, Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m (HasSup.sup.{u2} (Filter.{u2} β) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} β) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} β) (CompleteLattice.toLattice.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)))) g₁ g₂)) (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Filter.comap.{u1, u2} α β m g₁) (Filter.comap.{u1, u2} α β m g₂))
Case conversion may be inaccurate. Consider using '#align filter.comap_sup Filter.comap_supₓ'. -/
theorem comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ := by
  rw [sup_eq_supᵢ, comap_supr, supᵢ_bool_eq, Bool.cond_true, Bool.cond_false]
#align filter.comap_sup Filter.comap_sup

/- warning: filter.map_comap -> Filter.map_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Filter.{u2} β) (m : α -> β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (Filter.comap.{u1, u2} α β m f)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) f (Filter.principal.{u2} β (Set.range.{u2, succ u1} β α m)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Filter.{u2} β) (m : α -> β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (Filter.comap.{u1, u2} α β m f)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) f (Filter.principal.{u2} β (Set.range.{u2, succ u1} β α m)))
Case conversion may be inaccurate. Consider using '#align filter.map_comap Filter.map_comapₓ'. -/
theorem map_comap (f : Filter β) (m : α → β) : (f.comap m).map m = f ⊓ 𝓟 (range m) :=
  by
  refine' le_antisymm (le_inf map_comap_le <| le_principal_iff.2 range_mem_map) _
  rintro t' ⟨t, ht, sub⟩
  refine' mem_inf_principal.2 (mem_of_superset ht _)
  rintro _ hxt ⟨x, rfl⟩
  exact sub hxt
#align filter.map_comap Filter.map_comap

#print Filter.map_comap_of_mem /-
theorem map_comap_of_mem {f : Filter β} {m : α → β} (hf : range m ∈ f) : (f.comap m).map m = f := by
  rw [map_comap, inf_eq_left.2 (le_principal_iff.2 hf)]
#align filter.map_comap_of_mem Filter.map_comap_of_mem
-/

#print Filter.canLift /-
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Filter α) (Filter β) (map c) fun f => ∀ᶠ x : α in f, p x
    where prf f hf := ⟨comap c f, map_comap_of_mem <| hf.mono CanLift.prf⟩
#align filter.can_lift Filter.canLift
-/

/- warning: filter.comap_le_comap_iff -> Filter.comap_le_comap_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {g : Filter.{u2} β} {m : α -> β}, (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (Set.range.{u2, succ u1} β α m) f) -> (Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.comap.{u1, u2} α β m f) (Filter.comap.{u1, u2} α β m g)) (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {g : Filter.{u2} β} {m : α -> β}, (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (Set.range.{u2, succ u1} β α m) f) -> (Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.comap.{u1, u2} α β m f) (Filter.comap.{u1, u2} α β m g)) (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) f g))
Case conversion may be inaccurate. Consider using '#align filter.comap_le_comap_iff Filter.comap_le_comap_iffₓ'. -/
theorem comap_le_comap_iff {f g : Filter β} {m : α → β} (hf : range m ∈ f) :
    comap m f ≤ comap m g ↔ f ≤ g :=
  ⟨fun h => map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, fun h => comap_mono h⟩
#align filter.comap_le_comap_iff Filter.comap_le_comap_iff

#print Filter.map_comap_of_surjective /-
theorem map_comap_of_surjective {f : α → β} (hf : Surjective f) (l : Filter β) :
    map f (comap f l) = l :=
  map_comap_of_mem <| by simp only [hf.range_eq, univ_mem]
#align filter.map_comap_of_surjective Filter.map_comap_of_surjective
-/

/- warning: function.surjective.filter_map_top -> Function.Surjective.filter_map_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (Top.top.{u2} (Filter.{u2} β) (Filter.hasTop.{u2} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (Top.top.{u2} (Filter.{u2} β) (Filter.instTopFilter.{u2} β)))
Case conversion may be inaccurate. Consider using '#align function.surjective.filter_map_top Function.Surjective.filter_map_topₓ'. -/
theorem Function.Surjective.filter_map_top {f : α → β} (hf : Surjective f) : map f ⊤ = ⊤ :=
  (congr_arg _ comap_top).symm.trans <| map_comap_of_surjective hf ⊤
#align function.surjective.filter_map_top Function.Surjective.filter_map_top

/- warning: filter.subtype_coe_map_comap -> Filter.subtype_coe_map_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (f : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} α) (Filter.map.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) (Filter.comap.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) f)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f (Filter.principal.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (f : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} α) (Filter.map.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) (Filter.comap.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) f)) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f (Filter.principal.{u1} α s))
Case conversion may be inaccurate. Consider using '#align filter.subtype_coe_map_comap Filter.subtype_coe_map_comapₓ'. -/
theorem subtype_coe_map_comap (s : Set α) (f : Filter α) :
    map (coe : s → α) (comap (coe : s → α) f) = f ⊓ 𝓟 s := by rw [map_comap, Subtype.range_coe]
#align filter.subtype_coe_map_comap Filter.subtype_coe_map_comap

#print Filter.image_mem_of_mem_comap /-
theorem image_mem_of_mem_comap {f : Filter α} {c : β → α} (h : range c ∈ f) {W : Set β}
    (W_in : W ∈ comap c f) : c '' W ∈ f :=
  by
  rw [← map_comap_of_mem h]
  exact image_mem_map W_in
#align filter.image_mem_of_mem_comap Filter.image_mem_of_mem_comap
-/

#print Filter.image_coe_mem_of_mem_comap /-
theorem image_coe_mem_of_mem_comap {f : Filter α} {U : Set α} (h : U ∈ f) {W : Set U}
    (W_in : W ∈ comap (coe : U → α) f) : coe '' W ∈ f :=
  image_mem_of_mem_comap (by simp [h]) W_in
#align filter.image_coe_mem_of_mem_comap Filter.image_coe_mem_of_mem_comap
-/

#print Filter.comap_map /-
theorem comap_map {f : Filter α} {m : α → β} (h : Injective m) : comap m (map m f) = f :=
  le_antisymm
    (fun s hs =>
      mem_of_superset (preimage_mem_comap <| image_mem_map hs) <| by
        simp only [preimage_image_eq s h])
    le_comap_map
#align filter.comap_map Filter.comap_map
-/

#print Filter.mem_comap_iff /-
theorem mem_comap_iff {f : Filter β} {m : α → β} (inj : Injective m) (large : Set.range m ∈ f)
    {S : Set α} : S ∈ comap m f ↔ m '' S ∈ f := by
  rw [← image_mem_map_iff inj, map_comap_of_mem large]
#align filter.mem_comap_iff Filter.mem_comap_iff
-/

/- warning: filter.map_le_map_iff_of_inj_on -> Filter.map_le_map_iff_of_injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u1} α} {f : α -> β} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l₁) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l₂) -> (Set.InjOn.{u1, u2} α β f s) -> (Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.map.{u1, u2} α β f l₁) (Filter.map.{u1, u2} α β f l₂)) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l₁ l₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u1} α} {f : α -> β} {s : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l₁) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l₂) -> (Set.InjOn.{u1, u2} α β f s) -> (Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.map.{u1, u2} α β f l₁) (Filter.map.{u1, u2} α β f l₂)) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l₁ l₂))
Case conversion may be inaccurate. Consider using '#align filter.map_le_map_iff_of_inj_on Filter.map_le_map_iff_of_injOnₓ'. -/
theorem map_le_map_iff_of_injOn {l₁ l₂ : Filter α} {f : α → β} {s : Set α} (h₁ : s ∈ l₁)
    (h₂ : s ∈ l₂) (hinj : InjOn f s) : map f l₁ ≤ map f l₂ ↔ l₁ ≤ l₂ :=
  ⟨fun h t ht =>
    mp_mem h₁ <|
      mem_of_superset (h <| image_mem_map (inter_mem h₂ ht)) fun y ⟨x, ⟨hxs, hxt⟩, hxy⟩ hys =>
        hinj hxs hys hxy ▸ hxt,
    fun h => map_mono h⟩
#align filter.map_le_map_iff_of_inj_on Filter.map_le_map_iff_of_injOn

/- warning: filter.map_le_map_iff -> Filter.map_le_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {m : α -> β}, (Function.Injective.{succ u1, succ u2} α β m) -> (Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.map.{u1, u2} α β m f) (Filter.map.{u1, u2} α β m g)) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {m : α -> β}, (Function.Injective.{succ u1, succ u2} α β m) -> (Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.map.{u1, u2} α β m f) (Filter.map.{u1, u2} α β m g)) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g))
Case conversion may be inaccurate. Consider using '#align filter.map_le_map_iff Filter.map_le_map_iffₓ'. -/
theorem map_le_map_iff {f g : Filter α} {m : α → β} (hm : Injective m) :
    map m f ≤ map m g ↔ f ≤ g := by rw [map_le_iff_le_comap, comap_map hm]
#align filter.map_le_map_iff Filter.map_le_map_iff

#print Filter.map_eq_map_iff_of_injOn /-
theorem map_eq_map_iff_of_injOn {f g : Filter α} {m : α → β} {s : Set α} (hsf : s ∈ f) (hsg : s ∈ g)
    (hm : InjOn m s) : map m f = map m g ↔ f = g := by
  simp only [le_antisymm_iff, map_le_map_iff_of_inj_on hsf hsg hm,
    map_le_map_iff_of_inj_on hsg hsf hm]
#align filter.map_eq_map_iff_of_inj_on Filter.map_eq_map_iff_of_injOn
-/

#print Filter.map_inj /-
theorem map_inj {f g : Filter α} {m : α → β} (hm : Injective m) : map m f = map m g ↔ f = g :=
  map_eq_map_iff_of_injOn univ_mem univ_mem (hm.InjOn _)
#align filter.map_inj Filter.map_inj
-/

#print Filter.map_injective /-
theorem map_injective {m : α → β} (hm : Injective m) : Injective (map m) := fun f g =>
  (map_inj hm).1
#align filter.map_injective Filter.map_injective
-/

#print Filter.comap_neBot_iff /-
theorem comap_neBot_iff {f : Filter β} {m : α → β} : NeBot (comap m f) ↔ ∀ t ∈ f, ∃ a, m a ∈ t :=
  by
  simp only [← forall_mem_nonempty_iff_ne_bot, mem_comap, forall_exists_index]
  exact ⟨fun h t t_in => h (m ⁻¹' t) t t_in subset.rfl, fun h s t ht hst => (h t ht).imp hst⟩
#align filter.comap_ne_bot_iff Filter.comap_neBot_iff
-/

#print Filter.comap_neBot /-
theorem comap_neBot {f : Filter β} {m : α → β} (hm : ∀ t ∈ f, ∃ a, m a ∈ t) : NeBot (comap m f) :=
  comap_neBot_iff.mpr hm
#align filter.comap_ne_bot Filter.comap_neBot
-/

#print Filter.comap_neBot_iff_frequently /-
theorem comap_neBot_iff_frequently {f : Filter β} {m : α → β} :
    NeBot (comap m f) ↔ ∃ᶠ y in f, y ∈ range m := by
  simp [comap_ne_bot_iff, frequently_iff, ← exists_and_left, and_comm]
#align filter.comap_ne_bot_iff_frequently Filter.comap_neBot_iff_frequently
-/

/- warning: filter.comap_ne_bot_iff_compl_range -> Filter.comap_neBot_iff_compl_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {m : α -> β}, Iff (Filter.NeBot.{u1} α (Filter.comap.{u1, u2} α β m f)) (Not (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α m)) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {m : α -> β}, Iff (Filter.NeBot.{u1} α (Filter.comap.{u1, u2} α β m f)) (Not (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.range.{u2, succ u1} β α m)) f))
Case conversion may be inaccurate. Consider using '#align filter.comap_ne_bot_iff_compl_range Filter.comap_neBot_iff_compl_rangeₓ'. -/
theorem comap_neBot_iff_compl_range {f : Filter β} {m : α → β} : NeBot (comap m f) ↔ range mᶜ ∉ f :=
  comap_neBot_iff_frequently
#align filter.comap_ne_bot_iff_compl_range Filter.comap_neBot_iff_compl_range

/- warning: filter.comap_eq_bot_iff_compl_range -> Filter.comap_eq_bot_iff_compl_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {m : α -> β}, Iff (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m f) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α m)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {m : α -> β}, Iff (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m f) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.range.{u2, succ u1} β α m)) f)
Case conversion may be inaccurate. Consider using '#align filter.comap_eq_bot_iff_compl_range Filter.comap_eq_bot_iff_compl_rangeₓ'. -/
theorem comap_eq_bot_iff_compl_range {f : Filter β} {m : α → β} : comap m f = ⊥ ↔ range mᶜ ∈ f :=
  not_iff_not.mp <| neBot_iff.symm.trans comap_neBot_iff_compl_range
#align filter.comap_eq_bot_iff_compl_range Filter.comap_eq_bot_iff_compl_range

/- warning: filter.comap_surjective_eq_bot -> Filter.comap_surjective_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {m : α -> β}, (Function.Surjective.{succ u1, succ u2} α β m) -> (Iff (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m f) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Eq.{succ u2} (Filter.{u2} β) f (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toHasBot.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {m : α -> β}, (Function.Surjective.{succ u1, succ u2} α β m) -> (Iff (Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β m f) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Eq.{succ u2} (Filter.{u2} β) f (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toBot.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)))))
Case conversion may be inaccurate. Consider using '#align filter.comap_surjective_eq_bot Filter.comap_surjective_eq_botₓ'. -/
theorem comap_surjective_eq_bot {f : Filter β} {m : α → β} (hm : Surjective m) :
    comap m f = ⊥ ↔ f = ⊥ := by
  rw [comap_eq_bot_iff_compl_range, hm.range_eq, compl_univ, empty_mem_iff_bot]
#align filter.comap_surjective_eq_bot Filter.comap_surjective_eq_bot

/- warning: filter.disjoint_comap_iff -> Filter.disjoint_comap_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β} {m : α -> β}, (Function.Surjective.{succ u1, succ u2} α β m) -> (Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Filter.comap.{u1, u2} α β m g₁) (Filter.comap.{u1, u2} α β m g₂)) (Disjoint.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β} {m : α -> β}, (Function.Surjective.{succ u1, succ u2} α β m) -> (Iff (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Filter.comap.{u1, u2} α β m g₁) (Filter.comap.{u1, u2} α β m g₂)) (Disjoint.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align filter.disjoint_comap_iff Filter.disjoint_comap_iffₓ'. -/
theorem disjoint_comap_iff (h : Surjective m) :
    Disjoint (comap m g₁) (comap m g₂) ↔ Disjoint g₁ g₂ := by
  rw [disjoint_iff, disjoint_iff, ← comap_inf, comap_surjective_eq_bot h]
#align filter.disjoint_comap_iff Filter.disjoint_comap_iff

#print Filter.NeBot.comap_of_range_mem /-
theorem NeBot.comap_of_range_mem {f : Filter β} {m : α → β} (hf : NeBot f) (hm : range m ∈ f) :
    NeBot (comap m f) :=
  comap_neBot_iff_frequently.2 <| Eventually.frequently hm
#align filter.ne_bot.comap_of_range_mem Filter.NeBot.comap_of_range_mem
-/

#print Filter.comap_fst_neBot_iff /-
@[simp]
theorem comap_fst_neBot_iff {f : Filter α} :
    (f.comap (Prod.fst : α × β → α)).ne_bot ↔ f.ne_bot ∧ Nonempty β :=
  by
  cases isEmpty_or_nonempty β
  · rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not] <;> [simp [*], infer_instance]
  · simp [comap_ne_bot_iff_frequently, h]
#align filter.comap_fst_ne_bot_iff Filter.comap_fst_neBot_iff
-/

#print Filter.comap_fst_neBot /-
@[instance]
theorem comap_fst_neBot [Nonempty β] {f : Filter α} [NeBot f] :
    (f.comap (Prod.fst : α × β → α)).ne_bot :=
  comap_fst_neBot_iff.2 ⟨‹_›, ‹_›⟩
#align filter.comap_fst_ne_bot Filter.comap_fst_neBot
-/

#print Filter.comap_snd_neBot_iff /-
@[simp]
theorem comap_snd_neBot_iff {f : Filter β} :
    (f.comap (Prod.snd : α × β → β)).ne_bot ↔ Nonempty α ∧ f.ne_bot :=
  by
  cases' isEmpty_or_nonempty α with hα hα
  · rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not] <;> [simp, infer_instance]
  · simp [comap_ne_bot_iff_frequently, hα]
#align filter.comap_snd_ne_bot_iff Filter.comap_snd_neBot_iff
-/

#print Filter.comap_snd_neBot /-
@[instance]
theorem comap_snd_neBot [Nonempty α] {f : Filter β} [NeBot f] :
    (f.comap (Prod.snd : α × β → β)).ne_bot :=
  comap_snd_neBot_iff.2 ⟨‹_›, ‹_›⟩
#align filter.comap_snd_ne_bot Filter.comap_snd_neBot
-/

/- warning: filter.comap_eval_ne_bot_iff' -> Filter.comap_eval_neBot_iff' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {i : ι} {f : Filter.{u2} (α i)}, Iff (Filter.NeBot.{max u1 u2} (forall (x : ι), α x) (Filter.comap.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun {i : ι} => α i) i) f)) (And (forall (j : ι), Nonempty.{succ u2} (α j)) (Filter.NeBot.{u2} (α i) f))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {i : ι} {f : Filter.{u1} (α i)}, Iff (Filter.NeBot.{max u2 u1} (forall (x : ι), α x) (Filter.comap.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι α i) f)) (And (forall (j : ι), Nonempty.{succ u1} (α j)) (Filter.NeBot.{u1} (α i) f))
Case conversion may be inaccurate. Consider using '#align filter.comap_eval_ne_bot_iff' Filter.comap_eval_neBot_iff'ₓ'. -/
theorem comap_eval_neBot_iff' {ι : Type _} {α : ι → Type _} {i : ι} {f : Filter (α i)} :
    (comap (eval i) f).ne_bot ↔ (∀ j, Nonempty (α j)) ∧ NeBot f :=
  by
  cases' isEmpty_or_nonempty (∀ j, α j) with H H
  · rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not] <;> [skip, assumption]
    simp [← Classical.nonempty_pi]
  · have : ∀ j, Nonempty (α j) := Classical.nonempty_pi.1 H
    simp [comap_ne_bot_iff_frequently, *]
#align filter.comap_eval_ne_bot_iff' Filter.comap_eval_neBot_iff'

/- warning: filter.comap_eval_ne_bot_iff -> Filter.comap_eval_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (j : ι), Nonempty.{succ u2} (α j)] {i : ι} {f : Filter.{u2} (α i)}, Iff (Filter.NeBot.{max u1 u2} (forall (x : ι), α x) (Filter.comap.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun {i : ι} => α i) i) f)) (Filter.NeBot.{u2} (α i) f)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (j : ι), Nonempty.{succ u1} (α j)] {i : ι} {f : Filter.{u1} (α i)}, Iff (Filter.NeBot.{max u2 u1} (forall (x : ι), α x) (Filter.comap.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι α i) f)) (Filter.NeBot.{u1} (α i) f)
Case conversion may be inaccurate. Consider using '#align filter.comap_eval_ne_bot_iff Filter.comap_eval_neBot_iffₓ'. -/
@[simp]
theorem comap_eval_neBot_iff {ι : Type _} {α : ι → Type _} [∀ j, Nonempty (α j)] {i : ι}
    {f : Filter (α i)} : (comap (eval i) f).ne_bot ↔ NeBot f := by simp [comap_eval_ne_bot_iff', *]
#align filter.comap_eval_ne_bot_iff Filter.comap_eval_neBot_iff

/- warning: filter.comap_eval_ne_bot -> Filter.comap_eval_neBot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (j : ι), Nonempty.{succ u2} (α j)] (i : ι) (f : Filter.{u2} (α i)) [_inst_2 : Filter.NeBot.{u2} (α i) f], Filter.NeBot.{max u1 u2} (forall (x : ι), α x) (Filter.comap.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i) f)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (j : ι), Nonempty.{succ u1} (α j)] (i : ι) (f : Filter.{u1} (α i)) [_inst_2 : Filter.NeBot.{u1} (α i) f], Filter.NeBot.{max u2 u1} (forall (x : ι), α x) (Filter.comap.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι α i) f)
Case conversion may be inaccurate. Consider using '#align filter.comap_eval_ne_bot Filter.comap_eval_neBotₓ'. -/
@[instance]
theorem comap_eval_neBot {ι : Type _} {α : ι → Type _} [∀ j, Nonempty (α j)] (i : ι)
    (f : Filter (α i)) [NeBot f] : (comap (eval i) f).ne_bot :=
  comap_eval_neBot_iff.2 ‹_›
#align filter.comap_eval_ne_bot Filter.comap_eval_neBot

/- warning: filter.comap_inf_principal_ne_bot_of_image_mem -> Filter.comap_inf_principal_neBot_of_image_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {m : α -> β}, (Filter.NeBot.{u2} β f) -> (forall {s : Set.{u1} α}, (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (Set.image.{u1, u2} α β m s) f) -> (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (Filter.comap.{u1, u2} α β m f) (Filter.principal.{u1} α s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u2} β} {m : α -> β}, (Filter.NeBot.{u2} β f) -> (forall {s : Set.{u1} α}, (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (Set.image.{u1, u2} α β m s) f) -> (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (Filter.comap.{u1, u2} α β m f) (Filter.principal.{u1} α s))))
Case conversion may be inaccurate. Consider using '#align filter.comap_inf_principal_ne_bot_of_image_mem Filter.comap_inf_principal_neBot_of_image_memₓ'. -/
theorem comap_inf_principal_neBot_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f ⊓ 𝓟 s) :=
  by
  refine' ⟨compl_compl s ▸ mt mem_of_eq_bot _⟩
  rintro ⟨t, ht, hts⟩
  rcases hf.nonempty_of_mem (inter_mem hs ht) with ⟨_, ⟨x, hxs, rfl⟩, hxt⟩
  exact absurd hxs (hts hxt)
#align filter.comap_inf_principal_ne_bot_of_image_mem Filter.comap_inf_principal_neBot_of_image_mem

/- warning: filter.comap_coe_ne_bot_of_le_principal -> Filter.comap_coe_neBot_of_le_principal is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} {s : Set.{u1} γ} {l : Filter.{u1} γ} [h : Filter.NeBot.{u1} γ l], (LE.le.{u1} (Filter.{u1} γ) (Preorder.toLE.{u1} (Filter.{u1} γ) (PartialOrder.toPreorder.{u1} (Filter.{u1} γ) (Filter.partialOrder.{u1} γ))) l (Filter.principal.{u1} γ s)) -> (Filter.NeBot.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} γ) Type.{u1} (Set.hasCoeToSort.{u1} γ) s) (Filter.comap.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} γ) Type.{u1} (Set.hasCoeToSort.{u1} γ) s) γ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} γ) Type.{u1} (Set.hasCoeToSort.{u1} γ) s) γ (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} γ) Type.{u1} (Set.hasCoeToSort.{u1} γ) s) γ (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} γ) Type.{u1} (Set.hasCoeToSort.{u1} γ) s) γ (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} γ) Type.{u1} (Set.hasCoeToSort.{u1} γ) s) γ (coeSubtype.{succ u1} γ (fun (x : γ) => Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) x s)))))) l))
but is expected to have type
  forall {γ : Type.{u1}} {s : Set.{u1} γ} {l : Filter.{u1} γ} [h : Filter.NeBot.{u1} γ l], (LE.le.{u1} (Filter.{u1} γ) (Preorder.toLE.{u1} (Filter.{u1} γ) (PartialOrder.toPreorder.{u1} (Filter.{u1} γ) (Filter.instPartialOrderFilter.{u1} γ))) l (Filter.principal.{u1} γ s)) -> (Filter.NeBot.{u1} (Subtype.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s)) (Filter.comap.{u1, u1} (Subtype.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s)) γ (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s)) l))
Case conversion may be inaccurate. Consider using '#align filter.comap_coe_ne_bot_of_le_principal Filter.comap_coe_neBot_of_le_principalₓ'. -/
theorem comap_coe_neBot_of_le_principal {s : Set γ} {l : Filter γ} [h : NeBot l] (h' : l ≤ 𝓟 s) :
    NeBot (comap (coe : s → γ) l) :=
  h.comap_of_range_mem <| (@Subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)
#align filter.comap_coe_ne_bot_of_le_principal Filter.comap_coe_neBot_of_le_principal

#print Filter.NeBot.comap_of_surj /-
theorem NeBot.comap_of_surj {f : Filter β} {m : α → β} (hf : NeBot f) (hm : Surjective m) :
    NeBot (comap m f) :=
  hf.comap_of_range_mem <| univ_mem' hm
#align filter.ne_bot.comap_of_surj Filter.NeBot.comap_of_surj
-/

#print Filter.NeBot.comap_of_image_mem /-
theorem NeBot.comap_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f) :=
  hf.comap_of_range_mem <| mem_of_superset hs (image_subset_range _ _)
#align filter.ne_bot.comap_of_image_mem Filter.NeBot.comap_of_image_mem
-/

/- warning: filter.map_eq_bot_iff -> Filter.map_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β}, Iff (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m f) (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toHasBot.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β)))) (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β}, Iff (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m f) (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toBot.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)))) (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.map_eq_bot_iff Filter.map_eq_bot_iffₓ'. -/
@[simp]
theorem map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
  ⟨by
    rw [← empty_mem_iff_bot, ← empty_mem_iff_bot]
    exact id, fun h => by simp only [h, map_bot]⟩
#align filter.map_eq_bot_iff Filter.map_eq_bot_iff

#print Filter.map_neBot_iff /-
theorem map_neBot_iff (f : α → β) {F : Filter α} : NeBot (map f F) ↔ NeBot F := by
  simp only [ne_bot_iff, Ne, map_eq_bot_iff]
#align filter.map_ne_bot_iff Filter.map_neBot_iff
-/

#print Filter.NeBot.map /-
theorem NeBot.map (hf : NeBot f) (m : α → β) : NeBot (map m f) :=
  (map_neBot_iff m).2 hf
#align filter.ne_bot.map Filter.NeBot.map
-/

#print Filter.NeBot.of_map /-
theorem NeBot.of_map : NeBot (f.map m) → NeBot f :=
  (map_neBot_iff m).1
#align filter.ne_bot.of_map Filter.NeBot.of_map
-/

#print Filter.map_neBot /-
instance map_neBot [hf : NeBot f] : NeBot (f.map m) :=
  hf.map m
#align filter.map_ne_bot Filter.map_neBot
-/

#print Filter.interₛ_comap_sets /-
theorem interₛ_comap_sets (f : α → β) (F : Filter β) : ⋂₀ (comap f F).sets = ⋂ U ∈ F, f ⁻¹' U :=
  by
  ext x
  suffices (∀ (A : Set α) (B : Set β), B ∈ F → f ⁻¹' B ⊆ A → x ∈ A) ↔ ∀ B : Set β, B ∈ F → f x ∈ B
    by
    simp only [mem_sInter, mem_Inter, Filter.mem_sets, mem_comap, this, and_imp, exists_prop,
      mem_preimage, exists_imp]
  constructor
  · intro h U U_in
    simpa only [subset.refl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in
  · intro h V U U_in f_U_V
    exact f_U_V (h U U_in)
#align filter.sInter_comap_sets Filter.interₛ_comap_sets
-/

end Map

/- warning: filter.map_infi_le -> Filter.map_infᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> (Filter.{u1} α)} {m : α -> β}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.map.{u1, u2} α β m (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.map.{u1, u2} α β m (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> (Filter.{u1} α)} {m : α -> β}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.map.{u1, u2} α β m (infᵢ.{u1, u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (infᵢ.{u2, u3} (Filter.{u2} β) (CompleteLattice.toInfSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) ι (fun (i : ι) => Filter.map.{u1, u2} α β m (f i)))
Case conversion may be inaccurate. Consider using '#align filter.map_infi_le Filter.map_infᵢ_leₓ'. -/
-- this is a generic rule for monotone functions:
theorem map_infᵢ_le {f : ι → Filter α} {m : α → β} : map m (infᵢ f) ≤ ⨅ i, map m (f i) :=
  le_infᵢ fun i => map_mono <| infᵢ_le _ _
#align filter.map_infi_le Filter.map_infᵢ_le

/- warning: filter.map_infi_eq -> Filter.map_infᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> (Filter.{u1} α)} {m : α -> β}, (Directed.{u1, u3} (Filter.{u1} α) ι (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) f) -> (forall [_inst_1 : Nonempty.{u3} ι], Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι f)) (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => Filter.map.{u1, u2} α β m (f i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> (Filter.{u1} α)} {m : α -> β}, (Directed.{u1, u3} (Filter.{u1} α) ι (fun (x._@.Mathlib.Order.Filter.Basic._hyg.33223 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.33225 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.33223 x._@.Mathlib.Order.Filter.Basic._hyg.33225) f) -> (forall [_inst_1 : Nonempty.{u3} ι], Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (infᵢ.{u1, u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι f)) (infᵢ.{u2, u3} (Filter.{u2} β) (CompleteLattice.toInfSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) ι (fun (i : ι) => Filter.map.{u1, u2} α β m (f i))))
Case conversion may be inaccurate. Consider using '#align filter.map_infi_eq Filter.map_infᵢ_eqₓ'. -/
theorem map_infᵢ_eq {f : ι → Filter α} {m : α → β} (hf : Directed (· ≥ ·) f) [Nonempty ι] :
    map m (infᵢ f) = ⨅ i, map m (f i) :=
  map_infᵢ_le.antisymm fun s (hs : Preimage m s ∈ infᵢ f) =>
    let ⟨i, hi⟩ := (mem_infᵢ_of_directed hf _).1 hs
    have : (⨅ i, map m (f i)) ≤ 𝓟 s :=
      infᵢ_le_of_le i <| by
        simp only [le_principal_iff, mem_map]
        assumption
    Filter.le_principal_iff.1 this
#align filter.map_infi_eq Filter.map_infᵢ_eq

/- warning: filter.map_binfi_eq -> Filter.map_binfᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {f : ι -> (Filter.{u1} α)} {m : α -> β} {p : ι -> Prop}, (DirectedOn.{u3} ι (Order.Preimage.{succ u3, succ u1} ι (Filter.{u1} α) f (GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))))) (setOf.{u3} ι (fun (x : ι) => p x))) -> (Exists.{succ u3} ι (fun (i : ι) => p i)) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (infᵢ.{u1, succ u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (p i) (fun (h : p i) => f i)))) (infᵢ.{u2, succ u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => infᵢ.{u2, 0} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) (p i) (fun (h : p i) => Filter.map.{u1, u2} α β m (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {f : ι -> (Filter.{u1} α)} {m : α -> β} {p : ι -> Prop}, (DirectedOn.{u3} ι (Order.Preimage.{succ u3, succ u1} ι (Filter.{u1} α) f (fun (x._@.Mathlib.Order.Filter.Basic._hyg.33380 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.33382 : Filter.{u1} α) => GE.ge.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.33380 x._@.Mathlib.Order.Filter.Basic._hyg.33382)) (setOf.{u3} ι (fun (x : ι) => p x))) -> (Exists.{succ u3} ι (fun (i : ι) => p i)) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (infᵢ.{u1, succ u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => infᵢ.{u1, 0} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) (p i) (fun (h : p i) => f i)))) (infᵢ.{u2, succ u3} (Filter.{u2} β) (CompleteLattice.toInfSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) ι (fun (i : ι) => infᵢ.{u2, 0} (Filter.{u2} β) (CompleteLattice.toInfSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) (p i) (fun (h : p i) => Filter.map.{u1, u2} α β m (f i)))))
Case conversion may be inaccurate. Consider using '#align filter.map_binfi_eq Filter.map_binfᵢ_eqₓ'. -/
theorem map_binfᵢ_eq {ι : Type w} {f : ι → Filter α} {m : α → β} {p : ι → Prop}
    (h : DirectedOn (f ⁻¹'o (· ≥ ·)) { x | p x }) (ne : ∃ i, p i) :
    map m (⨅ (i) (h : p i), f i) = ⨅ (i) (h : p i), map m (f i) :=
  by
  haveI := nonempty_subtype.2 Ne
  simp only [infᵢ_subtype']
  exact map_infi_eq h.directed_coe
#align filter.map_binfi_eq Filter.map_binfᵢ_eq

/- warning: filter.map_inf_le -> Filter.map_inf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {m : α -> β}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.map.{u1, u2} α β m (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.map.{u1, u2} α β m f) (Filter.map.{u1, u2} α β m g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {m : α -> β}, LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.map.{u1, u2} α β m (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) (Filter.map.{u1, u2} α β m f) (Filter.map.{u1, u2} α β m g))
Case conversion may be inaccurate. Consider using '#align filter.map_inf_le Filter.map_inf_leₓ'. -/
theorem map_inf_le {f g : Filter α} {m : α → β} : map m (f ⊓ g) ≤ map m f ⊓ map m g :=
  (@map_mono _ _ m).map_inf_le f g
#align filter.map_inf_le Filter.map_inf_le

/- warning: filter.map_inf -> Filter.map_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {m : α -> β}, (Function.Injective.{succ u1, succ u2} α β m) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.map.{u1, u2} α β m f) (Filter.map.{u1, u2} α β m g)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {m : α -> β}, (Function.Injective.{succ u1, succ u2} α β m) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) (Filter.map.{u1, u2} α β m f) (Filter.map.{u1, u2} α β m g)))
Case conversion may be inaccurate. Consider using '#align filter.map_inf Filter.map_infₓ'. -/
theorem map_inf {f g : Filter α} {m : α → β} (h : Injective m) :
    map m (f ⊓ g) = map m f ⊓ map m g :=
  by
  refine' map_inf_le.antisymm _
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ ∩ s₂⟩
  refine' mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) _
  rw [← image_inter h, image_subset_iff, ht]
#align filter.map_inf Filter.map_inf

/- warning: filter.map_inf' -> Filter.map_inf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {m : α -> β} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) -> (Set.InjOn.{u1, u2} α β m t) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.map.{u1, u2} α β m f) (Filter.map.{u1, u2} α β m g)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {m : α -> β} {t : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) -> (Set.InjOn.{u1, u2} α β m t) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β m (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) (Filter.map.{u1, u2} α β m f) (Filter.map.{u1, u2} α β m g)))
Case conversion may be inaccurate. Consider using '#align filter.map_inf' Filter.map_inf'ₓ'. -/
theorem map_inf' {f g : Filter α} {m : α → β} {t : Set α} (htf : t ∈ f) (htg : t ∈ g)
    (h : InjOn m t) : map m (f ⊓ g) = map m f ⊓ map m g :=
  by
  lift f to Filter t using htf; lift g to Filter t using htg
  replace h : injective (m ∘ coe) := h.injective
  simp only [map_map, ← map_inf Subtype.coe_injective, map_inf h]
#align filter.map_inf' Filter.map_inf'

/- warning: filter.disjoint_map -> Filter.disjoint_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, (Function.Injective.{succ u1, succ u2} α β m) -> (forall {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α}, Iff (Disjoint.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) (Filter.map.{u1, u2} α β m f₁) (Filter.map.{u1, u2} α β m f₂)) (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β}, (Function.Injective.{succ u1, succ u2} α β m) -> (forall {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α}, Iff (Disjoint.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) (Filter.map.{u1, u2} α β m f₁) (Filter.map.{u1, u2} α β m f₂)) (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align filter.disjoint_map Filter.disjoint_mapₓ'. -/
theorem disjoint_map {m : α → β} (hm : Injective m) {f₁ f₂ : Filter α} :
    Disjoint (map m f₁) (map m f₂) ↔ Disjoint f₁ f₂ := by
  simp only [disjoint_iff, ← map_inf hm, map_eq_bot_iff]
#align filter.disjoint_map Filter.disjoint_map

#print Filter.map_equiv_symm /-
theorem map_equiv_symm (e : α ≃ β) (f : Filter β) : map e.symm f = comap e f :=
  map_injective e.Injective <| by
    rw [map_map, e.self_comp_symm, map_id, map_comap_of_surjective e.surjective]
#align filter.map_equiv_symm Filter.map_equiv_symm
-/

#print Filter.map_eq_comap_of_inverse /-
theorem map_eq_comap_of_inverse {f : Filter α} {m : α → β} {n : β → α} (h₁ : m ∘ n = id)
    (h₂ : n ∘ m = id) : map m f = comap n f :=
  map_equiv_symm ⟨n, m, congr_fun h₁, congr_fun h₂⟩ f
#align filter.map_eq_comap_of_inverse Filter.map_eq_comap_of_inverse
-/

#print Filter.comap_equiv_symm /-
theorem comap_equiv_symm (e : α ≃ β) (f : Filter α) : comap e.symm f = map e f :=
  (map_eq_comap_of_inverse e.self_comp_symm e.symm_comp_self).symm
#align filter.comap_equiv_symm Filter.comap_equiv_symm
-/

#print Filter.map_swap_eq_comap_swap /-
theorem map_swap_eq_comap_swap {f : Filter (α × β)} : Prod.swap <$> f = comap Prod.swap f :=
  map_eq_comap_of_inverse Prod.swap_swap_eq Prod.swap_swap_eq
#align filter.map_swap_eq_comap_swap Filter.map_swap_eq_comap_swap
-/

/- warning: filter.map_swap4_eq_comap -> Filter.map_swap4_eq_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {f : Filter.{max (max u1 u2) u3 u4} (Prod.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ))}, Eq.{succ (max (max u1 u3) u2 u4)} (Filter.{max (max u1 u3) u2 u4} (Prod.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ))) (Filter.map.{max (max u1 u2) u3 u4, max (max u1 u3) u2 u4} (Prod.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ)) (Prod.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ)) (fun (p : Prod.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ)) => Prod.mk.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.mk.{u1, u3} α γ (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) p)) (Prod.fst.{u3, u4} γ δ (Prod.snd.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) p))) (Prod.mk.{u2, u4} β δ (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) p)) (Prod.snd.{u3, u4} γ δ (Prod.snd.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) p)))) f) (Filter.comap.{max (max u1 u3) u2 u4, max (max u1 u2) u3 u4} (Prod.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ)) (Prod.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ)) (fun (p : Prod.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ)) => Prod.mk.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (Prod.mk.{u1, u2} α β (Prod.fst.{u1, u3} α γ (Prod.fst.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) p)) (Prod.fst.{u2, u4} β δ (Prod.snd.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) p))) (Prod.mk.{u3, u4} γ δ (Prod.snd.{u1, u3} α γ (Prod.fst.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) p)) (Prod.snd.{u2, u4} β δ (Prod.snd.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) p)))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u1}} {f : Filter.{max (max u1 u4) u3 u2} (Prod.{max u3 u2, max u1 u4} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ))}, Eq.{max (max (max (succ u2) (succ u3)) (succ u4)) (succ u1)} (Filter.{max (max u1 u3) u4 u2} (Prod.{max u4 u2, max u1 u3} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ))) (Filter.map.{max (max (max u2 u3) u4) u1, max (max u1 u3) u4 u2} (Prod.{max u3 u2, max u1 u4} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ)) (Prod.{max u4 u2, max u1 u3} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ)) (fun (p : Prod.{max u3 u2, max u1 u4} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ)) => Prod.mk.{max u4 u2, max u1 u3} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ) (Prod.mk.{u2, u4} α γ (Prod.fst.{u2, u3} α β (Prod.fst.{max u2 u3, max u4 u1} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ) p)) (Prod.fst.{u4, u1} γ δ (Prod.snd.{max u2 u3, max u4 u1} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ) p))) (Prod.mk.{u3, u1} β δ (Prod.snd.{u2, u3} α β (Prod.fst.{max u2 u3, max u4 u1} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ) p)) (Prod.snd.{u4, u1} γ δ (Prod.snd.{max u2 u3, max u4 u1} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ) p)))) f) (Filter.comap.{max (max (max u2 u3) u4) u1, max (max u1 u4) u3 u2} (Prod.{max u4 u2, max u1 u3} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ)) (Prod.{max u3 u2, max u1 u4} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ)) (fun (p : Prod.{max u4 u2, max u1 u3} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ)) => Prod.mk.{max u3 u2, max u1 u4} (Prod.{u2, u3} α β) (Prod.{u4, u1} γ δ) (Prod.mk.{u2, u3} α β (Prod.fst.{u2, u4} α γ (Prod.fst.{max u2 u4, max u3 u1} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ) p)) (Prod.fst.{u3, u1} β δ (Prod.snd.{max u2 u4, max u3 u1} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ) p))) (Prod.mk.{u4, u1} γ δ (Prod.snd.{u2, u4} α γ (Prod.fst.{max u2 u4, max u3 u1} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ) p)) (Prod.snd.{u3, u1} β δ (Prod.snd.{max u2 u4, max u3 u1} (Prod.{u2, u4} α γ) (Prod.{u3, u1} β δ) p)))) f)
Case conversion may be inaccurate. Consider using '#align filter.map_swap4_eq_comap Filter.map_swap4_eq_comapₓ'. -/
/-- A useful lemma when dealing with uniformities. -/
theorem map_swap4_eq_comap {f : Filter ((α × β) × γ × δ)} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f =
      comap (fun p : (α × γ) × β × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f :=
  map_eq_comap_of_inverse (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl) (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)
#align filter.map_swap4_eq_comap Filter.map_swap4_eq_comap

/- warning: filter.le_map -> Filter.le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β} {g : Filter.{u2} β}, (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (Set.image.{u1, u2} α β m s) g)) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) g (Filter.map.{u1, u2} α β m f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β} {g : Filter.{u2} β}, (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (Set.image.{u1, u2} α β m s) g)) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) g (Filter.map.{u1, u2} α β m f))
Case conversion may be inaccurate. Consider using '#align filter.le_map Filter.le_mapₓ'. -/
theorem le_map {f : Filter α} {m : α → β} {g : Filter β} (h : ∀ s ∈ f, m '' s ∈ g) : g ≤ f.map m :=
  fun s hs => mem_of_superset (h _ hs) <| image_preimage_subset _ _
#align filter.le_map Filter.le_map

/- warning: filter.le_map_iff -> Filter.le_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β} {g : Filter.{u2} β}, Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) g (Filter.map.{u1, u2} α β m f)) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (Set.image.{u1, u2} α β m s) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {m : α -> β} {g : Filter.{u2} β}, Iff (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) g (Filter.map.{u1, u2} α β m f)) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (Set.image.{u1, u2} α β m s) g))
Case conversion may be inaccurate. Consider using '#align filter.le_map_iff Filter.le_map_iffₓ'. -/
theorem le_map_iff {f : Filter α} {m : α → β} {g : Filter β} : g ≤ f.map m ↔ ∀ s ∈ f, m '' s ∈ g :=
  ⟨fun h s hs => h (image_mem_map hs), le_map⟩
#align filter.le_map_iff Filter.le_map_iff

/- warning: filter.push_pull -> Filter.push_pull is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (F : Filter.{u1} α) (G : Filter.{u2} β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) F (Filter.comap.{u1, u2} α β f G))) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.map.{u1, u2} α β f F) G)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (F : Filter.{u1} α) (G : Filter.{u2} β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) F (Filter.comap.{u1, u2} α β f G))) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) (Filter.map.{u1, u2} α β f F) G)
Case conversion may be inaccurate. Consider using '#align filter.push_pull Filter.push_pullₓ'. -/
protected theorem push_pull (f : α → β) (F : Filter α) (G : Filter β) :
    map f (F ⊓ comap f G) = map f F ⊓ G :=
  by
  apply le_antisymm
  ·
    calc
      map f (F ⊓ comap f G) ≤ map f F ⊓ (map f <| comap f G) := map_inf_le
      _ ≤ map f F ⊓ G := inf_le_inf_left (map f F) map_comap_le
      
  · rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩
    apply mem_inf_of_inter (image_mem_map V_in) Z_in
    calc
      f '' V ∩ Z = f '' (V ∩ f ⁻¹' Z) := by rw [image_inter_preimage]
      _ ⊆ f '' (V ∩ W) := image_subset _ (inter_subset_inter_right _ ‹_›)
      _ = f '' (f ⁻¹' U) := by rw [h]
      _ ⊆ U := image_preimage_subset f U
      
#align filter.push_pull Filter.push_pull

/- warning: filter.push_pull' -> Filter.push_pull' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (F : Filter.{u1} α) (G : Filter.{u2} β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (Filter.comap.{u1, u2} α β f G) F)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) G (Filter.map.{u1, u2} α β f F))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (F : Filter.{u1} α) (G : Filter.{u2} β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (Filter.comap.{u1, u2} α β f G) F)) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) G (Filter.map.{u1, u2} α β f F))
Case conversion may be inaccurate. Consider using '#align filter.push_pull' Filter.push_pull'ₓ'. -/
protected theorem push_pull' (f : α → β) (F : Filter α) (G : Filter β) :
    map f (comap f G ⊓ F) = G ⊓ map f F := by simp only [Filter.push_pull, inf_comm]
#align filter.push_pull' Filter.push_pull'

/- warning: filter.principal_eq_map_coe_top -> Filter.principal_eq_map_coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (Filter.principal.{u1} α s) (Filter.map.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) (Top.top.{u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Filter.hasTop.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s))))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (Filter.principal.{u1} α s) (Filter.map.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) (Top.top.{u1} (Filter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (Filter.instTopFilter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)))))
Case conversion may be inaccurate. Consider using '#align filter.principal_eq_map_coe_top Filter.principal_eq_map_coe_topₓ'. -/
theorem principal_eq_map_coe_top (s : Set α) : 𝓟 s = map (coe : s → α) ⊤ := by simp
#align filter.principal_eq_map_coe_top Filter.principal_eq_map_coe_top

/- warning: filter.inf_principal_eq_bot_iff_comap -> Filter.inf_principal_eq_bot_iff_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : Filter.{u1} α} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) F (Filter.principal.{u1} α s)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Eq.{succ u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Filter.comap.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) F) (Bot.bot.{u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (CompleteLattice.toHasBot.{u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Filter.completeLattice.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)))))
but is expected to have type
  forall {α : Type.{u1}} {F : Filter.{u1} α} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) F (Filter.principal.{u1} α s)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Eq.{succ u1} (Filter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (Filter.comap.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) F) (Bot.bot.{u1} (Filter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (CompleteLattice.toBot.{u1} (Filter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (Filter.instCompleteLatticeFilter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))))))
Case conversion may be inaccurate. Consider using '#align filter.inf_principal_eq_bot_iff_comap Filter.inf_principal_eq_bot_iff_comapₓ'. -/
theorem inf_principal_eq_bot_iff_comap {F : Filter α} {s : Set α} :
    F ⊓ 𝓟 s = ⊥ ↔ comap (coe : s → α) F = ⊥ := by
  rw [principal_eq_map_coe_top s, ← Filter.push_pull', inf_top_eq, map_eq_bot_iff]
#align filter.inf_principal_eq_bot_iff_comap Filter.inf_principal_eq_bot_iff_comap

section Applicative

#print Filter.singleton_mem_pure /-
theorem singleton_mem_pure {a : α} : {a} ∈ (pure a : Filter α) :=
  mem_singleton a
#align filter.singleton_mem_pure Filter.singleton_mem_pure
-/

#print Filter.pure_injective /-
theorem pure_injective : Injective (pure : α → Filter α) := fun a b hab =>
  (Filter.ext_iff.1 hab { x | a = x }).1 rfl
#align filter.pure_injective Filter.pure_injective
-/

#print Filter.pure_neBot /-
instance pure_neBot {α : Type u} {a : α} : NeBot (pure a) :=
  ⟨mt empty_mem_iff_bot.2 <| not_mem_empty a⟩
#align filter.pure_ne_bot Filter.pure_neBot
-/

/- warning: filter.le_pure_iff -> Filter.le_pure_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {a : α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {a : α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a)) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) f)
Case conversion may be inaccurate. Consider using '#align filter.le_pure_iff Filter.le_pure_iffₓ'. -/
@[simp]
theorem le_pure_iff {f : Filter α} {a : α} : f ≤ pure a ↔ {a} ∈ f := by
  rw [← principal_singleton, le_principal_iff]
#align filter.le_pure_iff Filter.le_pure_iff

/- warning: filter.mem_seq_def -> Filter.mem_seq_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{max u1 u2} (α -> β)} {g : Filter.{u1} α} {s : Set.{u2} β}, Iff (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (Filter.seq.{u1, u2} α β f g)) (Exists.{succ (max u1 u2)} (Set.{max u1 u2} (α -> β)) (fun (u : Set.{max u1 u2} (α -> β)) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (α -> β)) (Filter.{max u1 u2} (α -> β)) (Filter.hasMem.{max u1 u2} (α -> β)) u f) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (α -> β)) (Filter.{max u1 u2} (α -> β)) (Filter.hasMem.{max u1 u2} (α -> β)) u f) => Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) => forall (x : α -> β), (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) x u) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (x y) s)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{max u1 u2} (α -> β)} {g : Filter.{u1} α} {s : Set.{u2} β}, Iff (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s (Filter.seq.{u1, u2} α β f g)) (Exists.{succ (max u1 u2)} (Set.{max u1 u2} (α -> β)) (fun (u : Set.{max u1 u2} (α -> β)) => And (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (α -> β)) (Filter.{max u1 u2} (α -> β)) (instMembershipSetFilter.{max u1 u2} (α -> β)) u f) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) (forall (x : α -> β), (Membership.mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.instMembershipSet.{max u1 u2} (α -> β)) x u) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (x y) s)))))))
Case conversion may be inaccurate. Consider using '#align filter.mem_seq_def Filter.mem_seq_defₓ'. -/
theorem mem_seq_def {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, ∀ x ∈ u, ∀ y ∈ t, (x : α → β) y ∈ s :=
  Iff.rfl
#align filter.mem_seq_def Filter.mem_seq_def

/- warning: filter.mem_seq_iff -> Filter.mem_seq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{max u1 u2} (α -> β)} {g : Filter.{u1} α} {s : Set.{u2} β}, Iff (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (Filter.seq.{u1, u2} α β f g)) (Exists.{succ (max u1 u2)} (Set.{max u1 u2} (α -> β)) (fun (u : Set.{max u1 u2} (α -> β)) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (α -> β)) (Filter.{max u1 u2} (α -> β)) (Filter.hasMem.{max u1 u2} (α -> β)) u f) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (α -> β)) (Filter.{max u1 u2} (α -> β)) (Filter.hasMem.{max u1 u2} (α -> β)) u f) => Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t g) => HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.seq.{u1, u2} α β u t) s)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{max u1 u2} (α -> β)} {g : Filter.{u1} α} {s : Set.{u2} β}, Iff (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s (Filter.seq.{u1, u2} α β f g)) (Exists.{succ (max u1 u2)} (Set.{max u1 u2} (α -> β)) (fun (u : Set.{max u1 u2} (α -> β)) => And (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (α -> β)) (Filter.{max u1 u2} (α -> β)) (instMembershipSetFilter.{max u1 u2} (α -> β)) u f) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t g) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Set.seq.{u1, u2} α β u t) s)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_seq_iff Filter.mem_seq_iffₓ'. -/
theorem mem_seq_iff {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, Set.seq u t ⊆ s := by
  simp only [mem_seq_def, seq_subset, exists_prop, iff_self_iff]
#align filter.mem_seq_iff Filter.mem_seq_iff

#print Filter.mem_map_seq_iff /-
theorem mem_map_seq_iff {f : Filter α} {g : Filter β} {m : α → β → γ} {s : Set γ} :
    s ∈ (f.map m).seq g ↔ ∃ t u, t ∈ g ∧ u ∈ f ∧ ∀ x ∈ u, ∀ y ∈ t, m x y ∈ s :=
  Iff.intro (fun ⟨t, ht, s, hs, hts⟩ => ⟨s, m ⁻¹' t, hs, ht, fun a => hts _⟩)
    fun ⟨t, s, ht, hs, hts⟩ =>
    ⟨m '' s, image_mem_map hs, t, ht, fun f ⟨a, has, Eq⟩ => Eq ▸ hts _ has⟩
#align filter.mem_map_seq_iff Filter.mem_map_seq_iff
-/

#print Filter.seq_mem_seq /-
theorem seq_mem_seq {f : Filter (α → β)} {g : Filter α} {s : Set (α → β)} {t : Set α} (hs : s ∈ f)
    (ht : t ∈ g) : s.seq t ∈ f.seq g :=
  ⟨s, hs, t, ht, fun f hf a ha => ⟨f, hf, a, ha, rfl⟩⟩
#align filter.seq_mem_seq Filter.seq_mem_seq
-/

/- warning: filter.le_seq -> Filter.le_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{max u1 u2} (α -> β)} {g : Filter.{u1} α} {h : Filter.{u2} β}, (forall (t : Set.{max u1 u2} (α -> β)), (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (α -> β)) (Filter.{max u1 u2} (α -> β)) (Filter.hasMem.{max u1 u2} (α -> β)) t f) -> (forall (u : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u g) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (Set.seq.{u1, u2} α β t u) h))) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) h (Filter.seq.{u1, u2} α β f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{max u1 u2} (α -> β)} {g : Filter.{u1} α} {h : Filter.{u2} β}, (forall (t : Set.{max u1 u2} (α -> β)), (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (α -> β)) (Filter.{max u1 u2} (α -> β)) (instMembershipSetFilter.{max u1 u2} (α -> β)) t f) -> (forall (u : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u g) -> (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) (Set.seq.{u1, u2} α β t u) h))) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) h (Filter.seq.{u1, u2} α β f g))
Case conversion may be inaccurate. Consider using '#align filter.le_seq Filter.le_seqₓ'. -/
theorem le_seq {f : Filter (α → β)} {g : Filter α} {h : Filter β}
    (hh : ∀ t ∈ f, ∀ u ∈ g, Set.seq t u ∈ h) : h ≤ seq f g := fun s ⟨t, ht, u, hu, hs⟩ =>
  mem_of_superset (hh _ ht _ hu) fun b ⟨m, hm, a, ha, Eq⟩ => Eq ▸ hs _ hm _ ha
#align filter.le_seq Filter.le_seq

/- warning: filter.seq_mono -> Filter.seq_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f₁ : Filter.{max u1 u2} (α -> β)} {f₂ : Filter.{max u1 u2} (α -> β)} {g₁ : Filter.{u1} α} {g₂ : Filter.{u1} α}, (LE.le.{max u1 u2} (Filter.{max u1 u2} (α -> β)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (α -> β)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (α -> β)) (Filter.partialOrder.{max u1 u2} (α -> β)))) f₁ f₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) g₁ g₂) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.seq.{u1, u2} α β f₁ g₁) (Filter.seq.{u1, u2} α β f₂ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f₁ : Filter.{max u1 u2} (α -> β)} {f₂ : Filter.{max u1 u2} (α -> β)} {g₁ : Filter.{u1} α} {g₂ : Filter.{u1} α}, (LE.le.{max u1 u2} (Filter.{max u1 u2} (α -> β)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (α -> β)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (α -> β)) (Filter.instPartialOrderFilter.{max u1 u2} (α -> β)))) f₁ f₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) g₁ g₂) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.seq.{u1, u2} α β f₁ g₁) (Filter.seq.{u1, u2} α β f₂ g₂))
Case conversion may be inaccurate. Consider using '#align filter.seq_mono Filter.seq_monoₓ'. -/
@[mono]
theorem seq_mono {f₁ f₂ : Filter (α → β)} {g₁ g₂ : Filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁.seq g₁ ≤ f₂.seq g₂ :=
  le_seq fun s hs t ht => seq_mem_seq (hf hs) (hg ht)
#align filter.seq_mono Filter.seq_mono

#print Filter.pure_seq_eq_map /-
@[simp]
theorem pure_seq_eq_map (g : α → β) (f : Filter α) : seq (pure g) f = f.map g :=
  by
  refine' le_antisymm (le_map fun s hs => _) (le_seq fun s hs t ht => _)
  · rw [← singleton_seq]
    apply seq_mem_seq _ hs
    exact singleton_mem_pure
  · refine' sets_of_superset (map g f) (image_mem_map ht) _
    rintro b ⟨a, ha, rfl⟩
    exact ⟨g, hs, a, ha, rfl⟩
#align filter.pure_seq_eq_map Filter.pure_seq_eq_map
-/

#print Filter.seq_pure /-
@[simp]
theorem seq_pure (f : Filter (α → β)) (a : α) : seq f (pure a) = map (fun g : α → β => g a) f :=
  by
  refine' le_antisymm (le_map fun s hs => _) (le_seq fun s hs t ht => _)
  · rw [← seq_singleton]
    exact seq_mem_seq hs singleton_mem_pure
  · refine' sets_of_superset (map (fun g : α → β => g a) f) (image_mem_map hs) _
    rintro b ⟨g, hg, rfl⟩
    exact ⟨g, hg, a, ht, rfl⟩
#align filter.seq_pure Filter.seq_pure
-/

#print Filter.seq_assoc /-
@[simp]
theorem seq_assoc (x : Filter α) (g : Filter (α → β)) (h : Filter (β → γ)) :
    seq h (seq g x) = seq (seq (map (· ∘ ·) h) g) x :=
  by
  refine' le_antisymm (le_seq fun s hs t ht => _) (le_seq fun s hs t ht => _)
  · rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩
    refine' mem_of_superset _ (Set.seq_mono ((Set.seq_mono hu subset.rfl).trans hs) subset.rfl)
    rw [← Set.seq_seq]
    exact seq_mem_seq hw (seq_mem_seq hv ht)
  · rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
    refine' mem_of_superset _ (Set.seq_mono subset.rfl ht)
    rw [Set.seq_seq]
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv
#align filter.seq_assoc Filter.seq_assoc
-/

#print Filter.prod_map_seq_comm /-
theorem prod_map_seq_comm (f : Filter α) (g : Filter β) :
    (map Prod.mk f).seq g = seq (map (fun b a => (a, b)) g) f :=
  by
  refine' le_antisymm (le_seq fun s hs t ht => _) (le_seq fun s hs t ht => _)
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    refine' mem_of_superset _ (Set.seq_mono hs subset.rfl)
    rw [← Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    refine' mem_of_superset _ (Set.seq_mono hs subset.rfl)
    rw [Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
#align filter.prod_map_seq_comm Filter.prod_map_seq_comm
-/

instance : LawfulFunctor (Filter : Type u → Type u)
    where
  id_map α f := map_id
  comp_map α β γ f g a := map_map.symm

instance : LawfulApplicative (Filter : Type u → Type u)
    where
  pure_seq α β := pure_seq_eq_map
  map_pure α β := map_pure
  seq_pure α β := seq_pure
  seq_assoc α β γ := seq_assoc

instance : CommApplicative (Filter : Type u → Type u) :=
  ⟨fun α β f g => prod_map_seq_comm f g⟩

/- warning: filter.seq_eq_filter_seq -> Filter.seq_eq_filter_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : Filter.{u1} (α -> β)) (g : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} β) (Seq.seq.{u1, u1} Filter.{u1} Filter.hasSeq.{u1} α β f g) (Filter.seq.{u1, u1} α β f g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : Filter.{u1} (α -> β)) (g : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} β) (Seq.seq.{u1, u1} Filter.{u1} (Applicative.toSeq.{u1, u1} Filter.{u1} (Alternative.toApplicative.{u1, u1} Filter.{u1} Filter.instAlternativeFilter.{u1})) α β f (fun (x._@.Mathlib.Order.Filter.Basic._hyg.36231 : Unit) => g)) (Filter.seq.{u1, u1} α β f g)
Case conversion may be inaccurate. Consider using '#align filter.seq_eq_filter_seq Filter.seq_eq_filter_seqₓ'. -/
theorem seq_eq_filter_seq.{l} {α β : Type l} (f : Filter (α → β)) (g : Filter α) :
    f <*> g = seq f g :=
  rfl
#align filter.seq_eq_filter_seq Filter.seq_eq_filter_seq

end Applicative

/-! #### `bind` equations -/


section Bind

#print Filter.eventually_bind /-
@[simp]
theorem eventually_bind {f : Filter α} {m : α → Filter β} {p : β → Prop} :
    (∀ᶠ y in bind f m, p y) ↔ ∀ᶠ x in f, ∀ᶠ y in m x, p y :=
  Iff.rfl
#align filter.eventually_bind Filter.eventually_bind
-/

#print Filter.eventuallyEq_bind /-
@[simp]
theorem eventuallyEq_bind {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ =ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ =ᶠ[m x] g₂ :=
  Iff.rfl
#align filter.eventually_eq_bind Filter.eventuallyEq_bind
-/

#print Filter.eventuallyLe_bind /-
@[simp]
theorem eventuallyLe_bind [LE γ] {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ ≤ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ ≤ᶠ[m x] g₂ :=
  Iff.rfl
#align filter.eventually_le_bind Filter.eventuallyLe_bind
-/

#print Filter.mem_bind' /-
theorem mem_bind' {s : Set β} {f : Filter α} {m : α → Filter β} :
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f :=
  Iff.rfl
#align filter.mem_bind' Filter.mem_bind'
-/

/- warning: filter.mem_bind -> Filter.mem_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u2} β} {f : Filter.{u1} α} {m : α -> (Filter.{u2} β)}, Iff (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (Filter.bind.{u1, u2} α β f m)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (m x)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u2} β} {f : Filter.{u1} α} {m : α -> (Filter.{u2} β)}, Iff (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s (Filter.bind.{u1, u2} α β f m)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s (m x)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_bind Filter.mem_bindₓ'. -/
@[simp]
theorem mem_bind {s : Set β} {f : Filter α} {m : α → Filter β} :
    s ∈ bind f m ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x :=
  calc
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f := Iff.rfl
    _ ↔ ∃ t ∈ f, t ⊆ { a | s ∈ m a } := exists_mem_subset_iff.symm
    _ ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x := Iff.rfl
    
#align filter.mem_bind Filter.mem_bind

/- warning: filter.bind_le -> Filter.bind_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : α -> (Filter.{u2} β)} {l : Filter.{u2} β}, (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (g x) l) f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.bind.{u1, u2} α β f g) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : α -> (Filter.{u2} β)} {l : Filter.{u2} β}, (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (g x) l) f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.bind.{u1, u2} α β f g) l)
Case conversion may be inaccurate. Consider using '#align filter.bind_le Filter.bind_leₓ'. -/
theorem bind_le {f : Filter α} {g : α → Filter β} {l : Filter β} (h : ∀ᶠ x in f, g x ≤ l) :
    f.bind g ≤ l :=
  join_le <| eventually_map.2 h
#align filter.bind_le Filter.bind_le

/- warning: filter.bind_mono -> Filter.bind_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {g₁ : α -> (Filter.{u2} β)} {g₂ : α -> (Filter.{u2} β)}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f₁ f₂) -> (Filter.EventuallyLe.{u1, u2} α (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) f₁ g₁ g₂) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.bind.{u1, u2} α β f₁ g₁) (Filter.bind.{u1, u2} α β f₂ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {g₁ : α -> (Filter.{u2} β)} {g₂ : α -> (Filter.{u2} β)}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f₁ f₂) -> (Filter.EventuallyLe.{u1, u2} α (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) f₁ g₁ g₂) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.bind.{u1, u2} α β f₁ g₁) (Filter.bind.{u1, u2} α β f₂ g₂))
Case conversion may be inaccurate. Consider using '#align filter.bind_mono Filter.bind_monoₓ'. -/
@[mono]
theorem bind_mono {f₁ f₂ : Filter α} {g₁ g₂ : α → Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ᶠ[f₁] g₂) :
    bind f₁ g₁ ≤ bind f₂ g₂ :=
  by
  refine' le_trans (fun s hs => _) (join_mono <| map_mono hf)
  simp only [mem_join, mem_bind', mem_map] at hs⊢
  filter_upwards [hg, hs]with _ hx hs using hx hs
#align filter.bind_mono Filter.bind_mono

/- warning: filter.bind_inf_principal -> Filter.bind_inf_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : α -> (Filter.{u2} β)} {s : Set.{u2} β}, Eq.{succ u2} (Filter.{u2} β) (Filter.bind.{u1, u2} α β f (fun (x : α) => HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (g x) (Filter.principal.{u2} β s))) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.bind.{u1, u2} α β f g) (Filter.principal.{u2} β s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : α -> (Filter.{u2} β)} {s : Set.{u2} β}, Eq.{succ u2} (Filter.{u2} β) (Filter.bind.{u1, u2} α β f (fun (x : α) => HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) (g x) (Filter.principal.{u2} β s))) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) (Filter.bind.{u1, u2} α β f g) (Filter.principal.{u2} β s))
Case conversion may be inaccurate. Consider using '#align filter.bind_inf_principal Filter.bind_inf_principalₓ'. -/
theorem bind_inf_principal {f : Filter α} {g : α → Filter β} {s : Set β} :
    (f.bind fun x => g x ⊓ 𝓟 s) = f.bind g ⊓ 𝓟 s :=
  Filter.ext fun s => by simp only [mem_bind, mem_inf_principal]
#align filter.bind_inf_principal Filter.bind_inf_principal

/- warning: filter.sup_bind -> Filter.sup_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {h : α -> (Filter.{u2} β)}, Eq.{succ u2} (Filter.{u2} β) (Filter.bind.{u1, u2} α β (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g) h) (HasSup.sup.{u2} (Filter.{u2} β) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} β) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))))) (Filter.bind.{u1, u2} α β f h) (Filter.bind.{u1, u2} α β g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u1} α} {h : α -> (Filter.{u2} β)}, Eq.{succ u2} (Filter.{u2} β) (Filter.bind.{u1, u2} α β (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) f g) h) (HasSup.sup.{u2} (Filter.{u2} β) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} β) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} β) (CompleteLattice.toLattice.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)))) (Filter.bind.{u1, u2} α β f h) (Filter.bind.{u1, u2} α β g h))
Case conversion may be inaccurate. Consider using '#align filter.sup_bind Filter.sup_bindₓ'. -/
theorem sup_bind {f g : Filter α} {h : α → Filter β} : bind (f ⊔ g) h = bind f h ⊔ bind g h := by
  simp only [bind, sup_join, map_sup, eq_self_iff_true]
#align filter.sup_bind Filter.sup_bind

/- warning: filter.principal_bind -> Filter.principal_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> (Filter.{u2} β)}, Eq.{succ u2} (Filter.{u2} β) (Filter.bind.{u1, u2} α β (Filter.principal.{u1} α s) f) (supᵢ.{u2, succ u1} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasSup.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) α (fun (x : α) => supᵢ.{u2, 0} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasSup.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> (Filter.{u2} β)}, Eq.{succ u2} (Filter.{u2} β) (Filter.bind.{u1, u2} α β (Filter.principal.{u1} α s) f) (supᵢ.{u2, succ u1} (Filter.{u2} β) (CompleteLattice.toSupSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) α (fun (x : α) => supᵢ.{u2, 0} (Filter.{u2} β) (CompleteLattice.toSupSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => f x)))
Case conversion may be inaccurate. Consider using '#align filter.principal_bind Filter.principal_bindₓ'. -/
theorem principal_bind {s : Set α} {f : α → Filter β} : bind (𝓟 s) f = ⨆ x ∈ s, f x :=
  show join (map f (𝓟 s)) = ⨆ x ∈ s, f x by
    simp only [supₛ_image, join_principal_eq_Sup, map_principal, eq_self_iff_true]
#align filter.principal_bind Filter.principal_bind

end Bind

section ListTraverse

/- This is a separate section in order to open `list`, but mostly because of universe
   equality requirements in `traverse` -/
open List

/- warning: filter.sequence_mono -> Filter.sequence_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (as : List.{u1} (Filter.{u1} α)) (bs : List.{u1} (Filter.{u1} α)), (List.Forall₂.{u1, u1} (Filter.{u1} α) (Filter.{u1} α) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) as bs) -> (LE.le.{u1} (Filter.{u1} (List.{u1} α)) (Preorder.toLE.{u1} (Filter.{u1} (List.{u1} α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (List.{u1} α)) (Filter.partialOrder.{u1} (List.{u1} α)))) (sequence.{u1} List.{u1} α Filter.{u1} Filter.applicative.{u1} List.traversable.{u1} as) (sequence.{u1} List.{u1} α Filter.{u1} Filter.applicative.{u1} List.traversable.{u1} bs))
but is expected to have type
  forall {α : Type.{u1}} (as : List.{u1} (Filter.{u1} α)) (bs : List.{u1} (Filter.{u1} α)), (List.Forall₂.{u1, u1} (Filter.{u1} α) (Filter.{u1} α) (fun (x._@.Mathlib.Order.Filter.Basic._hyg.37086 : Filter.{u1} α) (x._@.Mathlib.Order.Filter.Basic._hyg.37088 : Filter.{u1} α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x._@.Mathlib.Order.Filter.Basic._hyg.37086 x._@.Mathlib.Order.Filter.Basic._hyg.37088) as bs) -> (LE.le.{u1} (Filter.{u1} (List.{u1} α)) (Preorder.toLE.{u1} (Filter.{u1} (List.{u1} α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (List.{u1} α)) (Filter.instPartialOrderFilter.{u1} (List.{u1} α)))) (sequence.{u1} List.{u1} α Filter.{u1} (Alternative.toApplicative.{u1, u1} Filter.{u1} Filter.instAlternativeFilter.{u1}) instTraversableList.{u1} as) (sequence.{u1} List.{u1} α Filter.{u1} (Alternative.toApplicative.{u1, u1} Filter.{u1} Filter.instAlternativeFilter.{u1}) instTraversableList.{u1} bs))
Case conversion may be inaccurate. Consider using '#align filter.sequence_mono Filter.sequence_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sequence_mono : ∀ as bs : List (Filter α), Forall₂ (· ≤ ·) as bs → sequence as ≤ sequence bs
  | [], [], forall₂.nil => le_rfl
  | a::as, b::bs, forall₂.cons h hs => seq_mono (map_mono h) (sequence_mono as bs hs)
#align filter.sequence_mono Filter.sequence_mono

variable {α' β' γ' : Type u} {f : β' → Filter α'} {s : γ' → Set α'}

/- warning: filter.mem_traverse -> Filter.mem_traverse is a dubious translation:
lean 3 declaration is
  forall {α' : Type.{u1}} {β' : Type.{u1}} {γ' : Type.{u1}} {f : β' -> (Filter.{u1} α')} {s : γ' -> (Set.{u1} α')} (fs : List.{u1} β') (us : List.{u1} γ'), (List.Forall₂.{u1, u1} β' γ' (fun (b : β') (c : γ') => Membership.Mem.{u1, u1} (Set.{u1} α') (Filter.{u1} α') (Filter.hasMem.{u1} α') (s c) (f b)) fs us) -> (Membership.Mem.{u1, u1} (Set.{u1} (List.{u1} α')) (Filter.{u1} (List.{u1} α')) (Filter.hasMem.{u1} (List.{u1} α')) (Traversable.traverse.{u1} (fun {γ' : Type.{u1}} => List.{u1} γ') List.traversable.{u1} Set.{u1} (Monad.toApplicative.{u1, u1} Set.{u1} Set.monad.{u1}) γ' α' s us) (Traversable.traverse.{u1} (fun {β' : Type.{u1}} => List.{u1} β') List.traversable.{u1} Filter.{u1} Filter.applicative.{u1} β' α' f fs))
but is expected to have type
  forall {α' : Type.{u1}} {β' : Type.{u1}} {γ' : Type.{u1}} {f : β' -> (Filter.{u1} α')} {s : γ' -> (Set.{u1} α')} (fs : List.{u1} β') (us : List.{u1} γ'), (List.Forall₂.{u1, u1} β' γ' (fun (b : β') (c : γ') => Membership.mem.{u1, u1} (Set.{u1} α') (Filter.{u1} α') (instMembershipSetFilter.{u1} α') (s c) (f b)) fs us) -> (Membership.mem.{u1, u1} (Set.{u1} (List.{u1} α')) (Filter.{u1} (List.{u1} α')) (instMembershipSetFilter.{u1} (List.{u1} α')) (Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} Set.{u1} (Alternative.toApplicative.{u1, u1} Set.{u1} Set.instAlternativeSet.{u1}) γ' α' s us) (Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} Filter.{u1} (Alternative.toApplicative.{u1, u1} Filter.{u1} Filter.instAlternativeFilter.{u1}) β' α' f fs))
Case conversion may be inaccurate. Consider using '#align filter.mem_traverse Filter.mem_traverseₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_traverse :
    ∀ (fs : List β') (us : List γ'),
      Forall₂ (fun b c => s c ∈ f b) fs us → traverse s us ∈ traverse f fs
  | [], [], forall₂.nil => mem_pure.2 <| mem_singleton _
  | f::fs, u::us, forall₂.cons h hs => seq_mem_seq (image_mem_map h) (mem_traverse fs us hs)
#align filter.mem_traverse Filter.mem_traverse

/- warning: filter.mem_traverse_iff -> Filter.mem_traverse_iff is a dubious translation:
lean 3 declaration is
  forall {α' : Type.{u1}} {β' : Type.{u1}} {f : β' -> (Filter.{u1} α')} (fs : List.{u1} β') (t : Set.{u1} (List.{u1} α')), Iff (Membership.Mem.{u1, u1} (Set.{u1} (List.{u1} α')) (Filter.{u1} (List.{u1} α')) (Filter.hasMem.{u1} (List.{u1} α')) t (Traversable.traverse.{u1} (fun {β' : Type.{u1}} => List.{u1} β') List.traversable.{u1} Filter.{u1} Filter.applicative.{u1} β' α' f fs)) (Exists.{succ u1} (List.{u1} (Set.{u1} α')) (fun (us : List.{u1} (Set.{u1} α')) => And (List.Forall₂.{u1, u1} β' (Set.{u1} α') (fun (b : β') (s : Set.{u1} α') => Membership.Mem.{u1, u1} (Set.{u1} α') (Filter.{u1} α') (Filter.hasMem.{u1} α') s (f b)) fs us) (HasSubset.Subset.{u1} (Set.{u1} (List.{u1} α')) (Set.hasSubset.{u1} (List.{u1} α')) (sequence.{u1} List.{u1} α' Set.{u1} (Monad.toApplicative.{u1, u1} Set.{u1} Set.monad.{u1}) List.traversable.{u1} us) t)))
but is expected to have type
  forall {α' : Type.{u1}} {β' : Type.{u1}} {f : β' -> (Filter.{u1} α')} (fs : List.{u1} β') (t : Set.{u1} (List.{u1} α')), Iff (Membership.mem.{u1, u1} (Set.{u1} (List.{u1} α')) (Filter.{u1} (List.{u1} α')) (instMembershipSetFilter.{u1} (List.{u1} α')) t (Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} Filter.{u1} (Alternative.toApplicative.{u1, u1} Filter.{u1} Filter.instAlternativeFilter.{u1}) β' α' f fs)) (Exists.{succ u1} (List.{u1} (Set.{u1} α')) (fun (us : List.{u1} (Set.{u1} α')) => And (List.Forall₂.{u1, u1} β' (Set.{u1} α') (fun (b : β') (s : Set.{u1} α') => Membership.mem.{u1, u1} (Set.{u1} α') (Filter.{u1} α') (instMembershipSetFilter.{u1} α') s (f b)) fs us) (HasSubset.Subset.{u1} (Set.{u1} (List.{u1} α')) (Set.instHasSubsetSet.{u1} (List.{u1} α')) (sequence.{u1} List.{u1} α' Set.{u1} (Alternative.toApplicative.{u1, u1} Set.{u1} Set.instAlternativeSet.{u1}) instTraversableList.{u1} us) t)))
Case conversion may be inaccurate. Consider using '#align filter.mem_traverse_iff Filter.mem_traverse_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_traverse_iff (fs : List β') (t : Set (List α')) :
    t ∈ traverse f fs ↔
      ∃ us : List (Set α'), Forall₂ (fun b (s : Set α') => s ∈ f b) fs us ∧ sequence us ⊆ t :=
  by
  constructor
  · induction fs generalizing t
    case nil =>
      simp only [sequence, mem_pure, imp_self, forall₂_nil_left_iff, exists_eq_left, Set.pure_def,
        singleton_subset_iff, traverse_nil]
    case cons b fs ih t =>
      intro ht
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
      rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hwu⟩
      rcases ih v hv with ⟨us, hus, hu⟩
      exact ⟨w::us, forall₂.cons hw hus, (Set.seq_mono hwu hu).trans ht⟩
  · rintro ⟨us, hus, hs⟩
    exact mem_of_superset (mem_traverse _ _ hus) hs
#align filter.mem_traverse_iff Filter.mem_traverse_iff

end ListTraverse

/-! ### Limits -/


#print Filter.Tendsto /-
/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
@[pp_nodot]
def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂
#align filter.tendsto Filter.Tendsto
-/

#print Filter.tendsto_def /-
theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl
#align filter.tendsto_def Filter.tendsto_def
-/

#print Filter.tendsto_iff_eventually /-
theorem tendsto_iff_eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ ⦃p : β → Prop⦄, (∀ᶠ y in l₂, p y) → ∀ᶠ x in l₁, p (f x) :=
  Iff.rfl
#align filter.tendsto_iff_eventually Filter.tendsto_iff_eventually
-/

#print Filter.Tendsto.eventually /-
theorem Tendsto.eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∀ᶠ y in l₂, p y) : ∀ᶠ x in l₁, p (f x) :=
  hf h
#align filter.tendsto.eventually Filter.Tendsto.eventually
-/

#print Filter.Tendsto.frequently /-
theorem Tendsto.frequently {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∃ᶠ x in l₁, p (f x)) : ∃ᶠ y in l₂, p y :=
  mt hf.Eventually h
#align filter.tendsto.frequently Filter.Tendsto.frequently
-/

#print Filter.Tendsto.frequently_map /-
theorem Tendsto.frequently_map {l₁ : Filter α} {l₂ : Filter β} {p : α → Prop} {q : β → Prop}
    (f : α → β) (c : Filter.Tendsto f l₁ l₂) (w : ∀ x, p x → q (f x)) (h : ∃ᶠ x in l₁, p x) :
    ∃ᶠ y in l₂, q y :=
  c.Frequently (h.mono w)
#align filter.tendsto.frequently_map Filter.Tendsto.frequently_map
-/

/- warning: filter.tendsto_bot -> Filter.tendsto_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : Filter.{u2} β}, Filter.Tendsto.{u1, u2} α β f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) l
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : Filter.{u2} β}, Filter.Tendsto.{u1, u2} α β f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) l
Case conversion may be inaccurate. Consider using '#align filter.tendsto_bot Filter.tendsto_botₓ'. -/
@[simp]
theorem tendsto_bot {f : α → β} {l : Filter β} : Tendsto f ⊥ l := by simp [tendsto]
#align filter.tendsto_bot Filter.tendsto_bot

/- warning: filter.tendsto_top -> Filter.tendsto_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : Filter.{u1} α}, Filter.Tendsto.{u1, u2} α β f l (Top.top.{u2} (Filter.{u2} β) (Filter.hasTop.{u2} β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : Filter.{u1} α}, Filter.Tendsto.{u1, u2} α β f l (Top.top.{u2} (Filter.{u2} β) (Filter.instTopFilter.{u2} β))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_top Filter.tendsto_topₓ'. -/
@[simp]
theorem tendsto_top {f : α → β} {l : Filter α} : Tendsto f l ⊤ :=
  le_top
#align filter.tendsto_top Filter.tendsto_top

/- warning: filter.le_map_of_right_inverse -> Filter.le_map_of_right_inverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mab : α -> β} {mba : β -> α} {f : Filter.{u1} α} {g : Filter.{u2} β}, (Filter.EventuallyEq.{u2, u2} β β g (Function.comp.{succ u2, succ u1, succ u2} β α β mab mba) (id.{succ u2} β)) -> (Filter.Tendsto.{u2, u1} β α mba g f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) g (Filter.map.{u1, u2} α β mab f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {mab : α -> β} {mba : β -> α} {f : Filter.{u1} α} {g : Filter.{u2} β}, (Filter.EventuallyEq.{u2, u2} β β g (Function.comp.{succ u2, succ u1, succ u2} β α β mab mba) (id.{succ u2} β)) -> (Filter.Tendsto.{u2, u1} β α mba g f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) g (Filter.map.{u1, u2} α β mab f))
Case conversion may be inaccurate. Consider using '#align filter.le_map_of_right_inverse Filter.le_map_of_right_inverseₓ'. -/
theorem le_map_of_right_inverse {mab : α → β} {mba : β → α} {f : Filter α} {g : Filter β}
    (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : Tendsto mba g f) : g ≤ map mab f :=
  by
  rw [← @map_id _ g, ← map_congr h₁, ← map_map]
  exact map_mono h₂
#align filter.le_map_of_right_inverse Filter.le_map_of_right_inverse

#print Filter.tendsto_of_isEmpty /-
theorem tendsto_of_isEmpty [IsEmpty α] {f : α → β} {la : Filter α} {lb : Filter β} :
    Tendsto f la lb := by simp only [filter_eq_bot_of_is_empty la, tendsto_bot]
#align filter.tendsto_of_is_empty Filter.tendsto_of_isEmpty
-/

#print Filter.eventuallyEq_of_left_inv_of_right_inv /-
theorem eventuallyEq_of_left_inv_of_right_inv {f : α → β} {g₁ g₂ : β → α} {fa : Filter α}
    {fb : Filter β} (hleft : ∀ᶠ x in fa, g₁ (f x) = x) (hright : ∀ᶠ y in fb, f (g₂ y) = y)
    (htendsto : Tendsto g₂ fb fa) : g₁ =ᶠ[fb] g₂ :=
  (htendsto.Eventually hleft).mp <| hright.mono fun y hr hl => (congr_arg g₁ hr.symm).trans hl
#align filter.eventually_eq_of_left_inv_of_right_inv Filter.eventuallyEq_of_left_inv_of_right_inv
-/

/- warning: filter.tendsto_iff_comap -> Filter.tendsto_iff_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} α β f l₁ l₂) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l₁ (Filter.comap.{u1, u2} α β f l₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} α β f l₁ l₂) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l₁ (Filter.comap.{u1, u2} α β f l₂))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_iff_comap Filter.tendsto_iff_comapₓ'. -/
theorem tendsto_iff_comap {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
  map_le_iff_le_comap
#align filter.tendsto_iff_comap Filter.tendsto_iff_comap

/- warning: filter.tendsto.le_comap -> Filter.Tendsto.le_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f l₁ l₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l₁ (Filter.comap.{u1, u2} α β f l₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f l₁ l₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l₁ (Filter.comap.{u1, u2} α β f l₂))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.le_comap Filter.Tendsto.le_comapₓ'. -/
alias tendsto_iff_comap ↔ tendsto.le_comap _
#align filter.tendsto.le_comap Filter.Tendsto.le_comap

/- warning: filter.tendsto.disjoint -> Filter.Tendsto.disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {la₁ : Filter.{u1} α} {la₂ : Filter.{u1} α} {lb₁ : Filter.{u2} β} {lb₂ : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f la₁ lb₁) -> (Disjoint.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) lb₁ lb₂) -> (Filter.Tendsto.{u1, u2} α β f la₂ lb₂) -> (Disjoint.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) la₁ la₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {la₁ : Filter.{u1} α} {la₂ : Filter.{u1} α} {lb₁ : Filter.{u2} β} {lb₂ : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f la₁ lb₁) -> (Disjoint.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) lb₁ lb₂) -> (Filter.Tendsto.{u1, u2} α β f la₂ lb₂) -> (Disjoint.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α) (BoundedOrder.toOrderBot.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (CompleteLattice.toBoundedOrder.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) la₁ la₂)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.disjoint Filter.Tendsto.disjointₓ'. -/
protected theorem Tendsto.disjoint {f : α → β} {la₁ la₂ : Filter α} {lb₁ lb₂ : Filter β}
    (h₁ : Tendsto f la₁ lb₁) (hd : Disjoint lb₁ lb₂) (h₂ : Tendsto f la₂ lb₂) : Disjoint la₁ la₂ :=
  (disjoint_comap hd).mono h₁.le_comap h₂.le_comap
#align filter.tendsto.disjoint Filter.Tendsto.disjoint

#print Filter.tendsto_congr' /-
theorem tendsto_congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ := by rw [tendsto, tendsto, map_congr hl]
#align filter.tendsto_congr' Filter.tendsto_congr'
-/

#print Filter.Tendsto.congr' /-
theorem Tendsto.congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
    (h : Tendsto f₁ l₁ l₂) : Tendsto f₂ l₁ l₂ :=
  (tendsto_congr' hl).1 h
#align filter.tendsto.congr' Filter.Tendsto.congr'
-/

#print Filter.tendsto_congr /-
theorem tendsto_congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ :=
  tendsto_congr' (univ_mem' h)
#align filter.tendsto_congr Filter.tendsto_congr
-/

#print Filter.Tendsto.congr /-
theorem Tendsto.congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂ :=
  (tendsto_congr h).1
#align filter.tendsto.congr Filter.Tendsto.congr
-/

/- warning: filter.tendsto_id' -> Filter.tendsto_id' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : Filter.{u1} α} {y : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u1} α α (id.{succ u1} α) x y) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) x y)
but is expected to have type
  forall {α : Type.{u1}} {x : Filter.{u1} α} {y : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u1} α α (id.{succ u1} α) x y) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) x y)
Case conversion may be inaccurate. Consider using '#align filter.tendsto_id' Filter.tendsto_id'ₓ'. -/
theorem tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x ≤ y :=
  Iff.rfl
#align filter.tendsto_id' Filter.tendsto_id'

#print Filter.tendsto_id /-
theorem tendsto_id {x : Filter α} : Tendsto id x x :=
  le_refl x
#align filter.tendsto_id Filter.tendsto_id
-/

#print Filter.Tendsto.comp /-
theorem Tendsto.comp {f : α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ}
    (hg : Tendsto g y z) (hf : Tendsto f x y) : Tendsto (g ∘ f) x z := fun s hs => hf (hg hs)
#align filter.tendsto.comp Filter.Tendsto.comp
-/

/- warning: filter.tendsto.mono_left -> Filter.Tendsto.mono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : Filter.{u1} α} {y : Filter.{u1} α} {z : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x z) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) y x) -> (Filter.Tendsto.{u1, u2} α β f y z)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : Filter.{u1} α} {y : Filter.{u1} α} {z : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x z) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) y x) -> (Filter.Tendsto.{u1, u2} α β f y z)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.mono_left Filter.Tendsto.mono_leftₓ'. -/
theorem Tendsto.mono_left {f : α → β} {x y : Filter α} {z : Filter β} (hx : Tendsto f x z)
    (h : y ≤ x) : Tendsto f y z :=
  (map_mono h).trans hx
#align filter.tendsto.mono_left Filter.Tendsto.mono_left

/- warning: filter.tendsto.mono_right -> Filter.Tendsto.mono_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : Filter.{u1} α} {y : Filter.{u2} β} {z : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x y) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) y z) -> (Filter.Tendsto.{u1, u2} α β f x z)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : Filter.{u1} α} {y : Filter.{u2} β} {z : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x y) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) y z) -> (Filter.Tendsto.{u1, u2} α β f x z)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.mono_right Filter.Tendsto.mono_rightₓ'. -/
theorem Tendsto.mono_right {f : α → β} {x : Filter α} {y z : Filter β} (hy : Tendsto f x y)
    (hz : y ≤ z) : Tendsto f x z :=
  le_trans hy hz
#align filter.tendsto.mono_right Filter.Tendsto.mono_right

#print Filter.Tendsto.neBot /-
theorem Tendsto.neBot {f : α → β} {x : Filter α} {y : Filter β} (h : Tendsto f x y) [hx : NeBot x] :
    NeBot y :=
  (hx.map _).mono h
#align filter.tendsto.ne_bot Filter.Tendsto.neBot
-/

#print Filter.tendsto_map /-
theorem tendsto_map {f : α → β} {x : Filter α} : Tendsto f x (map f x) :=
  le_refl (map f x)
#align filter.tendsto_map Filter.tendsto_map
-/

#print Filter.tendsto_map' /-
theorem tendsto_map' {f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ}
    (h : Tendsto (f ∘ g) x y) : Tendsto f (map g x) y := by rwa [tendsto, map_map]
#align filter.tendsto_map' Filter.tendsto_map'
-/

#print Filter.tendsto_map'_iff /-
@[simp]
theorem tendsto_map'_iff {f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ} :
    Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y :=
  by
  rw [tendsto, map_map]
  rfl
#align filter.tendsto_map'_iff Filter.tendsto_map'_iff
-/

#print Filter.tendsto_comap /-
theorem tendsto_comap {f : α → β} {x : Filter β} : Tendsto f (comap f x) x :=
  map_comap_le
#align filter.tendsto_comap Filter.tendsto_comap
-/

#print Filter.tendsto_comap_iff /-
@[simp]
theorem tendsto_comap_iff {f : α → β} {g : β → γ} {a : Filter α} {c : Filter γ} :
    Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c :=
  ⟨fun h => tendsto_comap.comp h, fun h => map_le_iff_le_comap.mp <| by rwa [map_map]⟩
#align filter.tendsto_comap_iff Filter.tendsto_comap_iff
-/

#print Filter.tendsto_comap'_iff /-
theorem tendsto_comap'_iff {m : α → β} {f : Filter α} {g : Filter β} {i : γ → α} (h : range i ∈ f) :
    Tendsto (m ∘ i) (comap i f) g ↔ Tendsto m f g :=
  by
  rw [tendsto, ← map_compose]
  simp only [(· ∘ ·), map_comap_of_mem h, tendsto]
#align filter.tendsto_comap'_iff Filter.tendsto_comap'_iff
-/

/- warning: filter.tendsto.of_tendsto_comp -> Filter.Tendsto.of_tendsto_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : β -> γ} {a : Filter.{u1} α} {b : Filter.{u2} β} {c : Filter.{u3} γ}, (Filter.Tendsto.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) a c) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.comap.{u2, u3} β γ g c) b) -> (Filter.Tendsto.{u1, u2} α β f a b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : β -> γ} {a : Filter.{u1} α} {b : Filter.{u2} β} {c : Filter.{u3} γ}, (Filter.Tendsto.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) a c) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.comap.{u2, u3} β γ g c) b) -> (Filter.Tendsto.{u1, u2} α β f a b)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.of_tendsto_comp Filter.Tendsto.of_tendsto_compₓ'. -/
theorem Tendsto.of_tendsto_comp {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ}
    (hfg : Tendsto (g ∘ f) a c) (hg : comap g c ≤ b) : Tendsto f a b :=
  by
  rw [tendsto_iff_comap] at hfg⊢
  calc
    a ≤ comap (g ∘ f) c := hfg
    _ ≤ comap f b := by simpa [comap_comap] using comap_mono hg
    
#align filter.tendsto.of_tendsto_comp Filter.Tendsto.of_tendsto_comp

#print Filter.comap_eq_of_inverse /-
theorem comap_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : ψ ∘ φ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : comap φ g = f :=
  by
  refine' ((comap_mono <| map_le_iff_le_comap.1 hψ).trans _).antisymm (map_le_iff_le_comap.1 hφ)
  rw [comap_comap, Eq, comap_id]
  exact le_rfl
#align filter.comap_eq_of_inverse Filter.comap_eq_of_inverse
-/

#print Filter.map_eq_of_inverse /-
theorem map_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : φ ∘ ψ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : map φ f = g :=
  by
  refine' le_antisymm hφ (le_trans _ (map_mono hψ))
  rw [map_map, Eq, map_id]
  exact le_rfl
#align filter.map_eq_of_inverse Filter.map_eq_of_inverse
-/

/- warning: filter.tendsto_inf -> Filter.tendsto_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : Filter.{u1} α} {y₁ : Filter.{u2} β} {y₂ : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} α β f x (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) y₁ y₂)) (And (Filter.Tendsto.{u1, u2} α β f x y₁) (Filter.Tendsto.{u1, u2} α β f x y₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : Filter.{u1} α} {y₁ : Filter.{u2} β} {y₂ : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} α β f x (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) y₁ y₂)) (And (Filter.Tendsto.{u1, u2} α β f x y₁) (Filter.Tendsto.{u1, u2} α β f x y₂))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_inf Filter.tendsto_infₓ'. -/
theorem tendsto_inf {f : α → β} {x : Filter α} {y₁ y₂ : Filter β} :
    Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂ := by
  simp only [tendsto, le_inf_iff, iff_self_iff]
#align filter.tendsto_inf Filter.tendsto_inf

/- warning: filter.tendsto_inf_left -> Filter.tendsto_inf_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x₁ y) -> (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) x₁ x₂) y)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x₁ y) -> (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) x₁ x₂) y)
Case conversion may be inaccurate. Consider using '#align filter.tendsto_inf_left Filter.tendsto_inf_leftₓ'. -/
theorem tendsto_inf_left {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₁ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_left) h
#align filter.tendsto_inf_left Filter.tendsto_inf_left

/- warning: filter.tendsto_inf_right -> Filter.tendsto_inf_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x₂ y) -> (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) x₁ x₂) y)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x₂ y) -> (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) x₁ x₂) y)
Case conversion may be inaccurate. Consider using '#align filter.tendsto_inf_right Filter.tendsto_inf_rightₓ'. -/
theorem tendsto_inf_right {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₂ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_right) h
#align filter.tendsto_inf_right Filter.tendsto_inf_right

/- warning: filter.tendsto.inf -> Filter.Tendsto.inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y₁ : Filter.{u2} β} {y₂ : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x₁ y₁) -> (Filter.Tendsto.{u1, u2} α β f x₂ y₂) -> (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) x₁ x₂) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) y₁ y₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y₁ : Filter.{u2} β} {y₂ : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x₁ y₁) -> (Filter.Tendsto.{u1, u2} α β f x₂ y₂) -> (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) x₁ x₂) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) y₁ y₂))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.inf Filter.Tendsto.infₓ'. -/
theorem Tendsto.inf {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β} (h₁ : Tendsto f x₁ y₁)
    (h₂ : Tendsto f x₂ y₂) : Tendsto f (x₁ ⊓ x₂) (y₁ ⊓ y₂) :=
  tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩
#align filter.tendsto.inf Filter.Tendsto.inf

/- warning: filter.tendsto_infi -> Filter.tendsto_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {x : Filter.{u1} α} {y : ι -> (Filter.{u2} β)}, Iff (Filter.Tendsto.{u1, u2} α β f x (infᵢ.{u2, u3} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) ι (fun (i : ι) => y i))) (forall (i : ι), Filter.Tendsto.{u1, u2} α β f x (y i))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {x : Filter.{u1} α} {y : ι -> (Filter.{u2} β)}, Iff (Filter.Tendsto.{u1, u2} α β f x (infᵢ.{u2, u3} (Filter.{u2} β) (CompleteLattice.toInfSet.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β)) ι (fun (i : ι) => y i))) (forall (i : ι), Filter.Tendsto.{u1, u2} α β f x (y i))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_infi Filter.tendsto_infᵢₓ'. -/
@[simp]
theorem tendsto_infᵢ {f : α → β} {x : Filter α} {y : ι → Filter β} :
    Tendsto f x (⨅ i, y i) ↔ ∀ i, Tendsto f x (y i) := by
  simp only [tendsto, iff_self_iff, le_infᵢ_iff]
#align filter.tendsto_infi Filter.tendsto_infᵢ

/- warning: filter.tendsto_infi' -> Filter.tendsto_infᵢ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {x : ι -> (Filter.{u1} α)} {y : Filter.{u2} β} (i : ι), (Filter.Tendsto.{u1, u2} α β f (x i) y) -> (Filter.Tendsto.{u1, u2} α β f (infᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => x i)) y)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {x : ι -> (Filter.{u1} α)} {y : Filter.{u2} β} (i : ι), (Filter.Tendsto.{u1, u2} α β f (x i) y) -> (Filter.Tendsto.{u1, u2} α β f (infᵢ.{u1, u3} (Filter.{u1} α) (CompleteLattice.toInfSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => x i)) y)
Case conversion may be inaccurate. Consider using '#align filter.tendsto_infi' Filter.tendsto_infᵢ'ₓ'. -/
theorem tendsto_infᵢ' {f : α → β} {x : ι → Filter α} {y : Filter β} (i : ι)
    (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y :=
  hi.mono_left <| infᵢ_le _ _
#align filter.tendsto_infi' Filter.tendsto_infᵢ'

/- warning: filter.tendsto_sup -> Filter.tendsto_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} α β f (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) x₁ x₂) y) (And (Filter.Tendsto.{u1, u2} α β f x₁ y) (Filter.Tendsto.{u1, u2} α β f x₂ y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} α β f (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) x₁ x₂) y) (And (Filter.Tendsto.{u1, u2} α β f x₁ y) (Filter.Tendsto.{u1, u2} α β f x₂ y))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_sup Filter.tendsto_supₓ'. -/
@[simp]
theorem tendsto_sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y := by
  simp only [tendsto, map_sup, sup_le_iff]
#align filter.tendsto_sup Filter.tendsto_sup

/- warning: filter.tendsto.sup -> Filter.Tendsto.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x₁ y) -> (Filter.Tendsto.{u1, u2} α β f x₂ y) -> (Filter.Tendsto.{u1, u2} α β f (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) x₁ x₂) y)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x₁ : Filter.{u1} α} {x₂ : Filter.{u1} α} {y : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f x₁ y) -> (Filter.Tendsto.{u1, u2} α β f x₂ y) -> (Filter.Tendsto.{u1, u2} α β f (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) x₁ x₂) y)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.sup Filter.Tendsto.supₓ'. -/
theorem Tendsto.sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f x₁ y → Tendsto f x₂ y → Tendsto f (x₁ ⊔ x₂) y := fun h₁ h₂ => tendsto_sup.mpr ⟨h₁, h₂⟩
#align filter.tendsto.sup Filter.Tendsto.sup

/- warning: filter.tendsto_supr -> Filter.tendsto_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {x : ι -> (Filter.{u1} α)} {y : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} α β f (supᵢ.{u1, u3} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => x i)) y) (forall (i : ι), Filter.Tendsto.{u1, u2} α β f (x i) y)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {x : ι -> (Filter.{u1} α)} {y : Filter.{u2} β}, Iff (Filter.Tendsto.{u1, u2} α β f (supᵢ.{u1, u3} (Filter.{u1} α) (CompleteLattice.toSupSet.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)) ι (fun (i : ι) => x i)) y) (forall (i : ι), Filter.Tendsto.{u1, u2} α β f (x i) y)
Case conversion may be inaccurate. Consider using '#align filter.tendsto_supr Filter.tendsto_supᵢₓ'. -/
@[simp]
theorem tendsto_supᵢ {f : α → β} {x : ι → Filter α} {y : Filter β} :
    Tendsto f (⨆ i, x i) y ↔ ∀ i, Tendsto f (x i) y := by simp only [tendsto, map_supᵢ, supᵢ_le_iff]
#align filter.tendsto_supr Filter.tendsto_supᵢ

#print Filter.tendsto_principal /-
@[simp]
theorem tendsto_principal {f : α → β} {l : Filter α} {s : Set β} :
    Tendsto f l (𝓟 s) ↔ ∀ᶠ a in l, f a ∈ s := by
  simp only [tendsto, le_principal_iff, mem_map', Filter.Eventually]
#align filter.tendsto_principal Filter.tendsto_principal
-/

#print Filter.tendsto_principal_principal /-
@[simp]
theorem tendsto_principal_principal {f : α → β} {s : Set α} {t : Set β} :
    Tendsto f (𝓟 s) (𝓟 t) ↔ ∀ a ∈ s, f a ∈ t := by
  simp only [tendsto_principal, eventually_principal]
#align filter.tendsto_principal_principal Filter.tendsto_principal_principal
-/

#print Filter.tendsto_pure /-
@[simp]
theorem tendsto_pure {f : α → β} {a : Filter α} {b : β} :
    Tendsto f a (pure b) ↔ ∀ᶠ x in a, f x = b := by
  simp only [tendsto, le_pure_iff, mem_map', mem_singleton_iff, Filter.Eventually]
#align filter.tendsto_pure Filter.tendsto_pure
-/

#print Filter.tendsto_pure_pure /-
theorem tendsto_pure_pure (f : α → β) (a : α) : Tendsto f (pure a) (pure (f a)) :=
  tendsto_pure.2 rfl
#align filter.tendsto_pure_pure Filter.tendsto_pure_pure
-/

#print Filter.tendsto_const_pure /-
theorem tendsto_const_pure {a : Filter α} {b : β} : Tendsto (fun x => b) a (pure b) :=
  tendsto_pure.2 <| univ_mem' fun _ => rfl
#align filter.tendsto_const_pure Filter.tendsto_const_pure
-/

/- warning: filter.pure_le_iff -> Filter.pure_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {l : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => Filter.{u1} α) Filter.hasPure.{u1} α a) l) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {l : Filter.{u1} α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a) l) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s l) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align filter.pure_le_iff Filter.pure_le_iffₓ'. -/
theorem pure_le_iff {a : α} {l : Filter α} : pure a ≤ l ↔ ∀ s ∈ l, a ∈ s :=
  Iff.rfl
#align filter.pure_le_iff Filter.pure_le_iff

#print Filter.tendsto_pure_left /-
theorem tendsto_pure_left {f : α → β} {a : α} {l : Filter β} :
    Tendsto f (pure a) l ↔ ∀ s ∈ l, f a ∈ s :=
  Iff.rfl
#align filter.tendsto_pure_left Filter.tendsto_pure_left
-/

/- warning: filter.map_inf_principal_preimage -> Filter.map_inf_principal_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β} {l : Filter.{u1} α}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l (Filter.principal.{u1} α (Set.preimage.{u1, u2} α β f s)))) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) (Filter.map.{u1, u2} α β f l) (Filter.principal.{u2} β s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β} {l : Filter.{u1} α}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l (Filter.principal.{u1} α (Set.preimage.{u1, u2} α β f s)))) (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) (Filter.map.{u1, u2} α β f l) (Filter.principal.{u2} β s))
Case conversion may be inaccurate. Consider using '#align filter.map_inf_principal_preimage Filter.map_inf_principal_preimageₓ'. -/
@[simp]
theorem map_inf_principal_preimage {f : α → β} {s : Set β} {l : Filter α} :
    map f (l ⊓ 𝓟 (f ⁻¹' s)) = map f l ⊓ 𝓟 s :=
  Filter.ext fun t => by simp only [mem_map', mem_inf_principal, mem_set_of_eq, mem_preimage]
#align filter.map_inf_principal_preimage Filter.map_inf_principal_preimage

/- warning: filter.tendsto.not_tendsto -> Filter.Tendsto.not_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {a : Filter.{u1} α} {b₁ : Filter.{u2} β} {b₂ : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f a b₁) -> (forall [_inst_1 : Filter.NeBot.{u1} α a], (Disjoint.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) b₁ b₂) -> (Not (Filter.Tendsto.{u1, u2} α β f a b₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {a : Filter.{u1} α} {b₁ : Filter.{u2} β} {b₂ : Filter.{u2} β}, (Filter.Tendsto.{u1, u2} α β f a b₁) -> (forall [_inst_1 : Filter.NeBot.{u1} α a], (Disjoint.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β) (BoundedOrder.toOrderBot.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (CompleteLattice.toBoundedOrder.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) b₁ b₂) -> (Not (Filter.Tendsto.{u1, u2} α β f a b₂)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.not_tendsto Filter.Tendsto.not_tendstoₓ'. -/
/-- If two filters are disjoint, then a function cannot tend to both of them along a non-trivial
filter. -/
theorem Tendsto.not_tendsto {f : α → β} {a : Filter α} {b₁ b₂ : Filter β} (hf : Tendsto f a b₁)
    [NeBot a] (hb : Disjoint b₁ b₂) : ¬Tendsto f a b₂ := fun hf' =>
  (tendsto_inf.2 ⟨hf, hf'⟩).ne_bot.Ne hb.eq_bot
#align filter.tendsto.not_tendsto Filter.Tendsto.not_tendsto

/- warning: filter.tendsto.if -> Filter.Tendsto.if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β} {f : α -> β} {g : α -> β} {p : α -> Prop} [_inst_1 : forall (x : α), Decidable (p x)], (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l₁ (Filter.principal.{u1} α (setOf.{u1} α (fun (x : α) => p x)))) l₂) -> (Filter.Tendsto.{u1, u2} α β g (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l₁ (Filter.principal.{u1} α (setOf.{u1} α (fun (x : α) => Not (p x))))) l₂) -> (Filter.Tendsto.{u1, u2} α β (fun (x : α) => ite.{succ u2} β (p x) (_inst_1 x) (f x) (g x)) l₁ l₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β} {f : α -> β} {g : α -> β} {p : α -> Prop} [_inst_1 : forall (x : α), Decidable (p x)], (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l₁ (Filter.principal.{u1} α (setOf.{u1} α (fun (x : α) => p x)))) l₂) -> (Filter.Tendsto.{u1, u2} α β g (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l₁ (Filter.principal.{u1} α (setOf.{u1} α (fun (x : α) => Not (p x))))) l₂) -> (Filter.Tendsto.{u1, u2} α β (fun (x : α) => ite.{succ u2} β (p x) (_inst_1 x) (f x) (g x)) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.if Filter.Tendsto.ifₓ'. -/
protected theorem Tendsto.if {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {p : α → Prop}
    [∀ x, Decidable (p x)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 { x | p x }) l₂)
    (h₁ : Tendsto g (l₁ ⊓ 𝓟 { x | ¬p x }) l₂) : Tendsto (fun x => if p x then f x else g x) l₁ l₂ :=
  by
  simp only [tendsto_def, mem_inf_principal] at *
  intro s hs
  filter_upwards [h₀ s hs, h₁ s hs]
  simp only [mem_preimage]
  intro x hp₀ hp₁
  split_ifs
  exacts[hp₀ h, hp₁ h]
#align filter.tendsto.if Filter.Tendsto.if

/- warning: filter.tendsto.if' -> Filter.Tendsto.if' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β} {f : α -> β} {g : α -> β} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p], (Filter.Tendsto.{u1, u2} α β f l₁ l₂) -> (Filter.Tendsto.{u1, u2} α β g l₁ l₂) -> (Filter.Tendsto.{u1, u2} α β (fun (a : α) => ite.{succ u2} β (p a) (_inst_1 a) (f a) (g a)) l₁ l₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l₁ : Filter.{u2} α} {l₂ : Filter.{u1} β} {f : α -> β} {g : α -> β} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u2} α p], (Filter.Tendsto.{u2, u1} α β f l₁ l₂) -> (Filter.Tendsto.{u2, u1} α β g l₁ l₂) -> (Filter.Tendsto.{u2, u1} α β (fun (a : α) => ite.{succ u1} β (p a) (_inst_1 a) (f a) (g a)) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.if' Filter.Tendsto.if'ₓ'. -/
protected theorem Tendsto.if' {α β : Type _} {l₁ : Filter α} {l₂ : Filter β} {f g : α → β}
    {p : α → Prop} [DecidablePred p] (hf : Tendsto f l₁ l₂) (hg : Tendsto g l₁ l₂) :
    Tendsto (fun a => if p a then f a else g a) l₁ l₂ :=
  by
  replace hf : tendsto f (l₁ ⊓ 𝓟 { x | p x }) l₂ := tendsto_inf_left hf
  replace hg : tendsto g (l₁ ⊓ 𝓟 { x | ¬p x }) l₂ := tendsto_inf_left hg
  exact hf.if hg
#align filter.tendsto.if' Filter.Tendsto.if'

/- warning: filter.tendsto.piecewise -> Filter.Tendsto.piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β} {f : α -> β} {g : α -> β} {s : Set.{u1} α} [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)], (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l₁ (Filter.principal.{u1} α s)) l₂) -> (Filter.Tendsto.{u1, u2} α β g (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l₁ (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) l₂) -> (Filter.Tendsto.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j)) l₁ l₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : Filter.{u1} α} {l₂ : Filter.{u2} β} {f : α -> β} {g : α -> β} {s : Set.{u1} α} [_inst_1 : forall (x : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)], (Filter.Tendsto.{u1, u2} α β f (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l₁ (Filter.principal.{u1} α s)) l₂) -> (Filter.Tendsto.{u1, u2} α β g (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l₁ (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) l₂) -> (Filter.Tendsto.{u1, u2} α β (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _inst_1 j)) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.piecewise Filter.Tendsto.piecewiseₓ'. -/
protected theorem Tendsto.piecewise {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {s : Set α}
    [∀ x, Decidable (x ∈ s)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 s) l₂) (h₁ : Tendsto g (l₁ ⊓ 𝓟 (sᶜ)) l₂) :
    Tendsto (piecewise s f g) l₁ l₂ :=
  h₀.if h₁
#align filter.tendsto.piecewise Filter.Tendsto.piecewise

end Filter

open Filter

/- warning: set.eq_on.eventually_eq -> Set.EqOn.eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {g : α -> β}, (Set.EqOn.{u1, u2} α β f g s) -> (Filter.EventuallyEq.{u1, u2} α β (Filter.principal.{u1} α s) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {g : α -> β}, (Set.EqOn.{u2, u1} α β f g s) -> (Filter.EventuallyEq.{u2, u1} α β (Filter.principal.{u2} α s) f g)
Case conversion may be inaccurate. Consider using '#align set.eq_on.eventually_eq Set.EqOn.eventuallyEqₓ'. -/
theorem Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α → β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g :=
  h
#align set.eq_on.eventually_eq Set.EqOn.eventuallyEq

/- warning: set.eq_on.eventually_eq_of_mem -> Set.EqOn.eventuallyEq_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Set.EqOn.{u1, u2} α β f g s) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s l) -> (Filter.EventuallyEq.{u1, u2} α β l f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {l : Filter.{u2} α} {f : α -> β} {g : α -> β}, (Set.EqOn.{u2, u1} α β f g s) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s l) -> (Filter.EventuallyEq.{u2, u1} α β l f g)
Case conversion may be inaccurate. Consider using '#align set.eq_on.eventually_eq_of_mem Set.EqOn.eventuallyEq_of_memₓ'. -/
theorem Set.EqOn.eventuallyEq_of_mem {α β} {s : Set α} {l : Filter α} {f g : α → β} (h : EqOn f g s)
    (hl : s ∈ l) : f =ᶠ[l] g :=
  h.EventuallyEq.filter_mono <| Filter.le_principal_iff.2 hl
#align set.eq_on.eventually_eq_of_mem Set.EqOn.eventuallyEq_of_mem

#print HasSubset.Subset.eventuallyLe /-
theorem HasSubset.Subset.eventuallyLe {α} {l : Filter α} {s t : Set α} (h : s ⊆ t) : s ≤ᶠ[l] t :=
  Filter.eventually_of_forall h
#align has_subset.subset.eventually_le HasSubset.Subset.eventuallyLe
-/

/- warning: set.maps_to.tendsto -> Set.MapsTo.tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t) -> (Filter.Tendsto.{u1, u2} α β f (Filter.principal.{u1} α s) (Filter.principal.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t) -> (Filter.Tendsto.{u2, u1} α β f (Filter.principal.{u2} α s) (Filter.principal.{u1} β t))
Case conversion may be inaccurate. Consider using '#align set.maps_to.tendsto Set.MapsTo.tendstoₓ'. -/
theorem Set.MapsTo.tendsto {α β} {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t) :
    Filter.Tendsto f (𝓟 s) (𝓟 t) :=
  Filter.tendsto_principal_principal.2 h
#align set.maps_to.tendsto Set.MapsTo.tendsto

