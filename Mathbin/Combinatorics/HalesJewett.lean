/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module combinatorics.hales_jewett
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Option
import Mathbin.Data.Fintype.Pi
import Mathbin.Data.Fintype.Sum
import Mathbin.Algebra.BigOperators.Basic

/-!
# The Hales-Jewett theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove the Hales-Jewett theorem and deduce Van der Waerden's theorem as a corollary.

The Hales-Jewett theorem is a result in Ramsey theory dealing with *combinatorial lines*. Given
an 'alphabet' `α : Type*` and `a b : α`, an example of a combinatorial line in `α^5` is
`{ (a, x, x, b, x) | x : α }`. See `combinatorics.line` for a precise general definition. The
Hales-Jewett theorem states that for any fixed finite types `α` and `κ`, there exists a (potentially
huge) finite type `ι` such that whenever `ι → α` is `κ`-colored (i.e. for any coloring
`C : (ι → α) → κ`), there exists a monochromatic line. We prove the Hales-Jewett theorem using
the idea of *color focusing* and a *product argument*. See the proof of
`combinatorics.line.exists_mono_in_high_dimension'` for details.

The version of Van der Waerden's theorem in this file states that whenever a commutative monoid `M`
is finitely colored and `S` is a finite subset, there exists a monochromatic homothetic copy of `S`.
This follows from the Hales-Jewett theorem by considering the map `(ι → S) → M` sending `v`
to `∑ i : ι, v i`, which sends a combinatorial line to a homothetic copy of `S`.

## Main results

- `combinatorics.line.exists_mono_in_high_dimension`: the Hales-Jewett theorem.
- `combinatorics.exists_mono_homothetic_copy`: a generalization of Van der Waerden's theorem.

## Implementation details

For convenience, we work directly with finite types instead of natural numbers. That is, we write
`α, ι, κ` for (finite) types where one might traditionally use natural numbers `n, H, c`. This
allows us to work directly with `α`, `option α`, `(ι → α) → κ`, and `ι ⊕ ι'` instead of `fin n`,
`fin (n+1)`, `fin (c^(n^H))`, and `fin (H + H')`.

## Todo

- Prove a finitary version of Van der Waerden's theorem (either by compactness or by modifying the
current proof).

- One could reformulate the proof of Hales-Jewett to give explicit upper bounds on the number of
coordinates needed.

## Tags

combinatorial line, Ramsey theory, arithmetic progession

### References

* https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem

-/


open Classical

open BigOperators

universe u v

namespace Combinatorics

#print Combinatorics.Line /-
/-- The type of combinatorial lines. A line `l : line α ι` in the hypercube `ι → α` defines a
function `α → ι → α` from `α` to the hypercube, such that for each coordinate `i : ι`, the function
`λ x, l x i` is either `id` or constant. We require lines to be nontrivial in the sense that
`λ x, l x i` is `id` for at least one `i`.

Formally, a line is represented by the function `l.idx_fun : ι → option α` which says whether
`λ x, l x i` is `id` (corresponding to `l.idx_fun i = none`) or constantly `y` (corresponding to
`l.idx_fun i = some y`).

When `α` has size `1` there can be many elements of `line α ι` defining the same function. -/
structure Line (α ι : Type _) where
  idxFun : ι → Option α
  proper : ∃ i, idx_fun i = none
#align combinatorics.line Combinatorics.Line
-/

namespace Line

-- This lets us treat a line `l : line α ι` as a function `α → ι → α`.
instance (α ι) : CoeFun (Line α ι) fun _ => α → ι → α :=
  ⟨fun l x i => (l.idxFun i).getD x⟩

#print Combinatorics.Line.IsMono /-
/-- A line is monochromatic if all its points are the same color. -/
def IsMono {α ι κ} (C : (ι → α) → κ) (l : Line α ι) : Prop :=
  ∃ c, ∀ x, C (l x) = c
#align combinatorics.line.is_mono Combinatorics.Line.IsMono
-/

#print Combinatorics.Line.diagonal /-
/-- The diagonal line. It is the identity at every coordinate. -/
def diagonal (α ι) [Nonempty ι] : Line α ι
    where
  idxFun _ := none
  proper := ⟨Classical.arbitrary ι, rfl⟩
#align combinatorics.line.diagonal Combinatorics.Line.diagonal
-/

instance (α ι) [Nonempty ι] : Inhabited (Line α ι) :=
  ⟨diagonal α ι⟩

#print Combinatorics.Line.AlmostMono /-
/-- The type of lines that are only one color except possibly at their endpoints. -/
structure AlmostMono {α ι κ : Type _} (C : (ι → Option α) → κ) where
  line : Line (Option α) ι
  Color : κ
  has_color : ∀ x : α, C (line (some x)) = color
#align combinatorics.line.almost_mono Combinatorics.Line.AlmostMono
-/

instance {α ι κ : Type _} [Nonempty ι] [Inhabited κ] :
    Inhabited (AlmostMono fun v : ι → Option α => (default : κ)) :=
  ⟨{  line := default
      Color := default
      has_color := fun _ => rfl }⟩

#print Combinatorics.Line.ColorFocused /-
/-- The type of collections of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.
Used in the proof `exists_mono_in_high_dimension`. -/
structure ColorFocused {α ι κ : Type _} (C : (ι → Option α) → κ) where
  lines : Multiset (AlmostMono C)
  focus : ι → Option α
  is_focused : ∀ p ∈ lines, AlmostMono.line p none = focus
  distinct_colors : (lines.map AlmostMono.color).Nodup
#align combinatorics.line.color_focused Combinatorics.Line.ColorFocused
-/

instance {α ι κ} (C : (ι → Option α) → κ) : Inhabited (ColorFocused C) :=
  ⟨⟨0, fun _ => none, fun _ => False.elim, Multiset.nodup_zero⟩⟩

#print Combinatorics.Line.map /-
/-- A function `f : α → α'` determines a function `line α ι → line α' ι`. For a coordinate `i`,
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is constantly `y` at `i`. -/
def map {α α' ι} (f : α → α') (l : Line α ι) : Line α' ι
    where
  idxFun i := (l.idxFun i).map f
  proper := ⟨l.proper.some, by rw [l.proper.some_spec, Option.map_none']⟩
#align combinatorics.line.map Combinatorics.Line.map
-/

#print Combinatorics.Line.vertical /-
/-- A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def vertical {α ι ι'} (v : ι → α) (l : Line α ι') : Line α (Sum ι ι')
    where
  idxFun := Sum.elim (some ∘ v) l.idxFun
  proper := ⟨Sum.inr l.proper.some, l.proper.choose_spec⟩
#align combinatorics.line.vertical Combinatorics.Line.vertical
-/

#print Combinatorics.Line.horizontal /-
/-- A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def horizontal {α ι ι'} (l : Line α ι) (v : ι' → α) : Line α (Sum ι ι')
    where
  idxFun := Sum.elim l.idxFun (some ∘ v)
  proper := ⟨Sum.inl l.proper.some, l.proper.choose_spec⟩
#align combinatorics.line.horizontal Combinatorics.Line.horizontal
-/

#print Combinatorics.Line.prod /-
/-- One line in `ι → α` and one in `ι' → α` together determine a line in `ι ⊕ ι' → α`. -/
def prod {α ι ι'} (l : Line α ι) (l' : Line α ι') : Line α (Sum ι ι')
    where
  idxFun := Sum.elim l.idxFun l'.idxFun
  proper := ⟨Sum.inl l.proper.some, l.proper.choose_spec⟩
#align combinatorics.line.prod Combinatorics.Line.prod
-/

/- warning: combinatorics.line.apply -> Combinatorics.Line.apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (l : Combinatorics.Line.{u1, u2} α ι) (x : α), Eq.{max (succ u2) (succ u1)} (ι -> α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Combinatorics.Line.{u1, u2} α ι) (fun (_x : Combinatorics.Line.{u1, u2} α ι) => α -> ι -> α) (Combinatorics.Line.hasCoeToFun.{u1, u2} α ι) l x) (fun (i : ι) => Option.getD.{u1} α (Combinatorics.Line.idxFun.{u1, u2} α ι l i) x)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (l : Combinatorics.Line.{u2, u1} α ι) (x : α), Eq.{max (succ u1) (succ u2)} (ι -> α) ((fun (x : α) (i : ι) => Option.getD.{u2} α (Combinatorics.Line.idxFun.{u2, u1} α ι l i) x) x) (fun (i : ι) => Option.getD.{u2} α (Combinatorics.Line.idxFun.{u2, u1} α ι l i) x)
Case conversion may be inaccurate. Consider using '#align combinatorics.line.apply Combinatorics.Line.applyₓ'. -/
theorem apply {α ι} (l : Line α ι) (x : α) : l x = fun i => (l.idxFun i).getD x :=
  rfl
#align combinatorics.line.apply Combinatorics.Line.apply

/- warning: combinatorics.line.apply_none -> Combinatorics.Line.apply_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (l : Combinatorics.Line.{u1, u2} α ι) (x : α) (i : ι), (Eq.{succ u1} (Option.{u1} α) (Combinatorics.Line.idxFun.{u1, u2} α ι l i) (Option.none.{u1} α)) -> (Eq.{succ u1} α (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Combinatorics.Line.{u1, u2} α ι) (fun (_x : Combinatorics.Line.{u1, u2} α ι) => α -> ι -> α) (Combinatorics.Line.hasCoeToFun.{u1, u2} α ι) l x i) x)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (l : Combinatorics.Line.{u2, u1} α ι) (x : α) (i : ι), (Eq.{succ u2} (Option.{u2} α) (Combinatorics.Line.idxFun.{u2, u1} α ι l i) (Option.none.{u2} α)) -> (Eq.{succ u2} α ((fun (x : α) (i : ι) => Option.getD.{u2} α (Combinatorics.Line.idxFun.{u2, u1} α ι l i) x) x i) x)
Case conversion may be inaccurate. Consider using '#align combinatorics.line.apply_none Combinatorics.Line.apply_noneₓ'. -/
theorem apply_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i = none) : l x i = x := by
  simp only [Option.getD_none, h, l.apply]
#align combinatorics.line.apply_none Combinatorics.Line.apply_none

/- warning: combinatorics.line.apply_of_ne_none -> Combinatorics.Line.apply_of_ne_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (l : Combinatorics.Line.{u1, u2} α ι) (x : α) (i : ι), (Ne.{succ u1} (Option.{u1} α) (Combinatorics.Line.idxFun.{u1, u2} α ι l i) (Option.none.{u1} α)) -> (Eq.{succ u1} (Option.{u1} α) (Option.some.{u1} α (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Combinatorics.Line.{u1, u2} α ι) (fun (_x : Combinatorics.Line.{u1, u2} α ι) => α -> ι -> α) (Combinatorics.Line.hasCoeToFun.{u1, u2} α ι) l x i)) (Combinatorics.Line.idxFun.{u1, u2} α ι l i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (l : Combinatorics.Line.{u2, u1} α ι) (x : α) (i : ι), (Ne.{succ u2} (Option.{u2} α) (Combinatorics.Line.idxFun.{u2, u1} α ι l i) (Option.none.{u2} α)) -> (Eq.{succ u2} (Option.{u2} α) (Option.some.{u2} α ((fun (x : α) (i : ι) => Option.getD.{u2} α (Combinatorics.Line.idxFun.{u2, u1} α ι l i) x) x i)) (Combinatorics.Line.idxFun.{u2, u1} α ι l i))
Case conversion may be inaccurate. Consider using '#align combinatorics.line.apply_of_ne_none Combinatorics.Line.apply_of_ne_noneₓ'. -/
theorem apply_of_ne_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i ≠ none) :
    some (l x i) = l.idxFun i := by rw [l.apply, Option.getD_of_ne_none h]
#align combinatorics.line.apply_of_ne_none Combinatorics.Line.apply_of_ne_none

/- warning: combinatorics.line.map_apply -> Combinatorics.Line.map_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {ι : Type.{u3}} (f : α -> α') (l : Combinatorics.Line.{u1, u3} α ι) (x : α), Eq.{max (succ u3) (succ u2)} (ι -> α') (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (Combinatorics.Line.{u2, u3} α' ι) (fun (_x : Combinatorics.Line.{u2, u3} α' ι) => α' -> ι -> α') (Combinatorics.Line.hasCoeToFun.{u2, u3} α' ι) (Combinatorics.Line.map.{u1, u2, u3} α α' ι f l) (f x)) (Function.comp.{succ u3, succ u1, succ u2} ι α α' f (coeFn.{max (succ u1) (succ u3), max (succ u3) (succ u1)} (Combinatorics.Line.{u1, u3} α ι) (fun (_x : Combinatorics.Line.{u1, u3} α ι) => α -> ι -> α) (Combinatorics.Line.hasCoeToFun.{u1, u3} α ι) l x))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u2}} {ι : Type.{u1}} (f : α -> α') (l : Combinatorics.Line.{u3, u1} α ι) (x : α), Eq.{max (succ u1) (succ u2)} (ι -> α') ((fun (x : α') (i : ι) => Option.getD.{u2} α' (Combinatorics.Line.idxFun.{u2, u1} α' ι (Combinatorics.Line.map.{u3, u2, u1} α α' ι f l) i) x) (f x)) (Function.comp.{succ u1, succ u3, succ u2} ι α α' f ((fun (x : α) (i : ι) => Option.getD.{u3} α (Combinatorics.Line.idxFun.{u3, u1} α ι l i) x) x))
Case conversion may be inaccurate. Consider using '#align combinatorics.line.map_apply Combinatorics.Line.map_applyₓ'. -/
@[simp]
theorem map_apply {α α' ι} (f : α → α') (l : Line α ι) (x : α) : l.map f (f x) = f ∘ l x := by
  simp only [line.apply, line.map, Option.getD_map]
#align combinatorics.line.map_apply Combinatorics.Line.map_apply

/- warning: combinatorics.line.vertical_apply -> Combinatorics.Line.vertical_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} (v : ι -> α) (l : Combinatorics.Line.{u1, u3} α ι') (x : α), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} ι ι') -> α) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u1)} (Combinatorics.Line.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) (fun (_x : Combinatorics.Line.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) => α -> (Sum.{u2, u3} ι ι') -> α) (Combinatorics.Line.hasCoeToFun.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) (Combinatorics.Line.vertical.{u1, u2, u3} α ι ι' v l) x) (Sum.elim.{u2, u3, succ u1} ι ι' α v (coeFn.{max (succ u1) (succ u3), max (succ u3) (succ u1)} (Combinatorics.Line.{u1, u3} α ι') (fun (_x : Combinatorics.Line.{u1, u3} α ι') => α -> ι' -> α) (Combinatorics.Line.hasCoeToFun.{u1, u3} α ι') l x))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {ι' : Type.{u1}} (v : ι -> α) (l : Combinatorics.Line.{u3, u1} α ι') (x : α), Eq.{max (max (succ u1) (succ u3)) (succ u2)} ((Sum.{u2, u1} ι ι') -> α) ((fun (x : α) (i : Sum.{u2, u1} ι ι') => Option.getD.{u3} α (Combinatorics.Line.idxFun.{u3, max u1 u2} α (Sum.{u2, u1} ι ι') (Combinatorics.Line.vertical.{u3, u2, u1} α ι ι' v l) i) x) x) (Sum.elim.{u2, u1, succ u3} ι ι' α v ((fun (x : α) (i : ι') => Option.getD.{u3} α (Combinatorics.Line.idxFun.{u3, u1} α ι' l i) x) x))
Case conversion may be inaccurate. Consider using '#align combinatorics.line.vertical_apply Combinatorics.Line.vertical_applyₓ'. -/
@[simp]
theorem vertical_apply {α ι ι'} (v : ι → α) (l : Line α ι') (x : α) :
    l.vertical v x = Sum.elim v (l x) := by funext i; cases i <;> rfl
#align combinatorics.line.vertical_apply Combinatorics.Line.vertical_apply

/- warning: combinatorics.line.horizontal_apply -> Combinatorics.Line.horizontal_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} (l : Combinatorics.Line.{u1, u2} α ι) (v : ι' -> α) (x : α), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} ι ι') -> α) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u1)} (Combinatorics.Line.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) (fun (_x : Combinatorics.Line.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) => α -> (Sum.{u2, u3} ι ι') -> α) (Combinatorics.Line.hasCoeToFun.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) (Combinatorics.Line.horizontal.{u1, u2, u3} α ι ι' l v) x) (Sum.elim.{u2, u3, succ u1} ι ι' α (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Combinatorics.Line.{u1, u2} α ι) (fun (_x : Combinatorics.Line.{u1, u2} α ι) => α -> ι -> α) (Combinatorics.Line.hasCoeToFun.{u1, u2} α ι) l x) v)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {ι' : Type.{u1}} (l : Combinatorics.Line.{u3, u2} α ι) (v : ι' -> α) (x : α), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u1} ι ι') -> α) ((fun (x : α) (i : Sum.{u2, u1} ι ι') => Option.getD.{u3} α (Combinatorics.Line.idxFun.{u3, max u2 u1} α (Sum.{u2, u1} ι ι') (Combinatorics.Line.horizontal.{u3, u2, u1} α ι ι' l v) i) x) x) (Sum.elim.{u2, u1, succ u3} ι ι' α ((fun (x : α) (i : ι) => Option.getD.{u3} α (Combinatorics.Line.idxFun.{u3, u2} α ι l i) x) x) v)
Case conversion may be inaccurate. Consider using '#align combinatorics.line.horizontal_apply Combinatorics.Line.horizontal_applyₓ'. -/
@[simp]
theorem horizontal_apply {α ι ι'} (l : Line α ι) (v : ι' → α) (x : α) :
    l.horizontal v x = Sum.elim (l x) v := by funext i; cases i <;> rfl
#align combinatorics.line.horizontal_apply Combinatorics.Line.horizontal_apply

/- warning: combinatorics.line.prod_apply -> Combinatorics.Line.prod_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} (l : Combinatorics.Line.{u1, u2} α ι) (l' : Combinatorics.Line.{u1, u3} α ι') (x : α), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} ι ι') -> α) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u1)} (Combinatorics.Line.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) (fun (_x : Combinatorics.Line.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) => α -> (Sum.{u2, u3} ι ι') -> α) (Combinatorics.Line.hasCoeToFun.{u1, max u2 u3} α (Sum.{u2, u3} ι ι')) (Combinatorics.Line.prod.{u1, u2, u3} α ι ι' l l') x) (Sum.elim.{u2, u3, succ u1} ι ι' α (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Combinatorics.Line.{u1, u2} α ι) (fun (_x : Combinatorics.Line.{u1, u2} α ι) => α -> ι -> α) (Combinatorics.Line.hasCoeToFun.{u1, u2} α ι) l x) (coeFn.{max (succ u1) (succ u3), max (succ u3) (succ u1)} (Combinatorics.Line.{u1, u3} α ι') (fun (_x : Combinatorics.Line.{u1, u3} α ι') => α -> ι' -> α) (Combinatorics.Line.hasCoeToFun.{u1, u3} α ι') l' x))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {ι' : Type.{u1}} (l : Combinatorics.Line.{u3, u2} α ι) (l' : Combinatorics.Line.{u3, u1} α ι') (x : α), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u1} ι ι') -> α) ((fun (x : α) (i : Sum.{u2, u1} ι ι') => Option.getD.{u3} α (Combinatorics.Line.idxFun.{u3, max u2 u1} α (Sum.{u2, u1} ι ι') (Combinatorics.Line.prod.{u3, u2, u1} α ι ι' l l') i) x) x) (Sum.elim.{u2, u1, succ u3} ι ι' α ((fun (x : α) (i : ι) => Option.getD.{u3} α (Combinatorics.Line.idxFun.{u3, u2} α ι l i) x) x) ((fun (x : α) (i : ι') => Option.getD.{u3} α (Combinatorics.Line.idxFun.{u3, u1} α ι' l' i) x) x))
Case conversion may be inaccurate. Consider using '#align combinatorics.line.prod_apply Combinatorics.Line.prod_applyₓ'. -/
@[simp]
theorem prod_apply {α ι ι'} (l : Line α ι) (l' : Line α ι') (x : α) :
    l.Prod l' x = Sum.elim (l x) (l' x) := by funext i; cases i <;> rfl
#align combinatorics.line.prod_apply Combinatorics.Line.prod_apply

/- warning: combinatorics.line.diagonal_apply -> Combinatorics.Line.diagonal_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Nonempty.{succ u2} ι] (x : α), Eq.{max (succ u2) (succ u1)} (ι -> α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Combinatorics.Line.{u1, u2} α ι) (fun (_x : Combinatorics.Line.{u1, u2} α ι) => α -> ι -> α) (Combinatorics.Line.hasCoeToFun.{u1, u2} α ι) (Combinatorics.Line.diagonal.{u1, u2} α ι _inst_1) x) (fun (i : ι) => x)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Nonempty.{succ u1} ι] (x : α), Eq.{max (succ u1) (succ u2)} (ι -> α) ((fun (x : α) (i : ι) => Option.getD.{u2} α (Combinatorics.Line.idxFun.{u2, u1} α ι (Combinatorics.Line.diagonal.{u2, u1} α ι _inst_1) i) x) x) (fun (i : ι) => x)
Case conversion may be inaccurate. Consider using '#align combinatorics.line.diagonal_apply Combinatorics.Line.diagonal_applyₓ'. -/
@[simp]
theorem diagonal_apply {α ι} [Nonempty ι] (x : α) : Line.diagonal α ι x = fun i => x := by
  simp_rw [line.apply, line.diagonal, Option.getD_none]
#align combinatorics.line.diagonal_apply Combinatorics.Line.diagonal_apply

/- warning: combinatorics.line.exists_mono_in_high_dimension' clashes with [anonymous] -> [anonymous]
Case conversion may be inaccurate. Consider using '#align combinatorics.line.exists_mono_in_high_dimension' [anonymous]ₓ'. -/
#print [anonymous] /-
/-- The Hales-Jewett theorem. This version has a restriction on universe levels which is necessary
for the proof. See `exists_mono_in_high_dimension` for a fully universe-polymorphic version. -/
private theorem [anonymous] :
    ∀ (α : Type u) [Finite α] (κ : Type max v u) [Finite κ],
      ∃ (ι : Type)(_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  -- The proof proceeds by induction on `α`.
    Finite.induction_empty_option
    (-- We have to show that the theorem is invariant under `α ≃ α'` for the induction to work.
    fun α α' e =>
      forall_imp fun κ =>
        forall_imp fun _ =>
          Exists.imp fun ι =>
            Exists.imp fun _ h C =>
              let ⟨l, c, lc⟩ := h fun v => C (e ∘ v)
              ⟨l.map e, c, e.forall_congr_left.mp fun x => by rw [← lc x, line.map_apply]⟩)
    (by
      -- This deals with the degenerate case where `α` is empty.
      intro κ _
      by_cases h : Nonempty κ
      · skip; exact ⟨Unit, inferInstance, fun C => ⟨default, Classical.arbitrary _, PEmpty.rec _⟩⟩
      · exact ⟨Empty, inferInstance, fun C => (h ⟨C (Empty.rec _)⟩).elim⟩)
    (by
      -- Now we have to show that the theorem holds for `option α` if it holds for `α`.
      intro α _ ihα κ _
      cases nonempty_fintype κ
      -- Later we'll need `α` to be nonempty. So we first deal with the trivial case where `α` is empty.
      -- Then `option α` has only one element, so any line is monochromatic.
      by_cases h : Nonempty α
      on_goal
        2 =>
        refine' ⟨Unit, inferInstance, fun C => ⟨diagonal _ _, C fun _ => none, _⟩⟩
        rintro (_ | ⟨a⟩); rfl; exact (h ⟨a⟩).elim
      -- The key idea is to show that for every `r`, in high dimension we can either find
      -- `r` color focused lines or a monochromatic line.
      suffices key :
        ∀ r : ℕ,
          ∃ (ι : Type)(_ : Fintype ι),
            ∀ C : (ι → Option α) → κ, (∃ s : color_focused C, s.lines.card = r) ∨ ∃ l, is_mono C l
      -- Given the key claim, we simply take `r = |κ| + 1`. We cannot have this many distinct colors so
      -- we must be in the second case, where there is a monochromatic line.
      · obtain ⟨ι, _inst, hι⟩ := key (Fintype.card κ + 1)
        refine' ⟨ι, _inst, fun C => (hι C).resolve_left _⟩
        rintro ⟨s, sr⟩
        apply Nat.not_succ_le_self (Fintype.card κ)
        rw [← Nat.add_one, ← sr, ← Multiset.card_map, ← Finset.card_mk]
        exact Finset.card_le_univ ⟨_, s.distinct_colors⟩
      -- We now prove the key claim, by induction on `r`.
      intro r
      induction' r with r ihr
      -- The base case `r = 0` is trivial as the empty collection is color-focused.
      · exact ⟨Empty, inferInstance, fun C => Or.inl ⟨default, Multiset.card_zero⟩⟩
      -- Supposing the key claim holds for `r`, we need to show it for `r+1`. First pick a high enough
      -- dimension `ι` for `r`.
      obtain ⟨ι, _inst, hι⟩ := ihr
      skip
      -- Then since the theorem holds for `α` with any number of colors, pick a dimension `ι'` such that
      -- `ι' → α` always has a monochromatic line whenever it is `(ι → option α) → κ`-colored.
      specialize ihα ((ι → Option α) → κ)
      obtain ⟨ι', _inst, hι'⟩ := ihα
      skip
      -- We claim that `ι ⊕ ι'` works for `option α` and `κ`-coloring.
      refine' ⟨Sum ι ι', inferInstance, _⟩
      intro C
      -- A `κ`-coloring of `ι ⊕ ι' → option α` induces an `(ι → option α) → κ`-coloring of `ι' → α`.
      specialize hι' fun v' v => C (Sum.elim v (some ∘ v'))
      -- By choice of `ι'` this coloring has a monochromatic line `l'` with color class `C'`, where
      -- `C'` is a `κ`-coloring of `ι → α`.
      obtain ⟨l', C', hl'⟩ := hι'
      -- If `C'` has a monochromatic line, then so does `C`. We use this in two places below.
      have mono_of_mono : (∃ l, is_mono C' l) → ∃ l, is_mono C l :=
        by
        rintro ⟨l, c, hl⟩
        refine' ⟨l.horizontal (some ∘ l' (Classical.arbitrary α)), c, fun x => _⟩
        rw [line.horizontal_apply, ← hl, ← hl']
      -- By choice of `ι`, `C'` either has `r` color-focused lines or a monochromatic line.
      specialize hι C'
      rcases hι with (⟨s, sr⟩ | _)
      on_goal 2 => exact Or.inr (mono_of_mono hι)
      -- Here we assume `C'` has `r` color focused lines. We split into cases depending on whether one of
      -- these `r` lines has the same color as the focus point.
      by_cases h : ∃ p ∈ s.lines, (p : almost_mono _).Color = C' s.focus
      -- If so then this is a `C'`-monochromatic line and we are done.
      · obtain ⟨p, p_mem, hp⟩ := h
        refine' Or.inr (mono_of_mono ⟨p.line, p.color, _⟩)
        rintro (_ | _); rw [hp, s.is_focused p p_mem]; apply p.has_color
      -- If not, we get `r+1` color focused lines by taking the product of the `r` lines with `l'` and
      -- adding to this the vertical line obtained by the focus point and `l`.
      refine'
        Or.inl
          ⟨⟨(s.lines.map _).cons ⟨(l'.map some).vertical s.focus, C' s.focus, fun x => _⟩,
              Sum.elim s.focus (l'.map some none), _, _⟩,
            _⟩
      -- The vertical line is almost monochromatic.
      · rw [vertical_apply, ← congr_fun (hl' x), line.map_apply]
      · refine' fun p => ⟨p.line.prod (l'.map some), p.Color, fun x => _⟩
        -- The product lines are almost monochromatic.
        rw [line.prod_apply, line.map_apply, ← p.has_color, ← congr_fun (hl' x)]
      -- Our `r+1` lines have the same endpoint.
      · simp_rw [Multiset.mem_cons, Multiset.mem_map]
        rintro _ (rfl | ⟨q, hq, rfl⟩)
        · rw [line.vertical_apply]
        · rw [line.prod_apply, s.is_focused q hq]
      -- Our `r+1` lines have distinct colors (this is why we needed to split into cases above).
      · rw [Multiset.map_cons, Multiset.map_map, Multiset.nodup_cons, Multiset.mem_map]
        exact ⟨fun ⟨q, hq, he⟩ => h ⟨q, hq, he⟩, s.distinct_colors⟩
      -- Finally, we really do have `r+1` lines!
      · rw [Multiset.card_cons, Multiset.card_map, sr])
-/

#print Combinatorics.Line.exists_mono_in_high_dimension /-
/-- The Hales-Jewett theorem: for any finite types `α` and `κ`, there exists a finite type `ι` such
that whenever the hypercube `ι → α` is `κ`-colored, there is a monochromatic combinatorial line. -/
theorem exists_mono_in_high_dimension (α : Type u) [Finite α] (κ : Type v) [Finite κ] :
    ∃ (ι : Type)(_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  let ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension' α (ULift κ)
  ⟨ι, ιfin, fun C =>
    let ⟨l, c, hc⟩ := hι (ULift.up ∘ C)
    ⟨l, c.down, fun x => by rw [← hc]⟩⟩
#align combinatorics.line.exists_mono_in_high_dimension Combinatorics.Line.exists_mono_in_high_dimension
-/

end Line

/- warning: combinatorics.exists_mono_homothetic_copy -> Combinatorics.exists_mono_homothetic_copy is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {κ : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} M] (S : Finset.{u1} M) [_inst_2 : Finite.{succ u2} κ] (C : M -> κ), Exists.{1} Nat (fun (a : Nat) => Exists.{0} (GT.gt.{0} Nat Nat.hasLt a (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (H : GT.gt.{0} Nat Nat.hasLt a (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Exists.{succ u1} M (fun (b : M) => Exists.{succ u2} κ (fun (c : κ) => forall (s : M), (Membership.Mem.{u1, u1} M (Finset.{u1} M) (Finset.hasMem.{u1} M) s S) -> (Eq.{succ u2} κ (C (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_1)))) (SMul.smul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_1)) a s) b)) c)))))
but is expected to have type
  forall {M : Type.{u2}} {κ : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} M] (S : Finset.{u2} M) [_inst_2 : Finite.{succ u1} κ] (C : M -> κ), Exists.{1} Nat (fun (a : Nat) => And (GT.gt.{0} Nat instLTNat a (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Exists.{succ u2} M (fun (b : M) => Exists.{succ u1} κ (fun (c : κ) => forall (s : M), (Membership.mem.{u2, u2} M (Finset.{u2} M) (Finset.instMembershipFinset.{u2} M) s S) -> (Eq.{succ u1} κ (C (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (HSMul.hSMul.{0, u2, u2} Nat M M (instHSMul.{0, u2} Nat M (AddMonoid.SMul.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) a s) b)) c)))))
Case conversion may be inaccurate. Consider using '#align combinatorics.exists_mono_homothetic_copy Combinatorics.exists_mono_homothetic_copyₓ'. -/
/-- A generalization of Van der Waerden's theorem: if `M` is a finitely colored commutative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic copy of `S`. -/
theorem exists_mono_homothetic_copy {M κ : Type _} [AddCommMonoid M] (S : Finset M) [Finite κ]
    (C : M → κ) : ∃ a > 0, ∃ (b : M)(c : κ), ∀ s ∈ S, C (a • s + b) = c :=
  by
  obtain ⟨ι, _inst, hι⟩ := line.exists_mono_in_high_dimension S κ
  skip
  specialize hι fun v => C <| ∑ i, v i
  obtain ⟨l, c, hl⟩ := hι
  set s : Finset ι := { i ∈ Finset.univ | l.idx_fun i = none } with hs
  refine'
    ⟨s.card, finset.card_pos.mpr ⟨l.proper.some, _⟩, ∑ i in sᶜ, ((l.idx_fun i).map coe).getD 0, c,
      _⟩
  · rw [hs, Finset.sep_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, l.proper.some_spec⟩
  intro x xs
  rw [← hl ⟨x, xs⟩]
  clear hl; congr
  rw [← Finset.sum_add_sum_compl s]
  congr 1
  · rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.sep_def, Finset.mem_filter] at hi
    rw [l.apply_none _ _ hi.right, Subtype.coe_mk]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.sep_def, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := option.ne_none_iff_exists.mp hi.right
    simp_rw [line.apply, ← hy, Option.map_some', Option.getD_some]
#align combinatorics.exists_mono_homothetic_copy Combinatorics.exists_mono_homothetic_copy

end Combinatorics

