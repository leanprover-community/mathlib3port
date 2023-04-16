/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.extr
! leanprover-community/mathlib commit 4f4a1c875d0baa92ab5d92f3fb1bb258ad9f3e5b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Ray
import Mathbin.Topology.LocalExtr

/-!
# (Local) maximums in a normed space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove the following lemma, see `is_max_filter.norm_add_same_ray`. If `f : α → E` is
a function such that `norm ∘ f` has a maximum along a filter `l` at a point `c` and `y` is a vector
on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a maximul along `l` at `c`.

Then we specialize it to the case `y = f c` and to different special cases of `is_max_filter`:
`is_max_on`, `is_local_max_on`, and `is_local_max`.

## Tags

local maximum, normed space
-/


variable {α X E : Type _} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

section

variable {f : α → E} {l : Filter α} {s : Set α} {c : α} {y : E}

/- warning: is_max_filter.norm_add_same_ray -> IsMaxFilter.norm_add_sameRay is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField _inst_1] {f : α -> E} {l : Filter.{u1} α} {c : α} {y : E}, (IsMaxFilter.{u1, 0} α Real Real.preorder (Function.comp.{succ u1, succ u2, 1} α E Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1)) f) l c) -> (SameRay.{0, u2} Real Real.strictOrderedCommSemiring E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (NormedSpace.toModule.{0, u2} Real E Real.normedField _inst_1 _inst_2) (f c) y) -> (IsMaxFilter.{u1, 0} α Real Real.preorder (fun (x : α) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1))))))) (f x) y)) l c)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField _inst_1] {f : α -> E} {l : Filter.{u2} α} {c : α} {y : E}, (IsMaxFilter.{u2, 0} α Real Real.instPreorderReal (Function.comp.{succ u2, succ u1, 1} α E Real (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) f) l c) -> (SameRay.{0, u1} Real Real.strictOrderedCommSemiring E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (NormedSpace.toModule.{0, u1} Real E Real.normedField _inst_1 _inst_2) (f c) y) -> (IsMaxFilter.{u2, 0} α Real Real.instPreorderReal (fun (x : α) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1))))))) (f x) y)) l c)
Case conversion may be inaccurate. Consider using '#align is_max_filter.norm_add_same_ray IsMaxFilter.norm_add_sameRayₓ'. -/
/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a maximul
along `l` at `c`. -/
theorem IsMaxFilter.norm_add_sameRay (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRay ℝ (f c) y) :
    IsMaxFilter (fun x => ‖f x + y‖) l c :=
  h.mono fun x hx =>
    calc
      ‖f x + y‖ ≤ ‖f x‖ + ‖y‖ := norm_add_le _ _
      _ ≤ ‖f c‖ + ‖y‖ := (add_le_add_right hx _)
      _ = ‖f c + y‖ := hy.norm_add.symm
      
#align is_max_filter.norm_add_same_ray IsMaxFilter.norm_add_sameRay

/- warning: is_max_filter.norm_add_self -> IsMaxFilter.norm_add_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField _inst_1] {f : α -> E} {l : Filter.{u1} α} {c : α}, (IsMaxFilter.{u1, 0} α Real Real.preorder (Function.comp.{succ u1, succ u2, 1} α E Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1)) f) l c) -> (IsMaxFilter.{u1, 0} α Real Real.preorder (fun (x : α) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1))))))) (f x) (f c))) l c)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField _inst_1] {f : α -> E} {l : Filter.{u2} α} {c : α}, (IsMaxFilter.{u2, 0} α Real Real.instPreorderReal (Function.comp.{succ u2, succ u1, 1} α E Real (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) f) l c) -> (IsMaxFilter.{u2, 0} α Real Real.instPreorderReal (fun (x : α) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1))))))) (f x) (f c))) l c)
Case conversion may be inaccurate. Consider using '#align is_max_filter.norm_add_self IsMaxFilter.norm_add_selfₓ'. -/
/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c`, then the function `λ x, ‖f x + f c‖` has a maximul along `l` at `c`. -/
theorem IsMaxFilter.norm_add_self (h : IsMaxFilter (norm ∘ f) l c) :
    IsMaxFilter (fun x => ‖f x + f c‖) l c :=
  h.norm_add_sameRay SameRay.rfl
#align is_max_filter.norm_add_self IsMaxFilter.norm_add_self

/- warning: is_max_on.norm_add_same_ray -> IsMaxOn.norm_add_sameRay is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField _inst_1] {f : α -> E} {s : Set.{u1} α} {c : α} {y : E}, (IsMaxOn.{u1, 0} α Real Real.preorder (Function.comp.{succ u1, succ u2, 1} α E Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1)) f) s c) -> (SameRay.{0, u2} Real Real.strictOrderedCommSemiring E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (NormedSpace.toModule.{0, u2} Real E Real.normedField _inst_1 _inst_2) (f c) y) -> (IsMaxOn.{u1, 0} α Real Real.preorder (fun (x : α) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1))))))) (f x) y)) s c)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField _inst_1] {f : α -> E} {s : Set.{u2} α} {c : α} {y : E}, (IsMaxOn.{u2, 0} α Real Real.instPreorderReal (Function.comp.{succ u2, succ u1, 1} α E Real (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) f) s c) -> (SameRay.{0, u1} Real Real.strictOrderedCommSemiring E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (NormedSpace.toModule.{0, u1} Real E Real.normedField _inst_1 _inst_2) (f c) y) -> (IsMaxOn.{u2, 0} α Real Real.instPreorderReal (fun (x : α) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1))))))) (f x) y)) s c)
Case conversion may be inaccurate. Consider using '#align is_max_on.norm_add_same_ray IsMaxOn.norm_add_sameRayₓ'. -/
/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c` and
`y` is a vector on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a maximul on `s` at
`c`. -/
theorem IsMaxOn.norm_add_sameRay (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsMaxOn (fun x => ‖f x + y‖) s c :=
  h.norm_add_sameRay hy
#align is_max_on.norm_add_same_ray IsMaxOn.norm_add_sameRay

/- warning: is_max_on.norm_add_self -> IsMaxOn.norm_add_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField _inst_1] {f : α -> E} {s : Set.{u1} α} {c : α}, (IsMaxOn.{u1, 0} α Real Real.preorder (Function.comp.{succ u1, succ u2, 1} α E Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1)) f) s c) -> (IsMaxOn.{u1, 0} α Real Real.preorder (fun (x : α) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1))))))) (f x) (f c))) s c)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField _inst_1] {f : α -> E} {s : Set.{u2} α} {c : α}, (IsMaxOn.{u2, 0} α Real Real.instPreorderReal (Function.comp.{succ u2, succ u1, 1} α E Real (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) f) s c) -> (IsMaxOn.{u2, 0} α Real Real.instPreorderReal (fun (x : α) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1))))))) (f x) (f c))) s c)
Case conversion may be inaccurate. Consider using '#align is_max_on.norm_add_self IsMaxOn.norm_add_selfₓ'. -/
/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c`,
then the function `λ x, ‖f x + f c‖` has a maximul on `s` at `c`. -/
theorem IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c) : IsMaxOn (fun x => ‖f x + f c‖) s c :=
  h.norm_add_self
#align is_max_on.norm_add_self IsMaxOn.norm_add_self

end

variable {f : X → E} {s : Set X} {c : X} {y : E}

/- warning: is_local_max_on.norm_add_same_ray -> IsLocalMaxOn.norm_add_sameRay is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField _inst_1] [_inst_3 : TopologicalSpace.{u1} X] {f : X -> E} {s : Set.{u1} X} {c : X} {y : E}, (IsLocalMaxOn.{u1, 0} X Real _inst_3 Real.preorder (Function.comp.{succ u1, succ u2, 1} X E Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1)) f) s c) -> (SameRay.{0, u2} Real Real.strictOrderedCommSemiring E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (NormedSpace.toModule.{0, u2} Real E Real.normedField _inst_1 _inst_2) (f c) y) -> (IsLocalMaxOn.{u1, 0} X Real _inst_3 Real.preorder (fun (x : X) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1))))))) (f x) y)) s c)
but is expected to have type
  forall {X : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField _inst_1] [_inst_3 : TopologicalSpace.{u2} X] {f : X -> E} {s : Set.{u2} X} {c : X} {y : E}, (IsLocalMaxOn.{u2, 0} X Real _inst_3 Real.instPreorderReal (Function.comp.{succ u2, succ u1, 1} X E Real (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) f) s c) -> (SameRay.{0, u1} Real Real.strictOrderedCommSemiring E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (NormedSpace.toModule.{0, u1} Real E Real.normedField _inst_1 _inst_2) (f c) y) -> (IsLocalMaxOn.{u2, 0} X Real _inst_3 Real.instPreorderReal (fun (x : X) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1))))))) (f x) y)) s c)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.norm_add_same_ray IsLocalMaxOn.norm_add_sameRayₓ'. -/
/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a local
maximul on `s` at `c`. -/
theorem IsLocalMaxOn.norm_add_sameRay (h : IsLocalMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsLocalMaxOn (fun x => ‖f x + y‖) s c :=
  h.norm_add_sameRay hy
#align is_local_max_on.norm_add_same_ray IsLocalMaxOn.norm_add_sameRay

/- warning: is_local_max_on.norm_add_self -> IsLocalMaxOn.norm_add_self is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField _inst_1] [_inst_3 : TopologicalSpace.{u1} X] {f : X -> E} {s : Set.{u1} X} {c : X}, (IsLocalMaxOn.{u1, 0} X Real _inst_3 Real.preorder (Function.comp.{succ u1, succ u2, 1} X E Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1)) f) s c) -> (IsLocalMaxOn.{u1, 0} X Real _inst_3 Real.preorder (fun (x : X) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1))))))) (f x) (f c))) s c)
but is expected to have type
  forall {X : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField _inst_1] [_inst_3 : TopologicalSpace.{u2} X] {f : X -> E} {s : Set.{u2} X} {c : X}, (IsLocalMaxOn.{u2, 0} X Real _inst_3 Real.instPreorderReal (Function.comp.{succ u2, succ u1, 1} X E Real (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) f) s c) -> (IsLocalMaxOn.{u2, 0} X Real _inst_3 Real.instPreorderReal (fun (x : X) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1))))))) (f x) (f c))) s c)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.norm_add_self IsLocalMaxOn.norm_add_selfₓ'. -/
/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c`, then the function `λ x, ‖f x + f c‖` has a local maximul on `s` at `c`. -/
theorem IsLocalMaxOn.norm_add_self (h : IsLocalMaxOn (norm ∘ f) s c) :
    IsLocalMaxOn (fun x => ‖f x + f c‖) s c :=
  h.norm_add_self
#align is_local_max_on.norm_add_self IsLocalMaxOn.norm_add_self

/- warning: is_local_max.norm_add_same_ray -> IsLocalMax.norm_add_sameRay is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField _inst_1] [_inst_3 : TopologicalSpace.{u1} X] {f : X -> E} {c : X} {y : E}, (IsLocalMax.{u1, 0} X Real _inst_3 Real.preorder (Function.comp.{succ u1, succ u2, 1} X E Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1)) f) c) -> (SameRay.{0, u2} Real Real.strictOrderedCommSemiring E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (NormedSpace.toModule.{0, u2} Real E Real.normedField _inst_1 _inst_2) (f c) y) -> (IsLocalMax.{u1, 0} X Real _inst_3 Real.preorder (fun (x : X) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1))))))) (f x) y)) c)
but is expected to have type
  forall {X : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField _inst_1] [_inst_3 : TopologicalSpace.{u2} X] {f : X -> E} {c : X} {y : E}, (IsLocalMax.{u2, 0} X Real _inst_3 Real.instPreorderReal (Function.comp.{succ u2, succ u1, 1} X E Real (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) f) c) -> (SameRay.{0, u1} Real Real.strictOrderedCommSemiring E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (NormedSpace.toModule.{0, u1} Real E Real.normedField _inst_1 _inst_2) (f c) y) -> (IsLocalMax.{u2, 0} X Real _inst_3 Real.instPreorderReal (fun (x : X) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1))))))) (f x) y)) c)
Case conversion may be inaccurate. Consider using '#align is_local_max.norm_add_same_ray IsLocalMax.norm_add_sameRayₓ'. -/
/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c` and `y` is
a vector on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a local maximul at `c`. -/
theorem IsLocalMax.norm_add_sameRay (h : IsLocalMax (norm ∘ f) c) (hy : SameRay ℝ (f c) y) :
    IsLocalMax (fun x => ‖f x + y‖) c :=
  h.norm_add_sameRay hy
#align is_local_max.norm_add_same_ray IsLocalMax.norm_add_sameRay

/- warning: is_local_max.norm_add_self -> IsLocalMax.norm_add_self is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField _inst_1] [_inst_3 : TopologicalSpace.{u1} X] {f : X -> E} {c : X}, (IsLocalMax.{u1, 0} X Real _inst_3 Real.preorder (Function.comp.{succ u1, succ u2, 1} X E Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1)) f) c) -> (IsLocalMax.{u1, 0} X Real _inst_3 Real.preorder (fun (x : X) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1))))))) (f x) (f c))) c)
but is expected to have type
  forall {X : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField _inst_1] [_inst_3 : TopologicalSpace.{u2} X] {f : X -> E} {c : X}, (IsLocalMax.{u2, 0} X Real _inst_3 Real.instPreorderReal (Function.comp.{succ u2, succ u1, 1} X E Real (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1)) f) c) -> (IsLocalMax.{u2, 0} X Real _inst_3 Real.instPreorderReal (fun (x : X) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1))))))) (f x) (f c))) c)
Case conversion may be inaccurate. Consider using '#align is_local_max.norm_add_self IsLocalMax.norm_add_selfₓ'. -/
/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c`, then the
function `λ x, ‖f x + f c‖` has a local maximul at `c`. -/
theorem IsLocalMax.norm_add_self (h : IsLocalMax (norm ∘ f) c) :
    IsLocalMax (fun x => ‖f x + f c‖) c :=
  h.norm_add_self
#align is_local_max.norm_add_self IsLocalMax.norm_add_self

