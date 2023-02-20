/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module topology.is_locally_homeomorph
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.LocalHomeomorph

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

* `is_locally_homeomorph`: A function `f : X → Y` satisfies `is_locally_homeomorph` if for each
  point `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.

  Note that `is_locally_homeomorph` is a global condition. This is in contrast to
  `local_homeomorph`, which is a homeomorphism between specific open subsets.
-/


open Topology

variable {X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)

#print IsLocallyHomeomorphOn /-
/-- A function `f : X → Y` satisfies `is_locally_homeomorph_on f s` if each `x ∈ s` is contained in
the source of some `e : local_homeomorph X Y` with `f = e`. -/
def IsLocallyHomeomorphOn :=
  ∀ x ∈ s, ∃ e : LocalHomeomorph X Y, x ∈ e.source ∧ f = e
#align is_locally_homeomorph_on IsLocallyHomeomorphOn
-/

namespace IsLocallyHomeomorphOn

/- warning: is_locally_homeomorph_on.mk -> IsLocallyHomeomorphOn.mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : X -> Y) (s : Set.{u1} X), (forall (x : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (Exists.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} X Y _inst_1 _inst_2) (fun (e : LocalHomeomorph.{u1, u2} X Y _inst_1 _inst_2) => And (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x (LocalEquiv.source.{u1, u2} X Y (LocalHomeomorph.toLocalEquiv.{u1, u2} X Y _inst_1 _inst_2 e))) (forall (y : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y (LocalEquiv.source.{u1, u2} X Y (LocalHomeomorph.toLocalEquiv.{u1, u2} X Y _inst_1 _inst_2 e))) -> (Eq.{succ u2} Y (f y) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} X Y _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} X Y _inst_1 _inst_2) => X -> Y) (LocalHomeomorph.hasCoeToFun.{u1, u2} X Y _inst_1 _inst_2) e y)))))) -> (IsLocallyHomeomorphOn.{u1, u2} X Y _inst_1 _inst_2 f s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] (f : X -> Y) (s : Set.{u2} X), (forall (x : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x s) -> (Exists.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} X Y _inst_1 _inst_2) (fun (e : LocalHomeomorph.{u2, u1} X Y _inst_1 _inst_2) => And (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x (LocalEquiv.source.{u2, u1} X Y (LocalHomeomorph.toLocalEquiv.{u2, u1} X Y _inst_1 _inst_2 e))) (forall (y : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y (LocalEquiv.source.{u2, u1} X Y (LocalHomeomorph.toLocalEquiv.{u2, u1} X Y _inst_1 _inst_2 e))) -> (Eq.{succ u1} Y (f y) (LocalHomeomorph.toFun'.{u2, u1} X Y _inst_1 _inst_2 e y)))))) -> (IsLocallyHomeomorphOn.{u2, u1} X Y _inst_1 _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph_on.mk IsLocallyHomeomorphOn.mkₓ'. -/
/-- Proves that `f` satisfies `is_locally_homeomorph_on f s`. The condition `h` is weaker than the
definition of `is_locally_homeomorph_on f s`, since it only requires `e : local_homeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x ∈ s, ∃ e : LocalHomeomorph X Y, x ∈ e.source ∧ ∀ y ∈ e.source, f y = e y) :
    IsLocallyHomeomorphOn f s := by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun x hx => by rw [he x hx] <;> exact e.map_source' hx
        left_inv' := fun x hx => by rw [he x hx] <;> exact e.left_inv' hx
        right_inv' := fun y hy => by rw [he _ (e.map_target' hy)] <;> exact e.right_inv' hy
        continuous_toFun := (continuousOn_congr he).mpr e.continuous_to_fun },
      hx, rfl⟩
#align is_locally_homeomorph_on.mk IsLocallyHomeomorphOn.mk

variable {g f s t}

/- warning: is_locally_homeomorph_on.map_nhds_eq -> IsLocallyHomeomorphOn.map_nhds_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y} {s : Set.{u1} X}, (IsLocallyHomeomorphOn.{u1, u2} X Y _inst_1 _inst_2 f s) -> (forall {x : X}, (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (Eq.{succ u2} (Filter.{u2} Y) (Filter.map.{u1, u2} X Y f (nhds.{u1} X _inst_1 x)) (nhds.{u2} Y _inst_2 (f x))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y} {s : Set.{u2} X}, (IsLocallyHomeomorphOn.{u2, u1} X Y _inst_1 _inst_2 f s) -> (forall {x : X}, (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x s) -> (Eq.{succ u1} (Filter.{u1} Y) (Filter.map.{u2, u1} X Y f (nhds.{u2} X _inst_1 x)) (nhds.{u1} Y _inst_2 (f x))))
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph_on.map_nhds_eq IsLocallyHomeomorphOn.map_nhds_eqₓ'. -/
theorem map_nhds_eq (hf : IsLocallyHomeomorphOn f s) {x : X} (hx : x ∈ s) : (𝓝 x).map f = 𝓝 (f x) :=
  let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx
#align is_locally_homeomorph_on.map_nhds_eq IsLocallyHomeomorphOn.map_nhds_eq

/- warning: is_locally_homeomorph_on.continuous_at -> IsLocallyHomeomorphOn.continuousAt is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y} {s : Set.{u1} X}, (IsLocallyHomeomorphOn.{u1, u2} X Y _inst_1 _inst_2 f s) -> (forall {x : X}, (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (ContinuousAt.{u1, u2} X Y _inst_1 _inst_2 f x))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y} {s : Set.{u2} X}, (IsLocallyHomeomorphOn.{u2, u1} X Y _inst_1 _inst_2 f s) -> (forall {x : X}, (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x s) -> (ContinuousAt.{u2, u1} X Y _inst_1 _inst_2 f x))
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph_on.continuous_at IsLocallyHomeomorphOn.continuousAtₓ'. -/
protected theorem continuousAt (hf : IsLocallyHomeomorphOn f s) {x : X} (hx : x ∈ s) :
    ContinuousAt f x :=
  (hf.map_nhds_eq hx).le
#align is_locally_homeomorph_on.continuous_at IsLocallyHomeomorphOn.continuousAt

/- warning: is_locally_homeomorph_on.continuous_on -> IsLocallyHomeomorphOn.continuousOn is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y} {s : Set.{u1} X}, (IsLocallyHomeomorphOn.{u1, u2} X Y _inst_1 _inst_2 f s) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y} {s : Set.{u2} X}, (IsLocallyHomeomorphOn.{u2, u1} X Y _inst_1 _inst_2 f s) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph_on.continuous_on IsLocallyHomeomorphOn.continuousOnₓ'. -/
protected theorem continuousOn (hf : IsLocallyHomeomorphOn f s) : ContinuousOn f s :=
  ContinuousAt.continuousOn fun x => hf.ContinuousAt
#align is_locally_homeomorph_on.continuous_on IsLocallyHomeomorphOn.continuousOn

/- warning: is_locally_homeomorph_on.comp -> IsLocallyHomeomorphOn.comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {g : Y -> Z} {f : X -> Y} {s : Set.{u1} X} {t : Set.{u2} Y}, (IsLocallyHomeomorphOn.{u2, u3} Y Z _inst_2 _inst_3 g t) -> (IsLocallyHomeomorphOn.{u1, u2} X Y _inst_1 _inst_2 f s) -> (Set.MapsTo.{u1, u2} X Y f s t) -> (IsLocallyHomeomorphOn.{u1, u3} X Z _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f) s)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} Y] [_inst_3 : TopologicalSpace.{u2} Z] {g : Y -> Z} {f : X -> Y} {s : Set.{u1} X} {t : Set.{u3} Y}, (IsLocallyHomeomorphOn.{u3, u2} Y Z _inst_2 _inst_3 g t) -> (IsLocallyHomeomorphOn.{u1, u3} X Y _inst_1 _inst_2 f s) -> (Set.MapsTo.{u1, u3} X Y f s t) -> (IsLocallyHomeomorphOn.{u1, u2} X Z _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} X Y Z g f) s)
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph_on.comp IsLocallyHomeomorphOn.compₓ'. -/
protected theorem comp (hg : IsLocallyHomeomorphOn g t) (hf : IsLocallyHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocallyHomeomorphOn (g ∘ f) s :=
  by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩
#align is_locally_homeomorph_on.comp IsLocallyHomeomorphOn.comp

end IsLocallyHomeomorphOn

#print IsLocallyHomeomorph /-
/-- A function `f : X → Y` satisfies `is_locally_homeomorph f` if each `x : x` is contained in
  the source of some `e : local_homeomorph X Y` with `f = e`. -/
def IsLocallyHomeomorph :=
  ∀ x : X, ∃ e : LocalHomeomorph X Y, x ∈ e.source ∧ f = e
#align is_locally_homeomorph IsLocallyHomeomorph
-/

variable {f}

/- warning: is_locally_homeomorph_iff_is_locally_homeomorph_on_univ -> isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y}, Iff (IsLocallyHomeomorph.{u1, u2} X Y _inst_1 _inst_2 f) (IsLocallyHomeomorphOn.{u1, u2} X Y _inst_1 _inst_2 f (Set.univ.{u1} X))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y}, Iff (IsLocallyHomeomorph.{u2, u1} X Y _inst_1 _inst_2 f) (IsLocallyHomeomorphOn.{u2, u1} X Y _inst_1 _inst_2 f (Set.univ.{u2} X))
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph_iff_is_locally_homeomorph_on_univ isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univₓ'. -/
theorem isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ :
    IsLocallyHomeomorph f ↔ IsLocallyHomeomorphOn f Set.univ := by
  simp only [IsLocallyHomeomorph, IsLocallyHomeomorphOn, Set.mem_univ, forall_true_left]
#align is_locally_homeomorph_iff_is_locally_homeomorph_on_univ isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ

/- warning: is_locally_homeomorph.is_locally_homeomorph_on -> IsLocallyHomeomorph.isLocallyHomeomorphOn is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y}, (IsLocallyHomeomorph.{u1, u2} X Y _inst_1 _inst_2 f) -> (IsLocallyHomeomorphOn.{u1, u2} X Y _inst_1 _inst_2 f (Set.univ.{u1} X))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y}, (IsLocallyHomeomorph.{u2, u1} X Y _inst_1 _inst_2 f) -> (IsLocallyHomeomorphOn.{u2, u1} X Y _inst_1 _inst_2 f (Set.univ.{u2} X))
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph.is_locally_homeomorph_on IsLocallyHomeomorph.isLocallyHomeomorphOnₓ'. -/
protected theorem IsLocallyHomeomorph.isLocallyHomeomorphOn (hf : IsLocallyHomeomorph f) :
    IsLocallyHomeomorphOn f Set.univ :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mp hf
#align is_locally_homeomorph.is_locally_homeomorph_on IsLocallyHomeomorph.isLocallyHomeomorphOn

variable (f)

namespace IsLocallyHomeomorph

/- warning: is_locally_homeomorph.mk -> IsLocallyHomeomorph.mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : X -> Y), (forall (x : X), Exists.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} X Y _inst_1 _inst_2) (fun (e : LocalHomeomorph.{u1, u2} X Y _inst_1 _inst_2) => And (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x (LocalEquiv.source.{u1, u2} X Y (LocalHomeomorph.toLocalEquiv.{u1, u2} X Y _inst_1 _inst_2 e))) (forall (y : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y (LocalEquiv.source.{u1, u2} X Y (LocalHomeomorph.toLocalEquiv.{u1, u2} X Y _inst_1 _inst_2 e))) -> (Eq.{succ u2} Y (f y) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} X Y _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} X Y _inst_1 _inst_2) => X -> Y) (LocalHomeomorph.hasCoeToFun.{u1, u2} X Y _inst_1 _inst_2) e y))))) -> (IsLocallyHomeomorph.{u1, u2} X Y _inst_1 _inst_2 f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] (f : X -> Y), (forall (x : X), Exists.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} X Y _inst_1 _inst_2) (fun (e : LocalHomeomorph.{u2, u1} X Y _inst_1 _inst_2) => And (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x (LocalEquiv.source.{u2, u1} X Y (LocalHomeomorph.toLocalEquiv.{u2, u1} X Y _inst_1 _inst_2 e))) (forall (y : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y (LocalEquiv.source.{u2, u1} X Y (LocalHomeomorph.toLocalEquiv.{u2, u1} X Y _inst_1 _inst_2 e))) -> (Eq.{succ u1} Y (f y) (LocalHomeomorph.toFun'.{u2, u1} X Y _inst_1 _inst_2 e y))))) -> (IsLocallyHomeomorph.{u2, u1} X Y _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph.mk IsLocallyHomeomorph.mkₓ'. -/
/-- Proves that `f` satisfies `is_locally_homeomorph f`. The condition `h` is weaker than the
definition of `is_locally_homeomorph f`, since it only requires `e : local_homeomorph X Y` to
agree with `f` on its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x : X, ∃ e : LocalHomeomorph X Y, x ∈ e.source ∧ ∀ y ∈ e.source, f y = e y) :
    IsLocallyHomeomorph f :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mpr
    (IsLocallyHomeomorphOn.mk f Set.univ fun x hx => h x)
#align is_locally_homeomorph.mk IsLocallyHomeomorph.mk

variable {g f}

/- warning: is_locally_homeomorph.map_nhds_eq -> IsLocallyHomeomorph.map_nhds_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y}, (IsLocallyHomeomorph.{u1, u2} X Y _inst_1 _inst_2 f) -> (forall (x : X), Eq.{succ u2} (Filter.{u2} Y) (Filter.map.{u1, u2} X Y f (nhds.{u1} X _inst_1 x)) (nhds.{u2} Y _inst_2 (f x)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y}, (IsLocallyHomeomorph.{u2, u1} X Y _inst_1 _inst_2 f) -> (forall (x : X), Eq.{succ u1} (Filter.{u1} Y) (Filter.map.{u2, u1} X Y f (nhds.{u2} X _inst_1 x)) (nhds.{u1} Y _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph.map_nhds_eq IsLocallyHomeomorph.map_nhds_eqₓ'. -/
theorem map_nhds_eq (hf : IsLocallyHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
  hf.IsLocallyHomeomorphOn.map_nhds_eq (Set.mem_univ x)
#align is_locally_homeomorph.map_nhds_eq IsLocallyHomeomorph.map_nhds_eq

/- warning: is_locally_homeomorph.continuous -> IsLocallyHomeomorph.continuous is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y}, (IsLocallyHomeomorph.{u1, u2} X Y _inst_1 _inst_2 f) -> (Continuous.{u1, u2} X Y _inst_1 _inst_2 f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y}, (IsLocallyHomeomorph.{u2, u1} X Y _inst_1 _inst_2 f) -> (Continuous.{u2, u1} X Y _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph.continuous IsLocallyHomeomorph.continuousₓ'. -/
protected theorem continuous (hf : IsLocallyHomeomorph f) : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.IsLocallyHomeomorphOn.ContinuousOn
#align is_locally_homeomorph.continuous IsLocallyHomeomorph.continuous

/- warning: is_locally_homeomorph.is_open_map -> IsLocallyHomeomorph.isOpenMap is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y}, (IsLocallyHomeomorph.{u1, u2} X Y _inst_1 _inst_2 f) -> (IsOpenMap.{u1, u2} X Y _inst_1 _inst_2 f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y}, (IsLocallyHomeomorph.{u2, u1} X Y _inst_1 _inst_2 f) -> (IsOpenMap.{u2, u1} X Y _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph.is_open_map IsLocallyHomeomorph.isOpenMapₓ'. -/
protected theorem isOpenMap (hf : IsLocallyHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x => ge_of_eq (hf.map_nhds_eq x)
#align is_locally_homeomorph.is_open_map IsLocallyHomeomorph.isOpenMap

/- warning: is_locally_homeomorph.comp -> IsLocallyHomeomorph.comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {g : Y -> Z} {f : X -> Y}, (IsLocallyHomeomorph.{u2, u3} Y Z _inst_2 _inst_3 g) -> (IsLocallyHomeomorph.{u1, u2} X Y _inst_1 _inst_2 f) -> (IsLocallyHomeomorph.{u1, u3} X Z _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} Y] [_inst_3 : TopologicalSpace.{u2} Z] {g : Y -> Z} {f : X -> Y}, (IsLocallyHomeomorph.{u3, u2} Y Z _inst_2 _inst_3 g) -> (IsLocallyHomeomorph.{u1, u3} X Y _inst_1 _inst_2 f) -> (IsLocallyHomeomorph.{u1, u2} X Z _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} X Y Z g f))
Case conversion may be inaccurate. Consider using '#align is_locally_homeomorph.comp IsLocallyHomeomorph.compₓ'. -/
protected theorem comp (hg : IsLocallyHomeomorph g) (hf : IsLocallyHomeomorph f) :
    IsLocallyHomeomorph (g ∘ f) :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mpr
    (hg.IsLocallyHomeomorphOn.comp hf.IsLocallyHomeomorphOn (Set.univ.mapsTo_univ f))
#align is_locally_homeomorph.comp IsLocallyHomeomorph.comp

end IsLocallyHomeomorph

