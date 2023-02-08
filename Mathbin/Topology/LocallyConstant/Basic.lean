/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.locally_constant.basic
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.Connected
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Tactic.Tfae
import Mathbin.Tactic.FinCases

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `is_locally_constant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `locally_constant X Y` : the type of locally constant maps from `X` to `Y`
* `locally_constant.map` : push-forward of locally constant maps
* `locally_constant.comap` : pull-back of locally constant maps

-/


variable {X Y Z α : Type _} [TopologicalSpace X]

open Set Filter

open Topology

#print IsLocallyConstant /-
/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
def IsLocallyConstant (f : X → Y) : Prop :=
  ∀ s : Set Y, IsOpen (f ⁻¹' s)
#align is_locally_constant IsLocallyConstant
-/

namespace IsLocallyConstant

/- warning: is_locally_constant.tfae -> IsLocallyConstant.tfae is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (f : X -> Y), List.TFAE (List.cons.{0} Prop (IsLocallyConstant.{u1, u2} X Y _inst_1 f) (List.cons.{0} Prop (forall (x : X), Filter.Eventually.{u1} X (fun (x' : X) => Eq.{succ u2} Y (f x') (f x)) (nhds.{u1} X _inst_1 x)) (List.cons.{0} Prop (forall (x : X), IsOpen.{u1} X _inst_1 (setOf.{u1} X (fun (x' : X) => Eq.{succ u2} Y (f x') (f x)))) (List.cons.{0} Prop (forall (y : Y), IsOpen.{u1} X _inst_1 (Set.preimage.{u1, u2} X Y f (Singleton.singleton.{u2, u2} Y (Set.{u2} Y) (Set.hasSingleton.{u2} Y) y))) (List.cons.{0} Prop (forall (x : X), Exists.{succ u1} (Set.{u1} X) (fun (U : Set.{u1} X) => Exists.{0} (IsOpen.{u1} X _inst_1 U) (fun (hU : IsOpen.{u1} X _inst_1 U) => Exists.{0} (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U) (fun (hx : Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U) => forall (x' : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x' U) -> (Eq.{succ u2} Y (f x') (f x)))))) (List.nil.{0} Prop))))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (f : X -> Y), List.TFAE (List.cons.{0} Prop (IsLocallyConstant.{u2, u1} X Y _inst_1 f) (List.cons.{0} Prop (forall (x : X), Filter.Eventually.{u2} X (fun (x' : X) => Eq.{succ u1} Y (f x') (f x)) (nhds.{u2} X _inst_1 x)) (List.cons.{0} Prop (forall (x : X), IsOpen.{u2} X _inst_1 (setOf.{u2} X (fun (x' : X) => Eq.{succ u1} Y (f x') (f x)))) (List.cons.{0} Prop (forall (y : Y), IsOpen.{u2} X _inst_1 (Set.preimage.{u2, u1} X Y f (Singleton.singleton.{u1, u1} Y (Set.{u1} Y) (Set.instSingletonSet.{u1} Y) y))) (List.cons.{0} Prop (forall (x : X), Exists.{succ u2} (Set.{u2} X) (fun (U : Set.{u2} X) => And (IsOpen.{u2} X _inst_1 U) (And (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x U) (forall (x' : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x' U) -> (Eq.{succ u1} Y (f x') (f x)))))) (List.nil.{0} Prop))))))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.tfae IsLocallyConstant.tfaeₓ'. -/
protected theorem tfae (f : X → Y) :
    TFAE
      [IsLocallyConstant f, ∀ x, ∀ᶠ x' in 𝓝 x, f x' = f x, ∀ x, IsOpen { x' | f x' = f x },
        ∀ y, IsOpen (f ⁻¹' {y}),
        ∀ x, ∃ (U : Set X)(hU : IsOpen U)(hx : x ∈ U), ∀ x' ∈ U, f x' = f x] :=
  by
  tfae_have 1 → 4; exact fun h y => h {y}
  tfae_have 4 → 3; exact fun h x => h (f x)
  tfae_have 3 → 2; exact fun h x => IsOpen.mem_nhds (h x) rfl
  tfae_have 2 → 5
  · intro h x
    rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩
    exact ⟨U, hU, hx, Eq⟩
  tfae_have 5 → 1
  · intro h s
    refine' isOpen_iff_forall_mem_open.2 fun x hx => _
    rcases h x with ⟨U, hU, hxU, eq⟩
    exact ⟨U, fun x' hx' => mem_preimage.2 <| (Eq x' hx').symm ▸ hx, hU, hxU⟩
  tfae_finish
#align is_locally_constant.tfae IsLocallyConstant.tfae

/- warning: is_locally_constant.of_discrete -> IsLocallyConstant.of_discrete is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : DiscreteTopology.{u1} X _inst_1] (f : X -> Y), IsLocallyConstant.{u1, u2} X Y _inst_1 f
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : DiscreteTopology.{u2} X _inst_1] (f : X -> Y), IsLocallyConstant.{u2, u1} X Y _inst_1 f
Case conversion may be inaccurate. Consider using '#align is_locally_constant.of_discrete IsLocallyConstant.of_discreteₓ'. -/
@[nontriviality]
theorem of_discrete [DiscreteTopology X] (f : X → Y) : IsLocallyConstant f := fun s =>
  isOpen_discrete _
#align is_locally_constant.of_discrete IsLocallyConstant.of_discrete

/- warning: is_locally_constant.is_open_fiber -> IsLocallyConstant.isOpen_fiber is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall (y : Y), IsOpen.{u1} X _inst_1 (setOf.{u1} X (fun (x : X) => Eq.{succ u2} Y (f x) y)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (forall (y : Y), IsOpen.{u2} X _inst_1 (setOf.{u2} X (fun (x : X) => Eq.{succ u1} Y (f x) y)))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.is_open_fiber IsLocallyConstant.isOpen_fiberₓ'. -/
theorem isOpen_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsOpen { x | f x = y } :=
  hf {y}
#align is_locally_constant.is_open_fiber IsLocallyConstant.isOpen_fiber

/- warning: is_locally_constant.is_closed_fiber -> IsLocallyConstant.isClosed_fiber is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall (y : Y), IsClosed.{u1} X _inst_1 (setOf.{u1} X (fun (x : X) => Eq.{succ u2} Y (f x) y)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (forall (y : Y), IsClosed.{u2} X _inst_1 (setOf.{u2} X (fun (x : X) => Eq.{succ u1} Y (f x) y)))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.is_closed_fiber IsLocallyConstant.isClosed_fiberₓ'. -/
theorem isClosed_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClosed { x | f x = y } :=
  ⟨hf ({y}ᶜ)⟩
#align is_locally_constant.is_closed_fiber IsLocallyConstant.isClosed_fiber

/- warning: is_locally_constant.is_clopen_fiber -> IsLocallyConstant.isClopen_fiber is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall (y : Y), IsClopen.{u1} X _inst_1 (setOf.{u1} X (fun (x : X) => Eq.{succ u2} Y (f x) y)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (forall (y : Y), IsClopen.{u2} X _inst_1 (setOf.{u2} X (fun (x : X) => Eq.{succ u1} Y (f x) y)))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.is_clopen_fiber IsLocallyConstant.isClopen_fiberₓ'. -/
theorem isClopen_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClopen { x | f x = y } :=
  ⟨isOpen_fiber hf _, isClosed_fiber hf _⟩
#align is_locally_constant.is_clopen_fiber IsLocallyConstant.isClopen_fiber

/- warning: is_locally_constant.iff_exists_open -> IsLocallyConstant.iff_exists_open is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (f : X -> Y), Iff (IsLocallyConstant.{u1, u2} X Y _inst_1 f) (forall (x : X), Exists.{succ u1} (Set.{u1} X) (fun (U : Set.{u1} X) => Exists.{0} (IsOpen.{u1} X _inst_1 U) (fun (hU : IsOpen.{u1} X _inst_1 U) => Exists.{0} (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U) (fun (hx : Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U) => forall (x' : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x' U) -> (Eq.{succ u2} Y (f x') (f x))))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (f : X -> Y), Iff (IsLocallyConstant.{u2, u1} X Y _inst_1 f) (forall (x : X), Exists.{succ u2} (Set.{u2} X) (fun (U : Set.{u2} X) => And (IsOpen.{u2} X _inst_1 U) (And (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x U) (forall (x' : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x' U) -> (Eq.{succ u1} Y (f x') (f x))))))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.iff_exists_open IsLocallyConstant.iff_exists_openₓ'. -/
theorem iff_exists_open (f : X → Y) :
    IsLocallyConstant f ↔ ∀ x, ∃ (U : Set X)(hU : IsOpen U)(hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
  (IsLocallyConstant.tfae f).out 0 4
#align is_locally_constant.iff_exists_open IsLocallyConstant.iff_exists_open

/- warning: is_locally_constant.iff_eventually_eq -> IsLocallyConstant.iff_eventually_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (f : X -> Y), Iff (IsLocallyConstant.{u1, u2} X Y _inst_1 f) (forall (x : X), Filter.Eventually.{u1} X (fun (y : X) => Eq.{succ u2} Y (f y) (f x)) (nhds.{u1} X _inst_1 x))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (f : X -> Y), Iff (IsLocallyConstant.{u2, u1} X Y _inst_1 f) (forall (x : X), Filter.Eventually.{u2} X (fun (y : X) => Eq.{succ u1} Y (f y) (f x)) (nhds.{u2} X _inst_1 x))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.iff_eventually_eq IsLocallyConstant.iff_eventually_eqₓ'. -/
theorem iff_eventually_eq (f : X → Y) : IsLocallyConstant f ↔ ∀ x, ∀ᶠ y in 𝓝 x, f y = f x :=
  (IsLocallyConstant.tfae f).out 0 1
#align is_locally_constant.iff_eventually_eq IsLocallyConstant.iff_eventually_eq

/- warning: is_locally_constant.exists_open -> IsLocallyConstant.exists_open is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall (x : X), Exists.{succ u1} (Set.{u1} X) (fun (U : Set.{u1} X) => Exists.{0} (IsOpen.{u1} X _inst_1 U) (fun (hU : IsOpen.{u1} X _inst_1 U) => Exists.{0} (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U) (fun (hx : Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U) => forall (x' : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x' U) -> (Eq.{succ u2} Y (f x') (f x))))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (forall (x : X), Exists.{succ u2} (Set.{u2} X) (fun (U : Set.{u2} X) => And (IsOpen.{u2} X _inst_1 U) (And (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x U) (forall (x' : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x' U) -> (Eq.{succ u1} Y (f x') (f x))))))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.exists_open IsLocallyConstant.exists_openₓ'. -/
theorem exists_open {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    ∃ (U : Set X)(hU : IsOpen U)(hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
  (iff_exists_open f).1 hf x
#align is_locally_constant.exists_open IsLocallyConstant.exists_open

/- warning: is_locally_constant.eventually_eq -> IsLocallyConstant.eventually_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall (x : X), Filter.Eventually.{u1} X (fun (y : X) => Eq.{succ u2} Y (f y) (f x)) (nhds.{u1} X _inst_1 x))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (forall (x : X), Filter.Eventually.{u2} X (fun (y : X) => Eq.{succ u1} Y (f y) (f x)) (nhds.{u2} X _inst_1 x))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.eventually_eq IsLocallyConstant.eventually_eqₓ'. -/
protected theorem eventually_eq {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    ∀ᶠ y in 𝓝 x, f y = f x :=
  (iff_eventually_eq f).1 hf x
#align is_locally_constant.eventually_eq IsLocallyConstant.eventually_eq

#print IsLocallyConstant.continuous /-
protected theorem continuous [TopologicalSpace Y] {f : X → Y} (hf : IsLocallyConstant f) :
    Continuous f :=
  ⟨fun U hU => hf _⟩
#align is_locally_constant.continuous IsLocallyConstant.continuous
-/

#print IsLocallyConstant.iff_continuous /-
theorem iff_continuous {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X → Y) :
    IsLocallyConstant f ↔ Continuous f :=
  ⟨IsLocallyConstant.continuous, fun h s => h.isOpen_preimage s (isOpen_discrete _)⟩
#align is_locally_constant.iff_continuous IsLocallyConstant.iff_continuous
-/

#print IsLocallyConstant.of_constant /-
theorem of_constant (f : X → Y) (h : ∀ x y, f x = f y) : IsLocallyConstant f :=
  (iff_eventually_eq f).2 fun x => eventually_of_forall fun x' => h _ _
#align is_locally_constant.of_constant IsLocallyConstant.of_constant
-/

/- warning: is_locally_constant.const -> IsLocallyConstant.const is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (y : Y), IsLocallyConstant.{u1, u2} X Y _inst_1 (Function.const.{succ u2, succ u1} Y X y)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (y : Y), IsLocallyConstant.{u2, u1} X Y _inst_1 (Function.const.{succ u1, succ u2} Y X y)
Case conversion may be inaccurate. Consider using '#align is_locally_constant.const IsLocallyConstant.constₓ'. -/
theorem const (y : Y) : IsLocallyConstant (Function.const X y) :=
  of_constant _ fun _ _ => rfl
#align is_locally_constant.const IsLocallyConstant.const

/- warning: is_locally_constant.comp -> IsLocallyConstant.comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall (g : Y -> Z), IsLocallyConstant.{u1, u3} X Z _inst_1 (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] {f : X -> Y}, (IsLocallyConstant.{u3, u2} X Y _inst_1 f) -> (forall (g : Y -> Z), IsLocallyConstant.{u3, u1} X Z _inst_1 (Function.comp.{succ u3, succ u2, succ u1} X Y Z g f))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.comp IsLocallyConstant.compₓ'. -/
theorem comp {f : X → Y} (hf : IsLocallyConstant f) (g : Y → Z) : IsLocallyConstant (g ∘ f) :=
  fun s => by
  rw [Set.preimage_comp]
  exact hf _
#align is_locally_constant.comp IsLocallyConstant.comp

/- warning: is_locally_constant.prod_mk -> IsLocallyConstant.prod_mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {Y' : Type.{u3}} {f : X -> Y} {f' : X -> Y'}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (IsLocallyConstant.{u1, u3} X Y' _inst_1 f') -> (IsLocallyConstant.{u1, max u2 u3} X (Prod.{u2, u3} Y Y') _inst_1 (fun (x : X) => Prod.mk.{u2, u3} Y Y' (f x) (f' x)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {Y' : Type.{u3}} {f : X -> Y} {f' : X -> Y'}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (IsLocallyConstant.{u2, u3} X Y' _inst_1 f') -> (IsLocallyConstant.{u2, max u3 u1} X (Prod.{u1, u3} Y Y') _inst_1 (fun (x : X) => Prod.mk.{u1, u3} Y Y' (f x) (f' x)))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.prod_mk IsLocallyConstant.prod_mkₓ'. -/
theorem prod_mk {Y'} {f : X → Y} {f' : X → Y'} (hf : IsLocallyConstant f)
    (hf' : IsLocallyConstant f') : IsLocallyConstant fun x => (f x, f' x) :=
  (iff_eventually_eq _).2 fun x =>
    (hf.EventuallyEq x).mp <| (hf'.EventuallyEq x).mono fun x' hf' hf => Prod.ext hf hf'
#align is_locally_constant.prod_mk IsLocallyConstant.prod_mk

/- warning: is_locally_constant.comp₂ -> IsLocallyConstant.comp₂ is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y₁ : Type.{u2}} {Y₂ : Type.{u3}} {Z : Type.{u4}} {f : X -> Y₁} {g : X -> Y₂}, (IsLocallyConstant.{u1, u2} X Y₁ _inst_1 f) -> (IsLocallyConstant.{u1, u3} X Y₂ _inst_1 g) -> (forall (h : Y₁ -> Y₂ -> Z), IsLocallyConstant.{u1, u4} X Z _inst_1 (fun (x : X) => h (f x) (g x)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y₁ : Type.{u4}} {Y₂ : Type.{u3}} {Z : Type.{u2}} {f : X -> Y₁} {g : X -> Y₂}, (IsLocallyConstant.{u1, u4} X Y₁ _inst_1 f) -> (IsLocallyConstant.{u1, u3} X Y₂ _inst_1 g) -> (forall (h : Y₁ -> Y₂ -> Z), IsLocallyConstant.{u1, u2} X Z _inst_1 (fun (x : X) => h (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.comp₂ IsLocallyConstant.comp₂ₓ'. -/
theorem comp₂ {Y₁ Y₂ Z : Type _} {f : X → Y₁} {g : X → Y₂} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (h : Y₁ → Y₂ → Z) : IsLocallyConstant fun x => h (f x) (g x) :=
  (hf.prod_mk hg).comp fun x : Y₁ × Y₂ => h x.1 x.2
#align is_locally_constant.comp₂ IsLocallyConstant.comp₂

/- warning: is_locally_constant.comp_continuous -> IsLocallyConstant.comp_continuous is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {g : Y -> Z} {f : X -> Y}, (IsLocallyConstant.{u2, u3} Y Z _inst_2 g) -> (Continuous.{u1, u2} X Y _inst_1 _inst_2 f) -> (IsLocallyConstant.{u1, u3} X Z _inst_1 (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} Y] {g : Y -> Z} {f : X -> Y}, (IsLocallyConstant.{u3, u2} Y Z _inst_2 g) -> (Continuous.{u1, u3} X Y _inst_1 _inst_2 f) -> (IsLocallyConstant.{u1, u2} X Z _inst_1 (Function.comp.{succ u1, succ u3, succ u2} X Y Z g f))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.comp_continuous IsLocallyConstant.comp_continuousₓ'. -/
theorem comp_continuous [TopologicalSpace Y] {g : Y → Z} {f : X → Y} (hg : IsLocallyConstant g)
    (hf : Continuous f) : IsLocallyConstant (g ∘ f) := fun s =>
  by
  rw [Set.preimage_comp]
  exact hf.is_open_preimage _ (hg _)
#align is_locally_constant.comp_continuous IsLocallyConstant.comp_continuous

/- warning: is_locally_constant.apply_eq_of_is_preconnected -> IsLocallyConstant.apply_eq_of_isPreconnected is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall {s : Set.{u1} X}, (IsPreconnected.{u1} X _inst_1 s) -> (forall {x : X} {y : X}, (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y s) -> (Eq.{succ u2} Y (f x) (f y))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (forall {s : Set.{u2} X}, (IsPreconnected.{u2} X _inst_1 s) -> (forall {x : X} {y : X}, (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x s) -> (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y s) -> (Eq.{succ u1} Y (f x) (f y))))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.apply_eq_of_is_preconnected IsLocallyConstant.apply_eq_of_isPreconnectedₓ'. -/
/-- A locally constant function is constant on any preconnected set. -/
theorem apply_eq_of_isPreconnected {f : X → Y} (hf : IsLocallyConstant f) {s : Set X}
    (hs : IsPreconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  by
  let U := f ⁻¹' {f y}
  suffices : x ∉ Uᶜ; exact Classical.not_not.1 this
  intro hxV
  specialize hs U (Uᶜ) (hf {f y}) (hf ({f y}ᶜ)) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩
  · simp only [union_compl_self, subset_univ]
  · simpa only [inter_empty, not_nonempty_empty, inter_compl_self] using hs
#align is_locally_constant.apply_eq_of_is_preconnected IsLocallyConstant.apply_eq_of_isPreconnected

/- warning: is_locally_constant.apply_eq_of_preconnected_space -> IsLocallyConstant.apply_eq_of_preconnectedSpace is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PreconnectedSpace.{u1} X _inst_1] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall (x : X) (y : X), Eq.{succ u2} Y (f x) (f y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PreconnectedSpace.{u2} X _inst_1] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (forall (x : X) (y : X), Eq.{succ u1} Y (f x) (f y))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.apply_eq_of_preconnected_space IsLocallyConstant.apply_eq_of_preconnectedSpaceₓ'. -/
theorem apply_eq_of_preconnectedSpace [PreconnectedSpace X] {f : X → Y} (hf : IsLocallyConstant f)
    (x y : X) : f x = f y :=
  hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
#align is_locally_constant.apply_eq_of_preconnected_space IsLocallyConstant.apply_eq_of_preconnectedSpace

/- warning: is_locally_constant.eq_const -> IsLocallyConstant.eq_const is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PreconnectedSpace.{u1} X _inst_1] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (forall (x : X), Eq.{max (succ u1) (succ u2)} (X -> Y) f (Function.const.{succ u2, succ u1} Y X (f x)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PreconnectedSpace.{u2} X _inst_1] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (forall (x : X), Eq.{max (succ u2) (succ u1)} (X -> Y) f (Function.const.{succ u1, succ u2} Y X (f x)))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.eq_const IsLocallyConstant.eq_constₓ'. -/
theorem eq_const [PreconnectedSpace X] {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    f = Function.const X (f x) :=
  funext fun y => hf.apply_eq_of_preconnectedSpace y x
#align is_locally_constant.eq_const IsLocallyConstant.eq_const

/- warning: is_locally_constant.exists_eq_const -> IsLocallyConstant.exists_eq_const is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PreconnectedSpace.{u1} X _inst_1] [_inst_3 : Nonempty.{succ u2} Y] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (Exists.{succ u2} Y (fun (y : Y) => Eq.{max (succ u1) (succ u2)} (X -> Y) f (Function.const.{succ u2, succ u1} Y X y)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PreconnectedSpace.{u2} X _inst_1] [_inst_3 : Nonempty.{succ u1} Y] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (Exists.{succ u1} Y (fun (y : Y) => Eq.{max (succ u2) (succ u1)} (X -> Y) f (Function.const.{succ u1, succ u2} Y X y)))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.exists_eq_const IsLocallyConstant.exists_eq_constₓ'. -/
theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] {f : X → Y} (hf : IsLocallyConstant f) :
    ∃ y, f = Function.const X y := by
  cases isEmpty_or_nonempty X
  · exact ⟨Classical.arbitrary Y, funext <| h.elim⟩
  · exact ⟨f (Classical.arbitrary X), hf.eq_const _⟩
#align is_locally_constant.exists_eq_const IsLocallyConstant.exists_eq_const

/- warning: is_locally_constant.iff_is_const -> IsLocallyConstant.iff_is_const is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PreconnectedSpace.{u1} X _inst_1] {f : X -> Y}, Iff (IsLocallyConstant.{u1, u2} X Y _inst_1 f) (forall (x : X) (y : X), Eq.{succ u2} Y (f x) (f y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PreconnectedSpace.{u2} X _inst_1] {f : X -> Y}, Iff (IsLocallyConstant.{u2, u1} X Y _inst_1 f) (forall (x : X) (y : X), Eq.{succ u1} Y (f x) (f y))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.iff_is_const IsLocallyConstant.iff_is_constₓ'. -/
theorem iff_is_const [PreconnectedSpace X] {f : X → Y} : IsLocallyConstant f ↔ ∀ x y, f x = f y :=
  ⟨fun h x y => h.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial, of_constant _⟩
#align is_locally_constant.iff_is_const IsLocallyConstant.iff_is_const

/- warning: is_locally_constant.range_finite -> IsLocallyConstant.range_finite is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : CompactSpace.{u1} X _inst_1] {f : X -> Y}, (IsLocallyConstant.{u1, u2} X Y _inst_1 f) -> (Set.Finite.{u2} Y (Set.range.{u2, succ u1} Y X f))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : CompactSpace.{u2} X _inst_1] {f : X -> Y}, (IsLocallyConstant.{u2, u1} X Y _inst_1 f) -> (Set.Finite.{u1} Y (Set.range.{u1, succ u2} Y X f))
Case conversion may be inaccurate. Consider using '#align is_locally_constant.range_finite IsLocallyConstant.range_finiteₓ'. -/
theorem range_finite [CompactSpace X] {f : X → Y} (hf : IsLocallyConstant f) :
    (Set.range f).Finite := by
  letI : TopologicalSpace Y := ⊥; haveI := discreteTopology_bot Y
  rw [@iff_continuous X Y ‹_› ‹_›] at hf
  exact (isCompact_range hf).finite_of_discrete
#align is_locally_constant.range_finite IsLocallyConstant.range_finite

#print IsLocallyConstant.one /-
@[to_additive]
theorem one [One Y] : IsLocallyConstant (1 : X → Y) :=
  const 1
#align is_locally_constant.one IsLocallyConstant.one
#align is_locally_constant.zero IsLocallyConstant.zero
-/

#print IsLocallyConstant.inv /-
@[to_additive]
theorem inv [Inv Y] ⦃f : X → Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant f⁻¹ :=
  hf.comp fun x => x⁻¹
#align is_locally_constant.inv IsLocallyConstant.inv
#align is_locally_constant.neg IsLocallyConstant.neg
-/

#print IsLocallyConstant.mul /-
@[to_additive]
theorem mul [Mul Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (f * g) :=
  hf.comp₂ hg (· * ·)
#align is_locally_constant.mul IsLocallyConstant.mul
#align is_locally_constant.add IsLocallyConstant.add
-/

#print IsLocallyConstant.div /-
@[to_additive]
theorem div [Div Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (f / g) :=
  hf.comp₂ hg (· / ·)
#align is_locally_constant.div IsLocallyConstant.div
#align is_locally_constant.sub IsLocallyConstant.sub
-/

/- warning: is_locally_constant.desc -> IsLocallyConstant.desc is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {α : Type.{u2}} {β : Type.{u3}} (f : X -> α) (g : α -> β), (IsLocallyConstant.{u1, u3} X β _inst_1 (Function.comp.{succ u1, succ u2, succ u3} X α β g f)) -> (Function.Injective.{succ u2, succ u3} α β g) -> (IsLocallyConstant.{u1, u2} X α _inst_1 f)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {α : Type.{u3}} {β : Type.{u2}} (f : X -> α) (g : α -> β), (IsLocallyConstant.{u1, u2} X β _inst_1 (Function.comp.{succ u1, succ u3, succ u2} X α β g f)) -> (Function.Injective.{succ u3, succ u2} α β g) -> (IsLocallyConstant.{u1, u3} X α _inst_1 f)
Case conversion may be inaccurate. Consider using '#align is_locally_constant.desc IsLocallyConstant.descₓ'. -/
/-- If a composition of a function `f` followed by an injection `g` is locally
constant, then the locally constant property descends to `f`. -/
theorem desc {α β : Type _} (f : X → α) (g : α → β) (h : IsLocallyConstant (g ∘ f))
    (inj : Function.Injective g) : IsLocallyConstant f :=
  by
  rw [(IsLocallyConstant.tfae f).out 0 3]
  intro a
  have : f ⁻¹' {a} = g ∘ f ⁻¹' {g a} := by
    ext x
    simp only [mem_singleton_iff, Function.comp_apply, mem_preimage]
    exact ⟨fun h => by rw [h], fun h => inj h⟩
  rw [this]
  apply h
#align is_locally_constant.desc IsLocallyConstant.desc

/- warning: is_locally_constant.of_constant_on_connected_components -> IsLocallyConstant.of_constant_on_connected_components is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LocallyConnectedSpace.{u1} X _inst_1] {f : X -> Y}, (forall (x : X) (y : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y (connectedComponent.{u1} X _inst_1 x)) -> (Eq.{succ u2} Y (f y) (f x))) -> (IsLocallyConstant.{u1, u2} X Y _inst_1 f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : LocallyConnectedSpace.{u2} X _inst_1] {f : X -> Y}, (forall (x : X) (y : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y (connectedComponent.{u2} X _inst_1 x)) -> (Eq.{succ u1} Y (f y) (f x))) -> (IsLocallyConstant.{u2, u1} X Y _inst_1 f)
Case conversion may be inaccurate. Consider using '#align is_locally_constant.of_constant_on_connected_components IsLocallyConstant.of_constant_on_connected_componentsₓ'. -/
theorem of_constant_on_connected_components [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ x, ∀ y ∈ connectedComponent x, f y = f x) : IsLocallyConstant f :=
  by
  rw [iff_exists_open]
  exact fun x => ⟨connectedComponent x, isOpen_connectedComponent, mem_connectedComponent, h x⟩
#align is_locally_constant.of_constant_on_connected_components IsLocallyConstant.of_constant_on_connected_components

/- warning: is_locally_constant.of_constant_on_preconnected_clopens -> IsLocallyConstant.of_constant_on_preconnected_clopens is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LocallyConnectedSpace.{u1} X _inst_1] {f : X -> Y}, (forall (U : Set.{u1} X), (IsPreconnected.{u1} X _inst_1 U) -> (IsClopen.{u1} X _inst_1 U) -> (forall (x : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U) -> (forall (y : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y U) -> (Eq.{succ u2} Y (f y) (f x))))) -> (IsLocallyConstant.{u1, u2} X Y _inst_1 f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : LocallyConnectedSpace.{u2} X _inst_1] {f : X -> Y}, (forall (U : Set.{u2} X), (IsPreconnected.{u2} X _inst_1 U) -> (IsClopen.{u2} X _inst_1 U) -> (forall (x : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x U) -> (forall (y : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y U) -> (Eq.{succ u1} Y (f y) (f x))))) -> (IsLocallyConstant.{u2, u1} X Y _inst_1 f)
Case conversion may be inaccurate. Consider using '#align is_locally_constant.of_constant_on_preconnected_clopens IsLocallyConstant.of_constant_on_preconnected_clopensₓ'. -/
theorem of_constant_on_preconnected_clopens [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ U : Set X, IsPreconnected U → IsClopen U → ∀ x ∈ U, ∀ y ∈ U, f y = f x) :
    IsLocallyConstant f :=
  of_constant_on_connected_components fun x =>
    h (connectedComponent x) isPreconnected_connectedComponent isClopen_connectedComponent x
      mem_connectedComponent
#align is_locally_constant.of_constant_on_preconnected_clopens IsLocallyConstant.of_constant_on_preconnected_clopens

end IsLocallyConstant

#print LocallyConstant /-
/-- A (bundled) locally constant function from a topological space `X` to a type `Y`. -/
@[protect_proj]
structure LocallyConstant (X Y : Type _) [TopologicalSpace X] where
  toFun : X → Y
  IsLocallyConstant : IsLocallyConstant to_fun
#align locally_constant LocallyConstant
-/

namespace LocallyConstant

instance [Inhabited Y] : Inhabited (LocallyConstant X Y) :=
  ⟨⟨_, IsLocallyConstant.const default⟩⟩

instance : CoeFun (LocallyConstant X Y) fun _ => X → Y :=
  ⟨LocallyConstant.toFun⟩

initialize_simps_projections LocallyConstant (toFun → apply)

/- warning: locally_constant.to_fun_eq_coe -> LocallyConstant.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (f : LocallyConstant.{u1, u2} X Y _inst_1), Eq.{max (succ u1) (succ u2)} (X -> Y) (LocallyConstant.toFun.{u1, u2} X Y _inst_1 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (f : LocallyConstant.{u2, u1} X Y _inst_1), Eq.{max (succ u2) (succ u1)} (X -> Y) (LocallyConstant.toFun.{u2, u1} X Y _inst_1 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f)
Case conversion may be inaccurate. Consider using '#align locally_constant.to_fun_eq_coe LocallyConstant.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe (f : LocallyConstant X Y) : f.toFun = f :=
  rfl
#align locally_constant.to_fun_eq_coe LocallyConstant.toFun_eq_coe

/- warning: locally_constant.coe_mk -> LocallyConstant.coe_mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (f : X -> Y) (h : IsLocallyConstant.{u1, u2} X Y _inst_1 f), Eq.{max (succ u1) (succ u2)} (X -> Y) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) (LocallyConstant.mk.{u1, u2} X Y _inst_1 f h)) f
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (f : X -> Y) (h : IsLocallyConstant.{u2, u1} X Y _inst_1 f), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : X), (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) (LocallyConstant.mk.{u2, u1} X Y _inst_1 f h)) f
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_mk LocallyConstant.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : X → Y) (h) : ⇑(⟨f, h⟩ : LocallyConstant X Y) = f :=
  rfl
#align locally_constant.coe_mk LocallyConstant.coe_mk

/- warning: locally_constant.congr_fun -> LocallyConstant.congr_fun is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : LocallyConstant.{u1, u2} X Y _inst_1} {g : LocallyConstant.{u1, u2} X Y _inst_1}, (Eq.{max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) f g) -> (forall (x : X), Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) g x))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : LocallyConstant.{u2, u1} X Y _inst_1} {g : LocallyConstant.{u2, u1} X Y _inst_1}, (Eq.{max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Y _inst_1) f g) -> (forall (x : X), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) g x))
Case conversion may be inaccurate. Consider using '#align locally_constant.congr_fun LocallyConstant.congr_funₓ'. -/
theorem congr_fun {f g : LocallyConstant X Y} (h : f = g) (x : X) : f x = g x :=
  congr_arg (fun h : LocallyConstant X Y => h x) h
#align locally_constant.congr_fun LocallyConstant.congr_fun

/- warning: locally_constant.congr_arg -> LocallyConstant.congr_arg is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (f : LocallyConstant.{u1, u2} X Y _inst_1) {x : X} {y : X}, (Eq.{succ u1} X x y) -> (Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (f : LocallyConstant.{u2, u1} X Y _inst_1) {x : X} {y : X}, (Eq.{succ u2} X x y) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f y))
Case conversion may be inaccurate. Consider using '#align locally_constant.congr_arg LocallyConstant.congr_argₓ'. -/
theorem congr_arg (f : LocallyConstant X Y) {x y : X} (h : x = y) : f x = f y :=
  congr_arg (fun x : X => f x) h
#align locally_constant.congr_arg LocallyConstant.congr_arg

#print LocallyConstant.coe_injective /-
theorem coe_injective : @Function.Injective (LocallyConstant X Y) (X → Y) coeFn
  | ⟨f, hf⟩, ⟨g, hg⟩, h => by
    have : f = g := h
    subst f
#align locally_constant.coe_injective LocallyConstant.coe_injective
-/

/- warning: locally_constant.coe_inj -> LocallyConstant.coe_inj is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : LocallyConstant.{u1, u2} X Y _inst_1} {g : LocallyConstant.{u1, u2} X Y _inst_1}, Iff (Eq.{max (succ u1) (succ u2)} ((fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) g)) (Eq.{max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) f g)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : LocallyConstant.{u2, u1} X Y _inst_1} {g : LocallyConstant.{u2, u1} X Y _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (forall (a : X), (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) g)) (Eq.{max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Y _inst_1) f g)
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_inj LocallyConstant.coe_injₓ'. -/
@[simp, norm_cast]
theorem coe_inj {f g : LocallyConstant X Y} : (f : X → Y) = g ↔ f = g :=
  coe_injective.eq_iff
#align locally_constant.coe_inj LocallyConstant.coe_inj

/- warning: locally_constant.ext -> LocallyConstant.ext is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {{f : LocallyConstant.{u1, u2} X Y _inst_1}} {{g : LocallyConstant.{u1, u2} X Y _inst_1}}, (forall (x : X), Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) g x)) -> (Eq.{max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) f g)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {{f : LocallyConstant.{u2, u1} X Y _inst_1}} {{g : LocallyConstant.{u2, u1} X Y _inst_1}}, (forall (x : X), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) g x)) -> (Eq.{max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Y _inst_1) f g)
Case conversion may be inaccurate. Consider using '#align locally_constant.ext LocallyConstant.extₓ'. -/
@[ext]
theorem ext ⦃f g : LocallyConstant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)
#align locally_constant.ext LocallyConstant.ext

/- warning: locally_constant.ext_iff -> LocallyConstant.ext_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : LocallyConstant.{u1, u2} X Y _inst_1} {g : LocallyConstant.{u1, u2} X Y _inst_1}, Iff (Eq.{max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) f g) (forall (x : X), Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) g x))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : LocallyConstant.{u2, u1} X Y _inst_1} {g : LocallyConstant.{u2, u1} X Y _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Y _inst_1) f g) (forall (x : X), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) g x))
Case conversion may be inaccurate. Consider using '#align locally_constant.ext_iff LocallyConstant.ext_iffₓ'. -/
theorem ext_iff {f g : LocallyConstant X Y} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩
#align locally_constant.ext_iff LocallyConstant.ext_iff

section CodomainTopologicalSpace

variable [TopologicalSpace Y] (f : LocallyConstant X Y)

/- warning: locally_constant.continuous -> LocallyConstant.continuous is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : LocallyConstant.{u1, u2} X Y _inst_1), Continuous.{u1, u2} X Y _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] (f : LocallyConstant.{u2, u1} X Y _inst_1), Continuous.{u2, u1} X Y _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f)
Case conversion may be inaccurate. Consider using '#align locally_constant.continuous LocallyConstant.continuousₓ'. -/
protected theorem continuous : Continuous f :=
  f.IsLocallyConstant.Continuous
#align locally_constant.continuous LocallyConstant.continuous

#print LocallyConstant.toContinuousMap /-
/-- We can turn a locally-constant function into a bundled `continuous_map`. -/
def toContinuousMap : C(X, Y) :=
  ⟨f, f.Continuous⟩
#align locally_constant.to_continuous_map LocallyConstant.toContinuousMap
-/

/-- As a shorthand, `locally_constant.to_continuous_map` is available as a coercion -/
instance : Coe (LocallyConstant X Y) C(X, Y) :=
  ⟨toContinuousMap⟩

/- warning: locally_constant.to_continuous_map_eq_coe clashes with [anonymous] -> [anonymous]
warning: locally_constant.to_continuous_map_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : LocallyConstant.{u1, u2} X Y _inst_1), Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.toContinuousMap.{u1, u2} X Y _inst_1 _inst_2 f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.ContinuousMap.hasCoe.{u1, u2} X Y _inst_1 _inst_2)))) f)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}}, (Nat -> X -> Y) -> Nat -> (List.{u1} X) -> (List.{u2} Y)
Case conversion may be inaccurate. Consider using '#align locally_constant.to_continuous_map_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] : f.toContinuousMap = f :=
  rfl
#align locally_constant.to_continuous_map_eq_coe [anonymous]

/- warning: locally_constant.coe_continuous_map -> LocallyConstant.coe_continuousMap is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : LocallyConstant.{u1, u2} X Y _inst_1), Eq.{max (succ u1) (succ u2)} ((fun (_x : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) => X -> Y) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.ContinuousMap.hasCoe.{u1, u2} X Y _inst_1 _inst_2)))) f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) => X -> Y) (ContinuousMap.hasCoeToFun.{u1, u2} X Y _inst_1 _inst_2) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.ContinuousMap.hasCoe.{u1, u2} X Y _inst_1 _inst_2)))) f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] (f : LocallyConstant.{u2, u1} X Y _inst_1), Eq.{max (succ u2) (succ u1)} (forall (a : X), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : X) => Y) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : X) => Y) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) X Y _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} X Y _inst_1 _inst_2)) (LocallyConstant.toContinuousMap.{u2, u1} X Y _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f)
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_continuous_map LocallyConstant.coe_continuousMapₓ'. -/
@[simp]
theorem coe_continuousMap : ((f : C(X, Y)) : X → Y) = (f : X → Y) :=
  rfl
#align locally_constant.coe_continuous_map LocallyConstant.coe_continuousMap

/- warning: locally_constant.to_continuous_map_injective -> LocallyConstant.toContinuousMap_injective is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y], Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (LocallyConstant.toContinuousMap.{u1, u2} X Y _inst_1 _inst_2)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Y _inst_1) (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) (LocallyConstant.toContinuousMap.{u2, u1} X Y _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align locally_constant.to_continuous_map_injective LocallyConstant.toContinuousMap_injectiveₓ'. -/
theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : LocallyConstant X Y → C(X, Y)) := fun _ _ h =>
  ext (ContinuousMap.congr_fun h)
#align locally_constant.to_continuous_map_injective LocallyConstant.toContinuousMap_injective

end CodomainTopologicalSpace

#print LocallyConstant.const /-
/-- The constant locally constant function on `X` with value `y : Y`. -/
def const (X : Type _) {Y : Type _} [TopologicalSpace X] (y : Y) : LocallyConstant X Y :=
  ⟨Function.const X y, IsLocallyConstant.const _⟩
#align locally_constant.const LocallyConstant.const
-/

/- warning: locally_constant.coe_const -> LocallyConstant.coe_const is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (y : Y), Eq.{max (succ u1) (succ u2)} ((fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.const.{u1, u2} X Y _inst_1 y)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) (LocallyConstant.const.{u1, u2} X Y _inst_1 y)) (Function.const.{succ u2, succ u1} Y X y)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (y : Y), Eq.{max (succ u2) (succ u1)} (forall (a : X), (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) (LocallyConstant.const.{u2, u1} X Y _inst_1 y)) (Function.const.{succ u1, succ u2} Y X y)
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_const LocallyConstant.coe_constₓ'. -/
@[simp]
theorem coe_const (y : Y) : (const X y : X → Y) = Function.const X y :=
  rfl
#align locally_constant.coe_const LocallyConstant.coe_const

#print LocallyConstant.ofClopen /-
/-- The locally constant function to `fin 2` associated to a clopen set. -/
def ofClopen {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : LocallyConstant X (Fin 2)
    where
  toFun x := if x ∈ U then 0 else 1
  IsLocallyConstant :=
    by
    rw [(IsLocallyConstant.tfae fun x => if x ∈ U then (0 : Fin 2) else 1).out 0 3]
    intro e
    fin_cases e
    · convert hU.1 using 1
      ext
      simp only [mem_singleton_iff, Fin.one_eq_zero_iff, mem_preimage, ite_eq_left_iff,
        Nat.succ_succ_ne_one]
      tauto
    · rw [← isClosed_compl_iff]
      convert hU.2
      ext
      simp
#align locally_constant.of_clopen LocallyConstant.ofClopen
-/

/- warning: locally_constant.of_clopen_fiber_zero -> LocallyConstant.ofClopen_fiber_zero is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {U : Set.{u1} X} [_inst_3 : forall (x : X), Decidable (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U)] (hU : IsClopen.{u1} X _inst_2 U), Eq.{succ u1} (Set.{u1} X) (Set.preimage.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (coeFn.{succ u1, succ u1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) (fun (_x : LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) => X -> (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (LocallyConstant.hasCoeToFun.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) (LocallyConstant.ofClopen.{u1} X _inst_2 U (fun (x : X) => _inst_3 x) hU)) (Singleton.singleton.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Set.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Set.hasSingleton.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))) U
but is expected to have type
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {U : Set.{u1} X} [_inst_3 : forall (x : X), Decidable (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x U)] (hU : IsClopen.{u1} X _inst_2 U), Eq.{succ u1} (Set.{u1} X) (Set.preimage.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (FunLike.coe.{succ u1, succ u1, 1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) (LocallyConstant.ofClopen.{u1} X _inst_2 U (fun (x : X) => _inst_3 x) hU)) (Singleton.singleton.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Set.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Set.instSingletonSet.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) U
Case conversion may be inaccurate. Consider using '#align locally_constant.of_clopen_fiber_zero LocallyConstant.ofClopen_fiber_zeroₓ'. -/
@[simp]
theorem ofClopen_fiber_zero {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : ofClopen hU ⁻¹' ({0} : Set (Fin 2)) = U :=
  by
  ext
  simp only [of_clopen, mem_singleton_iff, Fin.one_eq_zero_iff, coe_mk, mem_preimage,
    ite_eq_left_iff, Nat.succ_succ_ne_one]
  tauto
#align locally_constant.of_clopen_fiber_zero LocallyConstant.ofClopen_fiber_zero

/- warning: locally_constant.of_clopen_fiber_one -> LocallyConstant.ofClopen_fiber_one is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {U : Set.{u1} X} [_inst_3 : forall (x : X), Decidable (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U)] (hU : IsClopen.{u1} X _inst_2 U), Eq.{succ u1} (Set.{u1} X) (Set.preimage.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (coeFn.{succ u1, succ u1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) (fun (_x : LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) => X -> (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (LocallyConstant.hasCoeToFun.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) (LocallyConstant.ofClopen.{u1} X _inst_2 U (fun (x : X) => _inst_3 x) hU)) (Singleton.singleton.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Set.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Set.hasSingleton.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) U)
but is expected to have type
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {U : Set.{u1} X} [_inst_3 : forall (x : X), Decidable (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x U)] (hU : IsClopen.{u1} X _inst_2 U), Eq.{succ u1} (Set.{u1} X) (Set.preimage.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (FunLike.coe.{succ u1, succ u1, 1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) (LocallyConstant.ofClopen.{u1} X _inst_2 U (fun (x : X) => _inst_3 x) hU)) (Singleton.singleton.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Set.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Set.instSingletonSet.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) U)
Case conversion may be inaccurate. Consider using '#align locally_constant.of_clopen_fiber_one LocallyConstant.ofClopen_fiber_oneₓ'. -/
@[simp]
theorem ofClopen_fiber_one {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : ofClopen hU ⁻¹' ({1} : Set (Fin 2)) = Uᶜ :=
  by
  ext
  simp only [of_clopen, mem_singleton_iff, coe_mk, Fin.zero_eq_one_iff, mem_preimage,
    ite_eq_right_iff, mem_compl_iff, Nat.succ_succ_ne_one]
  tauto
#align locally_constant.of_clopen_fiber_one LocallyConstant.ofClopen_fiber_one

/- warning: locally_constant.locally_constant_eq_of_fiber_zero_eq -> LocallyConstant.locallyConstant_eq_of_fiber_zero_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] (f : LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) (g : LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2), (Eq.{succ u1} (Set.{u1} X) (Set.preimage.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (coeFn.{succ u1, succ u1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) (fun (_x : LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) => X -> (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (LocallyConstant.hasCoeToFun.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) f) (Singleton.singleton.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Set.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Set.hasSingleton.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))) (Set.preimage.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (coeFn.{succ u1, succ u1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) (fun (_x : LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) => X -> (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (LocallyConstant.hasCoeToFun.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) g) (Singleton.singleton.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Set.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Set.hasSingleton.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))))) -> (Eq.{succ u1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_2) f g)
but is expected to have type
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] (f : LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) (g : LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2), (Eq.{succ u1} (Set.{u1} X) (Set.preimage.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (FunLike.coe.{succ u1, succ u1, 1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) f) (Singleton.singleton.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Set.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Set.instSingletonSet.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (Set.preimage.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (FunLike.coe.{succ u1, succ u1, 1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) g) (Singleton.singleton.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Set.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Set.instSingletonSet.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))) -> (Eq.{succ u1} (LocallyConstant.{u1, 0} X (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align locally_constant.locally_constant_eq_of_fiber_zero_eq LocallyConstant.locallyConstant_eq_of_fiber_zero_eqₓ'. -/
theorem locallyConstant_eq_of_fiber_zero_eq {X : Type _} [TopologicalSpace X]
    (f g : LocallyConstant X (Fin 2)) (h : f ⁻¹' ({0} : Set (Fin 2)) = g ⁻¹' {0}) : f = g :=
  by
  simp only [Set.ext_iff, mem_singleton_iff, mem_preimage] at h
  ext1 x
  exact Fin.fin_two_eq_of_eq_zero_iff (h x)
#align locally_constant.locally_constant_eq_of_fiber_zero_eq LocallyConstant.locallyConstant_eq_of_fiber_zero_eq

/- warning: locally_constant.range_finite -> LocallyConstant.range_finite is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : CompactSpace.{u1} X _inst_1] (f : LocallyConstant.{u1, u2} X Y _inst_1), Set.Finite.{u2} Y (Set.range.{u2, succ u1} Y X (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : CompactSpace.{u2} X _inst_1] (f : LocallyConstant.{u2, u1} X Y _inst_1), Set.Finite.{u1} Y (Set.range.{u1, succ u2} Y X (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f))
Case conversion may be inaccurate. Consider using '#align locally_constant.range_finite LocallyConstant.range_finiteₓ'. -/
theorem range_finite [CompactSpace X] (f : LocallyConstant X Y) : (Set.range f).Finite :=
  f.IsLocallyConstant.range_finite
#align locally_constant.range_finite LocallyConstant.range_finite

/- warning: locally_constant.apply_eq_of_is_preconnected -> LocallyConstant.apply_eq_of_isPreconnected is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] (f : LocallyConstant.{u1, u2} X Y _inst_1) {s : Set.{u1} X}, (IsPreconnected.{u1} X _inst_1 s) -> (forall {x : X} {y : X}, (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y s) -> (Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f y)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] (f : LocallyConstant.{u2, u1} X Y _inst_1) {s : Set.{u2} X}, (IsPreconnected.{u2} X _inst_1 s) -> (forall {x : X} {y : X}, (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x s) -> (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y s) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f y)))
Case conversion may be inaccurate. Consider using '#align locally_constant.apply_eq_of_is_preconnected LocallyConstant.apply_eq_of_isPreconnectedₓ'. -/
theorem apply_eq_of_isPreconnected (f : LocallyConstant X Y) {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  f.IsLocallyConstant.apply_eq_of_isPreconnected hs hx hy
#align locally_constant.apply_eq_of_is_preconnected LocallyConstant.apply_eq_of_isPreconnected

/- warning: locally_constant.apply_eq_of_preconnected_space -> LocallyConstant.apply_eq_of_preconnectedSpace is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PreconnectedSpace.{u1} X _inst_1] (f : LocallyConstant.{u1, u2} X Y _inst_1) (x : X) (y : X), Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f y)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PreconnectedSpace.{u2} X _inst_1] (f : LocallyConstant.{u2, u1} X Y _inst_1) (x : X) (y : X), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f y)
Case conversion may be inaccurate. Consider using '#align locally_constant.apply_eq_of_preconnected_space LocallyConstant.apply_eq_of_preconnectedSpaceₓ'. -/
theorem apply_eq_of_preconnectedSpace [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X) :
    f x = f y :=
  f.IsLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
#align locally_constant.apply_eq_of_preconnected_space LocallyConstant.apply_eq_of_preconnectedSpace

/- warning: locally_constant.eq_const -> LocallyConstant.eq_const is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PreconnectedSpace.{u1} X _inst_1] (f : LocallyConstant.{u1, u2} X Y _inst_1) (x : X), Eq.{max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) f (LocallyConstant.const.{u1, u2} X Y _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) f x))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PreconnectedSpace.{u2} X _inst_1] (f : LocallyConstant.{u2, u1} X Y _inst_1) (x : X), Eq.{max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Y _inst_1) f (LocallyConstant.const.{u2, u1} X ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) f x))
Case conversion may be inaccurate. Consider using '#align locally_constant.eq_const LocallyConstant.eq_constₓ'. -/
theorem eq_const [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X) : f = const X (f x) :=
  ext fun y => apply_eq_of_preconnectedSpace f _ _
#align locally_constant.eq_const LocallyConstant.eq_const

/- warning: locally_constant.exists_eq_const -> LocallyConstant.exists_eq_const is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : PreconnectedSpace.{u1} X _inst_1] [_inst_3 : Nonempty.{succ u2} Y] (f : LocallyConstant.{u1, u2} X Y _inst_1), Exists.{succ u2} Y (fun (y : Y) => Eq.{max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) f (LocallyConstant.const.{u1, u2} X Y _inst_1 y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : PreconnectedSpace.{u2} X _inst_1] [_inst_3 : Nonempty.{succ u1} Y] (f : LocallyConstant.{u2, u1} X Y _inst_1), Exists.{succ u1} Y (fun (y : Y) => Eq.{max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Y _inst_1) f (LocallyConstant.const.{u2, u1} X Y _inst_1 y))
Case conversion may be inaccurate. Consider using '#align locally_constant.exists_eq_const LocallyConstant.exists_eq_constₓ'. -/
theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X Y) :
    ∃ y, f = const X y :=
  by
  rcases Classical.em (Nonempty X) with (⟨⟨x⟩⟩ | hX)
  · exact ⟨f x, f.eq_const x⟩
  · exact ⟨Classical.arbitrary Y, ext fun x => (hX ⟨x⟩).elim⟩
#align locally_constant.exists_eq_const LocallyConstant.exists_eq_const

#print LocallyConstant.map /-
/-- Push forward of locally constant maps under any map, by post-composition. -/
def map (f : Y → Z) : LocallyConstant X Y → LocallyConstant X Z := fun g =>
  ⟨f ∘ g, fun s => by
    rw [Set.preimage_comp]
    apply g.is_locally_constant⟩
#align locally_constant.map LocallyConstant.map
-/

/- warning: locally_constant.map_apply -> LocallyConstant.map_apply is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] (f : Y -> Z) (g : LocallyConstant.{u1, u2} X Y _inst_1), Eq.{max (succ u1) (succ u3)} (X -> Z) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocallyConstant.{u1, u3} X Z _inst_1) (fun (_x : LocallyConstant.{u1, u3} X Z _inst_1) => X -> Z) (LocallyConstant.hasCoeToFun.{u1, u3} X Z _inst_1) (LocallyConstant.map.{u1, u2, u3} X Y Z _inst_1 f g)) (Function.comp.{succ u1, succ u2, succ u3} X Y Z f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) g))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] (f : Y -> Z) (g : LocallyConstant.{u3, u2} X Y _inst_1), Eq.{max (succ u3) (succ u1)} (forall (ᾰ : X), (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Z) ᾰ) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (LocallyConstant.{u3, u1} X Z _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Z) _x) (LocallyConstant.instFunLikeLocallyConstant.{u3, u1} X Z _inst_1) (LocallyConstant.map.{u3, u2, u1} X Y Z _inst_1 f g)) (Function.comp.{succ u3, succ u2, succ u1} X Y Z f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (LocallyConstant.{u3, u2} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u3, u2} X Y _inst_1) g))
Case conversion may be inaccurate. Consider using '#align locally_constant.map_apply LocallyConstant.map_applyₓ'. -/
@[simp]
theorem map_apply (f : Y → Z) (g : LocallyConstant X Y) : ⇑(map f g) = f ∘ g :=
  rfl
#align locally_constant.map_apply LocallyConstant.map_apply

/- warning: locally_constant.map_id -> LocallyConstant.map_id is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X], Eq.{max (succ u1) (succ u2)} ((LocallyConstant.{u1, u2} X Y _inst_1) -> (LocallyConstant.{u1, u2} X Y _inst_1)) (LocallyConstant.map.{u1, u2, u2} X Y Y _inst_1 (id.{succ u2} Y)) (id.{max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X], Eq.{max (succ u2) (succ u1)} ((LocallyConstant.{u2, u1} X Y _inst_1) -> (LocallyConstant.{u2, u1} X Y _inst_1)) (LocallyConstant.map.{u2, u1, u1} X Y Y _inst_1 (id.{succ u1} Y)) (id.{max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Y _inst_1))
Case conversion may be inaccurate. Consider using '#align locally_constant.map_id LocallyConstant.map_idₓ'. -/
@[simp]
theorem map_id : @map X Y Y _ id = id := by
  ext
  rfl
#align locally_constant.map_id LocallyConstant.map_id

/- warning: locally_constant.map_comp -> LocallyConstant.map_comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y₁ : Type.{u2}} {Y₂ : Type.{u3}} {Y₃ : Type.{u4}} (g : Y₂ -> Y₃) (f : Y₁ -> Y₂), Eq.{max (max (succ u1) (succ u2)) (succ u1) (succ u4)} ((LocallyConstant.{u1, u2} X Y₁ _inst_1) -> (LocallyConstant.{u1, u4} X Y₃ _inst_1)) (Function.comp.{max (succ u1) (succ u2), max (succ u1) (succ u3), max (succ u1) (succ u4)} (LocallyConstant.{u1, u2} X Y₁ _inst_1) (LocallyConstant.{u1, u3} X Y₂ _inst_1) (LocallyConstant.{u1, u4} X Y₃ _inst_1) (LocallyConstant.map.{u1, u3, u4} X Y₂ Y₃ _inst_1 g) (LocallyConstant.map.{u1, u2, u3} X Y₁ Y₂ _inst_1 f)) (LocallyConstant.map.{u1, u2, u4} X Y₁ Y₃ _inst_1 (Function.comp.{succ u2, succ u3, succ u4} Y₁ Y₂ Y₃ g f))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y₁ : Type.{u4}} {Y₂ : Type.{u3}} {Y₃ : Type.{u2}} (g : Y₂ -> Y₃) (f : Y₁ -> Y₂), Eq.{max (max (succ u1) (succ u4)) (succ u2)} ((LocallyConstant.{u1, u4} X Y₁ _inst_1) -> (LocallyConstant.{u1, u2} X Y₃ _inst_1)) (Function.comp.{max (succ u4) (succ u1), max (succ u1) (succ u3), max (succ u1) (succ u2)} (LocallyConstant.{u1, u4} X Y₁ _inst_1) (LocallyConstant.{u1, u3} X Y₂ _inst_1) (LocallyConstant.{u1, u2} X Y₃ _inst_1) (LocallyConstant.map.{u1, u3, u2} X Y₂ Y₃ _inst_1 g) (LocallyConstant.map.{u1, u4, u3} X Y₁ Y₂ _inst_1 f)) (LocallyConstant.map.{u1, u4, u2} X Y₁ Y₃ _inst_1 (Function.comp.{succ u4, succ u3, succ u2} Y₁ Y₂ Y₃ g f))
Case conversion may be inaccurate. Consider using '#align locally_constant.map_comp LocallyConstant.map_compₓ'. -/
@[simp]
theorem map_comp {Y₁ Y₂ Y₃ : Type _} (g : Y₂ → Y₃) (f : Y₁ → Y₂) :
    @map X _ _ _ g ∘ map f = map (g ∘ f) := by
  ext
  rfl
#align locally_constant.map_comp LocallyConstant.map_comp

#print LocallyConstant.flip /-
/-- Given a locally constant function to `α → β`, construct a family of locally constant
functions with values in β indexed by α. -/
def flip {X α β : Type _} [TopologicalSpace X] (f : LocallyConstant X (α → β)) (a : α) :
    LocallyConstant X β :=
  f.map fun f => f a
#align locally_constant.flip LocallyConstant.flip
-/

/- warning: locally_constant.unflip -> LocallyConstant.unflip is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : Fintype.{u2} α] [_inst_3 : TopologicalSpace.{u1} X], (α -> (LocallyConstant.{u1, u3} X β _inst_3)) -> (LocallyConstant.{u1, max u2 u3} X (α -> β) _inst_3)
but is expected to have type
  forall {X : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : Finite.{succ u2} α] [_inst_3 : TopologicalSpace.{u1} X], (α -> (LocallyConstant.{u1, u3} X β _inst_3)) -> (LocallyConstant.{u1, max u2 u3} X (α -> β) _inst_3)
Case conversion may be inaccurate. Consider using '#align locally_constant.unflip LocallyConstant.unflipₓ'. -/
/-- If α is finite, this constructs a locally constant function to `α → β` given a
family of locally constant functions with values in β indexed by α. -/
def unflip {X α β : Type _} [Fintype α] [TopologicalSpace X] (f : α → LocallyConstant X β) :
    LocallyConstant X (α → β) where
  toFun x a := f a x
  IsLocallyConstant := by
    rw [(IsLocallyConstant.tfae fun x a => f a x).out 0 3]
    intro g
    have : (fun (x : X) (a : α) => f a x) ⁻¹' {g} = ⋂ a : α, f a ⁻¹' {g a} := by tidy
    rw [this]
    apply isOpen_interᵢ
    intro a
    apply (f a).IsLocallyConstant
#align locally_constant.unflip LocallyConstant.unflip

/- warning: locally_constant.unflip_flip -> LocallyConstant.unflip_flip is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : Fintype.{u2} α] [_inst_3 : TopologicalSpace.{u1} X] (f : LocallyConstant.{u1, max u2 u3} X (α -> β) _inst_3), Eq.{max (succ u1) (succ (max u2 u3))} (LocallyConstant.{u1, max u2 u3} X (α -> β) _inst_3) (LocallyConstant.unflip.{u1, u2, u3} X α β _inst_2 _inst_3 (LocallyConstant.flip.{u1, u2, u3} X α β _inst_3 f)) f
but is expected to have type
  forall {X : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : Finite.{succ u2} α] [_inst_3 : TopologicalSpace.{u3} X] (f : LocallyConstant.{u3, max u2 u1} X (α -> β) _inst_3), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (LocallyConstant.{u3, max u2 u1} X (α -> β) _inst_3) (LocallyConstant.unflip.{u3, u2, u1} X α β _inst_2 _inst_3 (LocallyConstant.flip.{u3, u2, u1} X α β _inst_3 f)) f
Case conversion may be inaccurate. Consider using '#align locally_constant.unflip_flip LocallyConstant.unflip_flipₓ'. -/
@[simp]
theorem unflip_flip {X α β : Type _} [Fintype α] [TopologicalSpace X]
    (f : LocallyConstant X (α → β)) : unflip f.flip = f :=
  by
  ext
  rfl
#align locally_constant.unflip_flip LocallyConstant.unflip_flip

/- warning: locally_constant.flip_unflip -> LocallyConstant.flip_unflip is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : Fintype.{u2} α] [_inst_3 : TopologicalSpace.{u1} X] (f : α -> (LocallyConstant.{u1, u3} X β _inst_3)), Eq.{max (succ u2) (succ u1) (succ u3)} (α -> (LocallyConstant.{u1, u3} X β _inst_3)) (LocallyConstant.flip.{u1, u2, u3} X α β _inst_3 (LocallyConstant.unflip.{u1, u2, u3} X α β _inst_2 _inst_3 f)) f
but is expected to have type
  forall {X : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : Finite.{succ u2} α] [_inst_3 : TopologicalSpace.{u3} X] (f : α -> (LocallyConstant.{u3, u1} X β _inst_3)), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (α -> (LocallyConstant.{u3, u1} X β _inst_3)) (LocallyConstant.flip.{u3, u2, u1} X α β _inst_3 (LocallyConstant.unflip.{u3, u2, u1} X α β _inst_2 _inst_3 f)) f
Case conversion may be inaccurate. Consider using '#align locally_constant.flip_unflip LocallyConstant.flip_unflipₓ'. -/
@[simp]
theorem flip_unflip {X α β : Type _} [Fintype α] [TopologicalSpace X]
    (f : α → LocallyConstant X β) : (unflip f).flip = f :=
  by
  ext
  rfl
#align locally_constant.flip_unflip LocallyConstant.flip_unflip

section Comap

open Classical

variable [TopologicalSpace Y]

#print LocallyConstant.comap /-
/-- Pull back of locally constant maps under any map, by pre-composition.

This definition only makes sense if `f` is continuous,
in which case it sends locally constant functions to their precomposition with `f`.
See also `locally_constant.coe_comap`. -/
noncomputable def comap (f : X → Y) : LocallyConstant Y Z → LocallyConstant X Z :=
  if hf : Continuous f then fun g => ⟨g ∘ f, g.IsLocallyConstant.comp_continuous hf⟩
  else by
    by_cases H : Nonempty X
    · intro g
      exact const X (g <| f <| Classical.arbitrary X)
    · intro g
      refine' ⟨fun x => (H ⟨x⟩).elim, _⟩
      intro s
      rw [isOpen_iff_nhds]
      intro x
      exact (H ⟨x⟩).elim
#align locally_constant.comap LocallyConstant.comap
-/

/- warning: locally_constant.coe_comap -> LocallyConstant.coe_comap is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : X -> Y) (g : LocallyConstant.{u2, u3} Y Z _inst_2), (Continuous.{u1, u2} X Y _inst_1 _inst_2 f) -> (Eq.{max (succ u1) (succ u3)} (X -> Z) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocallyConstant.{u1, u3} X Z _inst_1) (fun (_x : LocallyConstant.{u1, u3} X Z _inst_1) => X -> Z) (LocallyConstant.hasCoeToFun.{u1, u3} X Z _inst_1) (LocallyConstant.comap.{u1, u2, u3} X Y Z _inst_1 _inst_2 f g)) (Function.comp.{succ u1, succ u2, succ u3} X Y Z (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocallyConstant.{u2, u3} Y Z _inst_2) (fun (_x : LocallyConstant.{u2, u3} Y Z _inst_2) => Y -> Z) (LocallyConstant.hasCoeToFun.{u2, u3} Y Z _inst_2) g) f))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} Y] (f : X -> Y) (g : LocallyConstant.{u3, u2} Y Z _inst_2), (Continuous.{u1, u3} X Y _inst_1 _inst_2 f) -> (Eq.{max (succ u1) (succ u2)} (forall (ᾰ : X), (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Z) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LocallyConstant.{u1, u2} X Z _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Z) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, u2} X Z _inst_1) (LocallyConstant.comap.{u1, u3, u2} X Y Z _inst_1 _inst_2 f g)) (Function.comp.{succ u1, succ u3, succ u2} X Y Z (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (LocallyConstant.{u3, u2} Y Z _inst_2) Y (fun (_x : Y) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : Y) => Z) _x) (LocallyConstant.instFunLikeLocallyConstant.{u3, u2} Y Z _inst_2) g) f))
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_comap LocallyConstant.coe_comapₓ'. -/
@[simp]
theorem coe_comap (f : X → Y) (g : LocallyConstant Y Z) (hf : Continuous f) :
    ⇑(comap f g) = g ∘ f := by
  rw [comap, dif_pos hf]
  rfl
#align locally_constant.coe_comap LocallyConstant.coe_comap

/- warning: locally_constant.comap_id -> LocallyConstant.comap_id is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Z : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X], Eq.{max (succ u1) (succ u2)} ((LocallyConstant.{u1, u2} X Z _inst_1) -> (LocallyConstant.{u1, u2} X Z _inst_1)) (LocallyConstant.comap.{u1, u1, u2} X X Z _inst_1 _inst_1 (id.{succ u1} X)) (id.{max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Z _inst_1))
but is expected to have type
  forall {X : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X], Eq.{max (succ u2) (succ u1)} ((LocallyConstant.{u2, u1} X Z _inst_1) -> (LocallyConstant.{u2, u1} X Z _inst_1)) (LocallyConstant.comap.{u2, u2, u1} X X Z _inst_1 _inst_1 (id.{succ u2} X)) (id.{max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X Z _inst_1))
Case conversion may be inaccurate. Consider using '#align locally_constant.comap_id LocallyConstant.comap_idₓ'. -/
@[simp]
theorem comap_id : @comap X X Z _ _ id = id := by
  ext
  simp only [continuous_id, id.def, Function.comp.right_id, coe_comap]
#align locally_constant.comap_id LocallyConstant.comap_id

/- warning: locally_constant.comap_comp -> LocallyConstant.comap_comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} {α : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] (f : X -> Y) (g : Y -> Z), (Continuous.{u1, u2} X Y _inst_1 _inst_2 f) -> (Continuous.{u2, u3} Y Z _inst_2 _inst_3 g) -> (Eq.{max (max (succ u3) (succ u4)) (succ u1) (succ u4)} ((LocallyConstant.{u3, u4} Z α _inst_3) -> (LocallyConstant.{u1, u4} X α _inst_1)) (Function.comp.{max (succ u3) (succ u4), max (succ u2) (succ u4), max (succ u1) (succ u4)} (LocallyConstant.{u3, u4} Z α _inst_3) (LocallyConstant.{u2, u4} Y α _inst_2) (LocallyConstant.{u1, u4} X α _inst_1) (LocallyConstant.comap.{u1, u2, u4} X Y α _inst_1 _inst_2 f) (LocallyConstant.comap.{u2, u3, u4} Y Z α _inst_2 _inst_3 g)) (LocallyConstant.comap.{u1, u3, u4} X Z α _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f)))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u4}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u4} Z] (f : X -> Y) (g : Y -> Z), (Continuous.{u3, u2} X Y _inst_1 _inst_2 f) -> (Continuous.{u2, u4} Y Z _inst_2 _inst_3 g) -> (Eq.{max (max (succ u3) (succ u4)) (succ u1)} ((LocallyConstant.{u4, u1} Z α _inst_3) -> (LocallyConstant.{u3, u1} X α _inst_1)) (Function.comp.{max (succ u1) (succ u4), max (succ u1) (succ u2), max (succ u1) (succ u3)} (LocallyConstant.{u4, u1} Z α _inst_3) (LocallyConstant.{u2, u1} Y α _inst_2) (LocallyConstant.{u3, u1} X α _inst_1) (LocallyConstant.comap.{u3, u2, u1} X Y α _inst_1 _inst_2 f) (LocallyConstant.comap.{u2, u4, u1} Y Z α _inst_2 _inst_3 g)) (LocallyConstant.comap.{u3, u4, u1} X Z α _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u4} X Y Z g f)))
Case conversion may be inaccurate. Consider using '#align locally_constant.comap_comp LocallyConstant.comap_compₓ'. -/
theorem comap_comp [TopologicalSpace Z] (f : X → Y) (g : Y → Z) (hf : Continuous f)
    (hg : Continuous g) : @comap _ _ α _ _ f ∘ comap g = comap (g ∘ f) :=
  by
  ext
  simp only [hf, hg, hg.comp hf, coe_comap]
#align locally_constant.comap_comp LocallyConstant.comap_comp

/- warning: locally_constant.comap_const -> LocallyConstant.comap_const is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : X -> Y) (y : Y), (forall (x : X), Eq.{succ u2} Y (f x) y) -> (Eq.{max (max (succ u2) (succ u3)) (succ u1) (succ u3)} ((LocallyConstant.{u2, u3} Y Z _inst_2) -> (LocallyConstant.{u1, u3} X Z _inst_1)) (LocallyConstant.comap.{u1, u2, u3} X Y Z _inst_1 _inst_2 f) (fun (g : LocallyConstant.{u2, u3} Y Z _inst_2) => LocallyConstant.mk.{u1, u3} X Z _inst_1 (fun (x : X) => coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocallyConstant.{u2, u3} Y Z _inst_2) (fun (_x : LocallyConstant.{u2, u3} Y Z _inst_2) => Y -> Z) (LocallyConstant.hasCoeToFun.{u2, u3} Y Z _inst_2) g y) (IsLocallyConstant.const.{u1, u3} X Z _inst_1 (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocallyConstant.{u2, u3} Y Z _inst_2) (fun (_x : LocallyConstant.{u2, u3} Y Z _inst_2) => Y -> Z) (LocallyConstant.hasCoeToFun.{u2, u3} Y Z _inst_2) g y))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u3}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} Y] (f : X -> Y) (y : Y), (forall (x : X), Eq.{succ u3} Y (f x) y) -> (Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((LocallyConstant.{u3, u1} Y Z _inst_2) -> (LocallyConstant.{u2, u1} X Z _inst_1)) (LocallyConstant.comap.{u2, u3, u1} X Y Z _inst_1 _inst_2 f) (fun (g : LocallyConstant.{u3, u1} Y Z _inst_2) => LocallyConstant.mk.{u2, u1} X Z _inst_1 (fun (x : X) => FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (LocallyConstant.{u3, u1} Y Z _inst_2) Y (fun (_x : Y) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : Y) => Z) _x) (LocallyConstant.instFunLikeLocallyConstant.{u3, u1} Y Z _inst_2) g y) (IsLocallyConstant.const.{u1, u2} X Z _inst_1 (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (LocallyConstant.{u3, u1} Y Z _inst_2) Y (fun (_x : Y) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : Y) => Z) _x) (LocallyConstant.instFunLikeLocallyConstant.{u3, u1} Y Z _inst_2) g y))))
Case conversion may be inaccurate. Consider using '#align locally_constant.comap_const LocallyConstant.comap_constₓ'. -/
theorem comap_const (f : X → Y) (y : Y) (h : ∀ x, f x = y) :
    (comap f : LocallyConstant Y Z → LocallyConstant X Z) = fun g =>
      ⟨fun x => g y, IsLocallyConstant.const _⟩ :=
  by
  ext; rw [coe_comap]
  · simp only [h, coe_mk, Function.comp_apply]
  · rw [show f = fun x => y by ext <;> apply h]
    exact continuous_const
#align locally_constant.comap_const LocallyConstant.comap_const

end Comap

section Desc

#print LocallyConstant.desc /-
/-- If a locally constant function factors through an injection, then it factors through a locally
constant function. -/
def desc {X α β : Type _} [TopologicalSpace X] {g : α → β} (f : X → α) (h : LocallyConstant X β)
    (cond : g ∘ f = h) (inj : Function.Injective g) : LocallyConstant X α
    where
  toFun := f
  IsLocallyConstant :=
    IsLocallyConstant.desc _ g
      (by
        rw [cond]
        exact h.2)
      inj
#align locally_constant.desc LocallyConstant.desc
-/

/- warning: locally_constant.coe_desc -> LocallyConstant.coe_desc is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : TopologicalSpace.{u1} X] (f : X -> α) (g : α -> β) (h : LocallyConstant.{u1, u3} X β _inst_2) (cond : Eq.{max (succ u1) (succ u3)} (X -> β) (Function.comp.{succ u1, succ u2, succ u3} X α β g f) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocallyConstant.{u1, u3} X β _inst_2) (fun (_x : LocallyConstant.{u1, u3} X β _inst_2) => X -> β) (LocallyConstant.hasCoeToFun.{u1, u3} X β _inst_2) h)) (inj : Function.Injective.{succ u2, succ u3} α β g), Eq.{max (succ u1) (succ u2)} (X -> α) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X α _inst_2) (fun (_x : LocallyConstant.{u1, u2} X α _inst_2) => X -> α) (LocallyConstant.hasCoeToFun.{u1, u2} X α _inst_2) (LocallyConstant.desc.{u1, u2, u3} X α β _inst_2 g f h cond inj)) f
but is expected to have type
  forall {X : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} X] (f : X -> α) (g : α -> β) (h : LocallyConstant.{u3, u1} X β _inst_2) (cond : Eq.{max (succ u3) (succ u1)} (X -> β) (Function.comp.{succ u3, succ u2, succ u1} X α β g f) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (LocallyConstant.{u3, u1} X β _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => β) _x) (LocallyConstant.instFunLikeLocallyConstant.{u3, u1} X β _inst_2) h)) (inj : Function.Injective.{succ u2, succ u1} α β g), Eq.{max (succ u3) (succ u2)} (forall (ᾰ : X), (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => α) ᾰ) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (LocallyConstant.{u3, u2} X α _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => α) _x) (LocallyConstant.instFunLikeLocallyConstant.{u3, u2} X α _inst_2) (LocallyConstant.desc.{u3, u2, u1} X α β _inst_2 g f h cond inj)) f
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_desc LocallyConstant.coe_descₓ'. -/
@[simp]
theorem coe_desc {X α β : Type _} [TopologicalSpace X] (f : X → α) (g : α → β)
    (h : LocallyConstant X β) (cond : g ∘ f = h) (inj : Function.Injective g) :
    ⇑(desc f h cond inj) = f :=
  rfl
#align locally_constant.coe_desc LocallyConstant.coe_desc

end Desc

section Indicator

variable {R : Type _} [One R] {U : Set X} (f : LocallyConstant X R)

open Classical

#print LocallyConstant.mulIndicator /-
/-- Given a clopen set `U` and a locally constant function `f`, `locally_constant.mul_indicator`
  returns the locally constant function that is `f` on `U` and `1` otherwise. -/
@[to_additive
      " Given a clopen set `U` and a locally constant function `f`,\n  `locally_constant.indicator` returns the locally constant function that is `f` on `U` and `0`\n  otherwise. ",
  simps]
noncomputable def mulIndicator (hU : IsClopen U) : LocallyConstant X R
    where
  toFun := Set.mulIndicator U f
  IsLocallyConstant := by
    rw [IsLocallyConstant.iff_exists_open]; rintro x
    obtain ⟨V, hV, hx, h'⟩ := (IsLocallyConstant.iff_exists_open _).1 f.is_locally_constant x
    by_cases x ∈ U
    · refine' ⟨U ∩ V, IsOpen.inter hU.1 hV, Set.mem_inter h hx, _⟩
      rintro y hy
      rw [Set.mem_inter_iff] at hy
      rw [Set.mulIndicator_of_mem hy.1, Set.mulIndicator_of_mem h]
      apply h' y hy.2
    · rw [← Set.mem_compl_iff] at h
      refine' ⟨Uᶜ, (IsClopen.compl hU).1, h, _⟩
      rintro y hy
      rw [Set.mem_compl_iff] at h
      rw [Set.mem_compl_iff] at hy
      simp [h, hy]
#align locally_constant.mul_indicator LocallyConstant.mulIndicator
#align locally_constant.indicator LocallyConstant.indicator
-/

variable (a : X)

/- warning: locally_constant.mul_indicator_apply_eq_if -> LocallyConstant.mulIndicator_apply_eq_if is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {R : Type.{u2}} [_inst_2 : One.{u2} R] {U : Set.{u1} X} (f : LocallyConstant.{u1, u2} X R _inst_1) (a : X) (hU : IsClopen.{u1} X _inst_1 U), Eq.{succ u2} R (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X R _inst_1) (fun (_x : LocallyConstant.{u1, u2} X R _inst_1) => X -> R) (LocallyConstant.hasCoeToFun.{u1, u2} X R _inst_1) (LocallyConstant.mulIndicator.{u1, u2} X _inst_1 R _inst_2 U f hU) a) (ite.{succ u2} R (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) a U) (Classical.propDecidable (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) a U)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X R _inst_1) (fun (_x : LocallyConstant.{u1, u2} X R _inst_1) => X -> R) (LocallyConstant.hasCoeToFun.{u1, u2} X R _inst_1) f a) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R _inst_2))))
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {R : Type.{u1}} [_inst_2 : One.{u1} R] {U : Set.{u2} X} (f : LocallyConstant.{u2, u1} X R _inst_1) (a : X) (hU : IsClopen.{u2} X _inst_1 U), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X R _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X R _inst_1) (LocallyConstant.mulIndicator.{u2, u1} X _inst_1 R _inst_2 U f hU) a) (ite.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) a) (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) a U) (Classical.propDecidable (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) a U)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X R _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X R _inst_1) f a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) a) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) a) _inst_2)))
Case conversion may be inaccurate. Consider using '#align locally_constant.mul_indicator_apply_eq_if LocallyConstant.mulIndicator_apply_eq_ifₓ'. -/
@[to_additive]
theorem mulIndicator_apply_eq_if (hU : IsClopen U) :
    mulIndicator f hU a = if a ∈ U then f a else 1 :=
  Set.mulIndicator_apply U f a
#align locally_constant.mul_indicator_apply_eq_if LocallyConstant.mulIndicator_apply_eq_if
#align locally_constant.indicator_apply_eq_if LocallyConstant.indicator_apply_eq_if

variable {a}

/- warning: locally_constant.mul_indicator_of_mem -> LocallyConstant.mulIndicator_of_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {R : Type.{u2}} [_inst_2 : One.{u2} R] {U : Set.{u1} X} (f : LocallyConstant.{u1, u2} X R _inst_1) {a : X} (hU : IsClopen.{u1} X _inst_1 U), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) a U) -> (Eq.{succ u2} R (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X R _inst_1) (fun (_x : LocallyConstant.{u1, u2} X R _inst_1) => X -> R) (LocallyConstant.hasCoeToFun.{u1, u2} X R _inst_1) (LocallyConstant.mulIndicator.{u1, u2} X _inst_1 R _inst_2 U f hU) a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X R _inst_1) (fun (_x : LocallyConstant.{u1, u2} X R _inst_1) => X -> R) (LocallyConstant.hasCoeToFun.{u1, u2} X R _inst_1) f a))
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {R : Type.{u1}} [_inst_2 : One.{u1} R] {U : Set.{u2} X} (f : LocallyConstant.{u2, u1} X R _inst_1) {a : X} (hU : IsClopen.{u2} X _inst_1 U), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) a U) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X R _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X R _inst_1) (LocallyConstant.mulIndicator.{u2, u1} X _inst_1 R _inst_2 U f hU) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X R _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X R _inst_1) f a))
Case conversion may be inaccurate. Consider using '#align locally_constant.mul_indicator_of_mem LocallyConstant.mulIndicator_of_memₓ'. -/
@[to_additive]
theorem mulIndicator_of_mem (hU : IsClopen U) (h : a ∈ U) : f.mulIndicator hU a = f a :=
  by
  rw [mul_indicator_apply]
  apply Set.mulIndicator_of_mem h
#align locally_constant.mul_indicator_of_mem LocallyConstant.mulIndicator_of_mem
#align locally_constant.indicator_of_mem LocallyConstant.indicator_of_mem

/- warning: locally_constant.mul_indicator_of_not_mem -> LocallyConstant.mulIndicator_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {R : Type.{u2}} [_inst_2 : One.{u2} R] {U : Set.{u1} X} (f : LocallyConstant.{u1, u2} X R _inst_1) {a : X} (hU : IsClopen.{u1} X _inst_1 U), (Not (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) a U)) -> (Eq.{succ u2} R (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X R _inst_1) (fun (_x : LocallyConstant.{u1, u2} X R _inst_1) => X -> R) (LocallyConstant.hasCoeToFun.{u1, u2} X R _inst_1) (LocallyConstant.mulIndicator.{u1, u2} X _inst_1 R _inst_2 U f hU) a) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R _inst_2))))
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {R : Type.{u1}} [_inst_2 : One.{u1} R] {U : Set.{u2} X} (f : LocallyConstant.{u2, u1} X R _inst_1) {a : X} (hU : IsClopen.{u2} X _inst_1 U), (Not (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) a U)) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X R _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X R _inst_1) (LocallyConstant.mulIndicator.{u2, u1} X _inst_1 R _inst_2 U f hU) a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) a) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => R) a) _inst_2)))
Case conversion may be inaccurate. Consider using '#align locally_constant.mul_indicator_of_not_mem LocallyConstant.mulIndicator_of_not_memₓ'. -/
@[to_additive]
theorem mulIndicator_of_not_mem (hU : IsClopen U) (h : a ∉ U) : f.mulIndicator hU a = 1 :=
  by
  rw [mul_indicator_apply]
  apply Set.mulIndicator_of_not_mem h
#align locally_constant.mul_indicator_of_not_mem LocallyConstant.mulIndicator_of_not_mem
#align locally_constant.indicator_of_not_mem LocallyConstant.indicator_of_not_mem

end Indicator

end LocallyConstant

