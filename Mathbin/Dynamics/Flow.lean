/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo

! This file was ported from Lean 3 source module dynamics.flow
! leanprover-community/mathlib commit 717c073262cd9d59b1a1dcda7e8ab570c5b63370
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Group.Basic
import Mathbin.Logic.Function.Iterate

/-!
# Flows and invariant sets

This file defines a flow on a topological space `α` by a topological
monoid `τ` as a continuous monoid-act of `τ` on `α`. Anticipating the
cases where `τ` is one of `ℕ`, `ℤ`, `ℝ⁺`, or `ℝ`, we use additive
notation for the monoids, though the definition does not require
commutativity.

A subset `s` of `α` is invariant under a family of maps `ϕₜ : α → α`
if `ϕₜ s ⊆ s` for all `t`. In many cases `ϕ` will be a flow on
`α`. For the cases where `ϕ` is a flow by an ordered (additive,
commutative) monoid, we additionally define forward invariance, where
`t` ranges over those elements which are nonnegative.

Additionally, we define such constructions as the restriction of a
flow onto an invariant subset, and the time-reveral of a flow by a
group.
-/


open Set Function Filter

/-!
### Invariant sets
-/


section Invariant

variable {τ : Type _} {α : Type _}

#print IsInvariant /-
/-- A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t` in `τ`. -/
def IsInvariant (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ t, MapsTo (ϕ t) s s
#align is_invariant IsInvariant
-/

variable (ϕ : τ → α → α) (s : Set α)

/- warning: is_invariant_iff_image -> isInvariant_iff_image is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} (ϕ : τ -> α -> α) (s : Set.{u2} α), Iff (IsInvariant.{u1, u2} τ α ϕ s) (forall (t : τ), HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (Set.image.{u2, u2} α α (ϕ t) s) s)
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} (ϕ : τ -> α -> α) (s : Set.{u1} α), Iff (IsInvariant.{u2, u1} τ α ϕ s) (forall (t : τ), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.image.{u1, u1} α α (ϕ t) s) s)
Case conversion may be inaccurate. Consider using '#align is_invariant_iff_image isInvariant_iff_imageₓ'. -/
theorem isInvariant_iff_image : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s ⊆ s := by
  simp_rw [IsInvariant, maps_to']
#align is_invariant_iff_image isInvariant_iff_image

#print IsFwInvariant /-
/-- A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t ≥ 0`. -/
def IsFwInvariant [Preorder τ] [Zero τ] (ϕ : τ → α → α) (s : Set α) : Prop :=
  ∀ ⦃t⦄, 0 ≤ t → MapsTo (ϕ t) s s
#align is_fw_invariant IsFwInvariant
-/

/- warning: is_invariant.is_fw_invariant -> IsInvariant.isFwInvariant is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} τ] [_inst_2 : Zero.{u1} τ] {ϕ : τ -> α -> α} {s : Set.{u2} α}, (IsInvariant.{u1, u2} τ α ϕ s) -> (IsFwInvariant.{u1, u2} τ α _inst_1 _inst_2 ϕ s)
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} τ] [_inst_2 : Zero.{u2} τ] {ϕ : τ -> α -> α} {s : Set.{u1} α}, (IsInvariant.{u2, u1} τ α ϕ s) -> (IsFwInvariant.{u2, u1} τ α _inst_1 _inst_2 ϕ s)
Case conversion may be inaccurate. Consider using '#align is_invariant.is_fw_invariant IsInvariant.isFwInvariantₓ'. -/
theorem IsInvariant.isFwInvariant [Preorder τ] [Zero τ] {ϕ : τ → α → α} {s : Set α}
    (h : IsInvariant ϕ s) : IsFwInvariant ϕ s := fun t ht => h t
#align is_invariant.is_fw_invariant IsInvariant.isFwInvariant

/- warning: is_fw_invariant.is_invariant -> IsFwInvariant.isInvariant is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} τ] {ϕ : τ -> α -> α} {s : Set.{u2} α}, (IsFwInvariant.{u1, u2} τ α (PartialOrder.toPreorder.{u1} τ (OrderedAddCommMonoid.toPartialOrder.{u1} τ (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} τ _inst_1))) (AddZeroClass.toHasZero.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ (AddCommMonoid.toAddMonoid.{u1} τ (OrderedAddCommMonoid.toAddCommMonoid.{u1} τ (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} τ _inst_1))))) ϕ s) -> (IsInvariant.{u1, u2} τ α ϕ s)
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} τ] {ϕ : τ -> α -> α} {s : Set.{u1} α}, (IsFwInvariant.{u2, u1} τ α (PartialOrder.toPreorder.{u2} τ (OrderedAddCommMonoid.toPartialOrder.{u2} τ (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} τ _inst_1))) (AddMonoid.toZero.{u2} τ (AddCommMonoid.toAddMonoid.{u2} τ (OrderedAddCommMonoid.toAddCommMonoid.{u2} τ (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} τ _inst_1)))) ϕ s) -> (IsInvariant.{u2, u1} τ α ϕ s)
Case conversion may be inaccurate. Consider using '#align is_fw_invariant.is_invariant IsFwInvariant.isInvariantₓ'. -/
/-- If `τ` is a `canonically_ordered_add_monoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`is_fw_invariant` and `is_invariant` are equivalent. -/
theorem IsFwInvariant.isInvariant [CanonicallyOrderedAddMonoid τ] {ϕ : τ → α → α} {s : Set α}
    (h : IsFwInvariant ϕ s) : IsInvariant ϕ s := fun t => h (zero_le t)
#align is_fw_invariant.is_invariant IsFwInvariant.isInvariant

/- warning: is_fw_invariant_iff_is_invariant -> isFwInvariant_iff_isInvariant is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} τ] {ϕ : τ -> α -> α} {s : Set.{u2} α}, Iff (IsFwInvariant.{u1, u2} τ α (PartialOrder.toPreorder.{u1} τ (OrderedAddCommMonoid.toPartialOrder.{u1} τ (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} τ _inst_1))) (AddZeroClass.toHasZero.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ (AddCommMonoid.toAddMonoid.{u1} τ (OrderedAddCommMonoid.toAddCommMonoid.{u1} τ (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} τ _inst_1))))) ϕ s) (IsInvariant.{u1, u2} τ α ϕ s)
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} τ] {ϕ : τ -> α -> α} {s : Set.{u1} α}, Iff (IsFwInvariant.{u2, u1} τ α (PartialOrder.toPreorder.{u2} τ (OrderedAddCommMonoid.toPartialOrder.{u2} τ (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} τ _inst_1))) (AddMonoid.toZero.{u2} τ (AddCommMonoid.toAddMonoid.{u2} τ (OrderedAddCommMonoid.toAddCommMonoid.{u2} τ (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} τ _inst_1)))) ϕ s) (IsInvariant.{u2, u1} τ α ϕ s)
Case conversion may be inaccurate. Consider using '#align is_fw_invariant_iff_is_invariant isFwInvariant_iff_isInvariantₓ'. -/
/-- If `τ` is a `canonically_ordered_add_monoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`is_fw_invariant` and `is_invariant` are equivalent. -/
theorem isFwInvariant_iff_isInvariant [CanonicallyOrderedAddMonoid τ] {ϕ : τ → α → α} {s : Set α} :
    IsFwInvariant ϕ s ↔ IsInvariant ϕ s :=
  ⟨IsFwInvariant.isInvariant, IsInvariant.isFwInvariant⟩
#align is_fw_invariant_iff_is_invariant isFwInvariant_iff_isInvariant

end Invariant

/-!
### Flows
-/


/- warning: flow -> Flow is a dubious translation:
lean 3 declaration is
  forall (τ : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} τ] [_inst_2 : AddMonoid.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_1 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_2))] (α : Type.{u2}) [_inst_4 : TopologicalSpace.{u2} α], Sort.{max (succ u1) (succ u2)}
but is expected to have type
  forall (τ : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} τ] [_inst_2 : AddMonoid.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_1 (AddZeroClass.toAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_2))] (α : Type.{u2}) [_inst_4 : TopologicalSpace.{u2} α], Sort.{max (succ u1) (succ u2)}
Case conversion may be inaccurate. Consider using '#align flow Flowₓ'. -/
/-- A flow on a topological space `α` by an a additive topological
    monoid `τ` is a continuous monoid action of `τ` on `α`.-/
structure Flow (τ : Type _) [TopologicalSpace τ] [AddMonoid τ] [ContinuousAdd τ] (α : Type _)
  [TopologicalSpace α] where
  toFun : τ → α → α
  cont' : Continuous (uncurry to_fun)
  map_add' : ∀ t₁ t₂ x, to_fun (t₁ + t₂) x = to_fun t₁ (to_fun t₂ x)
  map_zero' : ∀ x, to_fun 0 x = x
#align flow Flow

namespace Flow

variable {τ : Type _} [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ] {α : Type _}
  [TopologicalSpace α] (ϕ : Flow τ α)

instance : Inhabited (Flow τ α) :=
  ⟨{  toFun := fun _ x => x
      cont' := continuous_snd
      map_add' := fun _ _ _ => rfl
      map_zero' := fun _ => rfl }⟩

instance : CoeFun (Flow τ α) fun _ => τ → α → α :=
  ⟨Flow.toFun⟩

/- warning: flow.ext -> Flow.ext is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] {ϕ₁ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4} {ϕ₂ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4}, (forall (t : τ) (x : α), Eq.{succ u2} α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ₁ t x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ₂ t x)) -> (Eq.{max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) ϕ₁ ϕ₂)
but is expected to have type
  forall {τ : Type.{u2}} [_inst_1 : AddMonoid.{u2} τ] [_inst_2 : TopologicalSpace.{u2} τ] [_inst_3 : ContinuousAdd.{u2} τ _inst_2 (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ _inst_1))] {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] {ϕ₁ : Flow.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4} {ϕ₂ : Flow.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4}, (forall (t : τ) (x : α), Eq.{succ u1} α (Flow.toFun.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ₁ t x) (Flow.toFun.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ₂ t x)) -> (Eq.{max (succ u2) (succ u1)} (Flow.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4) ϕ₁ ϕ₂)
Case conversion may be inaccurate. Consider using '#align flow.ext Flow.extₓ'. -/
@[ext]
theorem ext : ∀ {ϕ₁ ϕ₂ : Flow τ α}, (∀ t x, ϕ₁ t x = ϕ₂ t x) → ϕ₁ = ϕ₂
  | ⟨f₁, _, _, _⟩, ⟨f₂, _, _, _⟩, h => by
    congr
    funext
    exact h _ _
#align flow.ext Flow.ext

/- warning: flow.continuous -> Flow.continuous is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) {β : Type.{u3}} [_inst_5 : TopologicalSpace.{u3} β] {t : β -> τ}, (Continuous.{u3, u1} β τ _inst_5 _inst_2 t) -> (forall {f : β -> α}, (Continuous.{u3, u2} β α _inst_5 _inst_4 f) -> (Continuous.{u3, u2} β α _inst_5 _inst_4 (fun (x : β) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ (t x) (f x))))
but is expected to have type
  forall {τ : Type.{u2}} [_inst_1 : AddMonoid.{u2} τ] [_inst_2 : TopologicalSpace.{u2} τ] [_inst_3 : ContinuousAdd.{u2} τ _inst_2 (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ _inst_1))] {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] (ϕ : Flow.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4) {β : Type.{u3}} [_inst_5 : TopologicalSpace.{u3} β] {t : β -> τ}, (Continuous.{u3, u2} β τ _inst_5 _inst_2 t) -> (forall {f : β -> α}, (Continuous.{u3, u1} β α _inst_5 _inst_4 f) -> (Continuous.{u3, u1} β α _inst_5 _inst_4 (fun (x : β) => Flow.toFun.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ (t x) (f x))))
Case conversion may be inaccurate. Consider using '#align flow.continuous Flow.continuousₓ'. -/
@[continuity]
protected theorem continuous {β : Type _} [TopologicalSpace β] {t : β → τ} (ht : Continuous t)
    {f : β → α} (hf : Continuous f) : Continuous fun x => ϕ (t x) (f x) :=
  ϕ.cont'.comp (ht.prod_mk hf)
#align flow.continuous Flow.continuous

/- warning: continuous.flow -> continuous.flow is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) {β : Type.{u3}} [_inst_5 : TopologicalSpace.{u3} β] {t : β -> τ}, (Continuous.{u3, u1} β τ _inst_5 _inst_2 t) -> (forall {f : β -> α}, (Continuous.{u3, u2} β α _inst_5 _inst_4 f) -> (Continuous.{u3, u2} β α _inst_5 _inst_4 (fun (x : β) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ (t x) (f x))))
but is expected to have type
  forall {τ : Type.{u2}} [_inst_1 : AddMonoid.{u2} τ] [_inst_2 : TopologicalSpace.{u2} τ] [_inst_3 : ContinuousAdd.{u2} τ _inst_2 (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ _inst_1))] {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] (ϕ : Flow.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4) {β : Type.{u3}} [_inst_5 : TopologicalSpace.{u3} β] {t : β -> τ}, (Continuous.{u3, u2} β τ _inst_5 _inst_2 t) -> (forall {f : β -> α}, (Continuous.{u3, u1} β α _inst_5 _inst_4 f) -> (Continuous.{u3, u1} β α _inst_5 _inst_4 (fun (x : β) => Flow.toFun.{u2, u1} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ (t x) (f x))))
Case conversion may be inaccurate. Consider using '#align continuous.flow continuous.flowₓ'. -/
alias Flow.continuous ← _root_.continuous.flow
#align continuous.flow continuous.flow

/- warning: flow.map_add -> Flow.map_add is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (t₁ : τ) (t₂ : τ) (x : α), Eq.{succ u2} α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ (HAdd.hAdd.{u1, u1, u1} τ τ τ (instHAdd.{u1} τ (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))) t₁ t₂) x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ t₁ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ t₂ x))
but is expected to have type
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (t₁ : τ) (t₂ : τ) (x : α), Eq.{succ u2} α (Flow.toFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ (HAdd.hAdd.{u1, u1, u1} τ τ τ (instHAdd.{u1} τ (AddZeroClass.toAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))) t₁ t₂) x) (Flow.toFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ t₁ (Flow.toFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ t₂ x))
Case conversion may be inaccurate. Consider using '#align flow.map_add Flow.map_addₓ'. -/
theorem map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x) :=
  ϕ.map_add' _ _ _
#align flow.map_add Flow.map_add

/- warning: flow.map_zero -> Flow.map_zero is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4), Eq.{succ u2} (α -> α) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ (OfNat.ofNat.{u1} τ 0 (OfNat.mk.{u1} τ 0 (Zero.zero.{u1} τ (AddZeroClass.toHasZero.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1)))))) (id.{succ u2} α)
but is expected to have type
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4), Eq.{succ u2} (α -> α) (Flow.toFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ (OfNat.ofNat.{u1} τ 0 (Zero.toOfNat0.{u1} τ (AddMonoid.toZero.{u1} τ _inst_1)))) (id.{succ u2} α)
Case conversion may be inaccurate. Consider using '#align flow.map_zero Flow.map_zeroₓ'. -/
@[simp]
theorem map_zero : ϕ 0 = id :=
  funext ϕ.map_zero'
#align flow.map_zero Flow.map_zero

/- warning: flow.map_zero_apply -> Flow.map_zero_apply is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (x : α), Eq.{succ u2} α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ (OfNat.ofNat.{u1} τ 0 (OfNat.mk.{u1} τ 0 (Zero.zero.{u1} τ (AddZeroClass.toHasZero.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))))) x) x
but is expected to have type
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (x : α), Eq.{succ u2} α (Flow.toFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ (OfNat.ofNat.{u1} τ 0 (Zero.toOfNat0.{u1} τ (AddMonoid.toZero.{u1} τ _inst_1))) x) x
Case conversion may be inaccurate. Consider using '#align flow.map_zero_apply Flow.map_zero_applyₓ'. -/
theorem map_zero_apply (x : α) : ϕ 0 x = x :=
  ϕ.map_zero' x
#align flow.map_zero_apply Flow.map_zero_apply

/- warning: flow.from_iter -> Flow.fromIter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] {g : α -> α}, (Continuous.{u1, u1} α α _inst_4 _inst_4 g) -> (Flow.{0, u1} Nat Nat.topologicalSpace Nat.addMonoid Flow.fromIter._proof_1 α _inst_4)
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] {g : α -> α}, (Continuous.{u1, u1} α α _inst_4 _inst_4 g) -> (Flow.{0, u1} Nat instTopologicalSpaceNat Nat.addMonoid (continuousAdd_of_discreteTopology.{0} Nat instTopologicalSpaceNat (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) instDiscreteTopologyNatInstTopologicalSpaceNat) α _inst_4)
Case conversion may be inaccurate. Consider using '#align flow.from_iter Flow.fromIterₓ'. -/
/-- Iterations of a continuous function from a topological space `α`
    to itself defines a semiflow by `ℕ` on `α`. -/
def fromIter {g : α → α} (h : Continuous g) : Flow ℕ α
    where
  toFun n x := (g^[n]) x
  cont' := continuous_uncurry_of_discreteTopology_left (Continuous.iterate h)
  map_add' := iterate_add_apply _
  map_zero' x := rfl
#align flow.from_iter Flow.fromIter

/- warning: flow.restrict -> Flow.restrict is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) {s : Set.{u2} α}, (IsInvariant.{u1, u2} τ α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) ϕ) s) -> (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} α) Type.{u2} (Set.hasCoeToSort.{u2} α) s) (Subtype.topologicalSpace.{u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) x s) _inst_4))
but is expected to have type
  forall {τ : Type.{u1}} [_inst_1 : AddMonoid.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_2 (AddZeroClass.toAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_1))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) {s : Set.{u2} α}, (IsInvariant.{u1, u2} τ α (Flow.toFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4 ϕ) s) -> (Flow.{u1, u2} τ _inst_2 _inst_1 _inst_3 (Set.Elem.{u2} α s) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_4))
Case conversion may be inaccurate. Consider using '#align flow.restrict Flow.restrictₓ'. -/
/-- Restriction of a flow onto an invariant set. -/
def restrict {s : Set α} (h : IsInvariant ϕ s) : Flow τ ↥s
    where
  toFun t := (h t).restrict _ _ _
  cont' := (ϕ.Continuous continuous_fst continuous_subtype_val.snd').subtype_mk _
  map_add' _ _ _ := Subtype.ext (map_add _ _ _ _)
  map_zero' _ := Subtype.ext (map_zero_apply _ _)
#align flow.restrict Flow.restrict

end Flow

namespace Flow

variable {τ : Type _} [AddCommGroup τ] [TopologicalSpace τ] [TopologicalAddGroup τ] {α : Type _}
  [TopologicalSpace α] (ϕ : Flow τ α)

/- warning: flow.is_invariant_iff_image_eq -> Flow.isInvariant_iff_image_eq is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddCommGroup.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) (s : Set.{u2} α), Iff (IsInvariant.{u1, u2} τ α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) _inst_2 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) ϕ) s) (forall (t : τ), Eq.{succ u2} (Set.{u2} α) (Set.image.{u2, u2} α α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) _inst_2 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) ϕ t) s) s)
but is expected to have type
  forall {τ : Type.{u1}} [_inst_1 : AddCommGroup.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) (s : Set.{u2} α), Iff (IsInvariant.{u1, u2} τ α (Flow.toFun.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4 ϕ) s) (forall (t : τ), Eq.{succ u2} (Set.{u2} α) (Set.image.{u2, u2} α α (Flow.toFun.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4 ϕ t) s) s)
Case conversion may be inaccurate. Consider using '#align flow.is_invariant_iff_image_eq Flow.isInvariant_iff_image_eqₓ'. -/
theorem isInvariant_iff_image_eq (s : Set α) : IsInvariant ϕ s ↔ ∀ t, ϕ t '' s = s :=
  (isInvariant_iff_image _ _).trans
    (Iff.intro
      (fun h t => Subset.antisymm (h t) fun _ hx => ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp [← map_add]⟩)
      fun h t => by rw [h t])
#align flow.is_invariant_iff_image_eq Flow.isInvariant_iff_image_eq

/- warning: flow.reverse -> Flow.reverse is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddCommGroup.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α], (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (Flow.reverse._proof_1.{u1} τ _inst_1 _inst_2 _inst_3) α _inst_4) -> (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (Flow.reverse._proof_2.{u1} τ _inst_1 _inst_2 _inst_3) α _inst_4)
but is expected to have type
  forall {τ : Type.{u1}} [_inst_1 : AddCommGroup.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α], (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) -> (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4)
Case conversion may be inaccurate. Consider using '#align flow.reverse Flow.reverseₓ'. -/
/-- The time-reversal of a flow `ϕ` by a (commutative, additive) group
    is defined `ϕ.reverse t x = ϕ (-t) x`. -/
def reverse : Flow τ α where
  toFun t := ϕ (-t)
  cont' := ϕ.Continuous continuous_fst.neg continuous_snd
  map_add' _ _ _ := by rw [neg_add, map_add]
  map_zero' _ := by rw [neg_zero, map_zero_apply]
#align flow.reverse Flow.reverse

/- warning: flow.to_homeomorph -> Flow.toHomeomorph is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddCommGroup.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α], (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (Flow.toHomeomorph._proof_1.{u1} τ _inst_1 _inst_2 _inst_3) α _inst_4) -> τ -> (Homeomorph.{u2, u2} α α _inst_4 _inst_4)
but is expected to have type
  forall {τ : Type.{u1}} [_inst_1 : AddCommGroup.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α], (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) -> τ -> (Homeomorph.{u2, u2} α α _inst_4 _inst_4)
Case conversion may be inaccurate. Consider using '#align flow.to_homeomorph Flow.toHomeomorphₓ'. -/
/-- The map `ϕ t` as a homeomorphism. -/
def toHomeomorph (t : τ) : α ≃ₜ α where
  toFun := ϕ t
  invFun := ϕ (-t)
  left_inv x := by rw [← map_add, neg_add_self, map_zero_apply]
  right_inv x := by rw [← map_add, add_neg_self, map_zero_apply]
#align flow.to_homeomorph Flow.toHomeomorph

/- warning: flow.image_eq_preimage -> Flow.image_eq_preimage is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : AddCommGroup.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) (t : τ) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.image.{u2, u2} α α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) _inst_2 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) ϕ t) s) (Set.preimage.{u2, u2} α α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) _inst_2 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) ϕ (Neg.neg.{u1} τ (SubNegMonoid.toHasNeg.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) t)) s)
but is expected to have type
  forall {τ : Type.{u1}} [_inst_1 : AddCommGroup.{u1} τ] [_inst_2 : TopologicalSpace.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (ϕ : Flow.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4) (t : τ) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.image.{u2, u2} α α (Flow.toFun.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4 ϕ t) s) (Set.preimage.{u2, u2} α α (Flow.toFun.{u1, u2} τ _inst_2 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_1))) (TopologicalAddGroup.toContinuousAdd.{u1} τ _inst_2 (AddCommGroup.toAddGroup.{u1} τ _inst_1) _inst_3) α _inst_4 ϕ (Neg.neg.{u1} τ (NegZeroClass.toNeg.{u1} τ (SubNegZeroMonoid.toNegZeroClass.{u1} τ (SubtractionMonoid.toSubNegZeroMonoid.{u1} τ (SubtractionCommMonoid.toSubtractionMonoid.{u1} τ (AddCommGroup.toDivisionAddCommMonoid.{u1} τ _inst_1))))) t)) s)
Case conversion may be inaccurate. Consider using '#align flow.image_eq_preimage Flow.image_eq_preimageₓ'. -/
theorem image_eq_preimage (t : τ) (s : Set α) : ϕ t '' s = ϕ (-t) ⁻¹' s :=
  (ϕ.toHomeomorph t).toEquiv.image_eq_preimage s
#align flow.image_eq_preimage Flow.image_eq_preimage

end Flow

