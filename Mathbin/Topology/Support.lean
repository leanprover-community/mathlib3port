/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot

! This file was ported from Lean 3 source module topology.support
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Separation

/-!
# The topological support of a function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the topological support of a function `f`, `tsupport f`,
as the closure of the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `function.mul_tsupport` & `function.tsupport`
* `function.has_compact_mul_support` & `function.has_compact_support`

## Implementation Notes

* We write all lemmas for multiplicative functions, and use `@[to_additive]` to get the more common
  additive versions.
* We do not put the definitions in the `function` namespace, following many other topological
  definitions that are in the root namespace (compare `embedding` vs `function.embedding`).
-/


open Function Set Filter

open Topology

variable {X α α' β γ δ M E R : Type _}

section One

variable [One α]

variable [TopologicalSpace X]

#print mulTSupport /-
/-- The topological support of a function is the closure of its support, i.e. the closure of the
  set of all elements where the function is not equal to 1. -/
@[to_additive
      " The topological support of a function is the closure of its support. i.e. the closure of the\n  set of all elements where the function is nonzero. "]
def mulTSupport (f : X → α) : Set X :=
  closure (mulSupport f)
#align mul_tsupport mulTSupport
#align tsupport tsupport
-/

/- warning: subset_mul_tsupport -> subset_mulTSupport is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : One.{u2} α] [_inst_2 : TopologicalSpace.{u1} X] (f : X -> α), HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (Function.mulSupport.{u1, u2} X α _inst_1 f) (mulTSupport.{u1, u2} X α _inst_1 _inst_2 f)
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : TopologicalSpace.{u2} X] (f : X -> α), HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) (Function.mulSupport.{u2, u1} X α _inst_1 f) (mulTSupport.{u2, u1} X α _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align subset_mul_tsupport subset_mulTSupportₓ'. -/
@[to_additive]
theorem subset_mulTSupport (f : X → α) : mulSupport f ⊆ mulTSupport f :=
  subset_closure
#align subset_mul_tsupport subset_mulTSupport
#align subset_tsupport subset_tsupport

/- warning: is_closed_mul_tsupport -> isClosed_mulTSupport is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : One.{u2} α] [_inst_2 : TopologicalSpace.{u1} X] (f : X -> α), IsClosed.{u1} X _inst_2 (mulTSupport.{u1, u2} X α _inst_1 _inst_2 f)
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : TopologicalSpace.{u2} X] (f : X -> α), IsClosed.{u2} X _inst_2 (mulTSupport.{u2, u1} X α _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_closed_mul_tsupport isClosed_mulTSupportₓ'. -/
@[to_additive]
theorem isClosed_mulTSupport (f : X → α) : IsClosed (mulTSupport f) :=
  isClosed_closure
#align is_closed_mul_tsupport isClosed_mulTSupport
#align is_closed_tsupport isClosed_tsupport

/- warning: mul_tsupport_eq_empty_iff -> mulTSupport_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : One.{u2} α] [_inst_2 : TopologicalSpace.{u1} X] {f : X -> α}, Iff (Eq.{succ u1} (Set.{u1} X) (mulTSupport.{u1, u2} X α _inst_1 _inst_2 f) (EmptyCollection.emptyCollection.{u1} (Set.{u1} X) (Set.hasEmptyc.{u1} X))) (Eq.{max (succ u1) (succ u2)} (X -> α) f (OfNat.ofNat.{max u1 u2} (X -> α) 1 (OfNat.mk.{max u1 u2} (X -> α) 1 (One.one.{max u1 u2} (X -> α) (Pi.instOne.{u1, u2} X (fun (ᾰ : X) => α) (fun (i : X) => _inst_1))))))
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : TopologicalSpace.{u2} X] {f : X -> α}, Iff (Eq.{succ u2} (Set.{u2} X) (mulTSupport.{u2, u1} X α _inst_1 _inst_2 f) (EmptyCollection.emptyCollection.{u2} (Set.{u2} X) (Set.instEmptyCollectionSet.{u2} X))) (Eq.{max (succ u2) (succ u1)} (X -> α) f (OfNat.ofNat.{max u2 u1} (X -> α) 1 (One.toOfNat1.{max u2 u1} (X -> α) (Pi.instOne.{u2, u1} X (fun (a._@.Mathlib.Topology.Support._hyg.142 : X) => α) (fun (i : X) => _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mul_tsupport_eq_empty_iff mulTSupport_eq_empty_iffₓ'. -/
@[to_additive]
theorem mulTSupport_eq_empty_iff {f : X → α} : mulTSupport f = ∅ ↔ f = 1 := by
  rw [mulTSupport, closure_empty_iff, mul_support_eq_empty_iff]
#align mul_tsupport_eq_empty_iff mulTSupport_eq_empty_iff
#align tsupport_eq_empty_iff tsupport_eq_empty_iff

/- warning: image_eq_one_of_nmem_mul_tsupport -> image_eq_one_of_nmem_mulTSupport is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : One.{u2} α] [_inst_2 : TopologicalSpace.{u1} X] {f : X -> α} {x : X}, (Not (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x (mulTSupport.{u1, u2} X α _inst_1 _inst_2 f))) -> (Eq.{succ u2} α (f x) (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α _inst_1))))
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : TopologicalSpace.{u2} X] {f : X -> α} {x : X}, (Not (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x (mulTSupport.{u2, u1} X α _inst_1 _inst_2 f))) -> (Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align image_eq_one_of_nmem_mul_tsupport image_eq_one_of_nmem_mulTSupportₓ'. -/
@[to_additive]
theorem image_eq_one_of_nmem_mulTSupport {f : X → α} {x : X} (hx : x ∉ mulTSupport f) : f x = 1 :=
  mulSupport_subset_iff'.mp (subset_mulTSupport f) x hx
#align image_eq_one_of_nmem_mul_tsupport image_eq_one_of_nmem_mulTSupport
#align image_eq_zero_of_nmem_tsupport image_eq_zero_of_nmem_tsupport

#print range_subset_insert_image_mulTSupport /-
@[to_additive]
theorem range_subset_insert_image_mulTSupport (f : X → α) :
    range f ⊆ insert 1 (f '' mulTSupport f) :=
  (range_subset_insert_image_mulSupport f).trans <|
    insert_subset_insert <| image_subset _ subset_closure
#align range_subset_insert_image_mul_tsupport range_subset_insert_image_mulTSupport
#align range_subset_insert_image_tsupport range_subset_insert_image_tsupport
-/

#print range_eq_image_mulTSupport_or /-
@[to_additive]
theorem range_eq_image_mulTSupport_or (f : X → α) :
    range f = f '' mulTSupport f ∨ range f = insert 1 (f '' mulTSupport f) :=
  (wcovby_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mulTSupport f)
#align range_eq_image_mul_tsupport_or range_eq_image_mulTSupport_or
#align range_eq_image_tsupport_or range_eq_image_tsupport_or
-/

/- warning: tsupport_mul_subset_left -> tsupport_mul_subset_left is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {α : Type.{u2}} [_inst_3 : MulZeroClass.{u2} α] {f : X -> α} {g : X -> α}, HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (tsupport.{u1, u2} X α (MulZeroClass.toHasZero.{u2} α _inst_3) _inst_2 (fun (x : X) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulZeroClass.toHasMul.{u2} α _inst_3)) (f x) (g x))) (tsupport.{u1, u2} X α (MulZeroClass.toHasZero.{u2} α _inst_3) _inst_2 f)
but is expected to have type
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {α : Type.{u2}} [_inst_3 : MulZeroClass.{u2} α] {f : X -> α} {g : X -> α}, HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (tsupport.{u1, u2} X α (MulZeroClass.toZero.{u2} α _inst_3) _inst_2 (fun (x : X) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulZeroClass.toMul.{u2} α _inst_3)) (f x) (g x))) (tsupport.{u1, u2} X α (MulZeroClass.toZero.{u2} α _inst_3) _inst_2 f)
Case conversion may be inaccurate. Consider using '#align tsupport_mul_subset_left tsupport_mul_subset_leftₓ'. -/
theorem tsupport_mul_subset_left {α : Type _} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport f :=
  closure_mono (support_mul_subset_left _ _)
#align tsupport_mul_subset_left tsupport_mul_subset_left

/- warning: tsupport_mul_subset_right -> tsupport_mul_subset_right is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {α : Type.{u2}} [_inst_3 : MulZeroClass.{u2} α] {f : X -> α} {g : X -> α}, HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (tsupport.{u1, u2} X α (MulZeroClass.toHasZero.{u2} α _inst_3) _inst_2 (fun (x : X) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulZeroClass.toHasMul.{u2} α _inst_3)) (f x) (g x))) (tsupport.{u1, u2} X α (MulZeroClass.toHasZero.{u2} α _inst_3) _inst_2 g)
but is expected to have type
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {α : Type.{u2}} [_inst_3 : MulZeroClass.{u2} α] {f : X -> α} {g : X -> α}, HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (tsupport.{u1, u2} X α (MulZeroClass.toZero.{u2} α _inst_3) _inst_2 (fun (x : X) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulZeroClass.toMul.{u2} α _inst_3)) (f x) (g x))) (tsupport.{u1, u2} X α (MulZeroClass.toZero.{u2} α _inst_3) _inst_2 g)
Case conversion may be inaccurate. Consider using '#align tsupport_mul_subset_right tsupport_mul_subset_rightₓ'. -/
theorem tsupport_mul_subset_right {α : Type _} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport g :=
  closure_mono (support_mul_subset_right _ _)
#align tsupport_mul_subset_right tsupport_mul_subset_right

end One

/- warning: tsupport_smul_subset_left -> tsupport_smul_subset_left is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : Zero.{u2} M] [_inst_3 : Zero.{u3} α] [_inst_4 : SMulWithZero.{u2, u3} M α _inst_2 _inst_3] (f : X -> M) (g : X -> α), HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (tsupport.{u1, u3} X α _inst_3 _inst_1 (fun (x : X) => SMul.smul.{u2, u3} M α (SMulZeroClass.toHasSmul.{u2, u3} M α _inst_3 (SMulWithZero.toSmulZeroClass.{u2, u3} M α _inst_2 _inst_3 _inst_4)) (f x) (g x))) (tsupport.{u1, u2} X M _inst_2 _inst_1 f)
but is expected to have type
  forall {X : Type.{u1}} {M : Type.{u3}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : Zero.{u3} M] [_inst_3 : Zero.{u2} α] [_inst_4 : SMulWithZero.{u3, u2} M α _inst_2 _inst_3] (f : X -> M) (g : X -> α), HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (tsupport.{u1, u2} X α _inst_3 _inst_1 (fun (x : X) => HSMul.hSMul.{u3, u2, u2} M α α (instHSMul.{u3, u2} M α (SMulZeroClass.toSMul.{u3, u2} M α _inst_3 (SMulWithZero.toSMulZeroClass.{u3, u2} M α _inst_2 _inst_3 _inst_4))) (f x) (g x))) (tsupport.{u1, u3} X M _inst_2 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align tsupport_smul_subset_left tsupport_smul_subset_leftₓ'. -/
theorem tsupport_smul_subset_left {M α} [TopologicalSpace X] [Zero M] [Zero α] [SMulWithZero M α]
    (f : X → M) (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport f :=
  closure_mono <| support_smul_subset_left f g
#align tsupport_smul_subset_left tsupport_smul_subset_left

section

variable [TopologicalSpace α] [TopologicalSpace α']

variable [One β] [One γ] [One δ]

variable {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ} {x : α}

/- warning: not_mem_mul_tsupport_iff_eventually_eq -> not_mem_mulTSupport_iff_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] {f : α -> β} {x : α}, Iff (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (mulTSupport.{u1, u2} α β _inst_3 _inst_1 f))) (Filter.EventuallyEq.{u1, u2} α β (nhds.{u1} α _inst_1 x) f (OfNat.ofNat.{max u1 u2} (α -> β) 1 (OfNat.mk.{max u1 u2} (α -> β) 1 (One.one.{max u1 u2} (α -> β) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_3 : One.{u1} β] {f : α -> β} {x : α}, Iff (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (mulTSupport.{u2, u1} α β _inst_3 _inst_1 f))) (Filter.EventuallyEq.{u2, u1} α β (nhds.{u2} α _inst_1 x) f (OfNat.ofNat.{max u2 u1} (α -> β) 1 (One.toOfNat1.{max u2 u1} (α -> β) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => β) (fun (i : α) => _inst_3)))))
Case conversion may be inaccurate. Consider using '#align not_mem_mul_tsupport_iff_eventually_eq not_mem_mulTSupport_iff_eventuallyEqₓ'. -/
@[to_additive]
theorem not_mem_mulTSupport_iff_eventuallyEq : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1 := by
  simp_rw [mulTSupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, ←
    disjoint_iff_inter_eq_empty, disjoint_mul_support_iff, eventually_eq_iff_exists_mem]
#align not_mem_mul_tsupport_iff_eventually_eq not_mem_mulTSupport_iff_eventuallyEq
#align not_mem_tsupport_iff_eventually_eq not_mem_tsupport_iff_eventuallyEq

#print continuous_of_mulTSupport /-
@[to_additive]
theorem continuous_of_mulTSupport [TopologicalSpace β] {f : α → β}
    (hf : ∀ x ∈ mulTSupport f, ContinuousAt f x) : Continuous f :=
  continuous_iff_continuousAt.2 fun x =>
    (em _).elim (hf x) fun hx =>
      (@continuousAt_const _ _ _ _ _ 1).congr (not_mem_mulTSupport_iff_eventuallyEq.mp hx).symm
#align continuous_of_mul_tsupport continuous_of_mulTSupport
#align continuous_of_tsupport continuous_of_tsupport
-/

#print HasCompactMulSupport /-
/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive
      " A function `f` *has compact support* or is *compactly supported* if the closure of the support\nof `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a compact\nset. "]
def HasCompactMulSupport (f : α → β) : Prop :=
  IsCompact (mulTSupport f)
#align has_compact_mul_support HasCompactMulSupport
#align has_compact_support HasCompactSupport
-/

/- warning: has_compact_mul_support_def -> hasCompactMulSupport_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] {f : α -> β}, Iff (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f) (IsCompact.{u1} α _inst_1 (closure.{u1} α _inst_1 (Function.mulSupport.{u1, u2} α β _inst_3 f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_3 : One.{u1} β] {f : α -> β}, Iff (HasCompactMulSupport.{u2, u1} α β _inst_1 _inst_3 f) (IsCompact.{u2} α _inst_1 (closure.{u2} α _inst_1 (Function.mulSupport.{u2, u1} α β _inst_3 f)))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support_def hasCompactMulSupport_defₓ'. -/
@[to_additive]
theorem hasCompactMulSupport_def : HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f)) := by
  rfl
#align has_compact_mul_support_def hasCompactMulSupport_def
#align has_compact_support_def hasCompactSupport_def

/- warning: exists_compact_iff_has_compact_mul_support -> exists_compact_iff_hasCompactMulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] {f : α -> β} [_inst_6 : T2Space.{u1} α _inst_1], Iff (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (IsCompact.{u1} α _inst_1 K) (forall (x : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x K)) -> (Eq.{succ u2} β (f x) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_3))))))) (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_3 : One.{u1} β] {f : α -> β} [_inst_6 : T2Space.{u2} α _inst_1], Iff (Exists.{succ u2} (Set.{u2} α) (fun (K : Set.{u2} α) => And (IsCompact.{u2} α _inst_1 K) (forall (x : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x K)) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β _inst_3)))))) (HasCompactMulSupport.{u2, u1} α β _inst_1 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align exists_compact_iff_has_compact_mul_support exists_compact_iff_hasCompactMulSupportₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ∉ » K) -/
@[to_additive]
theorem exists_compact_iff_hasCompactMulSupport [T2Space α] :
    (∃ K : Set α, IsCompact K ∧ ∀ (x) (_ : x ∉ K), f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← nmem_mul_support, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_compact_superset_iff]
#align exists_compact_iff_has_compact_mul_support exists_compact_iff_hasCompactMulSupport
#align exists_compact_iff_has_compact_support exists_compact_iff_hasCompactSupport

/- warning: has_compact_mul_support.intro -> HasCompactMulSupport.intro is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] {f : α -> β} [_inst_6 : T2Space.{u1} α _inst_1] {K : Set.{u1} α}, (IsCompact.{u1} α _inst_1 K) -> (forall (x : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x K)) -> (Eq.{succ u2} β (f x) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_3))))) -> (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_3 : One.{u1} β] {f : α -> β} [_inst_6 : T2Space.{u2} α _inst_1] {K : Set.{u2} α}, (IsCompact.{u2} α _inst_1 K) -> (forall (x : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x K)) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β _inst_3)))) -> (HasCompactMulSupport.{u2, u1} α β _inst_1 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.intro HasCompactMulSupport.introₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ∉ » K) -/
@[to_additive]
theorem HasCompactMulSupport.intro [T2Space α] {K : Set α} (hK : IsCompact K)
    (hfK : ∀ (x) (_ : x ∉ K), f x = 1) : HasCompactMulSupport f :=
  exists_compact_iff_hasCompactMulSupport.mp ⟨K, hK, hfK⟩
#align has_compact_mul_support.intro HasCompactMulSupport.intro
#align has_compact_support.intro HasCompactSupport.intro

/- warning: has_compact_mul_support.is_compact -> HasCompactMulSupport.isCompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] {f : α -> β}, (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f) -> (IsCompact.{u1} α _inst_1 (mulTSupport.{u1, u2} α β _inst_3 _inst_1 f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_3 : One.{u1} β] {f : α -> β}, (HasCompactMulSupport.{u2, u1} α β _inst_1 _inst_3 f) -> (IsCompact.{u2} α _inst_1 (mulTSupport.{u2, u1} α β _inst_3 _inst_1 f))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.is_compact HasCompactMulSupport.isCompactₓ'. -/
@[to_additive]
theorem HasCompactMulSupport.isCompact (hf : HasCompactMulSupport f) : IsCompact (mulTSupport f) :=
  hf
#align has_compact_mul_support.is_compact HasCompactMulSupport.isCompact
#align has_compact_support.is_compact HasCompactSupport.isCompact

/- warning: has_compact_mul_support_iff_eventually_eq -> hasCompactMulSupport_iff_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] {f : α -> β}, Iff (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f) (Filter.EventuallyEq.{u1, u2} α β (Filter.coclosedCompact.{u1} α _inst_1) f (OfNat.ofNat.{max u1 u2} (α -> β) 1 (OfNat.mk.{max u1 u2} (α -> β) 1 (One.one.{max u1 u2} (α -> β) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_3 : One.{u1} β] {f : α -> β}, Iff (HasCompactMulSupport.{u2, u1} α β _inst_1 _inst_3 f) (Filter.EventuallyEq.{u2, u1} α β (Filter.coclosedCompact.{u2} α _inst_1) f (OfNat.ofNat.{max u2 u1} (α -> β) 1 (One.toOfNat1.{max u2 u1} (α -> β) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => β) (fun (i : α) => _inst_3)))))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support_iff_eventually_eq hasCompactMulSupport_iff_eventuallyEqₓ'. -/
@[to_additive]
theorem hasCompactMulSupport_iff_eventuallyEq :
    HasCompactMulSupport f ↔ f =ᶠ[coclosedCompact α] 1 :=
  ⟨fun h =>
    mem_coclosedCompact.mpr
      ⟨mulTSupport f, isClosed_mulTSupport _, h, fun x =>
        not_imp_comm.mpr fun hx => subset_mulTSupport f hx⟩,
    fun h =>
    let ⟨C, hC⟩ := mem_coclosed_compact'.mp h
    isCompact_of_isClosed_subset hC.2.1 (isClosed_mulTSupport _) (closure_minimal hC.2.2 hC.1)⟩
#align has_compact_mul_support_iff_eventually_eq hasCompactMulSupport_iff_eventuallyEq
#align has_compact_support_iff_eventually_eq hasCompactSupport_iff_eventuallyEq

#print HasCompactMulSupport.isCompact_range /-
@[to_additive]
theorem HasCompactMulSupport.isCompact_range [TopologicalSpace β] (h : HasCompactMulSupport f)
    (hf : Continuous f) : IsCompact (range f) :=
  by
  cases' range_eq_image_mulTSupport_or f with h2 h2 <;> rw [h2]
  exacts[h.image hf, (h.image hf).insert 1]
#align has_compact_mul_support.is_compact_range HasCompactMulSupport.isCompact_range
#align has_compact_support.is_compact_range HasCompactSupport.isCompact_range
-/

/- warning: has_compact_mul_support.mono' -> HasCompactMulSupport.mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] [_inst_4 : One.{u3} γ] {f : α -> β} {f' : α -> γ}, (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u3} α γ _inst_4 f') (mulTSupport.{u1, u2} α β _inst_3 _inst_1 f)) -> (HasCompactMulSupport.{u1, u3} α γ _inst_1 _inst_4 f')
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_3 : One.{u2} β] [_inst_4 : One.{u1} γ] {f : α -> β} {f' : α -> γ}, (HasCompactMulSupport.{u3, u2} α β _inst_1 _inst_3 f) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Function.mulSupport.{u3, u1} α γ _inst_4 f') (mulTSupport.{u3, u2} α β _inst_3 _inst_1 f)) -> (HasCompactMulSupport.{u3, u1} α γ _inst_1 _inst_4 f')
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.mono' HasCompactMulSupport.mono'ₓ'. -/
@[to_additive]
theorem HasCompactMulSupport.mono' {f' : α → γ} (hf : HasCompactMulSupport f)
    (hff' : mulSupport f' ⊆ mulTSupport f) : HasCompactMulSupport f' :=
  isCompact_of_isClosed_subset hf isClosed_closure <| closure_minimal hff' isClosed_closure
#align has_compact_mul_support.mono' HasCompactMulSupport.mono'
#align has_compact_support.mono' HasCompactSupport.mono'

/- warning: has_compact_mul_support.mono -> HasCompactMulSupport.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] [_inst_4 : One.{u3} γ] {f : α -> β} {f' : α -> γ}, (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u3} α γ _inst_4 f') (Function.mulSupport.{u1, u2} α β _inst_3 f)) -> (HasCompactMulSupport.{u1, u3} α γ _inst_1 _inst_4 f')
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_3 : One.{u2} β] [_inst_4 : One.{u1} γ] {f : α -> β} {f' : α -> γ}, (HasCompactMulSupport.{u3, u2} α β _inst_1 _inst_3 f) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Function.mulSupport.{u3, u1} α γ _inst_4 f') (Function.mulSupport.{u3, u2} α β _inst_3 f)) -> (HasCompactMulSupport.{u3, u1} α γ _inst_1 _inst_4 f')
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.mono HasCompactMulSupport.monoₓ'. -/
@[to_additive]
theorem HasCompactMulSupport.mono {f' : α → γ} (hf : HasCompactMulSupport f)
    (hff' : mulSupport f' ⊆ mulSupport f) : HasCompactMulSupport f' :=
  hf.mono' <| hff'.trans subset_closure
#align has_compact_mul_support.mono HasCompactMulSupport.mono
#align has_compact_support.mono HasCompactSupport.mono

/- warning: has_compact_mul_support.comp_left -> HasCompactMulSupport.comp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] [_inst_4 : One.{u3} γ] {g : β -> γ} {f : α -> β}, (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f) -> (Eq.{succ u3} γ (g (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_3)))) (OfNat.ofNat.{u3} γ 1 (OfNat.mk.{u3} γ 1 (One.one.{u3} γ _inst_4)))) -> (HasCompactMulSupport.{u1, u3} α γ _inst_1 _inst_4 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_3 : One.{u2} β] [_inst_4 : One.{u1} γ] {g : β -> γ} {f : α -> β}, (HasCompactMulSupport.{u3, u2} α β _inst_1 _inst_3 f) -> (Eq.{succ u1} γ (g (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_3))) (OfNat.ofNat.{u1} γ 1 (One.toOfNat1.{u1} γ _inst_4))) -> (HasCompactMulSupport.{u3, u1} α γ _inst_1 _inst_4 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.comp_left HasCompactMulSupport.comp_leftₓ'. -/
@[to_additive]
theorem HasCompactMulSupport.comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) :
    HasCompactMulSupport (g ∘ f) :=
  hf.mono <| mulSupport_comp_subset hg f
#align has_compact_mul_support.comp_left HasCompactMulSupport.comp_left
#align has_compact_support.comp_left HasCompactSupport.comp_left

#print hasCompactMulSupport_comp_left /-
@[to_additive]
theorem hasCompactMulSupport_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
    HasCompactMulSupport (g ∘ f) ↔ HasCompactMulSupport f := by
  simp_rw [hasCompactMulSupport_def, mul_support_comp_eq g (@hg) f]
#align has_compact_mul_support_comp_left hasCompactMulSupport_comp_left
#align has_compact_support_comp_left hasCompactSupport_comp_left
-/

/- warning: has_compact_mul_support.comp_closed_embedding -> HasCompactMulSupport.comp_closedEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} α'] [_inst_3 : One.{u3} β] {f : α -> β}, (HasCompactMulSupport.{u1, u3} α β _inst_1 _inst_3 f) -> (forall {g : α' -> α}, (ClosedEmbedding.{u2, u1} α' α _inst_2 _inst_1 g) -> (HasCompactMulSupport.{u2, u3} α' β _inst_2 _inst_3 (Function.comp.{succ u2, succ u1, succ u3} α' α β f g)))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} α'] [_inst_3 : One.{u2} β] {f : α -> β}, (HasCompactMulSupport.{u3, u2} α β _inst_1 _inst_3 f) -> (forall {g : α' -> α}, (ClosedEmbedding.{u1, u3} α' α _inst_2 _inst_1 g) -> (HasCompactMulSupport.{u1, u2} α' β _inst_2 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α' α β f g)))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.comp_closed_embedding HasCompactMulSupport.comp_closedEmbeddingₓ'. -/
@[to_additive]
theorem HasCompactMulSupport.comp_closedEmbedding (hf : HasCompactMulSupport f) {g : α' → α}
    (hg : ClosedEmbedding g) : HasCompactMulSupport (f ∘ g) :=
  by
  rw [hasCompactMulSupport_def, Function.mulSupport_comp_eq_preimage]
  refine' isCompact_of_isClosed_subset (hg.is_compact_preimage hf) isClosed_closure _
  rw [hg.to_embedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)
#align has_compact_mul_support.comp_closed_embedding HasCompactMulSupport.comp_closedEmbedding
#align has_compact_support.comp_closed_embedding HasCompactSupport.comp_closedEmbedding

/- warning: has_compact_mul_support.comp₂_left -> HasCompactMulSupport.comp₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : One.{u2} β] [_inst_4 : One.{u3} γ] [_inst_5 : One.{u4} δ] {f : α -> β} {f₂ : α -> γ} {m : β -> γ -> δ}, (HasCompactMulSupport.{u1, u2} α β _inst_1 _inst_3 f) -> (HasCompactMulSupport.{u1, u3} α γ _inst_1 _inst_4 f₂) -> (Eq.{succ u4} δ (m (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_3))) (OfNat.ofNat.{u3} γ 1 (OfNat.mk.{u3} γ 1 (One.one.{u3} γ _inst_4)))) (OfNat.ofNat.{u4} δ 1 (OfNat.mk.{u4} δ 1 (One.one.{u4} δ _inst_5)))) -> (HasCompactMulSupport.{u1, u4} α δ _inst_1 _inst_5 (fun (x : α) => m (f x) (f₂ x)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_3 : One.{u3} β] [_inst_4 : One.{u2} γ] [_inst_5 : One.{u1} δ] {f : α -> β} {f₂ : α -> γ} {m : β -> γ -> δ}, (HasCompactMulSupport.{u4, u3} α β _inst_1 _inst_3 f) -> (HasCompactMulSupport.{u4, u2} α γ _inst_1 _inst_4 f₂) -> (Eq.{succ u1} δ (m (OfNat.ofNat.{u3} β 1 (One.toOfNat1.{u3} β _inst_3)) (OfNat.ofNat.{u2} γ 1 (One.toOfNat1.{u2} γ _inst_4))) (OfNat.ofNat.{u1} δ 1 (One.toOfNat1.{u1} δ _inst_5))) -> (HasCompactMulSupport.{u4, u1} α δ _inst_1 _inst_5 (fun (x : α) => m (f x) (f₂ x)))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.comp₂_left HasCompactMulSupport.comp₂_leftₓ'. -/
@[to_additive]
theorem HasCompactMulSupport.comp₂_left (hf : HasCompactMulSupport f)
    (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) :
    HasCompactMulSupport fun x => m (f x) (f₂ x) :=
  by
  rw [hasCompactMulSupport_iff_eventuallyEq] at hf hf₂⊢
  filter_upwards [hf, hf₂]using fun x hx hx₂ => by simp_rw [hx, hx₂, Pi.one_apply, hm]
#align has_compact_mul_support.comp₂_left HasCompactMulSupport.comp₂_left
#align has_compact_support.comp₂_left HasCompactSupport.comp₂_left

end

section Monoid

variable [TopologicalSpace α] [Monoid β]

variable {f f' : α → β} {x : α}

/- warning: has_compact_mul_support.mul -> HasCompactMulSupport.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Monoid.{u2} β] {f : α -> β} {f' : α -> β}, (HasCompactMulSupport.{u1, u2} α β _inst_1 (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) f) -> (HasCompactMulSupport.{u1, u2} α β _inst_1 (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) f') -> (HasCompactMulSupport.{u1, u2} α β _inst_1 (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)))) f f'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Monoid.{u1} β] {f : α -> β} {f' : α -> β}, (HasCompactMulSupport.{u2, u1} α β _inst_1 (Monoid.toOne.{u1} β _inst_2) f) -> (HasCompactMulSupport.{u2, u1} α β _inst_1 (Monoid.toOne.{u1} β _inst_2) f') -> (HasCompactMulSupport.{u2, u1} α β _inst_1 (Monoid.toOne.{u1} β _inst_2) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_2)))) f f'))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.mul HasCompactMulSupport.mulₓ'. -/
@[to_additive]
theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f * f') := by apply hf.comp₂_left hf' (mul_one 1)
#align has_compact_mul_support.mul HasCompactMulSupport.mul
#align has_compact_support.add HasCompactSupport.add

-- `by apply` speeds up elaboration
end Monoid

section DistribMulAction

variable [TopologicalSpace α] [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]

variable {f : α → R} {f' : α → M} {x : α}

/- warning: has_compact_support.smul_left -> HasCompactSupport.smul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : MonoidWithZero.{u3} R] [_inst_3 : AddMonoid.{u2} M] [_inst_4 : DistribMulAction.{u3, u2} R M (MonoidWithZero.toMonoid.{u3} R _inst_2) _inst_3] {f : α -> R} {f' : α -> M}, (HasCompactSupport.{u1, u2} α M _inst_1 (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_3)) f') -> (HasCompactSupport.{u1, u2} α M _inst_1 (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_3)) (SMul.smul.{max u1 u3, max u1 u2} (α -> R) (α -> M) (Pi.smul'.{u1, u3, u2} α (fun (ᾰ : α) => R) (fun (ᾰ : α) => M) (fun (i : α) => SMulZeroClass.toHasSmul.{u3, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_3)) (DistribSMul.toSmulZeroClass.{u3, u2} R M (AddMonoid.toAddZeroClass.{u2} M _inst_3) (DistribMulAction.toDistribSMul.{u3, u2} R M (MonoidWithZero.toMonoid.{u3} R _inst_2) _inst_3 _inst_4)))) f f'))
but is expected to have type
  forall {α : Type.{u3}} {M : Type.{u2}} {R : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : MonoidWithZero.{u1} R] [_inst_3 : AddMonoid.{u2} M] [_inst_4 : DistribMulAction.{u1, u2} R M (MonoidWithZero.toMonoid.{u1} R _inst_2) _inst_3] {f : α -> R} {f' : α -> M}, (HasCompactSupport.{u3, u2} α M _inst_1 (AddMonoid.toZero.{u2} M _inst_3) f') -> (HasCompactSupport.{u3, u2} α M _inst_1 (AddMonoid.toZero.{u2} M _inst_3) (HSMul.hSMul.{max u3 u1, max u3 u2, max u3 u2} (α -> R) (α -> M) (α -> M) (instHSMul.{max u3 u1, max u3 u2} (α -> R) (α -> M) (Pi.smul'.{u3, u1, u2} α (fun (a._@.Mathlib.Topology.Support._hyg.2143 : α) => R) (fun (a._@.Mathlib.Topology.Support._hyg.2146 : α) => M) (fun (i : α) => SMulZeroClass.toSMul.{u1, u2} R M (AddMonoid.toZero.{u2} M _inst_3) (DistribSMul.toSMulZeroClass.{u1, u2} R M (AddMonoid.toAddZeroClass.{u2} M _inst_3) (DistribMulAction.toDistribSMul.{u1, u2} R M (MonoidWithZero.toMonoid.{u1} R _inst_2) _inst_3 _inst_4))))) f f'))
Case conversion may be inaccurate. Consider using '#align has_compact_support.smul_left HasCompactSupport.smul_leftₓ'. -/
theorem HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSupport (f • f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]
#align has_compact_support.smul_left HasCompactSupport.smul_left

end DistribMulAction

section SMulWithZero

variable [TopologicalSpace α] [Zero R] [Zero M] [SMulWithZero R M]

variable {f : α → R} {f' : α → M} {x : α}

/- warning: has_compact_support.smul_right -> HasCompactSupport.smul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Zero.{u3} R] [_inst_3 : Zero.{u2} M] [_inst_4 : SMulWithZero.{u3, u2} R M _inst_2 _inst_3] {f : α -> R} {f' : α -> M}, (HasCompactSupport.{u1, u3} α R _inst_1 _inst_2 f) -> (HasCompactSupport.{u1, u2} α M _inst_1 _inst_3 (SMul.smul.{max u1 u3, max u1 u2} (α -> R) (α -> M) (Pi.smul'.{u1, u3, u2} α (fun (ᾰ : α) => R) (fun (ᾰ : α) => M) (fun (i : α) => SMulZeroClass.toHasSmul.{u3, u2} R M _inst_3 (SMulWithZero.toSmulZeroClass.{u3, u2} R M _inst_2 _inst_3 _inst_4))) f f'))
but is expected to have type
  forall {α : Type.{u3}} {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : Zero.{u2} R] [_inst_3 : Zero.{u1} M] [_inst_4 : SMulWithZero.{u2, u1} R M _inst_2 _inst_3] {f : α -> R} {f' : α -> M}, (HasCompactSupport.{u3, u2} α R _inst_1 _inst_2 f) -> (HasCompactSupport.{u3, u1} α M _inst_1 _inst_3 (HSMul.hSMul.{max u3 u2, max u3 u1, max u3 u1} (α -> R) (α -> M) (α -> M) (instHSMul.{max u3 u2, max u3 u1} (α -> R) (α -> M) (Pi.smul'.{u3, u2, u1} α (fun (a._@.Mathlib.Topology.Support._hyg.2300 : α) => R) (fun (a._@.Mathlib.Topology.Support._hyg.2303 : α) => M) (fun (i : α) => SMulZeroClass.toSMul.{u2, u1} R M _inst_3 (SMulWithZero.toSMulZeroClass.{u2, u1} R M _inst_2 _inst_3 _inst_4)))) f f'))
Case conversion may be inaccurate. Consider using '#align has_compact_support.smul_right HasCompactSupport.smul_rightₓ'. -/
theorem HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSupport (f • f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]
#align has_compact_support.smul_right HasCompactSupport.smul_right

/- warning: has_compact_support.smul_left' -> HasCompactSupport.smul_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Zero.{u3} R] [_inst_3 : Zero.{u2} M] [_inst_4 : SMulWithZero.{u3, u2} R M _inst_2 _inst_3] {f : α -> R} {f' : α -> M}, (HasCompactSupport.{u1, u2} α M _inst_1 _inst_3 f') -> (HasCompactSupport.{u1, u2} α M _inst_1 _inst_3 (SMul.smul.{max u1 u3, max u1 u2} (α -> R) (α -> M) (Pi.smul'.{u1, u3, u2} α (fun (ᾰ : α) => R) (fun (ᾰ : α) => M) (fun (i : α) => SMulZeroClass.toHasSmul.{u3, u2} R M _inst_3 (SMulWithZero.toSmulZeroClass.{u3, u2} R M _inst_2 _inst_3 _inst_4))) f f'))
but is expected to have type
  forall {α : Type.{u3}} {M : Type.{u2}} {R : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : Zero.{u1} R] [_inst_3 : Zero.{u2} M] [_inst_4 : SMulWithZero.{u1, u2} R M _inst_2 _inst_3] {f : α -> R} {f' : α -> M}, (HasCompactSupport.{u3, u2} α M _inst_1 _inst_3 f') -> (HasCompactSupport.{u3, u2} α M _inst_1 _inst_3 (HSMul.hSMul.{max u3 u1, max u3 u2, max u3 u2} (α -> R) (α -> M) (α -> M) (instHSMul.{max u3 u1, max u3 u2} (α -> R) (α -> M) (Pi.smul'.{u3, u1, u2} α (fun (a._@.Mathlib.Topology.Support._hyg.2395 : α) => R) (fun (a._@.Mathlib.Topology.Support._hyg.2398 : α) => M) (fun (i : α) => SMulZeroClass.toSMul.{u1, u2} R M _inst_3 (SMulWithZero.toSMulZeroClass.{u1, u2} R M _inst_2 _inst_3 _inst_4)))) f f'))
Case conversion may be inaccurate. Consider using '#align has_compact_support.smul_left' HasCompactSupport.smul_left'ₓ'. -/
theorem HasCompactSupport.smul_left' (hf : HasCompactSupport f') : HasCompactSupport (f • f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]
#align has_compact_support.smul_left' HasCompactSupport.smul_left'

end SMulWithZero

section MulZeroClass

variable [TopologicalSpace α] [MulZeroClass β]

variable {f f' : α → β} {x : α}

/- warning: has_compact_support.mul_right -> HasCompactSupport.mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : MulZeroClass.{u2} β] {f : α -> β} {f' : α -> β}, (HasCompactSupport.{u1, u2} α β _inst_1 (MulZeroClass.toHasZero.{u2} β _inst_2) f) -> (HasCompactSupport.{u1, u2} α β _inst_1 (MulZeroClass.toHasZero.{u2} β _inst_2) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasMul.{u2} β _inst_2))) f f'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : MulZeroClass.{u1} β] {f : α -> β} {f' : α -> β}, (HasCompactSupport.{u2, u1} α β _inst_1 (MulZeroClass.toZero.{u1} β _inst_2) f) -> (HasCompactSupport.{u2, u1} α β _inst_1 (MulZeroClass.toZero.{u1} β _inst_2) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toMul.{u1} β _inst_2))) f f'))
Case conversion may be inaccurate. Consider using '#align has_compact_support.mul_right HasCompactSupport.mul_rightₓ'. -/
theorem HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport (f * f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]
#align has_compact_support.mul_right HasCompactSupport.mul_right

/- warning: has_compact_support.mul_left -> HasCompactSupport.mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : MulZeroClass.{u2} β] {f : α -> β} {f' : α -> β}, (HasCompactSupport.{u1, u2} α β _inst_1 (MulZeroClass.toHasZero.{u2} β _inst_2) f') -> (HasCompactSupport.{u1, u2} α β _inst_1 (MulZeroClass.toHasZero.{u2} β _inst_2) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasMul.{u2} β _inst_2))) f f'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : MulZeroClass.{u1} β] {f : α -> β} {f' : α -> β}, (HasCompactSupport.{u2, u1} α β _inst_1 (MulZeroClass.toZero.{u1} β _inst_2) f') -> (HasCompactSupport.{u2, u1} α β _inst_1 (MulZeroClass.toZero.{u1} β _inst_2) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toMul.{u1} β _inst_2))) f f'))
Case conversion may be inaccurate. Consider using '#align has_compact_support.mul_left HasCompactSupport.mul_leftₓ'. -/
theorem HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport (f * f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]
#align has_compact_support.mul_left HasCompactSupport.mul_left

end MulZeroClass

namespace LocallyFinite

variable {ι : Type _} {U : ι → Set X} [TopologicalSpace X] [One R]

/- warning: locally_finite.exists_finset_nhd_mul_support_subset -> LocallyFinite.exists_finset_nhd_mulSupport_subset is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {R : Type.{u2}} {ι : Type.{u3}} {U : ι -> (Set.{u1} X)} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : One.{u2} R] {f : ι -> X -> R}, (LocallyFinite.{u3, u1} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u1, u2} X R _inst_2 (f i))) -> (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (mulTSupport.{u1, u2} X R _inst_2 _inst_1 (f i)) (U i)) -> (forall (i : ι), IsOpen.{u1} X _inst_1 (U i)) -> (forall (x : X), Exists.{succ u3} (Finset.{u3} ι) (fun (is : Finset.{u3} ι) => Exists.{succ u1} (Set.{u1} X) (fun {n : Set.{u1} X} => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} X) (Filter.{u1} X) (Filter.hasMem.{u1} X) n (nhds.{u1} X _inst_1 x)) (fun (hn₁ : Membership.Mem.{u1, u1} (Set.{u1} X) (Filter.{u1} X) (Filter.hasMem.{u1} X) n (nhds.{u1} X _inst_1 x)) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) n (Set.interᵢ.{u1, succ u3} X ι (fun (i : ι) => Set.interᵢ.{u1, 0} X (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i is) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i is) => U i)))) (fun (hn₂ : HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) n (Set.interᵢ.{u1, succ u3} X ι (fun (i : ι) => Set.interᵢ.{u1, 0} X (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i is) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i is) => U i)))) => forall (z : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) z n) -> (HasSubset.Subset.{u3} (Set.{u3} ι) (Set.hasSubset.{u3} ι) (Function.mulSupport.{u3, u2} ι R _inst_2 (fun (i : ι) => f i z)) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} ι) (Set.{u3} ι) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (Finset.Set.hasCoeT.{u3} ι))) is)))))))
but is expected to have type
  forall {X : Type.{u2}} {R : Type.{u1}} {ι : Type.{u3}} {U : ι -> (Set.{u2} X)} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : One.{u1} R] {f : ι -> X -> R}, (LocallyFinite.{u3, u2} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u2, u1} X R _inst_2 (f i))) -> (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) (mulTSupport.{u2, u1} X R _inst_2 _inst_1 (f i)) (U i)) -> (forall (i : ι), IsOpen.{u2} X _inst_1 (U i)) -> (forall (x : X), Exists.{succ u3} (Finset.{u3} ι) (fun (is : Finset.{u3} ι) => Exists.{succ u2} (Set.{u2} X) (fun (n : Set.{u2} X) => And (Membership.mem.{u2, u2} (Set.{u2} X) (Filter.{u2} X) (instMembershipSetFilter.{u2} X) n (nhds.{u2} X _inst_1 x)) (And (HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) n (Set.interᵢ.{u2, succ u3} X ι (fun (i : ι) => Set.interᵢ.{u2, 0} X (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i is) (fun (h._@.Mathlib.Topology.Support._hyg.2812 : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i is) => U i)))) (forall (z : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) z n) -> (HasSubset.Subset.{u3} (Set.{u3} ι) (Set.instHasSubsetSet.{u3} ι) (Function.mulSupport.{u3, u1} ι R _inst_2 (fun (i : ι) => f i z)) (Finset.toSet.{u3} ι is)))))))
Case conversion may be inaccurate. Consider using '#align locally_finite.exists_finset_nhd_mul_support_subset LocallyFinite.exists_finset_nhd_mulSupport_subsetₓ'. -/
/-- If a family of functions `f` has locally-finite multiplicative support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are not equal to 1. -/
@[to_additive
      " If a family of functions `f` has locally-finite support, subordinate to a family of open sets,\nthen for any point we can find a neighbourhood on which only finitely-many members of `f` are\nnon-zero. "]
theorem exists_finset_nhd_mulSupport_subset {f : ι → X → R}
    (hlf : LocallyFinite fun i => mulSupport (f i)) (hso : ∀ i, mulTSupport (f i) ⊆ U i)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ (is : Finset ι)(n : Set X)(hn₁ : n ∈ 𝓝 x)(hn₂ : n ⊆ ⋂ i ∈ is, U i),
      ∀ z ∈ n, (mulSupport fun i => f i z) ⊆ is :=
  by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
    let is := hnf.to_finset.filter fun i => x ∈ U i
    let js := hnf.to_finset.filter fun j => x ∉ U j
    refine'
      ⟨is, (n ∩ ⋂ j ∈ js, mulTSupport (f j)ᶜ) ∩ ⋂ i ∈ is, U i, inter_mem (inter_mem hn _) _,
        inter_subset_right _ _, fun z hz => _⟩
    ·
      exact
        (bInter_finset_mem js).mpr fun j hj =>
          IsClosed.compl_mem_nhds (isClosed_mulTSupport _)
            (Set.not_mem_subset (hso j) (finset.mem_filter.mp hj).2)
    · exact (bInter_finset_mem is).mpr fun i hi => (ho i).mem_nhds (finset.mem_filter.mp hi).2
    · have hzn : z ∈ n := by
        rw [inter_assoc] at hz
        exact mem_of_mem_inter_left hz
      replace hz := mem_of_mem_inter_right (mem_of_mem_inter_left hz)
      simp only [Finset.mem_filter, finite.mem_to_finset, mem_set_of_eq, mem_Inter, and_imp] at hz
      suffices (mul_support fun i => f i z) ⊆ hnf.to_finset
        by
        refine' hnf.to_finset.subset_coe_filter_of_subset_forall _ this fun i hi => _
        specialize hz i ⟨z, ⟨hi, hzn⟩⟩
        contrapose hz
        simp [hz, subset_mulTSupport (f i) hi]
      intro i hi
      simp only [finite.coe_to_finset, mem_set_of_eq]
      exact ⟨z, ⟨hi, hzn⟩⟩
#align locally_finite.exists_finset_nhd_mul_support_subset LocallyFinite.exists_finset_nhd_mulSupport_subset
#align locally_finite.exists_finset_nhd_support_subset LocallyFinite.exists_finset_nhd_support_subset

end LocallyFinite

