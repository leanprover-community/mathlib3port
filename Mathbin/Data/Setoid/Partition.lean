/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen, Patrick Massot

! This file was ported from Lean 3 source module data.setoid.partition
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Set.Finite
import Mathbin.Data.Setoid.Basic
import Mathbin.Order.Partition.Finpartition

/-!
# Equivalence relations: partitions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file comprises properties of equivalence relations viewed as partitions.
There are two implementations of partitions here:
* A collection `c : set (set α)` of sets is a partition of `α` if `∅ ∉ c` and each element `a : α`
  belongs to a unique set `b ∈ c`. This is expressed as `is_partition c`
* An indexed partition is a map `s : ι → α` whose image is a partition. This is
  expressed as `indexed_partition s`.

Of course both implementations are related to `quotient` and `setoid`.

`setoid.is_partition.partition` and `finpartition.is_partition_parts` furnish
a link between `setoid.is_partition` and `finpartition`.

## TODO

Could the design of `finpartition` inform the one of `setoid.is_partition`? Maybe bundling it and
changing it from `set (set α)` to `set α` where `[lattice α] [order_bot α]` would make it more
usable.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/


namespace Setoid

variable {α : Type _}

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » c) -/
#print Setoid.eq_of_mem_eqv_class /-
/-- If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equal. -/
theorem eq_of_mem_eqv_class {c : Set (Set α)} (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) {x b b'}
    (hc : b ∈ c) (hb : x ∈ b) (hc' : b' ∈ c) (hb' : x ∈ b') : b = b' :=
  (H x).unique₂ hc hb hc' hb'
#align setoid.eq_of_mem_eqv_class Setoid.eq_of_mem_eqv_class
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » c) -/
#print Setoid.mkClasses /-
/-- Makes an equivalence relation from a set of sets partitioning α. -/
def mkClasses (c : Set (Set α)) (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) : Setoid α :=
  ⟨fun x y => ∀ s ∈ c, x ∈ s → y ∈ s,
    ⟨fun _ _ _ hx => hx, fun x y h s hs hy =>
      (H x).elim₂ fun t ht hx _ =>
        have : s = t := eq_of_mem_eqv_class H hs hy ht (h t ht hx)
        this.symm ▸ hx,
      fun x y z h1 h2 s hs hx =>
      (H y).elim₂ fun t ht hy _ =>
        (H z).elim₂ fun t' ht' hz _ =>
          have hst : s = t := eq_of_mem_eqv_class H hs (h1 _ hs hx) ht hy
          have htt' : t = t' := eq_of_mem_eqv_class H ht (h2 _ ht hy) ht' hz
          (hst.trans htt').symm ▸ hz⟩⟩
#align setoid.mk_classes Setoid.mkClasses
-/

#print Setoid.classes /-
/-- Makes the equivalence classes of an equivalence relation. -/
def classes (r : Setoid α) : Set (Set α) :=
  { s | ∃ y, s = { x | r.Rel x y } }
#align setoid.classes Setoid.classes
-/

#print Setoid.mem_classes /-
theorem mem_classes (r : Setoid α) (y) : { x | r.Rel x y } ∈ r.classes :=
  ⟨y, rfl⟩
#align setoid.mem_classes Setoid.mem_classes
-/

#print Setoid.classes_ker_subset_fiber_set /-
theorem classes_ker_subset_fiber_set {β : Type _} (f : α → β) :
    (Setoid.ker f).classes ⊆ Set.range fun y => { x | f x = y } :=
  by
  rintro s ⟨x, rfl⟩
  rw [Set.mem_range]
  exact ⟨f x, rfl⟩
#align setoid.classes_ker_subset_fiber_set Setoid.classes_ker_subset_fiber_set
-/

/- warning: setoid.finite_classes_ker -> Setoid.finite_classes_ker is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u2} β] (f : α -> β), Set.Finite.{u1} (Set.{u1} α) (Setoid.classes.{u1} α (Setoid.ker.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Finite.{succ u1} β] (f : α -> β), Set.Finite.{u2} (Set.{u2} α) (Setoid.classes.{u2} α (Setoid.ker.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align setoid.finite_classes_ker Setoid.finite_classes_kerₓ'. -/
theorem finite_classes_ker {α β : Type _} [Finite β] (f : α → β) : (Setoid.ker f).classes.Finite :=
  (Set.finite_range _).Subset <| classes_ker_subset_fiber_set f
#align setoid.finite_classes_ker Setoid.finite_classes_ker

/- warning: setoid.card_classes_ker_le -> Setoid.card_classes_ker_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u2} β] (f : α -> β) [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (Setoid.classes.{u1} α (Setoid.ker.{u1, u2} α β f)))], LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (Setoid.classes.{u1} α (Setoid.ker.{u1, u2} α β f))) _inst_2) (Fintype.card.{u2} β _inst_1)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u1} β] (f : α -> β) [_inst_2 : Fintype.{u2} (Set.Elem.{u2} (Set.{u2} α) (Setoid.classes.{u2} α (Setoid.ker.{u2, u1} α β f)))], LE.le.{0} Nat instLENat (Fintype.card.{u2} (Set.Elem.{u2} (Set.{u2} α) (Setoid.classes.{u2} α (Setoid.ker.{u2, u1} α β f))) _inst_2) (Fintype.card.{u1} β _inst_1)
Case conversion may be inaccurate. Consider using '#align setoid.card_classes_ker_le Setoid.card_classes_ker_leₓ'. -/
theorem card_classes_ker_le {α β : Type _} [Fintype β] (f : α → β)
    [Fintype (Setoid.ker f).classes] : Fintype.card (Setoid.ker f).classes ≤ Fintype.card β := by
  classical exact
      le_trans (Set.card_le_of_subset (classes_ker_subset_fiber_set f)) (Fintype.card_range_le _)
#align setoid.card_classes_ker_le Setoid.card_classes_ker_le

#print Setoid.eq_iff_classes_eq /-
/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
theorem eq_iff_classes_eq {r₁ r₂ : Setoid α} :
    r₁ = r₂ ↔ ∀ x, { y | r₁.Rel x y } = { y | r₂.Rel x y } :=
  ⟨fun h x => h ▸ rfl, fun h => ext' fun x => Set.ext_iff.1 <| h x⟩
#align setoid.eq_iff_classes_eq Setoid.eq_iff_classes_eq
-/

/- warning: setoid.rel_iff_exists_classes -> Setoid.rel_iff_exists_classes is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : Setoid.{succ u1} α) {x : α} {y : α}, Iff (Setoid.Rel.{u1} α r x y) (Exists.{succ u1} (Set.{u1} α) (fun (c : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) c (Setoid.classes.{u1} α r)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) c (Setoid.classes.{u1} α r)) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x c) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y c))))
but is expected to have type
  forall {α : Type.{u1}} (r : Setoid.{succ u1} α) {x : α} {y : α}, Iff (Setoid.Rel.{u1} α r x y) (Exists.{succ u1} (Set.{u1} α) (fun (c : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) c (Setoid.classes.{u1} α r)) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x c) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y c))))
Case conversion may be inaccurate. Consider using '#align setoid.rel_iff_exists_classes Setoid.rel_iff_exists_classesₓ'. -/
theorem rel_iff_exists_classes (r : Setoid α) {x y} : r.Rel x y ↔ ∃ c ∈ r.classes, x ∈ c ∧ y ∈ c :=
  ⟨fun h => ⟨_, r.mem_classes y, h, r.refl' y⟩, fun ⟨c, ⟨z, hz⟩, hx, hy⟩ =>
    by
    subst c
    exact r.trans' hx (r.symm' hy)⟩
#align setoid.rel_iff_exists_classes Setoid.rel_iff_exists_classes

#print Setoid.classes_inj /-
/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
theorem classes_inj {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ r₁.classes = r₂.classes :=
  ⟨fun h => h ▸ rfl, fun h => ext' fun a b => by simp only [rel_iff_exists_classes, exists_prop, h]⟩
#align setoid.classes_inj Setoid.classes_inj
-/

#print Setoid.empty_not_mem_classes /-
/-- The empty set is not an equivalence class. -/
theorem empty_not_mem_classes {r : Setoid α} : ∅ ∉ r.classes := fun ⟨y, hy⟩ =>
  Set.not_mem_empty y <| hy.symm ▸ r.refl' y
#align setoid.empty_not_mem_classes Setoid.empty_not_mem_classes
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » r.classes) -/
#print Setoid.classes_eqv_classes /-
/-- Equivalence classes partition the type. -/
theorem classes_eqv_classes {r : Setoid α} (a) : ∃! (b : _)(_ : b ∈ r.classes), a ∈ b :=
  ExistsUnique.intro₂ { x | r.Rel x a } (r.mem_classes a) (r.refl' _) <|
    by
    rintro _ ⟨y, rfl⟩ ha
    ext x
    exact ⟨fun hx => r.trans' hx (r.symm' ha), fun hx => r.trans' hx ha⟩
#align setoid.classes_eqv_classes Setoid.classes_eqv_classes
-/

#print Setoid.eq_of_mem_classes /-
/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
theorem eq_of_mem_classes {r : Setoid α} {x b} (hc : b ∈ r.classes) (hb : x ∈ b) {b'}
    (hc' : b' ∈ r.classes) (hb' : x ∈ b') : b = b' :=
  eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'
#align setoid.eq_of_mem_classes Setoid.eq_of_mem_classes
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » c) -/
#print Setoid.eq_eqv_class_of_mem /-
/-- The elements of a set of sets partitioning α are the equivalence classes of the
    equivalence relation defined by the set of sets. -/
theorem eq_eqv_class_of_mem {c : Set (Set α)} (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) {s y}
    (hs : s ∈ c) (hy : y ∈ s) : s = { x | (mkClasses c H).Rel x y } :=
  Set.ext fun x =>
    ⟨fun hs' => symm' (mkClasses c H) fun b' hb' h' => eq_of_mem_eqv_class H hs hy hb' h' ▸ hs',
      fun hx =>
      (H x).elim₂ fun b' hc' hb' h' =>
        (eq_of_mem_eqv_class H hs hy hc' <| hx b' hc' hb').symm ▸ hb'⟩
#align setoid.eq_eqv_class_of_mem Setoid.eq_eqv_class_of_mem
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » c) -/
#print Setoid.eqv_class_mem /-
/-- The equivalence classes of the equivalence relation defined by a set of sets
    partitioning α are elements of the set of sets. -/
theorem eqv_class_mem {c : Set (Set α)} (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) {y} :
    { x | (mkClasses c H).Rel x y } ∈ c :=
  (H y).elim₂ fun b hc hy hb => eq_eqv_class_of_mem H hc hy ▸ hc
#align setoid.eqv_class_mem Setoid.eqv_class_mem
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » c) -/
#print Setoid.eqv_class_mem' /-
theorem eqv_class_mem' {c : Set (Set α)} (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) {x} :
    { y : α | (mkClasses c H).Rel x y } ∈ c :=
  by
  convert Setoid.eqv_class_mem H
  ext
  rw [Setoid.comm']
#align setoid.eqv_class_mem' Setoid.eqv_class_mem'
-/

/- warning: setoid.eqv_classes_disjoint -> Setoid.eqv_classes_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, (forall (a : α), ExistsUnique.{succ u1} (Set.{u1} α) (fun (b : Set.{u1} α) => ExistsUnique.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) b c) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) b c) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a b))) -> (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) c (id.{succ u1} (Set.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, (forall (a : α), ExistsUnique.{succ u1} (Set.{u1} α) (fun (b : Set.{u1} α) => ExistsUnique.{0} (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) b c) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) b c) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a b))) -> (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) c (id.{succ u1} (Set.{u1} α)))
Case conversion may be inaccurate. Consider using '#align setoid.eqv_classes_disjoint Setoid.eqv_classes_disjointₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » c) -/
/-- Distinct elements of a set of sets partitioning α are disjoint. -/
theorem eqv_classes_disjoint {c : Set (Set α)} (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) :
    c.PairwiseDisjoint id := fun b₁ h₁ b₂ h₂ h =>
  Set.disjoint_left.2 fun x hx1 hx2 =>
    (H x).elim₂ fun b hc hx hb => h <| eq_of_mem_eqv_class H h₁ hx1 h₂ hx2
#align setoid.eqv_classes_disjoint Setoid.eqv_classes_disjoint

/- warning: setoid.eqv_classes_of_disjoint_union -> Setoid.eqv_classes_of_disjoint_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, (Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α c) (Set.univ.{u1} α)) -> (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) c (id.{succ u1} (Set.{u1} α))) -> (forall (a : α), ExistsUnique.{succ u1} (Set.{u1} α) (fun (b : Set.{u1} α) => ExistsUnique.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) b c) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) b c) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a b)))
but is expected to have type
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, (Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α c) (Set.univ.{u1} α)) -> (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) c (id.{succ u1} (Set.{u1} α))) -> (forall (a : α), ExistsUnique.{succ u1} (Set.{u1} α) (fun (b : Set.{u1} α) => ExistsUnique.{0} (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) b c) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) b c) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a b)))
Case conversion may be inaccurate. Consider using '#align setoid.eqv_classes_of_disjoint_union Setoid.eqv_classes_of_disjoint_unionₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » c) -/
/-- A set of disjoint sets covering α partition α (classical). -/
theorem eqv_classes_of_disjoint_union {c : Set (Set α)} (hu : Set.unionₛ c = @Set.univ α)
    (H : c.PairwiseDisjoint id) (a) : ∃! (b : _)(_ : b ∈ c), a ∈ b :=
  let ⟨b, hc, ha⟩ := Set.mem_unionₛ.1 <| show a ∈ _ by rw [hu] <;> exact Set.mem_univ a
  ExistsUnique.intro₂ b hc ha fun b' hc' ha' => H.elim_set hc' hc a ha' ha
#align setoid.eqv_classes_of_disjoint_union Setoid.eqv_classes_of_disjoint_union

/- warning: setoid.setoid_of_disjoint_union -> Setoid.setoidOfDisjointUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, (Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α c) (Set.univ.{u1} α)) -> (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) c (id.{succ u1} (Set.{u1} α))) -> (Setoid.{succ u1} α)
but is expected to have type
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, (Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α c) (Set.univ.{u1} α)) -> (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) c (id.{succ u1} (Set.{u1} α))) -> (Setoid.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align setoid.setoid_of_disjoint_union Setoid.setoidOfDisjointUnionₓ'. -/
/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
def setoidOfDisjointUnion {c : Set (Set α)} (hu : Set.unionₛ c = @Set.univ α)
    (H : c.PairwiseDisjoint id) : Setoid α :=
  Setoid.mkClasses c <| eqv_classes_of_disjoint_union hu H
#align setoid.setoid_of_disjoint_union Setoid.setoidOfDisjointUnion

#print Setoid.mkClasses_classes /-
/-- The equivalence relation made from the equivalence classes of an equivalence
    relation r equals r. -/
theorem mkClasses_classes (r : Setoid α) : mkClasses r.classes classes_eqv_classes = r :=
  ext' fun x y =>
    ⟨fun h => r.symm' (h { z | r.Rel z x } (r.mem_classes x) <| r.refl' x), fun h b hb hx =>
      eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩
#align setoid.mk_classes_classes Setoid.mkClasses_classes
-/

#print Setoid.unionₛ_classes /-
@[simp]
theorem unionₛ_classes (r : Setoid α) : ⋃₀ r.classes = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_unionₛ.2 ⟨{ y | r.Rel y x }, ⟨x, rfl⟩, Setoid.refl _⟩
#align setoid.sUnion_classes Setoid.unionₛ_classes
-/

section Partition

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ∈ » c) -/
#print Setoid.IsPartition /-
/-- A collection `c : set (set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def IsPartition (c : Set (Set α)) :=
  ∅ ∉ c ∧ ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b
#align setoid.is_partition Setoid.IsPartition
-/

#print Setoid.nonempty_of_mem_partition /-
/-- A partition of `α` does not contain the empty set. -/
theorem nonempty_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (h : s ∈ c) :
    s.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun hs0 => hc.1 <| hs0 ▸ h
#align setoid.nonempty_of_mem_partition Setoid.nonempty_of_mem_partition
-/

#print Setoid.isPartition_classes /-
theorem isPartition_classes (r : Setoid α) : IsPartition r.classes :=
  ⟨empty_not_mem_classes, classes_eqv_classes⟩
#align setoid.is_partition_classes Setoid.isPartition_classes
-/

/- warning: setoid.is_partition.pairwise_disjoint -> Setoid.IsPartition.pairwiseDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, (Setoid.IsPartition.{u1} α c) -> (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) c (id.{succ u1} (Set.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, (Setoid.IsPartition.{u1} α c) -> (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) c (id.{succ u1} (Set.{u1} α)))
Case conversion may be inaccurate. Consider using '#align setoid.is_partition.pairwise_disjoint Setoid.IsPartition.pairwiseDisjointₓ'. -/
theorem IsPartition.pairwiseDisjoint {c : Set (Set α)} (hc : IsPartition c) :
    c.PairwiseDisjoint id :=
  eqv_classes_disjoint hc.2
#align setoid.is_partition.pairwise_disjoint Setoid.IsPartition.pairwiseDisjoint

#print Setoid.IsPartition.unionₛ_eq_univ /-
theorem IsPartition.unionₛ_eq_univ {c : Set (Set α)} (hc : IsPartition c) : ⋃₀ c = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    Set.mem_unionₛ.2 <|
      let ⟨t, ht⟩ := hc.2 x
      ⟨t, by
        simp only [exists_unique_iff_exists] at ht
        tauto⟩
#align setoid.is_partition.sUnion_eq_univ Setoid.IsPartition.unionₛ_eq_univ
-/

#print Setoid.exists_of_mem_partition /-
/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
theorem exists_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (hs : s ∈ c) :
    ∃ y, s = { x | (mkClasses c hc.2).Rel x y } :=
  let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩
#align setoid.exists_of_mem_partition Setoid.exists_of_mem_partition
-/

#print Setoid.classes_mkClasses /-
/-- The equivalence classes of the equivalence relation defined by a partition of α equal
    the original partition. -/
theorem classes_mkClasses (c : Set (Set α)) (hc : IsPartition c) : (mkClasses c hc.2).classes = c :=
  Set.ext fun s =>
    ⟨fun ⟨y, hs⟩ =>
      (hc.2 y).elim₂ fun b hm hb hy => by
        rwa [show s = b from
            hs.symm ▸
              Set.ext fun x =>
                ⟨fun hx => symm' (mk_classes c hc.2) hx b hm hb, fun hx b' hc' hx' =>
                  eq_of_mem_eqv_class hc.2 hm hx hc' hx' ▸ hb⟩],
      exists_of_mem_partition hc⟩
#align setoid.classes_mk_classes Setoid.classes_mkClasses
-/

#print Setoid.Partition.le /-
/-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
instance Partition.le : LE (Subtype (@IsPartition α)) :=
  ⟨fun x y => mkClasses x.1 x.2.2 ≤ mkClasses y.1 y.2.2⟩
#align setoid.partition.le Setoid.Partition.le
-/

#print Setoid.Partition.partialOrder /-
/-- Defining a partial order on partitions as the partial order on their induced
    equivalence relations. -/
instance Partition.partialOrder : PartialOrder (Subtype (@IsPartition α))
    where
  le := (· ≤ ·)
  lt x y := x ≤ y ∧ ¬y ≤ x
  le_refl _ := @le_refl (Setoid α) _ _
  le_trans _ _ _ := @le_trans (Setoid α) _ _ _ _
  lt_iff_le_not_le _ _ := Iff.rfl
  le_antisymm x y hx hy := by
    let h := @le_antisymm (Setoid α) _ _ _ hx hy
    rw [Subtype.ext_iff_val, ← classes_mk_classes x.1 x.2, ← classes_mk_classes y.1 y.2, h]
#align setoid.partition.partial_order Setoid.Partition.partialOrder
-/

variable (α)

#print Setoid.Partition.orderIso /-
/-- The order-preserving bijection between equivalence relations on a type `α`, and
  partitions of `α` into subsets. -/
protected def Partition.orderIso : Setoid α ≃o { C : Set (Set α) // IsPartition C }
    where
  toFun r := ⟨r.classes, empty_not_mem_classes, classes_eqv_classes⟩
  invFun C := mkClasses C.1 C.2.2
  left_inv := mkClasses_classes
  right_inv C := by rw [Subtype.ext_iff_val, ← classes_mk_classes C.1 C.2]
  map_rel_iff' r s :=
    by
    conv_rhs => rw [← mk_classes_classes r, ← mk_classes_classes s]
    rfl
#align setoid.partition.order_iso Setoid.Partition.orderIso
-/

variable {α}

#print Setoid.Partition.completeLattice /-
/-- A complete lattice instance for partitions; there is more infrastructure for the
    equivalent complete lattice on equivalence relations. -/
instance Partition.completeLattice : CompleteLattice (Subtype (@IsPartition α)) :=
  GaloisInsertion.liftCompleteLattice <|
    @OrderIso.toGaloisInsertion _ (Subtype (@IsPartition α)) _ (PartialOrder.toPreorder _) <|
      Partition.orderIso α
#align setoid.partition.complete_lattice Setoid.Partition.completeLattice
-/

end Partition

/- warning: setoid.is_partition.finpartition -> Setoid.IsPartition.finpartition is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Finset.{u1} (Set.{u1} α)}, (Setoid.IsPartition.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (Finset.Set.hasCoeT.{u1} (Set.{u1} α)))) c)) -> (Finpartition.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {c : Finset.{u1} (Set.{u1} α)}, (Setoid.IsPartition.{u1} α (Finset.toSet.{u1} (Set.{u1} α) c)) -> (Finpartition.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align setoid.is_partition.finpartition Setoid.IsPartition.finpartitionₓ'. -/
/-- A finite setoid partition furnishes a finpartition -/
@[simps]
def IsPartition.finpartition {c : Finset (Set α)} (hc : Setoid.IsPartition (c : Set (Set α))) :
    Finpartition (Set.univ : Set α) where
  parts := c
  SupIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr <| eqv_classes_disjoint hc.2
  supParts := c.sup_id_set_eq_unionₛ.trans hc.unionₛ_eq_univ
  not_bot_mem := hc.left
#align setoid.is_partition.finpartition Setoid.IsPartition.finpartition

end Setoid

/- warning: finpartition.is_partition_parts -> Finpartition.isPartition_parts is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Finpartition.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.univ.{u1} α)), Setoid.IsPartition.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (Finset.Set.hasCoeT.{u1} (Set.{u1} α)))) (Finpartition.parts.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.univ.{u1} α) f))
but is expected to have type
  forall {α : Type.{u1}} (f : Finpartition.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.univ.{u1} α)), Setoid.IsPartition.{u1} α (Finset.toSet.{u1} (Set.{u1} α) (Finpartition.parts.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.univ.{u1} α) f))
Case conversion may be inaccurate. Consider using '#align finpartition.is_partition_parts Finpartition.isPartition_partsₓ'. -/
/-- A finpartition gives rise to a setoid partition -/
theorem Finpartition.isPartition_parts {α} (f : Finpartition (Set.univ : Set α)) :
    Setoid.IsPartition (f.parts : Set (Set α)) :=
  ⟨f.not_bot_mem,
    Setoid.eqv_classes_of_disjoint_union (f.parts.sup_id_set_eq_unionₛ.symm.trans f.supParts)
      f.SupIndep.PairwiseDisjoint⟩
#align finpartition.is_partition_parts Finpartition.isPartition_parts

#print IndexedPartition /-
/-- Constructive information associated with a partition of a type `α` indexed by another type `ι`,
`s : ι → set α`.

`indexed_partition.index` sends an element to its index, while `indexed_partition.some` sends
an index to an element of the corresponding set.

This type is primarily useful for definitional control of `s` - if this is not needed, then
`setoid.ker index` by itself may be sufficient. -/
structure IndexedPartition {ι α : Type _} (s : ι → Set α) where
  eq_of_mem : ∀ {x i j}, x ∈ s i → x ∈ s j → i = j
  some : ι → α
  some_mem : ∀ i, some i ∈ s i
  index : α → ι
  mem_index : ∀ x, x ∈ s (index x)
#align indexed_partition IndexedPartition
-/

/- warning: indexed_partition.mk' -> IndexedPartition.mk' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} (s : ι -> (Set.{u2} α)), (forall (i : ι) (j : ι), (Ne.{succ u1} ι i j) -> (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) (s i) (s j))) -> (forall (i : ι), Set.Nonempty.{u2} α (s i)) -> (forall (x : α), Exists.{succ u1} ι (fun (i : ι) => Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) x (s i))) -> (IndexedPartition.{u1, u2} ι α s)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} (s : ι -> (Set.{u2} α)), (forall (i : ι) (j : ι), (Ne.{succ u1} ι i j) -> (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (s i) (s j))) -> (forall (i : ι), Set.Nonempty.{u2} α (s i)) -> (forall (x : α), Exists.{succ u1} ι (fun (i : ι) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s i))) -> (IndexedPartition.{u1, u2} ι α s)
Case conversion may be inaccurate. Consider using '#align indexed_partition.mk' IndexedPartition.mk'ₓ'. -/
/-- The non-constructive constructor for `indexed_partition`. -/
noncomputable def IndexedPartition.mk' {ι α : Type _} (s : ι → Set α)
    (dis : ∀ i j, i ≠ j → Disjoint (s i) (s j)) (nonempty : ∀ i, (s i).Nonempty)
    (ex : ∀ x, ∃ i, x ∈ s i) : IndexedPartition s
    where
  eq_of_mem x i j hxi hxj := by_contradiction fun h => (dis _ _ h).le_bot ⟨hxi, hxj⟩
  some i := (Nonempty i).some
  some_mem i := (Nonempty i).choose_spec
  index x := (ex x).some
  mem_index x := (ex x).choose_spec
#align indexed_partition.mk' IndexedPartition.mk'

namespace IndexedPartition

open Set

variable {ι α : Type _} {s : ι → Set α} (hs : IndexedPartition s)

/-- On a unique index set there is the obvious trivial partition -/
instance [Unique ι] [Inhabited α] : Inhabited (IndexedPartition fun i : ι => (Set.univ : Set α)) :=
  ⟨{  eq_of_mem := fun x i j hi hj => Subsingleton.elim _ _
      some := default
      some_mem := Set.mem_univ
      index := default
      mem_index := Set.mem_univ }⟩

attribute [simp] some_mem mem_index

include hs

/- warning: indexed_partition.exists_mem -> IndexedPartition.exists_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : ι -> (Set.{u2} α)}, (IndexedPartition.{u1, u2} ι α s) -> (forall (x : α), Exists.{succ u1} ι (fun (i : ι) => Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) x (s i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : ι -> (Set.{u1} α)}, (IndexedPartition.{u2, u1} ι α s) -> (forall (x : α), Exists.{succ u2} ι (fun (i : ι) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (s i)))
Case conversion may be inaccurate. Consider using '#align indexed_partition.exists_mem IndexedPartition.exists_memₓ'. -/
theorem exists_mem (x : α) : ∃ i, x ∈ s i :=
  ⟨hs.index x, hs.mem_index x⟩
#align indexed_partition.exists_mem IndexedPartition.exists_mem

#print IndexedPartition.unionᵢ /-
theorem unionᵢ : (⋃ i, s i) = univ := by
  ext x
  simp [hs.exists_mem x]
#align indexed_partition.Union IndexedPartition.unionᵢ
-/

/- warning: indexed_partition.disjoint -> IndexedPartition.disjoint is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : ι -> (Set.{u2} α)}, (IndexedPartition.{u1, u2} ι α s) -> (forall {i : ι} {j : ι}, (Ne.{succ u1} ι i j) -> (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) (s i) (s j)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : ι -> (Set.{u1} α)}, (IndexedPartition.{u2, u1} ι α s) -> (forall {i : ι} {j : ι}, (Ne.{succ u2} ι i j) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (s i) (s j)))
Case conversion may be inaccurate. Consider using '#align indexed_partition.disjoint IndexedPartition.disjointₓ'. -/
theorem disjoint : ∀ {i j}, i ≠ j → Disjoint (s i) (s j) := fun i j h =>
  disjoint_left.mpr fun x hxi hxj => h (hs.eq_of_mem hxi hxj)
#align indexed_partition.disjoint IndexedPartition.disjoint

#print IndexedPartition.mem_iff_index_eq /-
theorem mem_iff_index_eq {x i} : x ∈ s i ↔ hs.index x = i :=
  ⟨fun hxi => (hs.eq_of_mem hxi (hs.mem_index x)).symm, fun h => h ▸ hs.mem_index _⟩
#align indexed_partition.mem_iff_index_eq IndexedPartition.mem_iff_index_eq
-/

#print IndexedPartition.eq /-
theorem eq (i) : s i = { x | hs.index x = i } :=
  Set.ext fun _ => hs.mem_iff_index_eq
#align indexed_partition.eq IndexedPartition.eq
-/

#print IndexedPartition.setoid /-
/-- The equivalence relation associated to an indexed partition. Two
elements are equivalent if they belong to the same set of the partition. -/
protected abbrev setoid (hs : IndexedPartition s) : Setoid α :=
  Setoid.ker hs.index
#align indexed_partition.setoid IndexedPartition.setoid
-/

/- warning: indexed_partition.index_some -> IndexedPartition.index_some is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : ι -> (Set.{u2} α)} (hs : IndexedPartition.{u1, u2} ι α s) (i : ι), Eq.{succ u1} ι (IndexedPartition.index.{u1, u2} ι α s hs (IndexedPartition.some.{u1, u2} ι α s hs i)) i
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : ι -> (Set.{u1} α)} (hs : IndexedPartition.{u2, u1} ι α s) (i : ι), Eq.{succ u2} ι (IndexedPartition.index.{u2, u1} ι α s hs (IndexedPartition.some.{u2, u1} ι α s hs i)) i
Case conversion may be inaccurate. Consider using '#align indexed_partition.index_some IndexedPartition.index_someₓ'. -/
@[simp]
theorem index_some (i : ι) : hs.index (hs.some i) = i :=
  (mem_iff_index_eq _).1 <| hs.some_mem i
#align indexed_partition.index_some IndexedPartition.index_some

#print IndexedPartition.some_index /-
theorem some_index (x : α) : hs.Setoid.Rel (hs.some (hs.index x)) x :=
  hs.index_some (hs.index x)
#align indexed_partition.some_index IndexedPartition.some_index
-/

#print IndexedPartition.Quotient /-
/-- The quotient associated to an indexed partition. -/
protected def Quotient :=
  Quotient hs.Setoid
#align indexed_partition.quotient IndexedPartition.Quotient
-/

#print IndexedPartition.proj /-
/-- The projection onto the quotient associated to an indexed partition. -/
def proj : α → hs.Quotient :=
  Quotient.mk''
#align indexed_partition.proj IndexedPartition.proj
-/

instance [Inhabited α] : Inhabited hs.Quotient :=
  ⟨hs.proj default⟩

#print IndexedPartition.proj_eq_iff /-
theorem proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.index x = hs.index y :=
  Quotient.eq_rel
#align indexed_partition.proj_eq_iff IndexedPartition.proj_eq_iff
-/

#print IndexedPartition.proj_some_index /-
@[simp]
theorem proj_some_index (x : α) : hs.proj (hs.some (hs.index x)) = hs.proj x :=
  Quotient.eq''.2 (hs.some_index x)
#align indexed_partition.proj_some_index IndexedPartition.proj_some_index
-/

#print IndexedPartition.equivQuotient /-
/-- The obvious equivalence between the quotient associated to an indexed partition and
the indexing type. -/
def equivQuotient : ι ≃ hs.Quotient :=
  (Setoid.quotientKerEquivOfRightInverse hs.index hs.some <| hs.index_some).symm
#align indexed_partition.equiv_quotient IndexedPartition.equivQuotient
-/

#print IndexedPartition.equivQuotient_index_apply /-
@[simp]
theorem equivQuotient_index_apply (x : α) : hs.equivQuotient (hs.index x) = hs.proj x :=
  hs.proj_eq_iff.mpr (some_index hs x)
#align indexed_partition.equiv_quotient_index_apply IndexedPartition.equivQuotient_index_apply
-/

/- warning: indexed_partition.equiv_quotient_symm_proj_apply -> IndexedPartition.equivQuotient_symm_proj_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : ι -> (Set.{u2} α)} (hs : IndexedPartition.{u1, u2} ι α s) (x : α), Eq.{succ u1} ι (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} (IndexedPartition.Quotient.{u1, u2} ι α s hs) ι) (fun (_x : Equiv.{succ u2, succ u1} (IndexedPartition.Quotient.{u1, u2} ι α s hs) ι) => (IndexedPartition.Quotient.{u1, u2} ι α s hs) -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} (IndexedPartition.Quotient.{u1, u2} ι α s hs) ι) (Equiv.symm.{succ u1, succ u2} ι (IndexedPartition.Quotient.{u1, u2} ι α s hs) (IndexedPartition.equivQuotient.{u1, u2} ι α s hs)) (IndexedPartition.proj.{u1, u2} ι α s hs x)) (IndexedPartition.index.{u1, u2} ι α s hs x)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : ι -> (Set.{u1} α)} (hs : IndexedPartition.{u2, u1} ι α s) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : IndexedPartition.Quotient.{u2, u1} ι α s hs) => ι) (IndexedPartition.proj.{u2, u1} ι α s hs x)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} (IndexedPartition.Quotient.{u2, u1} ι α s hs) ι) (IndexedPartition.Quotient.{u2, u1} ι α s hs) (fun (_x : IndexedPartition.Quotient.{u2, u1} ι α s hs) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : IndexedPartition.Quotient.{u2, u1} ι α s hs) => ι) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} (IndexedPartition.Quotient.{u2, u1} ι α s hs) ι) (Equiv.symm.{succ u2, succ u1} ι (IndexedPartition.Quotient.{u2, u1} ι α s hs) (IndexedPartition.equivQuotient.{u2, u1} ι α s hs)) (IndexedPartition.proj.{u2, u1} ι α s hs x)) (IndexedPartition.index.{u2, u1} ι α s hs x)
Case conversion may be inaccurate. Consider using '#align indexed_partition.equiv_quotient_symm_proj_apply IndexedPartition.equivQuotient_symm_proj_applyₓ'. -/
@[simp]
theorem equivQuotient_symm_proj_apply (x : α) : hs.equivQuotient.symm (hs.proj x) = hs.index x :=
  rfl
#align indexed_partition.equiv_quotient_symm_proj_apply IndexedPartition.equivQuotient_symm_proj_apply

#print IndexedPartition.equivQuotient_index /-
theorem equivQuotient_index : hs.equivQuotient ∘ hs.index = hs.proj :=
  funext hs.equivQuotient_index_apply
#align indexed_partition.equiv_quotient_index IndexedPartition.equivQuotient_index
-/

#print IndexedPartition.out /-
/-- A map choosing a representative for each element of the quotient associated to an indexed
partition. This is a computable version of `quotient.out'` using `indexed_partition.some`. -/
def out : hs.Quotient ↪ α :=
  hs.equivQuotient.symm.toEmbedding.trans ⟨hs.some, Function.LeftInverse.injective hs.index_some⟩
#align indexed_partition.out IndexedPartition.out
-/

#print IndexedPartition.out_proj /-
/-- This lemma is analogous to `quotient.mk_out'`. -/
@[simp]
theorem out_proj (x : α) : hs.out (hs.proj x) = hs.some (hs.index x) :=
  rfl
#align indexed_partition.out_proj IndexedPartition.out_proj
-/

/- warning: indexed_partition.index_out' -> IndexedPartition.index_out' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : ι -> (Set.{u2} α)} (hs : IndexedPartition.{u1, u2} ι α s) (x : IndexedPartition.Quotient.{u1, u2} ι α s hs), Eq.{succ u1} ι (IndexedPartition.index.{u1, u2} ι α s hs (Quotient.out'.{succ u2} α (IndexedPartition.setoid.{u1, u2} ι α s hs) x)) (IndexedPartition.index.{u1, u2} ι α s hs (coeFn.{succ u2, succ u2} (Function.Embedding.{succ u2, succ u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs) α) (fun (_x : Function.Embedding.{succ u2, succ u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs) α) => (IndexedPartition.Quotient.{u1, u2} ι α s hs) -> α) (Function.Embedding.hasCoeToFun.{succ u2, succ u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs) α) (IndexedPartition.out.{u1, u2} ι α s hs) x))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : ι -> (Set.{u1} α)} (hs : IndexedPartition.{u2, u1} ι α s) (x : IndexedPartition.Quotient.{u2, u1} ι α s hs), Eq.{succ u2} ι (IndexedPartition.index.{u2, u1} ι α s hs (Quotient.out'.{succ u1} α (IndexedPartition.setoid.{u2, u1} ι α s hs) x)) (IndexedPartition.index.{u2, u1} ι α s hs (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs) α) (IndexedPartition.Quotient.{u2, u1} ι α s hs) (fun (_x : IndexedPartition.Quotient.{u2, u1} ι α s hs) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : IndexedPartition.Quotient.{u2, u1} ι α s hs) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs) α) (IndexedPartition.Quotient.{u2, u1} ι α s hs) α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs) α)) (IndexedPartition.out.{u2, u1} ι α s hs) x))
Case conversion may be inaccurate. Consider using '#align indexed_partition.index_out' IndexedPartition.index_out'ₓ'. -/
/-- The indices of `quotient.out'` and `indexed_partition.out` are equal. -/
theorem index_out' (x : hs.Quotient) : hs.index x.out' = hs.index (hs.out x) :=
  Quotient.inductionOn' x fun x => (Setoid.ker_apply_mk_out' x).trans (hs.index_some _).symm
#align indexed_partition.index_out' IndexedPartition.index_out'

/- warning: indexed_partition.proj_out -> IndexedPartition.proj_out is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : ι -> (Set.{u2} α)} (hs : IndexedPartition.{u1, u2} ι α s) (x : IndexedPartition.Quotient.{u1, u2} ι α s hs), Eq.{succ u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs) (IndexedPartition.proj.{u1, u2} ι α s hs (coeFn.{succ u2, succ u2} (Function.Embedding.{succ u2, succ u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs) α) (fun (_x : Function.Embedding.{succ u2, succ u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs) α) => (IndexedPartition.Quotient.{u1, u2} ι α s hs) -> α) (Function.Embedding.hasCoeToFun.{succ u2, succ u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs) α) (IndexedPartition.out.{u1, u2} ι α s hs) x)) x
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : ι -> (Set.{u1} α)} (hs : IndexedPartition.{u2, u1} ι α s) (x : IndexedPartition.Quotient.{u2, u1} ι α s hs), Eq.{succ u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs) (IndexedPartition.proj.{u2, u1} ι α s hs (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs) α) (IndexedPartition.Quotient.{u2, u1} ι α s hs) (fun (_x : IndexedPartition.Quotient.{u2, u1} ι α s hs) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : IndexedPartition.Quotient.{u2, u1} ι α s hs) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs) α) (IndexedPartition.Quotient.{u2, u1} ι α s hs) α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs) α)) (IndexedPartition.out.{u2, u1} ι α s hs) x)) x
Case conversion may be inaccurate. Consider using '#align indexed_partition.proj_out IndexedPartition.proj_outₓ'. -/
/-- This lemma is analogous to `quotient.out_eq'`. -/
@[simp]
theorem proj_out (x : hs.Quotient) : hs.proj (hs.out x) = x :=
  Quotient.inductionOn' x fun x => Quotient.sound' <| hs.some_index x
#align indexed_partition.proj_out IndexedPartition.proj_out

#print IndexedPartition.class_of /-
theorem class_of {x : α} : setOf (hs.Setoid.Rel x) = s (hs.index x) :=
  Set.ext fun y => eq_comm.trans hs.mem_iff_index_eq.symm
#align indexed_partition.class_of IndexedPartition.class_of
-/

/- warning: indexed_partition.proj_fiber -> IndexedPartition.proj_fiber is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : ι -> (Set.{u2} α)} (hs : IndexedPartition.{u1, u2} ι α s) (x : IndexedPartition.Quotient.{u1, u2} ι α s hs), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u2} α (IndexedPartition.Quotient.{u1, u2} ι α s hs) (IndexedPartition.proj.{u1, u2} ι α s hs) (Singleton.singleton.{u2, u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs) (Set.{u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs)) (Set.hasSingleton.{u2} (IndexedPartition.Quotient.{u1, u2} ι α s hs)) x)) (s (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} (IndexedPartition.Quotient.{u1, u2} ι α s hs) ι) (fun (_x : Equiv.{succ u2, succ u1} (IndexedPartition.Quotient.{u1, u2} ι α s hs) ι) => (IndexedPartition.Quotient.{u1, u2} ι α s hs) -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} (IndexedPartition.Quotient.{u1, u2} ι α s hs) ι) (Equiv.symm.{succ u1, succ u2} ι (IndexedPartition.Quotient.{u1, u2} ι α s hs) (IndexedPartition.equivQuotient.{u1, u2} ι α s hs)) x))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : ι -> (Set.{u1} α)} (hs : IndexedPartition.{u2, u1} ι α s) (x : IndexedPartition.Quotient.{u2, u1} ι α s hs), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α (IndexedPartition.Quotient.{u2, u1} ι α s hs) (IndexedPartition.proj.{u2, u1} ι α s hs) (Singleton.singleton.{u1, u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs) (Set.{u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs)) (Set.instSingletonSet.{u1} (IndexedPartition.Quotient.{u2, u1} ι α s hs)) x)) (s (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} (IndexedPartition.Quotient.{u2, u1} ι α s hs) ι) (IndexedPartition.Quotient.{u2, u1} ι α s hs) (fun (_x : IndexedPartition.Quotient.{u2, u1} ι α s hs) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : IndexedPartition.Quotient.{u2, u1} ι α s hs) => ι) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} (IndexedPartition.Quotient.{u2, u1} ι α s hs) ι) (Equiv.symm.{succ u2, succ u1} ι (IndexedPartition.Quotient.{u2, u1} ι α s hs) (IndexedPartition.equivQuotient.{u2, u1} ι α s hs)) x))
Case conversion may be inaccurate. Consider using '#align indexed_partition.proj_fiber IndexedPartition.proj_fiberₓ'. -/
theorem proj_fiber (x : hs.Quotient) : hs.proj ⁻¹' {x} = s (hs.equivQuotient.symm x) :=
  Quotient.inductionOn' x fun x => by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hs.mem_iff_index_eq]
    exact Quotient.eq''
#align indexed_partition.proj_fiber IndexedPartition.proj_fiber

end IndexedPartition

