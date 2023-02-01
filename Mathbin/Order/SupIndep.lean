/-
Copyright (c) 2021 Aaron Anderson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kevin Buzzard, Yaël Dillies, Eric Wieser

! This file was ported from Lean 3 source module order.sup_indep
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Pairwise
import Mathbin.Data.Finset.Powerset
import Mathbin.Data.Fintype.Basic

/-!
# Supremum independence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `finset.sup_indep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `complete_lattice.set_independent s`: a set of elements are supremum independent.
* `complete_lattice.independent f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `finset.sup_indep_iff_pairwise_disjoint`
  * `complete_lattice.set_independent_iff_pairwise_disjoint`
  * `complete_lattice.independent_iff_pairwise_disjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `finset.sup_indep.pairwise_disjoint`
  * `complete_lattice.set_independent.pairwise_disjoint`
  * `complete_lattice.independent.pairwise_disjoint`

## Implementation notes

For the finite version, we avoid the "obvious" definition
`∀ i ∈ s, disjoint (f i) ((s.erase i).sup f)` because `erase` would require decidable equality on
`ι`.
-/


variable {α β ι ι' : Type _}

/-! ### On lattices with a bottom element, via `finset.sup` -/


namespace Finset

section Lattice

variable [Lattice α] [OrderBot α]

#print Finset.SupIndep /-
/-- Supremum independence of finite sets. We avoid the "obvious" definition using `s.erase i`
because `erase` would require decidable equality on `ι`. -/
def SupIndep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → Disjoint (f i) (t.sup f)
#align finset.sup_indep Finset.SupIndep
-/

variable {s t : Finset ι} {f : ι → α} {i : ι}

instance [DecidableEq ι] [DecidableEq α] : Decidable (SupIndep s f) :=
  by
  apply @Finset.decidableForallOfDecidableSubsets _ _ _ _
  intro t ht
  apply @Finset.decidableDforallFinset _ _ _ _
  exact fun i hi => @Implies.decidable _ _ _ (decidable_of_iff' (_ = ⊥) disjoint_iff)

/- warning: finset.sup_indep.subset -> Finset.SupIndep.subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Lattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] {s : Finset.{u2} ι} {t : Finset.{u2} ι} {f : ι -> α}, (Finset.SupIndep.{u1, u2} α ι _inst_1 _inst_2 t f) -> (HasSubset.Subset.{u2} (Finset.{u2} ι) (Finset.hasSubset.{u2} ι) s t) -> (Finset.SupIndep.{u1, u2} α ι _inst_1 _inst_2 s f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Lattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α _inst_1))))] {s : Finset.{u1} ι} {t : Finset.{u1} ι} {f : ι -> α}, (Finset.SupIndep.{u2, u1} α ι _inst_1 _inst_2 t f) -> (HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.instHasSubsetFinset.{u1} ι) s t) -> (Finset.SupIndep.{u2, u1} α ι _inst_1 _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align finset.sup_indep.subset Finset.SupIndep.subsetₓ'. -/
theorem SupIndep.subset (ht : t.SupIndep f) (h : s ⊆ t) : s.SupIndep f := fun u hu i hi =>
  ht (hu.trans h) (h hi)
#align finset.sup_indep.subset Finset.SupIndep.subset

/- warning: finset.sup_indep_empty -> Finset.supIndep_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Lattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] (f : ι -> α), Finset.SupIndep.{u1, u2} α ι _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u2} (Finset.{u2} ι) (Finset.hasEmptyc.{u2} ι)) f
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Lattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α _inst_1))))] (f : ι -> α), Finset.SupIndep.{u2, u1} α ι _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.instEmptyCollectionFinset.{u1} ι)) f
Case conversion may be inaccurate. Consider using '#align finset.sup_indep_empty Finset.supIndep_emptyₓ'. -/
theorem supIndep_empty (f : ι → α) : (∅ : Finset ι).SupIndep f := fun _ _ a ha => ha.elim
#align finset.sup_indep_empty Finset.supIndep_empty

/- warning: finset.sup_indep_singleton -> Finset.supIndep_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Lattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] (i : ι) (f : ι -> α), Finset.SupIndep.{u1, u2} α ι _inst_1 _inst_2 (Singleton.singleton.{u2, u2} ι (Finset.{u2} ι) (Finset.hasSingleton.{u2} ι) i) f
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Lattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α _inst_1))))] (i : ι) (f : ι -> α), Finset.SupIndep.{u2, u1} α ι _inst_1 _inst_2 (Singleton.singleton.{u1, u1} ι (Finset.{u1} ι) (Finset.instSingletonFinset.{u1} ι) i) f
Case conversion may be inaccurate. Consider using '#align finset.sup_indep_singleton Finset.supIndep_singletonₓ'. -/
theorem supIndep_singleton (i : ι) (f : ι → α) : ({i} : Finset ι).SupIndep f := fun s hs j hji hj =>
  by
  rw [eq_empty_of_ssubset_singleton ⟨hs, fun h => hj (h hji)⟩, sup_empty]
  exact disjoint_bot_right
#align finset.sup_indep_singleton Finset.supIndep_singleton

/- warning: finset.sup_indep.pairwise_disjoint -> Finset.SupIndep.pairwiseDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Lattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] {s : Finset.{u2} ι} {f : ι -> α}, (Finset.SupIndep.{u1, u2} α ι _inst_1 _inst_2 s f) -> (Set.PairwiseDisjoint.{u1, u2} α ι (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) _inst_2 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s) f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Lattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α _inst_1))))] {s : Finset.{u1} ι} {f : ι -> α}, (Finset.SupIndep.{u2, u1} α ι _inst_1 _inst_2 s f) -> (Set.PairwiseDisjoint.{u2, u1} α ι (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α _inst_1)) _inst_2 (Finset.toSet.{u1} ι s) f)
Case conversion may be inaccurate. Consider using '#align finset.sup_indep.pairwise_disjoint Finset.SupIndep.pairwiseDisjointₓ'. -/
theorem SupIndep.pairwiseDisjoint (hs : s.SupIndep f) : (s : Set ι).PairwiseDisjoint f :=
  fun a ha b hb hab =>
  sup_singleton.subst <| hs (singleton_subset_iff.2 hb) ha <| not_mem_singleton.2 hab
#align finset.sup_indep.pairwise_disjoint Finset.SupIndep.pairwiseDisjoint

#print Finset.supIndep_iff_disjoint_erase /-
/-- The RHS looks like the definition of `complete_lattice.independent`. -/
theorem supIndep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ ∀ i ∈ s, Disjoint (f i) ((s.eraseₓ i).sup f) :=
  ⟨fun hs i hi => hs (erase_subset _ _) hi (not_mem_erase _ _), fun hs t ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun j hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩
#align finset.sup_indep_iff_disjoint_erase Finset.supIndep_iff_disjoint_erase
-/

#print Finset.supIndep_pair /-
@[simp]
theorem supIndep_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j) :=
  ⟨fun h => h.PairwiseDisjoint (by simp) (by simp) hij, fun h =>
    by
    rw [sup_indep_iff_disjoint_erase]
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    obtain rfl | rfl := hk
    · convert h using 1
      rw [Finset.erase_insert, Finset.sup_singleton]
      simpa using hij
    · convert h.symm using 1
      have : ({i, k} : Finset ι).eraseₓ k = {i} := by
        ext
        rw [mem_erase, mem_insert, mem_singleton, mem_singleton, and_or_left, Ne.def,
          not_and_self_iff, or_false_iff, and_iff_right_of_imp]
        rintro rfl
        exact hij
      rw [this, Finset.sup_singleton]⟩
#align finset.sup_indep_pair Finset.supIndep_pair
-/

#print Finset.supIndep_univ_bool /-
theorem supIndep_univ_bool (f : Bool → α) :
    (Finset.univ : Finset Bool).SupIndep f ↔ Disjoint (f false) (f true) :=
  haveI : tt ≠ ff := by simp only [Ne.def, not_false_iff]
  (sup_indep_pair this).trans disjoint_comm
#align finset.sup_indep_univ_bool Finset.supIndep_univ_bool
-/

/- warning: finset.sup_indep_univ_fin_two -> Finset.supIndep_univ_fin_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] (f : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α), Iff (Finset.SupIndep.{u1, 0} α (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) _inst_1 _inst_2 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) f) (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) _inst_2 (f (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))) (f (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (ZeroLEOneClass.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] (f : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α), Iff (Finset.SupIndep.{u1, 0} α (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) _inst_1 _inst_2 (Finset.univ.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) f) (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) _inst_2 (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (f (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align finset.sup_indep_univ_fin_two Finset.supIndep_univ_fin_twoₓ'. -/
@[simp]
theorem supIndep_univ_fin_two (f : Fin 2 → α) :
    (Finset.univ : Finset (Fin 2)).SupIndep f ↔ Disjoint (f 0) (f 1) :=
  haveI : (0 : Fin 2) ≠ 1 := by simp
  sup_indep_pair this
#align finset.sup_indep_univ_fin_two Finset.supIndep_univ_fin_two

/- warning: finset.sup_indep.attach -> Finset.SupIndep.attach is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Lattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] {s : Finset.{u2} ι} {f : ι -> α}, (Finset.SupIndep.{u1, u2} α ι _inst_1 _inst_2 s f) -> (Finset.SupIndep.{u1, u2} α (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) _inst_1 _inst_2 (Finset.attach.{u2} ι s) (Function.comp.{succ u2, succ u2, succ u1} (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι α f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Lattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α _inst_1))))] {s : Finset.{u1} ι} {f : ι -> α}, (Finset.SupIndep.{u2, u1} α ι _inst_1 _inst_2 s f) -> (Finset.SupIndep.{u2, u1} α (Subtype.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)) _inst_1 _inst_2 (Finset.attach.{u1} ι s) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)) ι α f (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s))))
Case conversion may be inaccurate. Consider using '#align finset.sup_indep.attach Finset.SupIndep.attachₓ'. -/
theorem SupIndep.attach (hs : s.SupIndep f) : s.attach.SupIndep (f ∘ Subtype.val) :=
  by
  intro t ht i _ hi
  classical
    rw [← Finset.sup_image]
    refine' hs (image_subset_iff.2 fun (j : { x // x ∈ s }) _ => j.2) i.2 fun hi' => hi _
    rw [mem_image] at hi'
    obtain ⟨j, hj, hji⟩ := hi'
    rwa [Subtype.ext hji] at hj
#align finset.sup_indep.attach Finset.SupIndep.attach

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] {s : Finset ι} {f : ι → α}

/- warning: finset.sup_indep_iff_pairwise_disjoint -> Finset.supIndep_iff_pairwiseDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α}, Iff (Finset.SupIndep.{u1, u2} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 s f) (Set.PairwiseDisjoint.{u1, u2} α ι (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s) f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : DistribLattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)))))] {s : Finset.{u1} ι} {f : ι -> α}, Iff (Finset.SupIndep.{u2, u1} α ι (DistribLattice.toLattice.{u2} α _inst_1) _inst_2 s f) (Set.PairwiseDisjoint.{u2, u1} α ι (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 (Finset.toSet.{u1} ι s) f)
Case conversion may be inaccurate. Consider using '#align finset.sup_indep_iff_pairwise_disjoint Finset.supIndep_iff_pairwiseDisjointₓ'. -/
theorem supIndep_iff_pairwiseDisjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f :=
  ⟨SupIndep.pairwiseDisjoint, fun hs t ht i hi hit =>
    disjoint_sup_right.2 fun j hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩
#align finset.sup_indep_iff_pairwise_disjoint Finset.supIndep_iff_pairwiseDisjoint

/- warning: finset.sup_indep.pairwise_disjoint -> Finset.SupIndep.pairwiseDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Lattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))] {s : Finset.{u2} ι} {f : ι -> α}, (Finset.SupIndep.{u1, u2} α ι _inst_1 _inst_2 s f) -> (Set.PairwiseDisjoint.{u1, u2} α ι (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) _inst_2 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s) f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Lattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α _inst_1))))] {s : Finset.{u1} ι} {f : ι -> α}, (Finset.SupIndep.{u2, u1} α ι _inst_1 _inst_2 s f) -> (Set.PairwiseDisjoint.{u2, u1} α ι (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α _inst_1)) _inst_2 (Finset.toSet.{u1} ι s) f)
Case conversion may be inaccurate. Consider using '#align finset.sup_indep.pairwise_disjoint Finset.SupIndep.pairwiseDisjointₓ'. -/
/- warning: set.pairwise_disjoint.sup_indep -> Set.PairwiseDisjoint.supIndep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s) f) -> (Finset.SupIndep.{u1, u2} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 s f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : DistribLattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)))))] {s : Finset.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 (Finset.toSet.{u1} ι s) f) -> (Finset.SupIndep.{u2, u1} α ι (DistribLattice.toLattice.{u2} α _inst_1) _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.sup_indep Set.PairwiseDisjoint.supIndepₓ'. -/
alias sup_indep_iff_pairwise_disjoint ↔
  sup_indep.pairwise_disjoint _root_.set.pairwise_disjoint.sup_indep
#align finset.sup_indep.pairwise_disjoint Finset.SupIndep.pairwiseDisjoint
#align set.pairwise_disjoint.sup_indep Set.PairwiseDisjoint.supIndep

/- warning: finset.sup_indep.sup -> Finset.SupIndep.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DecidableEq.{succ u2} ι] {s : Finset.{u3} ι'} {g : ι' -> (Finset.{u2} ι)} {f : ι -> α}, (Finset.SupIndep.{u1, u3} α ι' (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 s (fun (i : ι') => Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 (g i) f)) -> (forall (i' : ι'), (Membership.Mem.{u3, u3} ι' (Finset.{u3} ι') (Finset.hasMem.{u3} ι') i' s) -> (Finset.SupIndep.{u1, u2} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 (g i') f)) -> (Finset.SupIndep.{u1, u2} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 (Finset.sup.{u2, u3} (Finset.{u2} ι) ι' (Lattice.toSemilatticeSup.{u2} (Finset.{u2} ι) (Finset.lattice.{u2} ι (fun (a : ι) (b : ι) => _inst_3 a b))) (Finset.orderBot.{u2} ι) s g) f)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DecidableEq.{succ u3} ι] {s : Finset.{u2} ι'} {g : ι' -> (Finset.{u3} ι)} {f : ι -> α}, (Finset.SupIndep.{u1, u2} α ι' (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 s (fun (i : ι') => Finset.sup.{u1, u3} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 (g i) f)) -> (forall (i' : ι'), (Membership.mem.{u2, u2} ι' (Finset.{u2} ι') (Finset.instMembershipFinset.{u2} ι') i' s) -> (Finset.SupIndep.{u1, u3} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 (g i') f)) -> (Finset.SupIndep.{u1, u3} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 (Finset.sup.{u3, u2} (Finset.{u3} ι) ι' (Lattice.toSemilatticeSup.{u3} (Finset.{u3} ι) (Finset.instLatticeFinset.{u3} ι (fun (a : ι) (b : ι) => _inst_3 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u3} ι) s g) f)
Case conversion may be inaccurate. Consider using '#align finset.sup_indep.sup Finset.SupIndep.supₓ'. -/
/-- Bind operation for `sup_indep`. -/
theorem SupIndep.sup [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.sup g).SupIndep f :=
  by
  simp_rw [sup_indep_iff_pairwise_disjoint] at hs hg⊢
  rw [sup_eq_bUnion, coe_bUnion]
  exact hs.bUnion_finset hg
#align finset.sup_indep.sup Finset.SupIndep.sup

/- warning: finset.sup_indep.bUnion -> Finset.SupIndep.bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DecidableEq.{succ u2} ι] {s : Finset.{u3} ι'} {g : ι' -> (Finset.{u2} ι)} {f : ι -> α}, (Finset.SupIndep.{u1, u3} α ι' (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 s (fun (i : ι') => Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 (g i) f)) -> (forall (i' : ι'), (Membership.Mem.{u3, u3} ι' (Finset.{u3} ι') (Finset.hasMem.{u3} ι') i' s) -> (Finset.SupIndep.{u1, u2} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 (g i') f)) -> (Finset.SupIndep.{u1, u2} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 (Finset.bunionᵢ.{u3, u2} ι' ι (fun (a : ι) (b : ι) => _inst_3 a b) s g) f)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DecidableEq.{succ u3} ι] {s : Finset.{u2} ι'} {g : ι' -> (Finset.{u3} ι)} {f : ι -> α}, (Finset.SupIndep.{u1, u2} α ι' (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 s (fun (i : ι') => Finset.sup.{u1, u3} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 (g i) f)) -> (forall (i' : ι'), (Membership.mem.{u2, u2} ι' (Finset.{u2} ι') (Finset.instMembershipFinset.{u2} ι') i' s) -> (Finset.SupIndep.{u1, u3} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 (g i') f)) -> (Finset.SupIndep.{u1, u3} α ι (DistribLattice.toLattice.{u1} α _inst_1) _inst_2 (Finset.bunionᵢ.{u2, u3} ι' ι (fun (a : ι) (b : ι) => _inst_3 a b) s g) f)
Case conversion may be inaccurate. Consider using '#align finset.sup_indep.bUnion Finset.SupIndep.bunionᵢₓ'. -/
/-- Bind operation for `sup_indep`. -/
theorem SupIndep.bunionᵢ [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀ i' ∈ s, (g i').SupIndep f) :
    (s.bunionᵢ g).SupIndep f := by
  rw [← sup_eq_bUnion]
  exact hs.sup hg
#align finset.sup_indep.bUnion Finset.SupIndep.bunionᵢ

end DistribLattice

end Finset

/-! ### On complete lattices via `has_Sup.Sup` -/


namespace CompleteLattice

variable [CompleteLattice α]

open Set Function

#print CompleteLattice.SetIndependent /-
/-- An independent set of elements in a complete lattice is one in which every element is disjoint
  from the `Sup` of the rest. -/
def SetIndependent (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint a (supₛ (s \ {a}))
#align complete_lattice.set_independent CompleteLattice.SetIndependent
-/

variable {s : Set α} (hs : SetIndependent s)

#print CompleteLattice.setIndependent_empty /-
@[simp]
theorem setIndependent_empty : SetIndependent (∅ : Set α) := fun x hx =>
  (Set.not_mem_empty x hx).elim
#align complete_lattice.set_independent_empty CompleteLattice.setIndependent_empty
-/

#print CompleteLattice.SetIndependent.mono /-
theorem SetIndependent.mono {t : Set α} (hst : t ⊆ s) : SetIndependent t := fun a ha =>
  (hs (hst ha)).mono_right (supₛ_le_supₛ (diff_subset_diff_left hst))
#align complete_lattice.set_independent.mono CompleteLattice.SetIndependent.mono
-/

#print CompleteLattice.SetIndependent.pairwiseDisjoint /-
/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem SetIndependent.pairwiseDisjoint : s.PairwiseDisjoint id := fun x hx y hy h =>
  disjoint_supₛ_right (hs hx) ((mem_diff y).mpr ⟨hy, h.symm⟩)
#align complete_lattice.set_independent.pairwise_disjoint CompleteLattice.SetIndependent.pairwiseDisjoint
-/

#print CompleteLattice.setIndependent_pair /-
theorem setIndependent_pair {a b : α} (hab : a ≠ b) :
    SetIndependent ({a, b} : Set α) ↔ Disjoint a b :=
  by
  constructor
  · intro h
    exact h.pairwise_disjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert h using 1
      simp [hab, supₛ_singleton]
    · convert h.symm using 1
      simp [hab, supₛ_singleton]
#align complete_lattice.set_independent_pair CompleteLattice.setIndependent_pair
-/

include hs

/- warning: complete_lattice.set_independent.disjoint_Sup -> CompleteLattice.SetIndependent.disjoint_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (CompleteLattice.SetIndependent.{u1} α _inst_1 s) -> (forall {x : α} {y : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) y s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x y)) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) x (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (CompleteLattice.SetIndependent.{u1} α _inst_1 s) -> (forall {x : α} {y : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) y s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x y)) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) x (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) y)))
Case conversion may be inaccurate. Consider using '#align complete_lattice.set_independent.disjoint_Sup CompleteLattice.SetIndependent.disjoint_supₛₓ'. -/
/-- If the elements of a set are independent, then any element is disjoint from the `Sup` of some
subset of the rest. -/
theorem SetIndependent.disjoint_supₛ {x : α} {y : Set α} (hx : x ∈ s) (hy : y ⊆ s) (hxy : x ∉ y) :
    Disjoint x (supₛ y) :=
  by
  have := (hs.mono <| insert_subset.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_diff_of_mem _ (mem_singleton _), diff_singleton_eq_self hxy] at this
  exact this
#align complete_lattice.set_independent.disjoint_Sup CompleteLattice.SetIndependent.disjoint_supₛ

omit hs

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (j «expr ≠ » i) -/
#print CompleteLattice.Independent /-
/-- An independent indexed family of elements in a complete lattice is one in which every element
  is disjoint from the `supr` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this sense if
  and only the natural map from the direct sum of the submodules to the module is injective. -/
def Independent {ι : Sort _} {α : Type _} [CompleteLattice α] (t : ι → α) : Prop :=
  ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j)
#align complete_lattice.independent CompleteLattice.Independent
-/

#print CompleteLattice.setIndependent_iff /-
theorem setIndependent_iff {α : Type _} [CompleteLattice α] (s : Set α) :
    SetIndependent s ↔ Independent (coe : s → α) :=
  by
  simp_rw [independent, set_independent, SetCoe.forall, supₛ_eq_supᵢ]
  refine' forall₂_congr fun a ha => _
  congr 2
  convert supr_subtype.symm
  simp [supᵢ_and]
#align complete_lattice.set_independent_iff CompleteLattice.setIndependent_iff
-/

variable {t : ι → α} (ht : Independent t)

/- warning: complete_lattice.independent_def -> CompleteLattice.independent_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {t : ι -> α}, Iff (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (t i) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (j : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Ne.{succ u2} ι j i) (fun (H : Ne.{succ u2} ι j i) => t j))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {t : ι -> α}, Iff (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (t i) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (j : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Ne.{succ u2} ι j i) (fun (H : Ne.{succ u2} ι j i) => t j))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_def CompleteLattice.independent_defₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (j «expr ≠ » i) -/
theorem independent_def : Independent t ↔ ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j) :=
  Iff.rfl
#align complete_lattice.independent_def CompleteLattice.independent_def

/- warning: complete_lattice.independent_def' -> CompleteLattice.independent_def' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {t : ι -> α}, Iff (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (t i) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Set.image.{u2, u1} ι α t (setOf.{u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {t : ι -> α}, Iff (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (t i) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.image.{u2, u1} ι α t (setOf.{u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_def' CompleteLattice.independent_def'ₓ'. -/
theorem independent_def' : Independent t ↔ ∀ i, Disjoint (t i) (supₛ (t '' { j | j ≠ i })) :=
  by
  simp_rw [supₛ_image]
  rfl
#align complete_lattice.independent_def' CompleteLattice.independent_def'

/- warning: complete_lattice.independent_def'' -> CompleteLattice.independent_def'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {t : ι -> α}, Iff (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (t i) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => Exists.{succ u2} ι (fun (j : ι) => Exists.{0} (Ne.{succ u2} ι j i) (fun (H : Ne.{succ u2} ι j i) => Eq.{succ u1} α (t j) a))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {t : ι -> α}, Iff (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (t i) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (setOf.{u1} α (fun (a : α) => Exists.{succ u2} ι (fun (j : ι) => Exists.{0} (Ne.{succ u2} ι j i) (fun (H : Ne.{succ u2} ι j i) => Eq.{succ u1} α (t j) a))))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_def'' CompleteLattice.independent_def''ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (j «expr ≠ » i) -/
theorem independent_def'' :
    Independent t ↔ ∀ i, Disjoint (t i) (supₛ { a | ∃ (j : _)(_ : j ≠ i), t j = a }) :=
  by
  rw [independent_def']
  tidy
#align complete_lattice.independent_def'' CompleteLattice.independent_def''

#print CompleteLattice.independent_empty /-
@[simp]
theorem independent_empty (t : Empty → α) : Independent t :=
  fun.
#align complete_lattice.independent_empty CompleteLattice.independent_empty
-/

#print CompleteLattice.independent_pempty /-
@[simp]
theorem independent_pempty (t : PEmpty → α) : Independent t :=
  fun.
#align complete_lattice.independent_pempty CompleteLattice.independent_pempty
-/

#print CompleteLattice.Independent.pairwiseDisjoint /-
/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem Independent.pairwiseDisjoint : Pairwise (Disjoint on t) := fun x y h =>
  disjoint_supₛ_right (ht x) ⟨y, supᵢ_pos h.symm⟩
#align complete_lattice.independent.pairwise_disjoint CompleteLattice.Independent.pairwiseDisjoint
-/

#print CompleteLattice.Independent.mono /-
theorem Independent.mono {s t : ι → α} (hs : Independent s) (hst : t ≤ s) : Independent t :=
  fun i => (hs i).mono (hst i) <| supᵢ₂_mono fun j _ => hst j
#align complete_lattice.independent.mono CompleteLattice.Independent.mono
-/

/- warning: complete_lattice.independent.comp -> CompleteLattice.Independent.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Sort.{u2}} {ι' : Sort.{u3}} {t : ι -> α} {f : ι' -> ι}, (CompleteLattice.Independent.{u2, u1} ι α _inst_1 t) -> (Function.Injective.{u3, u2} ι' ι f) -> (CompleteLattice.Independent.{u3, u1} ι' α _inst_1 (Function.comp.{u3, u2, succ u1} ι' ι α t f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Sort.{u3}} {ι' : Sort.{u2}} {t : ι -> α} {f : ι' -> ι}, (CompleteLattice.Independent.{u3, u1} ι α _inst_1 t) -> (Function.Injective.{u2, u3} ι' ι f) -> (CompleteLattice.Independent.{u2, u1} ι' α _inst_1 (Function.comp.{u2, u3, succ u1} ι' ι α t f))
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.comp CompleteLattice.Independent.compₓ'. -/
/-- Composing an independent indexed family with an injective function on the index results in
another indepedendent indexed family. -/
theorem Independent.comp {ι ι' : Sort _} {t : ι → α} {f : ι' → ι} (ht : Independent t)
    (hf : Injective f) : Independent (t ∘ f) := fun i =>
  (ht (f i)).mono_right <|
    by
    refine' (supᵢ_mono fun i => _).trans (supᵢ_comp_le _ f)
    exact supᵢ_const_mono hf.ne
#align complete_lattice.independent.comp CompleteLattice.Independent.comp

/- warning: complete_lattice.independent.comp' -> CompleteLattice.Independent.comp' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Sort.{u2}} {ι' : Sort.{u3}} {t : ι -> α} {f : ι' -> ι}, (CompleteLattice.Independent.{u3, u1} ι' α _inst_1 (Function.comp.{u3, u2, succ u1} ι' ι α t f)) -> (Function.Surjective.{u3, u2} ι' ι f) -> (CompleteLattice.Independent.{u2, u1} ι α _inst_1 t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Sort.{u3}} {ι' : Sort.{u2}} {t : ι -> α} {f : ι' -> ι}, (CompleteLattice.Independent.{u2, u1} ι' α _inst_1 (Function.comp.{u2, u3, succ u1} ι' ι α t f)) -> (Function.Surjective.{u2, u3} ι' ι f) -> (CompleteLattice.Independent.{u3, u1} ι α _inst_1 t)
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.comp' CompleteLattice.Independent.comp'ₓ'. -/
theorem Independent.comp' {ι ι' : Sort _} {t : ι → α} {f : ι' → ι} (ht : Independent <| t ∘ f)
    (hf : Surjective f) : Independent t := by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.supr_comp]
  exact (ht i').mono_right (bsupᵢ_mono fun j' hij => mt (congr_arg f) hij)
#align complete_lattice.independent.comp' CompleteLattice.Independent.comp'

#print CompleteLattice.Independent.setIndependent_range /-
theorem Independent.setIndependent_range (ht : Independent t) : SetIndependent <| range t :=
  by
  rw [set_independent_iff]
  rw [← coe_comp_range_factorization t] at ht
  exact ht.comp' surjective_onto_range
#align complete_lattice.independent.set_independent_range CompleteLattice.Independent.setIndependent_range
-/

/- warning: complete_lattice.independent.injective -> CompleteLattice.Independent.injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {t : ι -> α}, (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) -> (forall (i : ι), Ne.{succ u1} α (t i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) -> (Function.Injective.{succ u2, succ u1} ι α t)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {t : ι -> α}, (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) -> (forall (i : ι), Ne.{succ u1} α (t i) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))) -> (Function.Injective.{succ u2, succ u1} ι α t)
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.injective CompleteLattice.Independent.injectiveₓ'. -/
theorem Independent.injective (ht : Independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Injective t :=
  by
  intro i j h
  by_contra' contra
  apply h_ne_bot j
  suffices t j ≤ ⨆ (k) (hk : k ≠ i), t k
    by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j ≠ i
  · exact Ne.symm contra
  exact le_supᵢ₂ j contra
#align complete_lattice.independent.injective CompleteLattice.Independent.injective

#print CompleteLattice.independent_pair /-
theorem independent_pair {i j : ι} (hij : i ≠ j) (huniv : ∀ k, k = i ∨ k = j) :
    Independent t ↔ Disjoint (t i) (t j) := by
  constructor
  · exact fun h => h.PairwiseDisjoint hij
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine' h.mono_right (supᵢ_le fun i => supᵢ_le fun hi => Eq.le _)
      rw [(huniv i).resolve_left hi]
    · refine' h.symm.mono_right (supᵢ_le fun j => supᵢ_le fun hj => Eq.le _)
      rw [(huniv j).resolve_right hj]
#align complete_lattice.independent_pair CompleteLattice.independent_pair
-/

/- warning: complete_lattice.independent.map_order_iso -> CompleteLattice.Independent.map_orderIso is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : CompleteLattice.{u2} α] [_inst_3 : CompleteLattice.{u3} β] (f : OrderIso.{u2, u3} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_3))))) {a : ι -> α}, (CompleteLattice.Independent.{u1, u2} ι α _inst_2 a) -> (CompleteLattice.Independent.{u1, u3} ι β _inst_3 (Function.comp.{u1, succ u2, succ u3} ι α β (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (OrderIso.{u2, u3} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_3))))) (fun (_x : RelIso.{u2, u3} α β (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2))))) (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_3)))))) => α -> β) (RelIso.hasCoeToFun.{u2, u3} α β (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2))))) (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_3)))))) f) a))
but is expected to have type
  forall {ι : Sort.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CompleteLattice.{u2} α] [_inst_3 : CompleteLattice.{u1} β] (f : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_3))))) {a : ι -> α}, (CompleteLattice.Independent.{u3, u2} ι α _inst_2 a) -> (CompleteLattice.Independent.{u3, u1} ι β _inst_3 (Function.comp.{u3, succ u2, succ u1} ι α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_3)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_3)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f))) a))
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.map_order_iso CompleteLattice.Independent.map_orderIsoₓ'. -/
/-- Composing an indepedent indexed family with an order isomorphism on the elements results in
another indepedendent indexed family. -/
theorem Independent.map_orderIso {ι : Sort _} {α β : Type _} [CompleteLattice α] [CompleteLattice β]
    (f : α ≃o β) {a : ι → α} (ha : Independent a) : Independent (f ∘ a) := fun i =>
  ((ha i).map_orderIso f).mono_right (f.Monotone.le_map_supᵢ₂ _)
#align complete_lattice.independent.map_order_iso CompleteLattice.Independent.map_orderIso

/- warning: complete_lattice.independent_map_order_iso_iff -> CompleteLattice.independent_map_orderIso_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : CompleteLattice.{u2} α] [_inst_3 : CompleteLattice.{u3} β] (f : OrderIso.{u2, u3} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_3))))) {a : ι -> α}, Iff (CompleteLattice.Independent.{u1, u3} ι β _inst_3 (Function.comp.{u1, succ u2, succ u3} ι α β (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (OrderIso.{u2, u3} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_3))))) (fun (_x : RelIso.{u2, u3} α β (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2))))) (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_3)))))) => α -> β) (RelIso.hasCoeToFun.{u2, u3} α β (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2))))) (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_3)))))) f) a)) (CompleteLattice.Independent.{u1, u2} ι α _inst_2 a)
but is expected to have type
  forall {ι : Sort.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CompleteLattice.{u2} α] [_inst_3 : CompleteLattice.{u1} β] (f : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_3))))) {a : ι -> α}, Iff (CompleteLattice.Independent.{u3, u1} ι β _inst_3 (Function.comp.{u3, succ u2, succ u1} ι α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_3)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_3)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f))) a)) (CompleteLattice.Independent.{u3, u2} ι α _inst_2 a)
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_map_order_iso_iff CompleteLattice.independent_map_orderIso_iffₓ'. -/
@[simp]
theorem independent_map_orderIso_iff {ι : Sort _} {α β : Type _} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι → α} : Independent (f ∘ a) ↔ Independent a :=
  ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_orderIso f.symm,
    fun h => h.map_orderIso f⟩
#align complete_lattice.independent_map_order_iso_iff CompleteLattice.independent_map_orderIso_iff

/- warning: complete_lattice.independent.disjoint_bsupr -> CompleteLattice.Independent.disjoint_bsupᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : CompleteLattice.{u2} α] {t : ι -> α}, (CompleteLattice.Independent.{succ u1, u2} ι α _inst_2 t) -> (forall {x : ι} {y : Set.{u1} ι}, (Not (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) x y)) -> (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_2)))) (CompleteLattice.toBoundedOrder.{u2} α _inst_2)) (t x) (supᵢ.{u2, succ u1} α (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_2)) ι (fun (i : ι) => supᵢ.{u2, 0} α (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_2)) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i y) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i y) => t i)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_2 : CompleteLattice.{u1} α] {t : ι -> α}, (CompleteLattice.Independent.{succ u2, u1} ι α _inst_2 t) -> (forall {x : ι} {y : Set.{u2} ι}, (Not (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x y)) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_2)) (t x) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_2) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_2) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i y) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i y) => t i)))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.disjoint_bsupr CompleteLattice.Independent.disjoint_bsupᵢₓ'. -/
/-- If the elements of a set are independent, then any element is disjoint from the `supr` of some
subset of the rest. -/
theorem Independent.disjoint_bsupᵢ {ι : Type _} {α : Type _} [CompleteLattice α] {t : ι → α}
    (ht : Independent t) {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ i ∈ y, t i) :=
  Disjoint.mono_right (bsupᵢ_mono fun i hi => (ne_of_mem_of_not_mem hi hx : _)) (ht x)
#align complete_lattice.independent.disjoint_bsupr CompleteLattice.Independent.disjoint_bsupᵢ

end CompleteLattice

/- warning: complete_lattice.independent_iff_sup_indep -> CompleteLattice.independent_iff_supIndep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Finset.{u2} ι} {f : ι -> α}, Iff (CompleteLattice.Independent.{succ u2, u1} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) α _inst_1 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)))))))) (Finset.SupIndep.{u1, u2} α ι (CompleteLattice.toLattice.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : Finset.{u1} ι} {f : ι -> α}, Iff (CompleteLattice.Independent.{succ u1, u2} (Subtype.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)) α _inst_1 (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)) ι α f (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)))) (Finset.SupIndep.{u2, u1} α ι (CompleteLattice.toLattice.{u2} α _inst_1) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) s f)
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_iff_sup_indep CompleteLattice.independent_iff_supIndepₓ'. -/
theorem CompleteLattice.independent_iff_supIndep [CompleteLattice α] {s : Finset ι} {f : ι → α} :
    CompleteLattice.Independent (f ∘ (coe : s → ι)) ↔ s.SupIndep f := by
  classical
    rw [Finset.supIndep_iff_disjoint_erase]
    refine' subtype.forall.trans (forall₂_congr fun a b => _)
    rw [Finset.sup_eq_supᵢ]
    congr 2
    refine' supr_subtype.trans _
    congr 1 with x
    simp [supᵢ_and, @supᵢ_comm _ (x ∈ s)]
#align complete_lattice.independent_iff_sup_indep CompleteLattice.independent_iff_supIndep

/- warning: complete_lattice.independent.sup_indep -> CompleteLattice.Independent.supIndep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Finset.{u2} ι} {f : ι -> α}, (CompleteLattice.Independent.{succ u2, u1} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) α _inst_1 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)))))))) -> (Finset.SupIndep.{u1, u2} α ι (CompleteLattice.toLattice.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : Finset.{u1} ι} {f : ι -> α}, (CompleteLattice.Independent.{succ u1, u2} (Subtype.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)) α _inst_1 (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)) ι α f (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)))) -> (Finset.SupIndep.{u2, u1} α ι (CompleteLattice.toLattice.{u2} α _inst_1) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) s f)
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.sup_indep CompleteLattice.Independent.supIndepₓ'. -/
/- warning: finset.sup_indep.independent -> Finset.SupIndep.independent is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Finset.{u2} ι} {f : ι -> α}, (Finset.SupIndep.{u1, u2} α ι (CompleteLattice.toLattice.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s f) -> (CompleteLattice.Independent.{succ u2, u1} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) α _inst_1 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} ι) Type.{u2} (Finset.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s))))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : Finset.{u1} ι} {f : ι -> α}, (Finset.SupIndep.{u2, u1} α ι (CompleteLattice.toLattice.{u2} α _inst_1) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) s f) -> (CompleteLattice.Independent.{succ u1, u2} (Subtype.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)) α _inst_1 (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s)) ι α f (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s))))
Case conversion may be inaccurate. Consider using '#align finset.sup_indep.independent Finset.SupIndep.independentₓ'. -/
alias CompleteLattice.independent_iff_supIndep ↔
  CompleteLattice.Independent.supIndep Finset.SupIndep.independent
#align complete_lattice.independent.sup_indep CompleteLattice.Independent.supIndep
#align finset.sup_indep.independent Finset.SupIndep.independent

/- warning: complete_lattice.independent_iff_sup_indep_univ -> CompleteLattice.independent_iff_supIndep_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Fintype.{u2} ι] {f : ι -> α}, Iff (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 f) (Finset.SupIndep.{u1, u2} α ι (CompleteLattice.toLattice.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (Finset.univ.{u2} ι _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : Fintype.{u1} ι] {f : ι -> α}, Iff (CompleteLattice.Independent.{succ u1, u2} ι α _inst_1 f) (Finset.SupIndep.{u2, u1} α ι (CompleteLattice.toLattice.{u2} α _inst_1) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) (Finset.univ.{u1} ι _inst_2) f)
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent_iff_sup_indep_univ CompleteLattice.independent_iff_supIndep_univₓ'. -/
/-- A variant of `complete_lattice.independent_iff_sup_indep` for `fintype`s. -/
theorem CompleteLattice.independent_iff_supIndep_univ [CompleteLattice α] [Fintype ι] {f : ι → α} :
    CompleteLattice.Independent f ↔ Finset.univ.SupIndep f := by
  classical simp [Finset.supIndep_iff_disjoint_erase, CompleteLattice.Independent,
      Finset.sup_eq_supᵢ]
#align complete_lattice.independent_iff_sup_indep_univ CompleteLattice.independent_iff_supIndep_univ

/- warning: complete_lattice.independent.sup_indep_univ -> CompleteLattice.Independent.sup_indep_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Fintype.{u2} ι] {f : ι -> α}, (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 f) -> (Finset.SupIndep.{u1, u2} α ι (CompleteLattice.toLattice.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (Finset.univ.{u2} ι _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : Fintype.{u1} ι] {f : ι -> α}, (CompleteLattice.Independent.{succ u1, u2} ι α _inst_1 f) -> (Finset.SupIndep.{u2, u1} α ι (CompleteLattice.toLattice.{u2} α _inst_1) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) (Finset.univ.{u1} ι _inst_2) f)
Case conversion may be inaccurate. Consider using '#align complete_lattice.independent.sup_indep_univ CompleteLattice.Independent.sup_indep_univₓ'. -/
/- warning: finset.sup_indep.independent_of_univ -> Finset.SupIndep.independent_of_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Fintype.{u2} ι] {f : ι -> α}, (Finset.SupIndep.{u1, u2} α ι (CompleteLattice.toLattice.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (Finset.univ.{u2} ι _inst_2) f) -> (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : Fintype.{u1} ι] {f : ι -> α}, (Finset.SupIndep.{u2, u1} α ι (CompleteLattice.toLattice.{u2} α _inst_1) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) (Finset.univ.{u1} ι _inst_2) f) -> (CompleteLattice.Independent.{succ u1, u2} ι α _inst_1 f)
Case conversion may be inaccurate. Consider using '#align finset.sup_indep.independent_of_univ Finset.SupIndep.independent_of_univₓ'. -/
alias CompleteLattice.independent_iff_supIndep_univ ↔
  CompleteLattice.Independent.sup_indep_univ Finset.SupIndep.independent_of_univ
#align complete_lattice.independent.sup_indep_univ CompleteLattice.Independent.sup_indep_univ
#align finset.sup_indep.independent_of_univ Finset.SupIndep.independent_of_univ

section Frame

namespace CompleteLattice

variable [Order.Frame α]

#print CompleteLattice.setIndependent_iff_pairwiseDisjoint /-
theorem setIndependent_iff_pairwiseDisjoint {s : Set α} :
    SetIndependent s ↔ s.PairwiseDisjoint id :=
  ⟨SetIndependent.pairwiseDisjoint, fun hs i hi =>
    disjoint_supₛ_iff.2 fun j hj => hs hi hj.1 <| Ne.symm hj.2⟩
#align complete_lattice.set_independent_iff_pairwise_disjoint CompleteLattice.setIndependent_iff_pairwiseDisjoint
-/

alias set_independent_iff_pairwise_disjoint ↔ _ _root_.set.pairwise_disjoint.set_independent
#align set.pairwise_disjoint.set_independent Set.PairwiseDisjoint.setIndependent

#print CompleteLattice.independent_iff_pairwiseDisjoint /-
theorem independent_iff_pairwiseDisjoint {f : ι → α} : Independent f ↔ Pairwise (Disjoint on f) :=
  ⟨Independent.pairwiseDisjoint, fun hs i =>
    disjoint_supᵢ_iff.2 fun j => disjoint_supᵢ_iff.2 fun hij => hs hij.symm⟩
#align complete_lattice.independent_iff_pairwise_disjoint CompleteLattice.independent_iff_pairwiseDisjoint
-/

end CompleteLattice

end Frame

