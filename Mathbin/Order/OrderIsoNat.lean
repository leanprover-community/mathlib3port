/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module order.order_iso_nat
! leanprover-community/mathlib commit 210657c4ea4a4a7b234392f70a3a2a83346dfa90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Lattice
import Mathbin.Logic.Denumerable
import Mathbin.Logic.Function.Iterate
import Mathbin.Order.Hom.Basic
import Mathbin.Tactic.Congrm

/-!
# Relation embeddings from the naturals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `nat_lt`/`nat_gt`: Make an order embedding `ℕ ↪ α` from an increasing/decreasing function `ℕ → α`.
* `monotonic_sequence_limit`: The limit of an eventually-constant monotone sequence `ℕ →o α`.
* `monotonic_sequence_limit_index`: The index of the first occurence of `monotonic_sequence_limit`
  in the sequence.
-/


variable {α : Type _}

namespace RelEmbedding

variable {r : α → α → Prop} [IsStrictOrder α r]

#print RelEmbedding.natLt /-
/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def natLt (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n + 1))) : ((· < ·) : ℕ → ℕ → Prop) ↪r r :=
  ofMonotone f <| Nat.rel_of_forall_rel_succ_of_lt r H
#align rel_embedding.nat_lt RelEmbedding.natLt
-/

/- warning: rel_embedding.coe_nat_lt -> RelEmbedding.coe_natLt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {f : Nat -> α} {H : forall (n : Nat), r (f n) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))}, Eq.{succ u1} (Nat -> α) (coeFn.{succ u1, succ u1} (RelEmbedding.{0, u1} Nat α (LT.lt.{0} Nat Nat.hasLt) r) (fun (_x : RelEmbedding.{0, u1} Nat α (LT.lt.{0} Nat Nat.hasLt) r) => Nat -> α) (RelEmbedding.hasCoeToFun.{0, u1} Nat α (LT.lt.{0} Nat Nat.hasLt) r) (RelEmbedding.natLt.{u1} α r _inst_1 f H)) f
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {f : Nat -> α} {H : forall (n : Nat), r (f n) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))}, Eq.{succ u1} (forall (ᾰ : Nat), (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => α) ᾰ) (FunLike.coe.{succ u1, 1, succ u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.75 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.77 : Nat) => LT.lt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.75 x._@.Mathlib.Order.OrderIsoNat._hyg.77) r) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => α) _x) (RelHomClass.toFunLike.{u1, 0, u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.75 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.77 : Nat) => LT.lt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.75 x._@.Mathlib.Order.OrderIsoNat._hyg.77) r) Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.75 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.77 : Nat) => LT.lt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.75 x._@.Mathlib.Order.OrderIsoNat._hyg.77) r (RelEmbedding.instRelHomClassRelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.75 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.77 : Nat) => LT.lt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.75 x._@.Mathlib.Order.OrderIsoNat._hyg.77) r)) (RelEmbedding.natLt.{u1} α r _inst_1 f H)) f
Case conversion may be inaccurate. Consider using '#align rel_embedding.coe_nat_lt RelEmbedding.coe_natLtₓ'. -/
@[simp]
theorem coe_natLt {f : ℕ → α} {H : ∀ n : ℕ, r (f n) (f (n + 1))} : ⇑(natLt f H) = f :=
  rfl
#align rel_embedding.coe_nat_lt RelEmbedding.coe_natLt

#print RelEmbedding.natGt /-
/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def natGt (f : ℕ → α) (H : ∀ n : ℕ, r (f (n + 1)) (f n)) : ((· > ·) : ℕ → ℕ → Prop) ↪r r :=
  haveI := IsStrictOrder.swap r
  RelEmbedding.swap (nat_lt f H)
#align rel_embedding.nat_gt RelEmbedding.natGt
-/

/- warning: rel_embedding.coe_nat_gt -> RelEmbedding.coe_natGt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {f : Nat -> α} {H : forall (n : Nat), r (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (f n)}, Eq.{succ u1} (Nat -> α) (coeFn.{succ u1, succ u1} (RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) (fun (_x : RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) => Nat -> α) (RelEmbedding.hasCoeToFun.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) (RelEmbedding.natGt.{u1} α r _inst_1 f H)) f
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {f : Nat -> α} {H : forall (n : Nat), r (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f n)}, Eq.{succ u1} (forall (ᾰ : Nat), (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => α) ᾰ) (FunLike.coe.{succ u1, 1, succ u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.202 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.204 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.202 x._@.Mathlib.Order.OrderIsoNat._hyg.204) r) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => α) _x) (RelHomClass.toFunLike.{u1, 0, u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.202 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.204 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.202 x._@.Mathlib.Order.OrderIsoNat._hyg.204) r) Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.202 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.204 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.202 x._@.Mathlib.Order.OrderIsoNat._hyg.204) r (RelEmbedding.instRelHomClassRelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.202 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.204 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.202 x._@.Mathlib.Order.OrderIsoNat._hyg.204) r)) (RelEmbedding.natGt.{u1} α r _inst_1 f H)) f
Case conversion may be inaccurate. Consider using '#align rel_embedding.coe_nat_gt RelEmbedding.coe_natGtₓ'. -/
@[simp]
theorem coe_natGt {f : ℕ → α} {H : ∀ n : ℕ, r (f (n + 1)) (f n)} : ⇑(natGt f H) = f :=
  rfl
#align rel_embedding.coe_nat_gt RelEmbedding.coe_natGt

#print RelEmbedding.exists_not_acc_lt_of_not_acc /-
theorem exists_not_acc_lt_of_not_acc {a : α} {r} (h : ¬Acc r a) : ∃ b, ¬Acc r b ∧ r b a :=
  by
  contrapose! h
  refine' ⟨_, fun b hr => _⟩
  by_contra hb
  exact h b hb hr
#align rel_embedding.exists_not_acc_lt_of_not_acc RelEmbedding.exists_not_acc_lt_of_not_acc
-/

/- warning: rel_embedding.acc_iff_no_decreasing_seq -> RelEmbedding.acc_iff_no_decreasing_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {x : α}, Iff (Acc.{succ u1} α r x) (IsEmpty.{succ u1} (Subtype.{succ u1} (RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) (fun (f : RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.range.{u1, 1} α Nat (coeFn.{succ u1, succ u1} (RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) (fun (_x : RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) => Nat -> α) (RelEmbedding.hasCoeToFun.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) f)))))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {x : α}, Iff (Acc.{succ u1} α r x) (IsEmpty.{succ u1} (Subtype.{succ u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.421 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.423 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.421 x._@.Mathlib.Order.OrderIsoNat._hyg.423) r) (fun (f : RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.421 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.423 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.421 x._@.Mathlib.Order.OrderIsoNat._hyg.423) r) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.range.{u1, 1} α Nat (FunLike.coe.{succ u1, 1, succ u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.421 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.423 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.421 x._@.Mathlib.Order.OrderIsoNat._hyg.423) r) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => α) _x) (RelHomClass.toFunLike.{u1, 0, u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.421 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.423 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.421 x._@.Mathlib.Order.OrderIsoNat._hyg.423) r) Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.421 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.423 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.421 x._@.Mathlib.Order.OrderIsoNat._hyg.423) r (RelEmbedding.instRelHomClassRelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.421 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.423 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.421 x._@.Mathlib.Order.OrderIsoNat._hyg.423) r)) f)))))
Case conversion may be inaccurate. Consider using '#align rel_embedding.acc_iff_no_decreasing_seq RelEmbedding.acc_iff_no_decreasing_seqₓ'. -/
/-- A value is accessible iff it isn't contained in any infinite decreasing sequence. -/
theorem acc_iff_no_decreasing_seq {x} :
    Acc r x ↔ IsEmpty { f : ((· > ·) : ℕ → ℕ → Prop) ↪r r // x ∈ Set.range f } :=
  by
  constructor
  · refine' fun h => h.recOn fun x h IH => _
    constructor
    rintro ⟨f, k, hf⟩
    exact IsEmpty.elim' (IH (f (k + 1)) (hf ▸ f.map_rel_iff.2 (lt_add_one k))) ⟨f, _, rfl⟩
  · have : ∀ x : { a // ¬Acc r a }, ∃ y : { a // ¬Acc r a }, r y.1 x.1 :=
      by
      rintro ⟨x, hx⟩
      cases exists_not_acc_lt_of_not_acc hx
      exact ⟨⟨w, h.1⟩, h.2⟩
    obtain ⟨f, h⟩ := Classical.axiom_of_choice this
    refine' fun E =>
      by_contradiction fun hx => E.elim' ⟨nat_gt (fun n => ((f^[n]) ⟨x, hx⟩).1) fun n => _, 0, rfl⟩
    rw [Function.iterate_succ']
    apply h
#align rel_embedding.acc_iff_no_decreasing_seq RelEmbedding.acc_iff_no_decreasing_seq

/- warning: rel_embedding.not_acc_of_decreasing_seq -> RelEmbedding.not_acc_of_decreasing_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] (f : RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) (k : Nat), Not (Acc.{succ u1} α r (coeFn.{succ u1, succ u1} (RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) (fun (_x : RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) => Nat -> α) (RelEmbedding.hasCoeToFun.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) f k))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] (f : RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.659 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.661 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.659 x._@.Mathlib.Order.OrderIsoNat._hyg.661) r) (k : Nat), Not (Acc.{succ u1} α r (FunLike.coe.{succ u1, 1, succ u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.659 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.661 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.659 x._@.Mathlib.Order.OrderIsoNat._hyg.661) r) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => α) _x) (RelHomClass.toFunLike.{u1, 0, u1} (RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.659 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.661 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.659 x._@.Mathlib.Order.OrderIsoNat._hyg.661) r) Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.659 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.661 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.659 x._@.Mathlib.Order.OrderIsoNat._hyg.661) r (RelEmbedding.instRelHomClassRelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.659 : Nat) (x._@.Mathlib.Order.OrderIsoNat._hyg.661 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.OrderIsoNat._hyg.659 x._@.Mathlib.Order.OrderIsoNat._hyg.661) r)) f k))
Case conversion may be inaccurate. Consider using '#align rel_embedding.not_acc_of_decreasing_seq RelEmbedding.not_acc_of_decreasing_seqₓ'. -/
theorem not_acc_of_decreasing_seq (f : ((· > ·) : ℕ → ℕ → Prop) ↪r r) (k : ℕ) : ¬Acc r (f k) :=
  by
  rw [acc_iff_no_decreasing_seq, not_isEmpty_iff]
  exact ⟨⟨f, k, rfl⟩⟩
#align rel_embedding.not_acc_of_decreasing_seq RelEmbedding.not_acc_of_decreasing_seq

#print RelEmbedding.wellFounded_iff_no_descending_seq /-
/-- A relation is well-founded iff it doesn't have any infinite decreasing sequence. -/
theorem wellFounded_iff_no_descending_seq :
    WellFounded r ↔ IsEmpty (((· > ·) : ℕ → ℕ → Prop) ↪r r) :=
  by
  constructor
  · rintro ⟨h⟩
    exact ⟨fun f => not_acc_of_decreasing_seq f 0 (h _)⟩
  · intro h
    exact ⟨fun x => acc_iff_no_decreasing_seq.2 inferInstance⟩
#align rel_embedding.well_founded_iff_no_descending_seq RelEmbedding.wellFounded_iff_no_descending_seq
-/

#print RelEmbedding.not_wellFounded_of_decreasing_seq /-
theorem not_wellFounded_of_decreasing_seq (f : ((· > ·) : ℕ → ℕ → Prop) ↪r r) : ¬WellFounded r :=
  by
  rw [well_founded_iff_no_descending_seq, not_isEmpty_iff]
  exact ⟨f⟩
#align rel_embedding.not_well_founded_of_decreasing_seq RelEmbedding.not_wellFounded_of_decreasing_seq
-/

end RelEmbedding

namespace Nat

variable (s : Set ℕ) [Infinite s]

#print Nat.orderEmbeddingOfSet /-
/-- An order embedding from `ℕ` to itself with a specified range -/
def orderEmbeddingOfSet [DecidablePred (· ∈ s)] : ℕ ↪o ℕ :=
  (RelEmbedding.orderEmbeddingOfLTEmbedding
        (RelEmbedding.natLt (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype s)
#align nat.order_embedding_of_set Nat.orderEmbeddingOfSet
-/

#print Nat.Subtype.orderIsoOfNat /-
/-- `nat.subtype.of_nat` as an order isomorphism between `ℕ` and an infinite subset. See also
`nat.nth` for a version where the subset may be finite. -/
noncomputable def Subtype.orderIsoOfNat : ℕ ≃o s := by
  classical exact
      RelIso.ofSurjective
        (RelEmbedding.orderEmbeddingOfLTEmbedding
          (RelEmbedding.natLt (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
        Nat.Subtype.ofNat_surjective
#align nat.subtype.order_iso_of_nat Nat.Subtype.orderIsoOfNat
-/

variable {s}

/- warning: nat.coe_order_embedding_of_set -> Nat.coe_orderEmbeddingOfSet is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Nat} [_inst_1 : Infinite.{1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s)] [_inst_2 : DecidablePred.{1} Nat (fun (_x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) _x s)], Eq.{1} (Nat -> Nat) (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) (Nat.orderEmbeddingOfSet s _inst_1 (fun (a : Nat) => _inst_2 a))) (Function.comp.{1, 1, 1} Nat (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat (coeSubtype.{1} Nat (fun (x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) x s)))))) (Nat.Subtype.ofNat s (fun (a : Nat) => _inst_2 a) _inst_1))
but is expected to have type
  forall {s : Set.{0} Nat} [_inst_1 : Infinite.{1} (Set.Elem.{0} Nat s)] [_inst_2 : DecidablePred.{1} Nat (fun (_x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) _x s)], Eq.{1} (forall (ᾰ : Nat), (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) ᾰ) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (Nat.orderEmbeddingOfSet s _inst_1 (fun (a : Nat) => _inst_2 a))) (Function.comp.{1, 1, 1} Nat (Set.Elem.{0} Nat s) Nat (Subtype.val.{1} Nat (fun (x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) x s)) (Nat.Subtype.ofNat s (fun (a : Nat) => _inst_2 a) _inst_1))
Case conversion may be inaccurate. Consider using '#align nat.coe_order_embedding_of_set Nat.coe_orderEmbeddingOfSetₓ'. -/
@[simp]
theorem coe_orderEmbeddingOfSet [DecidablePred (· ∈ s)] :
    ⇑(orderEmbeddingOfSet s) = coe ∘ Subtype.ofNat s :=
  rfl
#align nat.coe_order_embedding_of_set Nat.coe_orderEmbeddingOfSet

/- warning: nat.order_embedding_of_set_apply -> Nat.orderEmbeddingOfSet_apply is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Nat} [_inst_1 : Infinite.{1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s)] [_inst_2 : DecidablePred.{1} Nat (fun (_x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) _x s)] {n : Nat}, Eq.{1} Nat (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) (Nat.orderEmbeddingOfSet s _inst_1 (fun (a : Nat) => _inst_2 a)) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat (coeSubtype.{1} Nat (fun (x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) x s))))) (Nat.Subtype.ofNat s (fun (a : Nat) => _inst_2 a) _inst_1 n))
but is expected to have type
  forall {s : Set.{0} Nat} [_inst_1 : Infinite.{1} (Set.Elem.{0} Nat s)] [_inst_2 : DecidablePred.{1} Nat (fun (_x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) _x s)] {n : Nat}, Eq.{1} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) n) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (Nat.orderEmbeddingOfSet s _inst_1 (fun (a : Nat) => _inst_2 a)) n) (Subtype.val.{1} Nat (fun (x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) x s) (Nat.Subtype.ofNat s (fun (a : Nat) => _inst_2 a) _inst_1 n))
Case conversion may be inaccurate. Consider using '#align nat.order_embedding_of_set_apply Nat.orderEmbeddingOfSet_applyₓ'. -/
theorem orderEmbeddingOfSet_apply [DecidablePred (· ∈ s)] {n : ℕ} :
    orderEmbeddingOfSet s n = Subtype.ofNat s n :=
  rfl
#align nat.order_embedding_of_set_apply Nat.orderEmbeddingOfSet_apply

/- warning: nat.subtype.order_iso_of_nat_apply -> Nat.Subtype.orderIsoOfNat_apply is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Nat} [_inst_1 : Infinite.{1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s)] [_inst_2 : DecidablePred.{1} Nat (fun (_x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) _x s)] {n : Nat}, Eq.{1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) (coeFn.{1, 1} (OrderIso.{0, 0} Nat (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) Nat.hasLe (Subtype.hasLe.{0} Nat Nat.hasLe (fun (x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) x s))) (fun (_x : RelIso.{0, 0} Nat (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) (Subtype.hasLe.{0} Nat Nat.hasLe (fun (x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) x s)))) => Nat -> (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s)) (RelIso.hasCoeToFun.{0, 0} Nat (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s) (Subtype.hasLe.{0} Nat Nat.hasLe (fun (x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) x s)))) (Nat.Subtype.orderIsoOfNat s _inst_1) n) (Nat.Subtype.ofNat s (fun (a : Nat) => _inst_2 a) _inst_1 n)
but is expected to have type
  forall {s : Set.{0} Nat} [_inst_1 : Infinite.{1} (Set.Elem.{0} Nat s)] [_inst_2 : DecidablePred.{1} Nat (fun (_x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) _x s)] {n : Nat}, Eq.{1} (Set.Elem.{0} Nat s) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} Nat (Set.Elem.{0} Nat s) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Nat s) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Nat s) => LE.le.{0} (Set.Elem.{0} Nat s) (Subtype.le.{0} Nat instLENat (fun (x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) x s)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) Nat (fun (_x : Nat) => Set.Elem.{0} Nat s) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} Nat (Set.Elem.{0} Nat s) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Nat s) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Nat s) => LE.le.{0} (Set.Elem.{0} Nat s) (Subtype.le.{0} Nat instLENat (fun (x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) x s)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) Nat (Set.Elem.{0} Nat s) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Nat s) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Nat s) => LE.le.{0} (Set.Elem.{0} Nat s) (Subtype.le.{0} Nat instLENat (fun (x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) x s)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{0, 0} Nat (Set.Elem.{0} Nat s) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Nat s) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Nat s) => LE.le.{0} (Set.Elem.{0} Nat s) (Subtype.le.{0} Nat instLENat (fun (x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) x s)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) (Nat.Subtype.orderIsoOfNat s _inst_1) n) (Nat.Subtype.ofNat s (fun (a : Nat) => _inst_2 a) _inst_1 n)
Case conversion may be inaccurate. Consider using '#align nat.subtype.order_iso_of_nat_apply Nat.Subtype.orderIsoOfNat_applyₓ'. -/
@[simp]
theorem Subtype.orderIsoOfNat_apply [DecidablePred (· ∈ s)] {n : ℕ} :
    Subtype.orderIsoOfNat s n = Subtype.ofNat s n :=
  by
  simp [subtype.order_iso_of_nat]
  congr
#align nat.subtype.order_iso_of_nat_apply Nat.Subtype.orderIsoOfNat_apply

variable (s)

/- warning: nat.order_embedding_of_set_range -> Nat.orderEmbeddingOfSet_range is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Nat) [_inst_1 : Infinite.{1} (coeSort.{1, 2} (Set.{0} Nat) Type (Set.hasCoeToSort.{0} Nat) s)] [_inst_2 : DecidablePred.{1} Nat (fun (_x : Nat) => Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) _x s)], Eq.{1} (Set.{0} Nat) (Set.range.{0, 1} Nat Nat (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) (Nat.orderEmbeddingOfSet s _inst_1 (fun (a : Nat) => _inst_2 a)))) s
but is expected to have type
  forall (s : Set.{0} Nat) [_inst_1 : Infinite.{1} (Set.Elem.{0} Nat s)] [_inst_2 : DecidablePred.{1} Nat (fun (_x : Nat) => Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) _x s)], Eq.{1} (Set.{0} Nat) (Set.range.{0, 1} Nat Nat (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (Nat.orderEmbeddingOfSet s _inst_1 (fun (a : Nat) => _inst_2 a)))) s
Case conversion may be inaccurate. Consider using '#align nat.order_embedding_of_set_range Nat.orderEmbeddingOfSet_rangeₓ'. -/
theorem orderEmbeddingOfSet_range [DecidablePred (· ∈ s)] :
    Set.range (Nat.orderEmbeddingOfSet s) = s :=
  Subtype.coe_comp_ofNat_range
#align nat.order_embedding_of_set_range Nat.orderEmbeddingOfSet_range

/- warning: nat.exists_subseq_of_forall_mem_union -> Nat.exists_subseq_of_forall_mem_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (e : Nat -> α), (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (e n) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (g : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) => Or (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (e (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g n)) s) (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (e (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g n)) t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (e : Nat -> α), (forall (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (e n) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) (fun (g : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) => Or (forall (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (e (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g n)) s) (forall (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (e (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g n)) t)))
Case conversion may be inaccurate. Consider using '#align nat.exists_subseq_of_forall_mem_union Nat.exists_subseq_of_forall_mem_unionₓ'. -/
theorem exists_subseq_of_forall_mem_union {s t : Set α} (e : ℕ → α) (he : ∀ n, e n ∈ s ∪ t) :
    ∃ g : ℕ ↪o ℕ, (∀ n, e (g n) ∈ s) ∨ ∀ n, e (g n) ∈ t := by
  classical
    have : Infinite (e ⁻¹' s) ∨ Infinite (e ⁻¹' t) := by
      simp only [Set.infinite_coe_iff, ← Set.infinite_union, ← Set.preimage_union,
        Set.eq_univ_of_forall fun n => Set.mem_preimage.2 (he n), Set.infinite_univ]
    cases this
    exacts[⟨Nat.orderEmbeddingOfSet (e ⁻¹' s), Or.inl fun n => (Nat.Subtype.ofNat (e ⁻¹' s) _).2⟩,
      ⟨Nat.orderEmbeddingOfSet (e ⁻¹' t), Or.inr fun n => (Nat.Subtype.ofNat (e ⁻¹' t) _).2⟩]
#align nat.exists_subseq_of_forall_mem_union Nat.exists_subseq_of_forall_mem_union

end Nat

/- warning: exists_increasing_or_nonincreasing_subseq' -> exists_increasing_or_nonincreasing_subseq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : α -> α -> Prop) (f : Nat -> α), Exists.{1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (g : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) => Or (forall (n : Nat), r (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g n)) (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (forall (m : Nat) (n : Nat), (LT.lt.{0} Nat Nat.hasLt m n) -> (Not (r (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g m)) (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g n))))))
but is expected to have type
  forall {α : Type.{u1}} (r : α -> α -> Prop) (f : Nat -> α), Exists.{1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) (fun (g : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) => Or (forall (n : Nat), r (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g n)) (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (forall (m : Nat) (n : Nat), (LT.lt.{0} Nat instLTNat m n) -> (Not (r (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g m)) (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g n))))))
Case conversion may be inaccurate. Consider using '#align exists_increasing_or_nonincreasing_subseq' exists_increasing_or_nonincreasing_subseq'ₓ'. -/
theorem exists_increasing_or_nonincreasing_subseq' (r : α → α → Prop) (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ,
      (∀ n : ℕ, r (f (g n)) (f (g (n + 1)))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) :=
  by
  classical
    let bad : Set ℕ := { m | ∀ n, m < n → ¬r (f m) (f n) }
    by_cases hbad : Infinite bad
    · haveI := hbad
      refine' ⟨Nat.orderEmbeddingOfSet bad, Or.intro_right _ fun m n mn => _⟩
      have h := Set.mem_range_self m
      rw [Nat.orderEmbeddingOfSet_range bad] at h
      exact h _ ((OrderEmbedding.lt_iff_lt _).2 mn)
    · rw [Set.infinite_coe_iff, Set.Infinite, Classical.not_not] at hbad
      obtain ⟨m, hm⟩ : ∃ m, ∀ n, m ≤ n → ¬n ∈ bad :=
        by
        by_cases he : hbad.to_finset.nonempty
        ·
          refine'
            ⟨(hbad.to_finset.max' he).succ, fun n hn nbad =>
              Nat.not_succ_le_self _
                (hn.trans (hbad.to_finset.le_max' n (hbad.mem_to_finset.2 nbad)))⟩
        · exact ⟨0, fun n hn nbad => he ⟨n, hbad.mem_to_finset.2 nbad⟩⟩
      have h : ∀ n : ℕ, ∃ n' : ℕ, n < n' ∧ r (f (n + m)) (f (n' + m)) :=
        by
        intro n
        have h := hm _ (le_add_of_nonneg_left n.zero_le)
        simp only [exists_prop, Classical.not_not, Set.mem_setOf_eq, not_forall] at h
        obtain ⟨n', hn1, hn2⟩ := h
        obtain ⟨x, hpos, rfl⟩ := exists_pos_add_of_lt hn1
        refine' ⟨n + x, add_lt_add_left hpos n, _⟩
        rw [add_assoc, add_comm x m, ← add_assoc]
        exact hn2
      let g' : ℕ → ℕ := @Nat.rec (fun _ => ℕ) m fun n gn => Nat.find (h gn)
      exact
        ⟨(RelEmbedding.natLt (fun n => g' n + m) fun n =>
              Nat.add_lt_add_right (Nat.find_spec (h (g' n))).1 m).orderEmbeddingOfLTEmbedding,
          Or.intro_left _ fun n => (Nat.find_spec (h (g' n))).2⟩
#align exists_increasing_or_nonincreasing_subseq' exists_increasing_or_nonincreasing_subseq'

/- warning: exists_increasing_or_nonincreasing_subseq -> exists_increasing_or_nonincreasing_subseq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : α -> α -> Prop) [_inst_1 : IsTrans.{u1} α r] (f : Nat -> α), Exists.{1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (g : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) => Or (forall (m : Nat) (n : Nat), (LT.lt.{0} Nat Nat.hasLt m n) -> (r (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g m)) (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g n)))) (forall (m : Nat) (n : Nat), (LT.lt.{0} Nat Nat.hasLt m n) -> (Not (r (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g m)) (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g n))))))
but is expected to have type
  forall {α : Type.{u1}} (r : α -> α -> Prop) [_inst_1 : IsTrans.{u1} α r] (f : Nat -> α), Exists.{1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) (fun (g : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) => Or (forall (m : Nat) (n : Nat), (LT.lt.{0} Nat instLTNat m n) -> (r (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g m)) (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g n)))) (forall (m : Nat) (n : Nat), (LT.lt.{0} Nat instLTNat m n) -> (Not (r (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g m)) (f (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Nat) => Nat) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) g n))))))
Case conversion may be inaccurate. Consider using '#align exists_increasing_or_nonincreasing_subseq exists_increasing_or_nonincreasing_subseqₓ'. -/
/-- This is the infinitary Erdős–Szekeres theorem, and an important lemma in the usual proof of
    Bolzano-Weierstrass for `ℝ`. -/
theorem exists_increasing_or_nonincreasing_subseq (r : α → α → Prop) [IsTrans α r] (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ,
      (∀ m n : ℕ, m < n → r (f (g m)) (f (g n))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) :=
  by
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
  · refine' ⟨g, Or.intro_left _ fun m n mn => _⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le (Nat.succ_le_iff.2 mn)
    induction' x with x ih
    · apply hr
    · apply IsTrans.trans _ _ _ _ (hr _)
      exact ih (lt_of_lt_of_le m.lt_succ_self (Nat.le_add_right _ _))
  · exact ⟨g, Or.intro_right _ hnr⟩
#align exists_increasing_or_nonincreasing_subseq exists_increasing_or_nonincreasing_subseq

#print WellFounded.monotone_chain_condition' /-
theorem WellFounded.monotone_chain_condition' [Preorder α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → ¬a n < a m :=
  by
  refine' ⟨fun h a => _, fun h => _⟩
  · have hne : (Set.range a).Nonempty := ⟨a 0, by simp⟩
    obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.has_min _ hne
    exact ⟨n, fun m hm => H _ (Set.mem_range_self _)⟩
  · refine' RelEmbedding.wellFounded_iff_no_descending_seq.2 ⟨fun a => _⟩
    obtain ⟨n, hn⟩ := h (a.swap : ((· < ·) : ℕ → ℕ → Prop) →r ((· < ·) : α → α → Prop)).toOrderHom
    exact hn n.succ n.lt_succ_self.le ((RelEmbedding.map_rel_iff _).2 n.lt_succ_self)
#align well_founded.monotone_chain_condition' WellFounded.monotone_chain_condition'
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ∀ a, «expr∃ , »((n), ∀ (m) (h : «expr ≤ »(n, m)), (_ : exprProp()))]] -/
#print WellFounded.monotone_chain_condition /-
/-- The "monotone chain condition" below is sometimes a convenient form of well foundedness. -/
theorem WellFounded.monotone_chain_condition [PartialOrder α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → a n = a m :=
  WellFounded.monotone_chain_condition'.trans <|
    by
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ∀ a, «expr∃ , »((n), ∀ (m) (h : «expr ≤ »(n, m)), (_ : exprProp()))]]"
    rw [lt_iff_le_and_ne]
    simp [a.mono h]
#align well_founded.monotone_chain_condition WellFounded.monotone_chain_condition
-/

#print monotonicSequenceLimitIndex /-
/-- Given an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partially-ordered
type, `monotonic_sequence_limit_index a` is the least natural number `n` for which `aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonic_sequence_limit_index a`
is defined, but is a junk value. -/
noncomputable def monotonicSequenceLimitIndex [Preorder α] (a : ℕ →o α) : ℕ :=
  infₛ { n | ∀ m, n ≤ m → a n = a m }
#align monotonic_sequence_limit_index monotonicSequenceLimitIndex
-/

#print monotonicSequenceLimit /-
/-- The constant value of an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a
partially-ordered type. -/
noncomputable def monotonicSequenceLimit [Preorder α] (a : ℕ →o α) :=
  a (monotonicSequenceLimitIndex a)
#align monotonic_sequence_limit monotonicSequenceLimit
-/

/- warning: well_founded.supr_eq_monotonic_sequence_limit -> WellFounded.supᵢ_eq_monotonicSequenceLimit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], (WellFounded.{succ u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) -> (forall (a : OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))), Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (coeFn.{succ u1, succ u1} (OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (fun (_x : OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) => Nat -> α) (OrderHom.hasCoeToFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a)) (monotonicSequenceLimit.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], (WellFounded.{succ u1} α (fun (x._@.Mathlib.Order.OrderIsoNat._hyg.2645 : α) (x._@.Mathlib.Order.OrderIsoNat._hyg.2647 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.OrderIsoNat._hyg.2645 x._@.Mathlib.Order.OrderIsoNat._hyg.2647)) -> (forall (a : OrderHom.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))), Eq.{succ u1} α (supᵢ.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (OrderHom.toFun.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a)) (monotonicSequenceLimit.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a))
Case conversion may be inaccurate. Consider using '#align well_founded.supr_eq_monotonic_sequence_limit WellFounded.supᵢ_eq_monotonicSequenceLimitₓ'. -/
theorem WellFounded.supᵢ_eq_monotonicSequenceLimit [CompleteLattice α]
    (h : WellFounded ((· > ·) : α → α → Prop)) (a : ℕ →o α) : supᵢ a = monotonicSequenceLimit a :=
  by
  apply (supᵢ_le fun m => _).antisymm (le_supᵢ a _)
  cases' le_or_lt m (monotonicSequenceLimitIndex a) with hm hm
  · exact a.monotone hm
  · cases' WellFounded.monotone_chain_condition'.1 h a with n hn
    exact (Nat.infₛ_mem ⟨n, fun k hk => (a.mono hk).eq_of_not_lt (hn k hk)⟩ m hm.le).ge
#align well_founded.supr_eq_monotonic_sequence_limit WellFounded.supᵢ_eq_monotonicSequenceLimit

