/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.set.pairwise
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Relation
import Mathbin.Logic.Pairwise
import Mathbin.Data.Set.Lattice

/-!
# Relations holding pairwise

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops pairwise relations and defines pairwise disjoint indexed sets.

We also prove many basic facts about `pairwise`. It is possible that an intermediate file,
with more imports than `logic.pairwise` but not importing `data.set.lattice` would be appropriate
to hold many of these basic facts.

## Main declarations

* `set.pairwise_disjoint`: `s.pairwise_disjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `disjoint`.

## Notes

The spelling `s.pairwise_disjoint id` is preferred over `s.pairwise disjoint` to permit dot notation
on `set.pairwise_disjoint`, even though the latter unfolds to something nicer.
-/


open Set Function

variable {α β γ ι ι' : Type _} {r p q : α → α → Prop}

section Pairwise

variable {f g : ι → α} {s t u : Set α} {a b : α}

#print pairwise_on_bool /-
theorem pairwise_on_bool (hr : Symmetric r) {a b : α} :
    Pairwise (r on fun c => cond c a b) ↔ r a b := by simpa [Pairwise, Function.onFun] using @hr a b
#align pairwise_on_bool pairwise_on_bool
-/

#print pairwise_disjoint_on_bool /-
theorem pairwise_disjoint_on_bool [SemilatticeInf α] [OrderBot α] {a b : α} :
    Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b :=
  pairwise_on_bool Disjoint.symm
#align pairwise_disjoint_on_bool pairwise_disjoint_on_bool
-/

#print Symmetric.pairwise_on /-
theorem Symmetric.pairwise_on [LinearOrder ι] (hr : Symmetric r) (f : ι → α) :
    Pairwise (r on f) ↔ ∀ ⦃m n⦄, m < n → r (f m) (f n) :=
  ⟨fun h m n hmn => h hmn.Ne, fun h m n hmn => hmn.lt_or_lt.elim (@h _ _) fun h' => hr (h h')⟩
#align symmetric.pairwise_on Symmetric.pairwise_on
-/

/- warning: pairwise_disjoint_on -> pairwise_disjoint_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LinearOrder.{u2} ι] (f : ι -> α), Iff (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι α Prop (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2) f)) (forall {{m : ι}} {{n : ι}}, (LT.lt.{u2} ι (Preorder.toLT.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (LinearOrder.toLattice.{u2} ι _inst_3))))) m n) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 (f m) (f n)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] [_inst_3 : LinearOrder.{u1} ι] (f : ι -> α), Iff (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι α Prop (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1) _inst_2) f)) (forall {{m : ι}} {{n : ι}}, (LT.lt.{u1} ι (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (DistribLattice.toLattice.{u1} ι (instDistribLattice.{u1} ι _inst_3)))))) m n) -> (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1) _inst_2 (f m) (f n)))
Case conversion may be inaccurate. Consider using '#align pairwise_disjoint_on pairwise_disjoint_onₓ'. -/
theorem pairwise_disjoint_on [SemilatticeInf α] [OrderBot α] [LinearOrder ι] (f : ι → α) :
    Pairwise (Disjoint on f) ↔ ∀ ⦃m n⦄, m < n → Disjoint (f m) (f n) :=
  Symmetric.pairwise_on Disjoint.symm f
#align pairwise_disjoint_on pairwise_disjoint_on

/- warning: pairwise_disjoint.mono -> pairwise_disjoint_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> α} {g : ι -> α} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))], (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι α Prop (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2) f)) -> (LE.le.{max u2 u1} (ι -> α) (Pi.hasLe.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) g f) -> (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι α Prop (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2) g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {f : ι -> α} {g : ι -> α} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))], (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι α Prop (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1) _inst_2) f)) -> (LE.le.{max u2 u1} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))) g f) -> (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι α Prop (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1) _inst_2) g))
Case conversion may be inaccurate. Consider using '#align pairwise_disjoint.mono pairwise_disjoint_monoₓ'. -/
theorem pairwise_disjoint_mono [SemilatticeInf α] [OrderBot α] (hs : Pairwise (Disjoint on f))
    (h : g ≤ f) : Pairwise (Disjoint on g) :=
  hs.mono fun i j hij => Disjoint.mono (h i) (h j) hij
#align pairwise_disjoint.mono pairwise_disjoint_mono

alias Function.injective_iff_pairwise_ne ↔ Function.Injective.pairwise_ne _
#align function.injective.pairwise_ne Function.Injective.pairwise_ne

namespace Set

#print Set.Pairwise.mono /-
theorem Pairwise.mono (h : t ⊆ s) (hs : s.Pairwise r) : t.Pairwise r := fun x xt y yt =>
  hs (h xt) (h yt)
#align set.pairwise.mono Set.Pairwise.mono
-/

#print Set.Pairwise.mono' /-
theorem Pairwise.mono' (H : r ≤ p) (hr : s.Pairwise r) : s.Pairwise p :=
  hr.imp H
#align set.pairwise.mono' Set.Pairwise.mono'
-/

/- warning: set.pairwise_top -> Set.pairwise_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Set.Pairwise.{u1} α s (Top.top.{u1} (α -> α -> Prop) (Pi.hasTop.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasTop.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice))))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Set.Pairwise.{u1} α s (Top.top.{u1} (α -> α -> Prop) (Pi.instTopForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instTopForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toTop.{0} Prop Prop.completeLattice))))
Case conversion may be inaccurate. Consider using '#align set.pairwise_top Set.pairwise_topₓ'. -/
theorem pairwise_top (s : Set α) : s.Pairwise ⊤ :=
  pairwise_of_forall s _ fun a b => trivial
#align set.pairwise_top Set.pairwise_top

#print Set.Subsingleton.pairwise /-
protected theorem Subsingleton.pairwise (h : s.Subsingleton) (r : α → α → Prop) : s.Pairwise r :=
  fun x hx y hy hne => (hne (h hx hy)).elim
#align set.subsingleton.pairwise Set.Subsingleton.pairwise
-/

#print Set.pairwise_empty /-
@[simp]
theorem pairwise_empty (r : α → α → Prop) : (∅ : Set α).Pairwise r :=
  subsingleton_empty.Pairwise r
#align set.pairwise_empty Set.pairwise_empty
-/

#print Set.pairwise_singleton /-
@[simp]
theorem pairwise_singleton (a : α) (r : α → α → Prop) : Set.Pairwise {a} r :=
  subsingleton_singleton.Pairwise r
#align set.pairwise_singleton Set.pairwise_singleton
-/

#print Set.pairwise_iff_of_refl /-
theorem pairwise_iff_of_refl [IsRefl α r] : s.Pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
  forall₄_congr fun a _ b _ => or_iff_not_imp_left.symm.trans <| or_iff_right_of_imp of_eq
#align set.pairwise_iff_of_refl Set.pairwise_iff_of_refl
-/

alias pairwise_iff_of_refl ↔ pairwise.of_refl _
#align set.pairwise.of_refl Set.Pairwise.of_refl

/- warning: set.nonempty.pairwise_iff_exists_forall -> Set.Nonempty.pairwise_iff_exists_forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {r : α -> α -> Prop} {f : ι -> α} [_inst_1 : IsEquiv.{u1} α r] {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Iff (Set.Pairwise.{u2} ι s (Function.onFun.{succ u2, succ u1, 1} ι α Prop r f)) (Exists.{succ u1} α (fun (z : α) => forall (x : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s) -> (r (f x) z))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {r : α -> α -> Prop} {f : ι -> α} [_inst_1 : IsEquiv.{u2} α r] {s : Set.{u1} ι}, (Set.Nonempty.{u1} ι s) -> (Iff (Set.Pairwise.{u1} ι s (Function.onFun.{succ u1, succ u2, 1} ι α Prop r f)) (Exists.{succ u2} α (fun (z : α) => forall (x : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x s) -> (r (f x) z))))
Case conversion may be inaccurate. Consider using '#align set.nonempty.pairwise_iff_exists_forall Set.Nonempty.pairwise_iff_exists_forallₓ'. -/
theorem Nonempty.pairwise_iff_exists_forall [IsEquiv α r] {s : Set ι} (hs : s.Nonempty) :
    s.Pairwise (r on f) ↔ ∃ z, ∀ x ∈ s, r (f x) z :=
  by
  fconstructor
  · rcases hs with ⟨y, hy⟩
    refine' fun H => ⟨f y, fun x hx => _⟩
    rcases eq_or_ne x y with (rfl | hne)
    · apply IsRefl.refl
    · exact H hx hy hne
  · rintro ⟨z, hz⟩ x hx y hy hne
    exact @IsTrans.trans α r _ (f x) z (f y) (hz _ hx) (IsSymm.symm _ _ <| hz _ hy)
#align set.nonempty.pairwise_iff_exists_forall Set.Nonempty.pairwise_iff_exists_forall

/- warning: set.nonempty.pairwise_eq_iff_exists_eq -> Set.Nonempty.pairwise_eq_iff_exists_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {f : α -> ι}, Iff (Set.Pairwise.{u1} α s (fun (x : α) (y : α) => Eq.{succ u2} ι (f x) (f y))) (Exists.{succ u2} ι (fun (z : ι) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u2} ι (f x) z))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall {f : α -> ι}, Iff (Set.Pairwise.{u2} α s (fun (x : α) (y : α) => Eq.{succ u1} ι (f x) (f y))) (Exists.{succ u1} ι (fun (z : ι) => forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Eq.{succ u1} ι (f x) z))))
Case conversion may be inaccurate. Consider using '#align set.nonempty.pairwise_eq_iff_exists_eq Set.Nonempty.pairwise_eq_iff_exists_eqₓ'. -/
/-- For a nonempty set `s`, a function `f` takes pairwise equal values on `s` if and only if
for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`set.pairwise_eq_iff_exists_eq` for a version that assumes `[nonempty ι]` instead of
`set.nonempty s`. -/
theorem Nonempty.pairwise_eq_iff_exists_eq {s : Set α} (hs : s.Nonempty) {f : α → ι} :
    (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z :=
  hs.pairwise_iff_exists_forall
#align set.nonempty.pairwise_eq_iff_exists_eq Set.Nonempty.pairwise_eq_iff_exists_eq

#print Set.pairwise_iff_exists_forall /-
theorem pairwise_iff_exists_forall [Nonempty ι] (s : Set α) (f : α → ι) {r : ι → ι → Prop}
    [IsEquiv ι r] : s.Pairwise (r on f) ↔ ∃ z, ∀ x ∈ s, r (f x) z :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  · exact hne.pairwise_iff_exists_forall
#align set.pairwise_iff_exists_forall Set.pairwise_iff_exists_forall
-/

#print Set.pairwise_eq_iff_exists_eq /-
/-- A function `f : α → ι` with nonempty codomain takes pairwise equal values on a set `s` if and
only if for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`set.nonempty.pairwise_eq_iff_exists_eq` for a version that assumes `set.nonempty s` instead of
`[nonempty ι]`. -/
theorem pairwise_eq_iff_exists_eq [Nonempty ι] (s : Set α) (f : α → ι) :
    (s.Pairwise fun x y => f x = f y) ↔ ∃ z, ∀ x ∈ s, f x = z :=
  pairwise_iff_exists_forall s f
#align set.pairwise_eq_iff_exists_eq Set.pairwise_eq_iff_exists_eq
-/

/- warning: set.pairwise_union -> Set.pairwise_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Pairwise.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) r) (And (Set.Pairwise.{u1} α s r) (And (Set.Pairwise.{u1} α t r) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (Ne.{succ u1} α a b) -> (And (r a b) (r b a))))))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Pairwise.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) r) (And (Set.Pairwise.{u1} α s r) (And (Set.Pairwise.{u1} α t r) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (Ne.{succ u1} α a b) -> (And (r a b) (r b a))))))
Case conversion may be inaccurate. Consider using '#align set.pairwise_union Set.pairwise_unionₓ'. -/
theorem pairwise_union :
    (s ∪ t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b ∧ r b a :=
  by
  simp only [Set.Pairwise, mem_union, or_imp, forall_and]
  exact
    ⟨fun H => ⟨H.1.1, H.2.2, H.2.1, fun x hx y hy hne => H.1.2 y hy x hx hne.symm⟩, fun H =>
      ⟨⟨H.1, fun x hx y hy hne => H.2.2.2 y hy x hx hne.symm⟩, H.2.2.1, H.2.1⟩⟩
#align set.pairwise_union Set.pairwise_union

/- warning: set.pairwise_union_of_symmetric -> Set.pairwise_union_of_symmetric is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} {t : Set.{u1} α}, (Symmetric.{succ u1} α r) -> (Iff (Set.Pairwise.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) r) (And (Set.Pairwise.{u1} α s r) (And (Set.Pairwise.{u1} α t r) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t) -> (Ne.{succ u1} α a b) -> (r a b))))))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} {t : Set.{u1} α}, (Symmetric.{succ u1} α r) -> (Iff (Set.Pairwise.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) r) (And (Set.Pairwise.{u1} α s r) (And (Set.Pairwise.{u1} α t r) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t) -> (Ne.{succ u1} α a b) -> (r a b))))))
Case conversion may be inaccurate. Consider using '#align set.pairwise_union_of_symmetric Set.pairwise_union_of_symmetricₓ'. -/
theorem pairwise_union_of_symmetric (hr : Symmetric r) :
    (s ∪ t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b :=
  pairwise_union.trans <| by simp only [hr.iff, and_self_iff]
#align set.pairwise_union_of_symmetric Set.pairwise_union_of_symmetric

#print Set.pairwise_insert /-
theorem pairwise_insert : (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b ∧ r b a :=
  by
  simp only [insert_eq, pairwise_union, pairwise_singleton, true_and_iff, mem_singleton_iff,
    forall_eq]
#align set.pairwise_insert Set.pairwise_insert
-/

#print Set.pairwise_insert_of_not_mem /-
theorem pairwise_insert_of_not_mem (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b ∧ r b a :=
  pairwise_insert.trans <|
    and_congr_right' <| forall₂_congr fun b hb => by simp [(ne_of_mem_of_not_mem hb ha).symm]
#align set.pairwise_insert_of_not_mem Set.pairwise_insert_of_not_mem
-/

#print Set.Pairwise.insert /-
theorem Pairwise.insert (hs : s.Pairwise r) (h : ∀ b ∈ s, a ≠ b → r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  pairwise_insert.2 ⟨hs, h⟩
#align set.pairwise.insert Set.Pairwise.insert
-/

#print Set.Pairwise.insert_of_not_mem /-
theorem Pairwise.insert_of_not_mem (ha : a ∉ s) (hs : s.Pairwise r) (h : ∀ b ∈ s, r a b ∧ r b a) :
    (insert a s).Pairwise r :=
  (pairwise_insert_of_not_mem ha).2 ⟨hs, h⟩
#align set.pairwise.insert_of_not_mem Set.Pairwise.insert_of_not_mem
-/

#print Set.pairwise_insert_of_symmetric /-
theorem pairwise_insert_of_symmetric (hr : Symmetric r) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, a ≠ b → r a b := by
  simp only [pairwise_insert, hr.iff a, and_self_iff]
#align set.pairwise_insert_of_symmetric Set.pairwise_insert_of_symmetric
-/

#print Set.pairwise_insert_of_symmetric_of_not_mem /-
theorem pairwise_insert_of_symmetric_of_not_mem (hr : Symmetric r) (ha : a ∉ s) :
    (insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b := by
  simp only [pairwise_insert_of_not_mem ha, hr.iff a, and_self_iff]
#align set.pairwise_insert_of_symmetric_of_not_mem Set.pairwise_insert_of_symmetric_of_not_mem
-/

#print Set.Pairwise.insert_of_symmetric /-
theorem Pairwise.insert_of_symmetric (hs : s.Pairwise r) (hr : Symmetric r)
    (h : ∀ b ∈ s, a ≠ b → r a b) : (insert a s).Pairwise r :=
  (pairwise_insert_of_symmetric hr).2 ⟨hs, h⟩
#align set.pairwise.insert_of_symmetric Set.Pairwise.insert_of_symmetric
-/

#print Set.Pairwise.insert_of_symmetric_of_not_mem /-
theorem Pairwise.insert_of_symmetric_of_not_mem (hs : s.Pairwise r) (hr : Symmetric r) (ha : a ∉ s)
    (h : ∀ b ∈ s, r a b) : (insert a s).Pairwise r :=
  (pairwise_insert_of_symmetric_of_not_mem hr ha).2 ⟨hs, h⟩
#align set.pairwise.insert_of_symmetric_of_not_mem Set.Pairwise.insert_of_symmetric_of_not_mem
-/

#print Set.pairwise_pair /-
theorem pairwise_pair : Set.Pairwise {a, b} r ↔ a ≠ b → r a b ∧ r b a := by simp [pairwise_insert]
#align set.pairwise_pair Set.pairwise_pair
-/

#print Set.pairwise_pair_of_symmetric /-
theorem pairwise_pair_of_symmetric (hr : Symmetric r) : Set.Pairwise {a, b} r ↔ a ≠ b → r a b := by
  simp [pairwise_insert_of_symmetric hr]
#align set.pairwise_pair_of_symmetric Set.pairwise_pair_of_symmetric
-/

#print Set.pairwise_univ /-
theorem pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise r := by
  simp only [Set.Pairwise, Pairwise, mem_univ, forall_const]
#align set.pairwise_univ Set.pairwise_univ
-/

/- warning: set.pairwise_bot_iff -> Set.pairwise_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Set.Pairwise.{u1} α s (Bot.bot.{u1} (α -> α -> Prop) (Pi.hasBot.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasBot.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasBot.{0} Prop Prop.completeLattice))))) (Set.Subsingleton.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Set.Pairwise.{u1} α s (Bot.bot.{u1} (α -> α -> Prop) (Pi.instBotForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instBotForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toBot.{0} Prop Prop.completeLattice))))) (Set.Subsingleton.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.pairwise_bot_iff Set.pairwise_bot_iffₓ'. -/
@[simp]
theorem pairwise_bot_iff : s.Pairwise (⊥ : α → α → Prop) ↔ (s : Set α).Subsingleton :=
  ⟨fun h a ha b hb => h.Eq ha hb id, fun h => h.Pairwise _⟩
#align set.pairwise_bot_iff Set.pairwise_bot_iff

/- warning: set.pairwise.subsingleton -> Set.Pairwise.subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Pairwise.{u1} α s (Bot.bot.{u1} (α -> α -> Prop) (Pi.hasBot.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasBot.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasBot.{0} Prop Prop.completeLattice))))) -> (Set.Subsingleton.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Pairwise.{u1} α s (Bot.bot.{u1} (α -> α -> Prop) (Pi.instBotForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instBotForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toBot.{0} Prop Prop.completeLattice))))) -> (Set.Subsingleton.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.pairwise.subsingleton Set.Pairwise.subsingletonₓ'. -/
alias pairwise_bot_iff ↔ pairwise.subsingleton _
#align set.pairwise.subsingleton Set.Pairwise.subsingleton

#print Set.InjOn.pairwise_image /-
theorem InjOn.pairwise_image {s : Set ι} (h : s.InjOn f) :
    (f '' s).Pairwise r ↔ s.Pairwise (r on f) := by
  simp (config := { contextual := true }) [h.eq_iff, Set.Pairwise]
#align set.inj_on.pairwise_image Set.InjOn.pairwise_image
-/

/- warning: set.pairwise_Union -> Set.pairwise_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {r : α -> α -> Prop} {f : ι -> (Set.{u1} α)}, (Directed.{u1, succ u2} (Set.{u1} α) ι (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) f) -> (Iff (Set.Pairwise.{u1} α (Set.unionᵢ.{u1, succ u2} α ι (fun (n : ι) => f n)) r) (forall (n : ι), Set.Pairwise.{u1} α (f n) r))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {r : α -> α -> Prop} {f : ι -> (Set.{u2} α)}, (Directed.{u2, succ u1} (Set.{u2} α) ι (fun (x._@.Mathlib.Data.Set.Pairwise._hyg.2714 : Set.{u2} α) (x._@.Mathlib.Data.Set.Pairwise._hyg.2716 : Set.{u2} α) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) x._@.Mathlib.Data.Set.Pairwise._hyg.2714 x._@.Mathlib.Data.Set.Pairwise._hyg.2716) f) -> (Iff (Set.Pairwise.{u2} α (Set.unionᵢ.{u2, succ u1} α ι (fun (n : ι) => f n)) r) (forall (n : ι), Set.Pairwise.{u2} α (f n) r))
Case conversion may be inaccurate. Consider using '#align set.pairwise_Union Set.pairwise_unionᵢₓ'. -/
theorem pairwise_unionᵢ {f : ι → Set α} (h : Directed (· ⊆ ·) f) :
    (⋃ n, f n).Pairwise r ↔ ∀ n, (f n).Pairwise r :=
  by
  constructor
  · intro H n
    exact Pairwise.mono (subset_Union _ _) H
  · intro H i hi j hj hij
    rcases mem_Union.1 hi with ⟨m, hm⟩
    rcases mem_Union.1 hj with ⟨n, hn⟩
    rcases h m n with ⟨p, mp, np⟩
    exact H p (mp hm) (np hn) hij
#align set.pairwise_Union Set.pairwise_unionᵢ

#print Set.pairwise_unionₛ /-
theorem pairwise_unionₛ {r : α → α → Prop} {s : Set (Set α)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).Pairwise r ↔ ∀ a ∈ s, Set.Pairwise a r :=
  by
  rw [sUnion_eq_Union, pairwise_Union h.directed_coe, SetCoe.forall]
  rfl
#align set.pairwise_sUnion Set.pairwise_unionₛ
-/

end Set

end Pairwise

#print pairwise_subtype_iff_pairwise_set /-
theorem pairwise_subtype_iff_pairwise_set (s : Set α) (r : α → α → Prop) :
    (Pairwise fun (x : s) (y : s) => r x y) ↔ s.Pairwise r := by
  simp only [Pairwise, Set.Pairwise, SetCoe.forall, Ne.def, Subtype.ext_iff, Subtype.coe_mk]
#align pairwise_subtype_iff_pairwise_set pairwise_subtype_iff_pairwise_set
-/

alias pairwise_subtype_iff_pairwise_set ↔ Pairwise.set_of_subtype Set.Pairwise.subtype
#align pairwise.set_of_subtype Pairwise.set_of_subtype
#align set.pairwise.subtype Set.Pairwise.subtype

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s t : Set ι} {f g : ι → α}

#print Set.PairwiseDisjoint /-
/-- A set is `pairwise_disjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint.

`s.pairwise disjoint` is (definitionally) the same as `s.pairwise_disjoint id`. We prefer the latter
in order to allow dot notation on `set.pairwise_disjoint`, even though the former unfolds more
nicely. -/
def PairwiseDisjoint (s : Set ι) (f : ι → α) : Prop :=
  s.Pairwise (Disjoint on f)
#align set.pairwise_disjoint Set.PairwiseDisjoint
-/

/- warning: set.pairwise_disjoint.subset -> Set.PairwiseDisjoint.subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {t : Set.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 t f) -> (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) s t) -> (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {t : Set.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 t f) -> (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) s t) -> (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.subset Set.PairwiseDisjoint.subsetₓ'. -/
theorem PairwiseDisjoint.subset (ht : t.PairwiseDisjoint f) (h : s ⊆ t) : s.PairwiseDisjoint f :=
  Pairwise.mono h ht
#align set.pairwise_disjoint.subset Set.PairwiseDisjoint.subset

/- warning: set.pairwise_disjoint.mono_on -> Set.PairwiseDisjoint.mono_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {f : ι -> α} {g : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) -> (forall {{i : ι}}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (g i) (f i))) -> (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s g)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {f : ι -> α} {g : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) -> (forall {{i : ι}}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (g i) (f i))) -> (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s g)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.mono_on Set.PairwiseDisjoint.mono_onₓ'. -/
theorem PairwiseDisjoint.mono_on (hs : s.PairwiseDisjoint f) (h : ∀ ⦃i⦄, i ∈ s → g i ≤ f i) :
    s.PairwiseDisjoint g := fun a ha b hb hab => (hs ha hb hab).mono (h ha) (h hb)
#align set.pairwise_disjoint.mono_on Set.PairwiseDisjoint.mono_on

/- warning: set.pairwise_disjoint.mono -> Set.PairwiseDisjoint.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {f : ι -> α} {g : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) -> (LE.le.{max u2 u1} (ι -> α) (Pi.hasLe.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) g f) -> (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s g)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {f : ι -> α} {g : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) -> (LE.le.{max u2 u1} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))) g f) -> (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s g)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.mono Set.PairwiseDisjoint.monoₓ'. -/
theorem PairwiseDisjoint.mono (hs : s.PairwiseDisjoint f) (h : g ≤ f) : s.PairwiseDisjoint g :=
  hs.mono_on fun i _ => h i
#align set.pairwise_disjoint.mono Set.PairwiseDisjoint.mono

/- warning: set.pairwise_disjoint_empty -> Set.pairwiseDisjoint_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {f : ι -> α}, Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u2} (Set.{u2} ι) (Set.hasEmptyc.{u2} ι)) f
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {f : ι -> α}, Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u1} (Set.{u1} ι) (Set.instEmptyCollectionSet.{u1} ι)) f
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_empty Set.pairwiseDisjoint_emptyₓ'. -/
@[simp]
theorem pairwiseDisjoint_empty : (∅ : Set ι).PairwiseDisjoint f :=
  pairwise_empty _
#align set.pairwise_disjoint_empty Set.pairwiseDisjoint_empty

/- warning: set.pairwise_disjoint_singleton -> Set.pairwiseDisjoint_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] (i : ι) (f : ι -> α), Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Singleton.singleton.{u2, u2} ι (Set.{u2} ι) (Set.hasSingleton.{u2} ι) i) f
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] (i : ι) (f : ι -> α), Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.instSingletonSet.{u1} ι) i) f
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_singleton Set.pairwiseDisjoint_singletonₓ'. -/
@[simp]
theorem pairwiseDisjoint_singleton (i : ι) (f : ι → α) : PairwiseDisjoint {i} f :=
  pairwise_singleton i _
#align set.pairwise_disjoint_singleton Set.pairwiseDisjoint_singleton

/- warning: set.pairwise_disjoint_insert -> Set.pairwiseDisjoint_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {f : ι -> α} {i : ι}, Iff (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Insert.insert.{u2, u2} ι (Set.{u2} ι) (Set.hasInsert.{u2} ι) i s) f) (And (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) (forall (j : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j s) -> (Ne.{succ u2} ι i j) -> (Disjoint.{u1} α _inst_1 _inst_2 (f i) (f j))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {f : ι -> α} {i : ι}, Iff (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 (Insert.insert.{u1, u1} ι (Set.{u1} ι) (Set.instInsertSet.{u1} ι) i s) f) (And (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) (forall (j : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) j s) -> (Ne.{succ u1} ι i j) -> (Disjoint.{u2} α _inst_1 _inst_2 (f i) (f j))))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_insert Set.pairwiseDisjoint_insertₓ'. -/
theorem pairwiseDisjoint_insert {i : ι} :
    (insert i s).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧ ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j) :=
  Set.pairwise_insert_of_symmetric <| symmetric_disjoint.comap f
#align set.pairwise_disjoint_insert Set.pairwiseDisjoint_insert

#print Set.pairwiseDisjoint_insert_of_not_mem /-
theorem pairwiseDisjoint_insert_of_not_mem {i : ι} (hi : i ∉ s) :
    (insert i s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧ ∀ j ∈ s, Disjoint (f i) (f j) :=
  pairwise_insert_of_symmetric_of_not_mem (symmetric_disjoint.comap f) hi
#align set.pairwise_disjoint_insert_of_not_mem Set.pairwiseDisjoint_insert_of_not_mem
-/

/- warning: set.pairwise_disjoint.insert -> Set.PairwiseDisjoint.insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) -> (forall {i : ι}, (forall (j : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j s) -> (Ne.{succ u2} ι i j) -> (Disjoint.{u1} α _inst_1 _inst_2 (f i) (f j))) -> (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Insert.insert.{u2, u2} ι (Set.{u2} ι) (Set.hasInsert.{u2} ι) i s) f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) -> (forall {i : ι}, (forall (j : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) j s) -> (Ne.{succ u1} ι i j) -> (Disjoint.{u2} α _inst_1 _inst_2 (f i) (f j))) -> (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 (Insert.insert.{u1, u1} ι (Set.{u1} ι) (Set.instInsertSet.{u1} ι) i s) f))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.insert Set.PairwiseDisjoint.insertₓ'. -/
theorem PairwiseDisjoint.insert (hs : s.PairwiseDisjoint f) {i : ι}
    (h : ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  Set.pairwiseDisjoint_insert.2 ⟨hs, h⟩
#align set.pairwise_disjoint.insert Set.PairwiseDisjoint.insert

/- warning: set.pairwise_disjoint.insert_of_not_mem -> Set.PairwiseDisjoint.insert_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) -> (forall {i : ι}, (Not (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s)) -> (forall (j : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j s) -> (Disjoint.{u1} α _inst_1 _inst_2 (f i) (f j))) -> (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Insert.insert.{u2, u2} ι (Set.{u2} ι) (Set.hasInsert.{u2} ι) i s) f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) -> (forall {i : ι}, (Not (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s)) -> (forall (j : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) j s) -> (Disjoint.{u2} α _inst_1 _inst_2 (f i) (f j))) -> (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 (Insert.insert.{u1, u1} ι (Set.{u1} ι) (Set.instInsertSet.{u1} ι) i s) f))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.insert_of_not_mem Set.PairwiseDisjoint.insert_of_not_memₓ'. -/
theorem PairwiseDisjoint.insert_of_not_mem (hs : s.PairwiseDisjoint f) {i : ι} (hi : i ∉ s)
    (h : ∀ j ∈ s, Disjoint (f i) (f j)) : (insert i s).PairwiseDisjoint f :=
  (Set.pairwiseDisjoint_insert_of_not_mem hi).2 ⟨hs, h⟩
#align set.pairwise_disjoint.insert_of_not_mem Set.PairwiseDisjoint.insert_of_not_mem

/- warning: set.pairwise_disjoint.image_of_le -> Set.PairwiseDisjoint.image_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) -> (forall {g : ι -> ι}, (LE.le.{max u2 u1} (ι -> α) (Pi.hasLe.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Function.comp.{succ u2, succ u2, succ u1} ι ι α f g) f) -> (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Set.image.{u2, u2} ι ι g s) f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) -> (forall {g : ι -> ι}, (LE.le.{max u2 u1} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))) (Function.comp.{succ u1, succ u1, succ u2} ι ι α f g) f) -> (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 (Set.image.{u1, u1} ι ι g s) f))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.image_of_le Set.PairwiseDisjoint.image_of_leₓ'. -/
theorem PairwiseDisjoint.image_of_le (hs : s.PairwiseDisjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
    (g '' s).PairwiseDisjoint f :=
  by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  exact (hs ha hb <| ne_of_apply_ne _ h).mono (hg a) (hg b)
#align set.pairwise_disjoint.image_of_le Set.PairwiseDisjoint.image_of_le

#print Set.InjOn.pairwiseDisjoint_image /-
theorem InjOn.pairwiseDisjoint_image {g : ι' → ι} {s : Set ι'} (h : s.InjOn g) :
    (g '' s).PairwiseDisjoint f ↔ s.PairwiseDisjoint (f ∘ g) :=
  h.pairwise_image
#align set.inj_on.pairwise_disjoint_image Set.InjOn.pairwiseDisjoint_image
-/

#print Set.PairwiseDisjoint.range /-
theorem PairwiseDisjoint.range (g : s → ι) (hg : ∀ i : s, f (g i) ≤ f i)
    (ht : s.PairwiseDisjoint f) : (range g).PairwiseDisjoint f :=
  by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  exact (ht x.2 y.2 fun h => hxy <| congr_arg g <| Subtype.ext h).mono (hg x) (hg y)
#align set.pairwise_disjoint.range Set.PairwiseDisjoint.range
-/

/- warning: set.pairwise_disjoint_union -> Set.pairwiseDisjoint_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {t : Set.{u2} ι} {f : ι -> α}, Iff (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Union.union.{u2} (Set.{u2} ι) (Set.hasUnion.{u2} ι) s t) f) (And (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) (And (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 t f) (forall {{i : ι}}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (forall {{j : ι}}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j t) -> (Ne.{succ u2} ι i j) -> (Disjoint.{u1} α _inst_1 _inst_2 (f i) (f j))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {t : Set.{u1} ι} {f : ι -> α}, Iff (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 (Union.union.{u1} (Set.{u1} ι) (Set.instUnionSet.{u1} ι) s t) f) (And (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) (And (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 t f) (forall {{i : ι}}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (forall {{j : ι}}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) j t) -> (Ne.{succ u1} ι i j) -> (Disjoint.{u2} α _inst_1 _inst_2 (f i) (f j))))))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_union Set.pairwiseDisjoint_unionₓ'. -/
theorem pairwiseDisjoint_union :
    (s ∪ t).PairwiseDisjoint f ↔
      s.PairwiseDisjoint f ∧
        t.PairwiseDisjoint f ∧ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j) :=
  pairwise_union_of_symmetric <| symmetric_disjoint.comap f
#align set.pairwise_disjoint_union Set.pairwiseDisjoint_union

/- warning: set.pairwise_disjoint.union -> Set.PairwiseDisjoint.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {t : Set.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) -> (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 t f) -> (forall {{i : ι}}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (forall {{j : ι}}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j t) -> (Ne.{succ u2} ι i j) -> (Disjoint.{u1} α _inst_1 _inst_2 (f i) (f j)))) -> (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Union.union.{u2} (Set.{u2} ι) (Set.hasUnion.{u2} ι) s t) f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {t : Set.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) -> (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 t f) -> (forall {{i : ι}}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (forall {{j : ι}}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) j t) -> (Ne.{succ u1} ι i j) -> (Disjoint.{u2} α _inst_1 _inst_2 (f i) (f j)))) -> (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 (Union.union.{u1} (Set.{u1} ι) (Set.instUnionSet.{u1} ι) s t) f)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.union Set.PairwiseDisjoint.unionₓ'. -/
theorem PairwiseDisjoint.union (hs : s.PairwiseDisjoint f) (ht : t.PairwiseDisjoint f)
    (h : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → Disjoint (f i) (f j)) : (s ∪ t).PairwiseDisjoint f :=
  pairwiseDisjoint_union.2 ⟨hs, ht, h⟩
#align set.pairwise_disjoint.union Set.PairwiseDisjoint.union

/- warning: set.pairwise_disjoint_Union -> Set.pairwiseDisjoint_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {f : ι -> α} {g : ι' -> (Set.{u2} ι)}, (Directed.{u2, succ u3} (Set.{u2} ι) ι' (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι)) g) -> (Iff (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (Set.unionᵢ.{u2, succ u3} ι ι' (fun (n : ι') => g n)) f) (forall {{n : ι'}}, Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 (g n) f))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {ι' : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {f : ι -> α} {g : ι' -> (Set.{u3} ι)}, (Directed.{u3, succ u2} (Set.{u3} ι) ι' (fun (x._@.Mathlib.Data.Set.Pairwise._hyg.4274 : Set.{u3} ι) (x._@.Mathlib.Data.Set.Pairwise._hyg.4276 : Set.{u3} ι) => HasSubset.Subset.{u3} (Set.{u3} ι) (Set.instHasSubsetSet.{u3} ι) x._@.Mathlib.Data.Set.Pairwise._hyg.4274 x._@.Mathlib.Data.Set.Pairwise._hyg.4276) g) -> (Iff (Set.PairwiseDisjoint.{u1, u3} α ι _inst_1 _inst_2 (Set.unionᵢ.{u3, succ u2} ι ι' (fun (n : ι') => g n)) f) (forall {{n : ι'}}, Set.PairwiseDisjoint.{u1, u3} α ι _inst_1 _inst_2 (g n) f))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_Union Set.pairwiseDisjoint_unionᵢₓ'. -/
theorem pairwiseDisjoint_unionᵢ {g : ι' → Set ι} (h : Directed (· ⊆ ·) g) :
    (⋃ n, g n).PairwiseDisjoint f ↔ ∀ ⦃n⦄, (g n).PairwiseDisjoint f :=
  pairwise_unionᵢ h
#align set.pairwise_disjoint_Union Set.pairwiseDisjoint_unionᵢ

#print Set.pairwiseDisjoint_unionₛ /-
theorem pairwiseDisjoint_unionₛ {s : Set (Set ι)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).PairwiseDisjoint f ↔ ∀ ⦃a⦄, a ∈ s → Set.PairwiseDisjoint a f :=
  pairwise_unionₛ h
#align set.pairwise_disjoint_sUnion Set.pairwiseDisjoint_unionₛ
-/

/- warning: set.pairwise_disjoint.elim -> Set.PairwiseDisjoint.elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {s : Set.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι _inst_1 _inst_2 s f) -> (forall {i : ι} {j : ι}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j s) -> (Not (Disjoint.{u1} α _inst_1 _inst_2 (f i) (f j))) -> (Eq.{succ u2} ι i j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] {s : Set.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι _inst_1 _inst_2 s f) -> (forall {i : ι} {j : ι}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) j s) -> (Not (Disjoint.{u2} α _inst_1 _inst_2 (f i) (f j))) -> (Eq.{succ u1} ι i j))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.elim Set.PairwiseDisjoint.elimₓ'. -/
-- classical
theorem PairwiseDisjoint.elim (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : ¬Disjoint (f i) (f j)) : i = j :=
  hs.Eq hi hj h
#align set.pairwise_disjoint.elim Set.PairwiseDisjoint.elim

end PartialOrderBot

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {s t : Set ι} {f g : ι → α}

/- warning: set.pairwise_disjoint.elim' -> Set.PairwiseDisjoint.elim' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 s f) -> (forall {i : ι} {j : ι}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j s) -> (Ne.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (f i) (f j)) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) -> (Eq.{succ u2} ι i j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {s : Set.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι (SemilatticeInf.toPartialOrder.{u2} α _inst_1) _inst_2 s f) -> (forall {i : ι} {j : ι}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) j s) -> (Ne.{succ u2} α (HasInf.inf.{u2} α (SemilatticeInf.toHasInf.{u2} α _inst_1) (f i) (f j)) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2))) -> (Eq.{succ u1} ι i j))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.elim' Set.PairwiseDisjoint.elim'ₓ'. -/
-- classical
theorem PairwiseDisjoint.elim' (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : f i ⊓ f j ≠ ⊥) : i = j :=
  hs.elim hi hj fun hij => h hij.eq_bot
#align set.pairwise_disjoint.elim' Set.PairwiseDisjoint.elim'

/- warning: set.pairwise_disjoint.eq_of_le -> Set.PairwiseDisjoint.eq_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u2} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u2} α ι (SemilatticeInf.toPartialOrder.{u1} α _inst_1) _inst_2 s f) -> (forall {i : ι} {j : ι}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j s) -> (Ne.{succ u1} α (f i) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (f i) (f j)) -> (Eq.{succ u2} ι i j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {s : Set.{u1} ι} {f : ι -> α}, (Set.PairwiseDisjoint.{u2, u1} α ι (SemilatticeInf.toPartialOrder.{u2} α _inst_1) _inst_2 s f) -> (forall {i : ι} {j : ι}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) j s) -> (Ne.{succ u2} α (f i) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) (f i) (f j)) -> (Eq.{succ u1} ι i j))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.eq_of_le Set.PairwiseDisjoint.eq_of_leₓ'. -/
theorem PairwiseDisjoint.eq_of_le (hs : s.PairwiseDisjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hf : f i ≠ ⊥) (hij : f i ≤ f j) : i = j :=
  hs.elim' hi hj fun h => hf <| (inf_of_le_left hij).symm.trans h
#align set.pairwise_disjoint.eq_of_le Set.PairwiseDisjoint.eq_of_le

end SemilatticeInfBot

section CompleteLattice

variable [CompleteLattice α]

/- warning: set.pairwise_disjoint.bUnion -> Set.PairwiseDisjoint.bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u3} ι'} {g : ι' -> (Set.{u2} ι)} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u3} α ι' (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s (fun (i' : ι') => supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (g i')) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (g i')) => f i)))) -> (forall (i : ι'), (Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') i s) -> (Set.PairwiseDisjoint.{u1, u2} α ι (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (g i) f)) -> (Set.PairwiseDisjoint.{u1, u2} α ι (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (Set.unionᵢ.{u2, succ u3} ι ι' (fun (i : ι') => Set.unionᵢ.{u2, 0} ι (Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') i s) (fun (H : Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') i s) => g i))) f)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u3} ι'} {g : ι' -> (Set.{u2} ι)} {f : ι -> α}, (Set.PairwiseDisjoint.{u1, u3} α ι' (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s (fun (i' : ι') => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (g i')) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (g i')) => f i)))) -> (forall (i : ι'), (Membership.mem.{u3, u3} ι' (Set.{u3} ι') (Set.instMembershipSet.{u3} ι') i s) -> (Set.PairwiseDisjoint.{u1, u2} α ι (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (g i) f)) -> (Set.PairwiseDisjoint.{u1, u2} α ι (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (Set.unionᵢ.{u2, succ u3} ι ι' (fun (i : ι') => Set.unionᵢ.{u2, 0} ι (Membership.mem.{u3, u3} ι' (Set.{u3} ι') (Set.instMembershipSet.{u3} ι') i s) (fun (H : Membership.mem.{u3, u3} ι' (Set.{u3} ι') (Set.instMembershipSet.{u3} ι') i s) => g i))) f)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.bUnion Set.PairwiseDisjoint.bunionᵢₓ'. -/
/-- Bind operation for `set.pairwise_disjoint`. If you want to only consider finsets of indices, you
can use `set.pairwise_disjoint.bUnion_finset`. -/
theorem PairwiseDisjoint.bunionᵢ {s : Set ι'} {g : ι' → Set ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => ⨆ i ∈ g i', f i)
    (hg : ∀ i ∈ s, (g i).PairwiseDisjoint f) : (⋃ i ∈ s, g i).PairwiseDisjoint f :=
  by
  rintro a ha b hb hab
  simp_rw [Set.mem_unionᵢ] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (hcd.subst ha) hb hab
  · exact (hs hc hd <| ne_of_apply_ne _ hcd).mono (le_supᵢ₂ a ha) (le_supᵢ₂ b hb)
#align set.pairwise_disjoint.bUnion Set.PairwiseDisjoint.bunionᵢ

end CompleteLattice

/-! ### Pairwise disjoint set of sets -/


/- warning: set.pairwise_disjoint_range_singleton -> Set.pairwiseDisjoint_range_singleton is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}}, Set.PairwiseDisjoint.{u1, u1} (Set.{u1} ι) (Set.{u1} ι) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} ι) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.completeBooleanAlgebra.{u1} ι)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} ι) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} ι) (Set.booleanAlgebra.{u1} ι))) (Set.range.{u1, succ u1} (Set.{u1} ι) ι (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.hasSingleton.{u1} ι))) (id.{succ u1} (Set.{u1} ι))
but is expected to have type
  forall {ι : Type.{u1}}, Set.PairwiseDisjoint.{u1, u1} (Set.{u1} ι) (Set.{u1} ι) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} ι) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} ι) (Preorder.toLE.{u1} (Set.{u1} ι) (PartialOrder.toPreorder.{u1} (Set.{u1} ι) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} ι) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι)))))) (Set.range.{u1, succ u1} (Set.{u1} ι) ι (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.instSingletonSet.{u1} ι))) (id.{succ u1} (Set.{u1} ι))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_range_singleton Set.pairwiseDisjoint_range_singletonₓ'. -/
theorem pairwiseDisjoint_range_singleton :
    (Set.range (singleton : ι → Set ι)).PairwiseDisjoint id :=
  by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)
#align set.pairwise_disjoint_range_singleton Set.pairwiseDisjoint_range_singleton

/- warning: set.pairwise_disjoint_fiber -> Set.pairwiseDisjoint_fiber is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (f : ι -> α) (s : Set.{u1} α), Set.PairwiseDisjoint.{u2, u1} (Set.{u2} ι) α (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} ι) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} ι) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} ι) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} ι) (Set.completeBooleanAlgebra.{u2} ι)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} ι) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} ι) (Set.booleanAlgebra.{u2} ι))) s (fun (a : α) => Set.preimage.{u2, u1} ι α f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (f : ι -> α) (s : Set.{u2} α), Set.PairwiseDisjoint.{u1, u2} (Set.{u1} ι) α (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} ι) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} ι) (Preorder.toLE.{u1} (Set.{u1} ι) (PartialOrder.toPreorder.{u1} (Set.{u1} ι) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} ι) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι)))))) s (fun (a : α) => Set.preimage.{u1, u2} ι α f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_fiber Set.pairwiseDisjoint_fiberₓ'. -/
theorem pairwiseDisjoint_fiber (f : ι → α) (s : Set α) : s.PairwiseDisjoint fun a => f ⁻¹' {a} :=
  fun a _ b _ h => disjoint_iff_inf_le.mpr fun i ⟨hia, hib⟩ => h <| (Eq.symm hia).trans hib
#align set.pairwise_disjoint_fiber Set.pairwiseDisjoint_fiber

/- warning: set.pairwise_disjoint.elim_set -> Set.PairwiseDisjoint.elim_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s f) -> (forall {i : ι} {j : ι}, (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) j s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (f i)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (f j)) -> (Eq.{succ u2} ι i j)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s f) -> (forall {i : ι} {j : ι}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) j s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (f i)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (f j)) -> (Eq.{succ u2} ι i j)))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.elim_set Set.PairwiseDisjoint.elim_setₓ'. -/
-- classical
theorem PairwiseDisjoint.elim_set {s : Set ι} {f : ι → Set α} (hs : s.PairwiseDisjoint f) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj <| not_disjoint_iff.2 ⟨a, hai, haj⟩
#align set.pairwise_disjoint.elim_set Set.PairwiseDisjoint.elim_set

/- warning: set.bUnion_diff_bUnion_eq -> Set.bunionᵢ_diff_bunionᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {t : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Union.union.{u2} (Set.{u2} ι) (Set.hasUnion.{u2} ι) s t) f) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => f i)))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (SDiff.sdiff.{u2} (Set.{u2} ι) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} ι) (Set.booleanAlgebra.{u2} ι)) s t)) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i (SDiff.sdiff.{u2} (Set.{u2} ι) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} ι) (Set.booleanAlgebra.{u2} ι)) s t)) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {t : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Union.union.{u2} (Set.{u2} ι) (Set.instUnionSet.{u2} ι) s t) f) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) => f i)))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (SDiff.sdiff.{u2} (Set.{u2} ι) (Set.instSDiffSet.{u2} ι) s t)) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (SDiff.sdiff.{u2} (Set.{u2} ι) (Set.instSDiffSet.{u2} ι) s t)) => f i))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_diff_bUnion_eq Set.bunionᵢ_diff_bunionᵢ_eqₓ'. -/
theorem bunionᵢ_diff_bunionᵢ_eq {s t : Set ι} {f : ι → Set α} (h : (s ∪ t).PairwiseDisjoint f) :
    ((⋃ i ∈ s, f i) \ ⋃ i ∈ t, f i) = ⋃ i ∈ s \ t, f i :=
  by
  refine'
    (bUnion_diff_bUnion_subset f s t).antisymm
      (Union₂_subset fun i hi a ha => (mem_diff _).2 ⟨mem_bUnion hi.1 ha, _⟩)
  rw [mem_Union₂]; rintro ⟨j, hj, haj⟩
  exact (h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩
#align set.bUnion_diff_bUnion_eq Set.bunionᵢ_diff_bunionᵢ_eq

/- warning: set.bUnion_eq_sigma_of_disjoint -> Set.bunionᵢEqSigmaOfDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s f) -> (Equiv.{succ u1, max (succ u2) (succ u1)} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i)))) (Sigma.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s f) -> (Equiv.{succ u1, max (succ u1) (succ u2)} (Set.Elem.{u1} α (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i)))) (Sigma.{u2, u1} (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => Set.Elem.{u1} α (f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i)))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_eq_sigma_of_disjoint Set.bunionᵢEqSigmaOfDisjointₓ'. -/
/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def bunionᵢEqSigmaOfDisjoint {s : Set ι} {f : ι → Set α} (h : s.PairwiseDisjoint f) :
    (⋃ i ∈ s, f i) ≃ Σi : s, f i :=
  (Equiv.setCongr (bunionᵢ_eq_unionᵢ _ _)).trans <|
    unionEqSigmaOfDisjoint fun ⟨i, hi⟩ ⟨j, hj⟩ ne => h hi hj fun eq => Ne <| Subtype.eq Eq
#align set.bUnion_eq_sigma_of_disjoint Set.bunionᵢEqSigmaOfDisjoint

/- warning: set.pairwise_disjoint_image_right_iff -> Set.pairwiseDisjoint_image_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Function.Injective.{succ u2, succ u3} β γ (f a))) -> (Iff (Set.PairwiseDisjoint.{u3, u1} (Set.{u3} γ) α (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} γ) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} γ) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} γ) (Set.completeBooleanAlgebra.{u3} γ)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u3} (Set.{u3} γ) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u3} (Set.{u3} γ) (Set.booleanAlgebra.{u3} γ))) s (fun (a : α) => Set.image.{u2, u3} β γ (f a) t)) (Set.InjOn.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)) (Set.prod.{u1, u2} α β s t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β}, (forall (a : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a s) -> (Function.Injective.{succ u2, succ u1} β γ (f a))) -> (Iff (Set.PairwiseDisjoint.{u1, u3} (Set.{u1} γ) α (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} γ) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} γ) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} γ) (Set.instCompleteBooleanAlgebraSet.{u1} γ)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} γ) (Preorder.toLE.{u1} (Set.{u1} γ) (PartialOrder.toPreorder.{u1} (Set.{u1} γ) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} γ) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} γ) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} γ) (Set.instCompleteBooleanAlgebraSet.{u1} γ)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} γ) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} γ) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} γ) (Set.instCompleteBooleanAlgebraSet.{u1} γ)))))) s (fun (a : α) => Set.image.{u2, u1} β γ (f a) t)) (Set.InjOn.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)) (Set.prod.{u3, u2} α β s t)))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_image_right_iff Set.pairwiseDisjoint_image_right_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
theorem pairwiseDisjoint_image_right_iff {f : α → β → γ} {s : Set α} {t : Set β}
    (hf : ∀ a ∈ s, Injective (f a)) :
    (s.PairwiseDisjoint fun a => f a '' t) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 :=
  by
  refine' ⟨fun hs x hx y hy (h : f _ _ = _) => _, fun hs x hx y hy h => _⟩
  · suffices x.1 = y.1 by exact Prod.ext this (hf _ hx.1 <| h.trans <| by rw [this])
    refine' hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, _⟩)
    rw [h]
    exact mem_image_of_mem _ hy.2
  · refine' disjoint_iff_inf_le.mpr _
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.fst <| hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab)
#align set.pairwise_disjoint_image_right_iff Set.pairwiseDisjoint_image_right_iff

/- warning: set.pairwise_disjoint_image_left_iff -> Set.pairwiseDisjoint_image_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, (forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (Function.Injective.{succ u1, succ u3} α γ (fun (a : α) => f a b))) -> (Iff (Set.PairwiseDisjoint.{u3, u2} (Set.{u3} γ) β (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} γ) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} γ) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} γ) (Set.completeBooleanAlgebra.{u3} γ)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u3} (Set.{u3} γ) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u3} (Set.{u3} γ) (Set.booleanAlgebra.{u3} γ))) t (fun (b : β) => Set.image.{u1, u3} α γ (fun (a : α) => f a b) s)) (Set.InjOn.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)) (Set.prod.{u1, u2} α β s t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β}, (forall (b : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) -> (Function.Injective.{succ u3, succ u1} α γ (fun (a : α) => f a b))) -> (Iff (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} γ) β (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} γ) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} γ) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} γ) (Set.instCompleteBooleanAlgebraSet.{u1} γ)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} γ) (Preorder.toLE.{u1} (Set.{u1} γ) (PartialOrder.toPreorder.{u1} (Set.{u1} γ) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} γ) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} γ) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} γ) (Set.instCompleteBooleanAlgebraSet.{u1} γ)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} γ) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} γ) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} γ) (Set.instCompleteBooleanAlgebraSet.{u1} γ)))))) t (fun (b : β) => Set.image.{u3, u1} α γ (fun (a : α) => f a b) s)) (Set.InjOn.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)) (Set.prod.{u3, u2} α β s t)))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_image_left_iff Set.pairwiseDisjoint_image_left_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
theorem pairwiseDisjoint_image_left_iff {f : α → β → γ} {s : Set α} {t : Set β}
    (hf : ∀ b ∈ t, Injective fun a => f a b) :
    (t.PairwiseDisjoint fun b => (fun a => f a b) '' s) ↔ (s ×ˢ t).InjOn fun p => f p.1 p.2 :=
  by
  refine' ⟨fun ht x hx y hy (h : f _ _ = _) => _, fun ht x hx y hy h => _⟩
  · suffices x.2 = y.2 by exact Prod.ext (hf _ hx.2 <| h.trans <| by rw [this]) this
    refine' ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, _⟩)
    rw [h]
    exact mem_image_of_mem _ hy.1
  · refine' disjoint_iff_inf_le.mpr _
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩
    exact h (congr_arg Prod.snd <| ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab)
#align set.pairwise_disjoint_image_left_iff Set.pairwiseDisjoint_image_left_iff

end Set

/- warning: pairwise_disjoint_fiber -> pairwise_disjoint_fiber is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (f : ι -> α), Pairwise.{u1} α (Function.onFun.{succ u1, succ u2, 1} α (Set.{u2} ι) Prop (Disjoint.{u2} (Set.{u2} ι) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} ι) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} ι) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} ι) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} ι) (Set.completeBooleanAlgebra.{u2} ι)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} ι) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} ι) (Set.booleanAlgebra.{u2} ι)))) (fun (a : α) => Set.preimage.{u2, u1} ι α f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (f : ι -> α), Pairwise.{u2} α (Function.onFun.{succ u2, succ u1, 1} α (Set.{u1} ι) Prop (Disjoint.{u1} (Set.{u1} ι) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} ι) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} ι) (Preorder.toLE.{u1} (Set.{u1} ι) (PartialOrder.toPreorder.{u1} (Set.{u1} ι) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} ι) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} ι) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} ι) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} ι) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} ι) (Set.instCompleteBooleanAlgebraSet.{u1} ι))))))) (fun (a : α) => Set.preimage.{u1, u2} ι α f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a)))
Case conversion may be inaccurate. Consider using '#align pairwise_disjoint_fiber pairwise_disjoint_fiberₓ'. -/
theorem pairwise_disjoint_fiber (f : ι → α) : Pairwise (Disjoint on fun a : α => f ⁻¹' {a}) :=
  Set.pairwise_univ.1 <| Set.pairwiseDisjoint_fiber f univ
#align pairwise_disjoint_fiber pairwise_disjoint_fiber

section

variable {f : ι → Set α} {s t : Set ι}

/- warning: set.pairwise_disjoint.subset_of_bUnion_subset_bUnion -> Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)} {s : Set.{u2} ι} {t : Set.{u2} ι}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Union.union.{u2} (Set.{u2} ι) (Set.hasUnion.{u2} ι) s t) f) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Set.Nonempty.{u1} α (f i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => f i)))) -> (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) s t)
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {f : ι -> (Set.{u2} α)} {s : Set.{u1} ι} {t : Set.{u1} ι}, (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Union.union.{u1} (Set.{u1} ι) (Set.instUnionSet.{u1} ι) s t) f) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (Set.Nonempty.{u2} α (f i))) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) => f i))) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i t) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i t) => f i)))) -> (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) s t)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.subset_of_bUnion_subset_bUnion Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢₓ'. -/
theorem Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢ (h₀ : (s ∪ t).PairwiseDisjoint f)
    (h₁ : ∀ i ∈ s, (f i).Nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) : s ⊆ t :=
  by
  rintro i hi
  obtain ⟨a, hai⟩ := h₁ i hi
  obtain ⟨j, hj, haj⟩ := mem_Union₂.1 (h <| mem_Union₂_of_mem hi hai)
  rwa [h₀.eq (subset_union_left _ _ hi) (subset_union_right _ _ hj)
      (not_disjoint_iff.2 ⟨a, hai, haj⟩)]
#align set.pairwise_disjoint.subset_of_bUnion_subset_bUnion Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢ

/- warning: pairwise.subset_of_bUnion_subset_bUnion -> Pairwise.subset_of_bunionᵢ_subset_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)} {s : Set.{u2} ι} {t : Set.{u2} ι}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Set.Nonempty.{u1} α (f i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => f i)))) -> (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) s t)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)} {s : Set.{u2} ι} {t : Set.{u2} ι}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Set.Nonempty.{u1} α (f i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) => f i)))) -> (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.instHasSubsetSet.{u2} ι) s t)
Case conversion may be inaccurate. Consider using '#align pairwise.subset_of_bUnion_subset_bUnion Pairwise.subset_of_bunionᵢ_subset_bunionᵢₓ'. -/
theorem Pairwise.subset_of_bunionᵢ_subset_bunionᵢ (h₀ : Pairwise (Disjoint on f))
    (h₁ : ∀ i ∈ s, (f i).Nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) : s ⊆ t :=
  Set.PairwiseDisjoint.subset_of_bunionᵢ_subset_bunionᵢ (h₀.set_pairwise _) h₁ h
#align pairwise.subset_of_bUnion_subset_bUnion Pairwise.subset_of_bunionᵢ_subset_bunionᵢ

/- warning: pairwise.bUnion_injective -> Pairwise.bunionᵢ_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (forall (i : ι), Set.Nonempty.{u1} α (f i)) -> (Function.Injective.{succ u2, succ u1} (Set.{u2} ι) (Set.{u1} α) (fun (s : Set.{u2} ι) => Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (forall (i : ι), Set.Nonempty.{u1} α (f i)) -> (Function.Injective.{succ u2, succ u1} (Set.{u2} ι) (Set.{u1} α) (fun (s : Set.{u2} ι) => Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align pairwise.bUnion_injective Pairwise.bunionᵢ_injectiveₓ'. -/
theorem Pairwise.bunionᵢ_injective (h₀ : Pairwise (Disjoint on f)) (h₁ : ∀ i, (f i).Nonempty) :
    Injective fun s : Set ι => ⋃ i ∈ s, f i := fun s t h =>
  ((h₀.subset_of_bunionᵢ_subset_bunionᵢ fun _ _ => h₁ _) <| h.Subset).antisymm <|
    (h₀.subset_of_bunionᵢ_subset_bunionᵢ fun _ _ => h₁ _) <| h.Superset
#align pairwise.bUnion_injective Pairwise.bunionᵢ_injective

end

