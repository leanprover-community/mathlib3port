/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.semiquot
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Lattice

/-! # Semiquotients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A data type for semiquotients, which are classically equivalent to
nonempty sets, but are useful for programming; the idea is that
a semiquotient set `S` represents some (particular but unknown)
element of `S`. This can be used to model nondeterministic functions,
which return something in a range of values (represented by the
predicate `S`) but are not completely determined.
-/


/-- A member of `semiquot α` is classically a nonempty `set α`,
  and in the VM is represented by an element of `α`; the relation
  between these is that the VM element is required to be a member
  of the set `s`. The specific element of `s` that the VM computes
  is hidden by a quotient construction, allowing for the representation
  of nondeterministic functions. -/
structure Semiquot.{u} (α : Type _) where mk' ::
  s : Set α
  val : Trunc ↥s
#align semiquot Semiquotₓ

namespace Semiquot

variable {α : Type _} {β : Type _}

instance : Membership α (Semiquot α) :=
  ⟨fun a q => a ∈ q.s⟩

/- warning: semiquot.mk -> Semiquot.mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {s : Set.{u_1} α}, (Membership.Mem.{u_1, u_1} α (Set.{u_1} α) (Set.hasMem.{u_1} α) a s) -> (Semiquotₓ.{u_2, u_1} α)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {s : Set.{u_1} α}, (Membership.mem.{u_1, u_1} α (Set.{u_1} α) (Set.instMembershipSet.{u_1} α) a s) -> (Semiquot.{u_1} α)
Case conversion may be inaccurate. Consider using '#align semiquot.mk Semiquot.mkₓ'. -/
/-- Construct a `semiquot α` from `h : a ∈ s` where `s : set α`. -/
def mk {a : α} {s : Set α} (h : a ∈ s) : Semiquot α :=
  ⟨s, Trunc.mk ⟨a, h⟩⟩
#align semiquot.mk Semiquot.mk

/- warning: semiquot.ext_s -> Semiquot.ext_s is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {q₁ : Semiquotₓ.{u_2, u_1} α} {q₂ : Semiquotₓ.{u_2, u_1} α}, Iff (Eq.{succ u_1} (Semiquotₓ.{u_2, u_1} α) q₁ q₂) (Eq.{max (succ u_1) 1} (Set.{u_1} α) (Semiquotₓ.s.{u_2, u_1} α q₁) (Semiquotₓ.s.{u_2, u_1} α q₂))
but is expected to have type
  forall {α : Type.{u_1}} {q₁ : Semiquot.{u_1} α} {q₂ : Semiquot.{u_1} α}, Iff (Eq.{succ u_1} (Semiquot.{u_1} α) q₁ q₂) (Eq.{succ u_1} (Set.{u_1} α) (Semiquot.s.{u_1} α q₁) (Semiquot.s.{u_1} α q₂))
Case conversion may be inaccurate. Consider using '#align semiquot.ext_s Semiquot.ext_sₓ'. -/
theorem ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s :=
  by
  refine' ⟨congr_arg _, fun h => _⟩
  cases q₁
  cases q₂
  cc
#align semiquot.ext_s Semiquot.ext_s

/- warning: semiquot.ext -> Semiquot.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {q₁ : Semiquotₓ.{u_2, u_1} α} {q₂ : Semiquotₓ.{u_2, u_1} α}, Iff (Eq.{succ u_1} (Semiquotₓ.{u_2, u_1} α) q₁ q₂) (forall (a : α), Iff (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a q₁) (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a q₂))
but is expected to have type
  forall {α : Type.{u_1}} {q₁ : Semiquot.{u_1} α} {q₂ : Semiquot.{u_1} α}, Iff (Eq.{succ u_1} (Semiquot.{u_1} α) q₁ q₂) (forall (a : α), Iff (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q₁) (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q₂))
Case conversion may be inaccurate. Consider using '#align semiquot.ext Semiquot.extₓ'. -/
theorem ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ ∀ a, a ∈ q₁ ↔ a ∈ q₂ :=
  ext_s.trans Set.ext_iff
#align semiquot.ext Semiquot.ext

/- warning: semiquot.exists_mem -> Semiquot.exists_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (q : Semiquotₓ.{u_2, u_1} α), Exists.{succ u_1} α (fun (a : α) => Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a q)
but is expected to have type
  forall {α : Type.{u_1}} (q : Semiquot.{u_1} α), Exists.{succ u_1} α (fun (a : α) => Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q)
Case conversion may be inaccurate. Consider using '#align semiquot.exists_mem Semiquot.exists_memₓ'. -/
theorem exists_mem (q : Semiquot α) : ∃ a, a ∈ q :=
  let ⟨⟨a, h⟩, h₂⟩ := q.2.exists_rep
  ⟨a, h⟩
#align semiquot.exists_mem Semiquot.exists_mem

/- warning: semiquot.eq_mk_of_mem -> Semiquot.eq_mk_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {q : Semiquotₓ.{u_2, u_1} α} {a : α} (h : Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a q), Eq.{succ u_1} (Semiquotₓ.{u_2, u_1} α) q (Semiquot.mk.{u_1, u_2} α a (Semiquotₓ.s.{u_2, u_1} α q) h)
but is expected to have type
  forall {α : Type.{u_1}} {q : Semiquot.{u_1} α} {a : α} (h : Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q), Eq.{succ u_1} (Semiquot.{u_1} α) q (Semiquot.mk.{u_1} α a (Semiquot.s.{u_1} α q) h)
Case conversion may be inaccurate. Consider using '#align semiquot.eq_mk_of_mem Semiquot.eq_mk_of_memₓ'. -/
theorem eq_mk_of_mem {q : Semiquot α} {a : α} (h : a ∈ q) : q = @mk _ a q.1 h :=
  ext_s.2 rfl
#align semiquot.eq_mk_of_mem Semiquot.eq_mk_of_mem

/- warning: semiquot.nonempty -> Semiquot.nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (q : Semiquotₓ.{u_2, u_1} α), Set.Nonempty.{u_1} α (Semiquotₓ.s.{u_2, u_1} α q)
but is expected to have type
  forall {α : Type.{u_1}} (q : Semiquot.{u_1} α), Set.Nonempty.{u_1} α (Semiquot.s.{u_1} α q)
Case conversion may be inaccurate. Consider using '#align semiquot.nonempty Semiquot.nonemptyₓ'. -/
theorem nonempty (q : Semiquot α) : q.s.Nonempty :=
  q.exists_mem
#align semiquot.nonempty Semiquot.nonempty

/- warning: semiquot.pure -> Semiquot.pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, α -> (Semiquotₓ.{u_2, u_1} α)
but is expected to have type
  forall {α : Type.{u_1}}, α -> (Semiquot.{u_1} α)
Case conversion may be inaccurate. Consider using '#align semiquot.pure Semiquot.pureₓ'. -/
/-- `pure a` is `a` reinterpreted as an unspecified element of `{a}`. -/
protected def pure (a : α) : Semiquot α :=
  mk (Set.mem_singleton a)
#align semiquot.pure Semiquot.pure

/- warning: semiquot.mem_pure' -> Semiquot.mem_pure' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α}, Iff (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a (Semiquot.pure.{u_1, u_2} α b)) (Eq.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α}, Iff (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a (Semiquot.pure.{u_1} α b)) (Eq.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align semiquot.mem_pure' Semiquot.mem_pure'ₓ'. -/
@[simp]
theorem mem_pure' {a b : α} : a ∈ Semiquot.pure b ↔ a = b :=
  Set.mem_singleton_iff
#align semiquot.mem_pure' Semiquot.mem_pure'

/- warning: semiquot.blur' -> Semiquot.blur' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (q : Semiquotₓ.{u_2, u_1} α) {s : Set.{u_1} α}, (HasSubset.Subset.{u_1} (Set.{u_1} α) (Set.hasSubset.{u_1} α) (Semiquotₓ.s.{u_2, u_1} α q) s) -> (Semiquotₓ.{u_3, u_1} α)
but is expected to have type
  forall {α : Type.{u_1}} (q : Semiquot.{u_1} α) {s : Set.{u_1} α}, (HasSubset.Subset.{u_1} (Set.{u_1} α) (Set.instHasSubsetSet_1.{u_1} α) (Semiquot.s.{u_1} α q) s) -> (Semiquot.{u_1} α)
Case conversion may be inaccurate. Consider using '#align semiquot.blur' Semiquot.blur'ₓ'. -/
/-- Replace `s` in a `semiquot` with a superset. -/
def blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) : Semiquot α :=
  ⟨s, Trunc.lift (fun a : q.s => Trunc.mk ⟨a.1, h a.2⟩) (fun _ _ => Trunc.eq _ _) q.2⟩
#align semiquot.blur' Semiquot.blur'

/- warning: semiquot.blur -> Semiquot.blur is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, (Set.{u_1} α) -> (Semiquotₓ.{u_2, u_1} α) -> (Semiquotₓ.{u_3, u_1} α)
but is expected to have type
  forall {α : Type.{u_1}}, (Set.{u_1} α) -> (Semiquot.{u_1} α) -> (Semiquot.{u_1} α)
Case conversion may be inaccurate. Consider using '#align semiquot.blur Semiquot.blurₓ'. -/
/-- Replace `s` in a `q : semiquot α` with a union `s ∪ q.s` -/
def blur (s : Set α) (q : Semiquot α) : Semiquot α :=
  blur' q (Set.subset_union_right s q.s)
#align semiquot.blur Semiquot.blur

/- warning: semiquot.blur_eq_blur' -> Semiquot.blur_eq_blur' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (q : Semiquotₓ.{u_2, u_1} α) (s : Set.{u_1} α) (h : HasSubset.Subset.{u_1} (Set.{u_1} α) (Set.hasSubset.{u_1} α) (Semiquotₓ.s.{u_2, u_1} α q) s), Eq.{succ u_1} (Semiquotₓ.{u_3, u_1} α) (Semiquot.blur.{u_1, u_2, u_3} α s q) (Semiquot.blur'.{u_1, u_2, u_3} α q s h)
but is expected to have type
  forall {α : Type.{u_1}} (q : Semiquot.{u_1} α) (s : Set.{u_1} α) (h : HasSubset.Subset.{u_1} (Set.{u_1} α) (Set.instHasSubsetSet_1.{u_1} α) (Semiquot.s.{u_1} α q) s), Eq.{succ u_1} (Semiquot.{u_1} α) (Semiquot.blur.{u_1} α s q) (Semiquot.blur'.{u_1} α q s h)
Case conversion may be inaccurate. Consider using '#align semiquot.blur_eq_blur' Semiquot.blur_eq_blur'ₓ'. -/
theorem blur_eq_blur' (q : Semiquot α) (s : Set α) (h : q.s ⊆ s) : blur s q = blur' q h := by
  unfold blur <;> congr <;> exact Set.union_eq_self_of_subset_right h
#align semiquot.blur_eq_blur' Semiquot.blur_eq_blur'

/- warning: semiquot.mem_blur' -> Semiquot.mem_blur' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (q : Semiquotₓ.{u_2, u_1} α) {s : Set.{u_1} α} (h : HasSubset.Subset.{u_1} (Set.{u_1} α) (Set.hasSubset.{u_1} α) (Semiquotₓ.s.{u_2, u_1} α q) s) {a : α}, Iff (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) a (Semiquot.blur'.{u_1, u_2, u_3} α q s h)) (Membership.Mem.{u_1, u_1} α (Set.{u_1} α) (Set.hasMem.{u_1} α) a s)
but is expected to have type
  forall {α : Type.{u_1}} (q : Semiquot.{u_1} α) {s : Set.{u_1} α} (h : HasSubset.Subset.{u_1} (Set.{u_1} α) (Set.instHasSubsetSet_1.{u_1} α) (Semiquot.s.{u_1} α q) s) {a : α}, Iff (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a (Semiquot.blur'.{u_1} α q s h)) (Membership.mem.{u_1, u_1} α (Set.{u_1} α) (Set.instMembershipSet.{u_1} α) a s)
Case conversion may be inaccurate. Consider using '#align semiquot.mem_blur' Semiquot.mem_blur'ₓ'. -/
@[simp]
theorem mem_blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) {a : α} : a ∈ blur' q h ↔ a ∈ s :=
  Iff.rfl
#align semiquot.mem_blur' Semiquot.mem_blur'

/- warning: semiquot.of_trunc -> Semiquot.ofTrunc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, (Trunc.{succ u_1} α) -> (Semiquotₓ.{u_2, u_1} α)
but is expected to have type
  forall {α : Type.{u_1}}, (Trunc.{succ u_1} α) -> (Semiquot.{u_1} α)
Case conversion may be inaccurate. Consider using '#align semiquot.of_trunc Semiquot.ofTruncₓ'. -/
/-- Convert a `trunc α` to a `semiquot α`. -/
def ofTrunc (q : Trunc α) : Semiquot α :=
  ⟨Set.univ, q.map fun a => ⟨a, trivial⟩⟩
#align semiquot.of_trunc Semiquot.ofTrunc

/- warning: semiquot.to_trunc -> Semiquot.toTrunc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, (Semiquotₓ.{u_2, u_1} α) -> (Trunc.{succ u_1} α)
but is expected to have type
  forall {α : Type.{u_1}}, (Semiquot.{u_1} α) -> (Trunc.{succ u_1} α)
Case conversion may be inaccurate. Consider using '#align semiquot.to_trunc Semiquot.toTruncₓ'. -/
/-- Convert a `semiquot α` to a `trunc α`. -/
def toTrunc (q : Semiquot α) : Trunc α :=
  q.2.map Subtype.val
#align semiquot.to_trunc Semiquot.toTrunc

/- warning: semiquot.lift_on -> Semiquot.liftOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (q : Semiquotₓ.{u_3, u_1} α) (f : α -> β), (forall (a : α), (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) a q) -> (forall (b : α), (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) b q) -> (Eq.{succ u_2} β (f a) (f b)))) -> β
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (q : Semiquot.{u_1} α) (f : α -> β), (forall (a : α), (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q) -> (forall (b : α), (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) b q) -> (Eq.{succ u_2} β (f a) (f b)))) -> β
Case conversion may be inaccurate. Consider using '#align semiquot.lift_on Semiquot.liftOnₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a b «expr ∈ » q) -/
/-- If `f` is a constant on `q.s`, then `q.lift_on f` is the value of `f`
at any point of `q`. -/
def liftOn (q : Semiquot α) (f : α → β) (h : ∀ (a) (_ : a ∈ q) (b) (_ : b ∈ q), f a = f b) : β :=
  Trunc.liftOn q.2 (fun x => f x.1) fun x y => h _ x.2 _ y.2
#align semiquot.lift_on Semiquot.liftOn

/- warning: semiquot.lift_on_of_mem -> Semiquot.liftOn_ofMem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (q : Semiquotₓ.{u_3, u_1} α) (f : α -> β) (h : forall (a : α), (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) a q) -> (forall (b : α), (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) b q) -> (Eq.{succ u_2} β (f a) (f b)))) (a : α), (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) a q) -> (Eq.{succ u_2} β (Semiquot.liftOn.{u_1, u_2, u_3} α β q f h) (f a))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (q : Semiquot.{u_1} α) (f : α -> β) (h : forall (a : α), (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q) -> (forall (b : α), (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) b q) -> (Eq.{succ u_2} β (f a) (f b)))) (a : α), (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q) -> (Eq.{succ u_2} β (Semiquot.liftOn.{u_1, u_2} α β q f h) (f a))
Case conversion may be inaccurate. Consider using '#align semiquot.lift_on_of_mem Semiquot.liftOn_ofMemₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a b «expr ∈ » q) -/
theorem liftOn_ofMem (q : Semiquot α) (f : α → β) (h : ∀ (a) (_ : a ∈ q) (b) (_ : b ∈ q), f a = f b)
    (a : α) (aq : a ∈ q) : liftOn q f h = f a := by
  revert h <;> rw [eq_mk_of_mem aq] <;> intro <;> rfl
#align semiquot.lift_on_of_mem Semiquot.liftOn_ofMem

/- warning: semiquot.map -> Semiquot.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, (α -> β) -> (Semiquotₓ.{u_3, u_1} α) -> (Semiquotₓ.{u_4, u_2} β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, (α -> β) -> (Semiquot.{u_1} α) -> (Semiquot.{u_2} β)
Case conversion may be inaccurate. Consider using '#align semiquot.map Semiquot.mapₓ'. -/
/-- Apply a function to the unknown value stored in a `semiquot α`. -/
def map (f : α → β) (q : Semiquot α) : Semiquot β :=
  ⟨f '' q.1, q.2.map fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩⟩
#align semiquot.map Semiquot.map

/- warning: semiquot.mem_map -> Semiquot.mem_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (q : Semiquotₓ.{u_3, u_1} α) (b : β), Iff (Membership.Mem.{u_2, u_2} β (Semiquotₓ.{u_4, u_2} β) (Semiquotₓ.hasMem.{u_2, u_4} β) b (Semiquot.map.{u_1, u_2, u_3, u_4} α β f q)) (Exists.{succ u_1} α (fun (a : α) => And (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) a q) (Eq.{succ u_2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (q : Semiquot.{u_1} α) (b : β), Iff (Membership.mem.{u_2, u_2} β (Semiquot.{u_2} β) (Semiquot.instMembershipSemiquot.{u_2} β) b (Semiquot.map.{u_1, u_2} α β f q)) (Exists.{succ u_1} α (fun (a : α) => And (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q) (Eq.{succ u_2} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align semiquot.mem_map Semiquot.mem_mapₓ'. -/
@[simp]
theorem mem_map (f : α → β) (q : Semiquot α) (b : β) : b ∈ map f q ↔ ∃ a, a ∈ q ∧ f a = b :=
  Set.mem_image _ _ _
#align semiquot.mem_map Semiquot.mem_map

/- warning: semiquot.bind -> Semiquot.bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, (Semiquotₓ.{u_3, u_1} α) -> (α -> (Semiquotₓ.{u_4, u_2} β)) -> (Semiquotₓ.{u_5, u_2} β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, (Semiquot.{u_1} α) -> (α -> (Semiquot.{u_2} β)) -> (Semiquot.{u_2} β)
Case conversion may be inaccurate. Consider using '#align semiquot.bind Semiquot.bindₓ'. -/
/-- Apply a function returning a `semiquot` to a `semiquot`. -/
def bind (q : Semiquot α) (f : α → Semiquot β) : Semiquot β :=
  ⟨⋃ a ∈ q.1, (f a).1, q.2.bind fun a => (f a.1).2.map fun b => ⟨b.1, Set.mem_bunionᵢ a.2 b.2⟩⟩
#align semiquot.bind Semiquot.bind

/- warning: semiquot.mem_bind -> Semiquot.mem_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (q : Semiquotₓ.{u_3, u_1} α) (f : α -> (Semiquotₓ.{u_4, u_2} β)) (b : β), Iff (Membership.Mem.{u_2, u_2} β (Semiquotₓ.{u_5, u_2} β) (Semiquotₓ.hasMem.{u_2, u_5} β) b (Semiquot.bind.{u_1, u_2, u_3, u_4, u_5} α β q f)) (Exists.{succ u_1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) a q) (fun (H : Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_3, u_1} α) (Semiquotₓ.hasMem.{u_1, u_3} α) a q) => Membership.Mem.{u_2, u_2} β (Semiquotₓ.{u_4, u_2} β) (Semiquotₓ.hasMem.{u_2, u_4} β) b (f a))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (q : Semiquot.{u_1} α) (f : α -> (Semiquot.{u_2} β)) (b : β), Iff (Membership.mem.{u_2, u_2} β (Semiquot.{u_2} β) (Semiquot.instMembershipSemiquot.{u_2} β) b (Semiquot.bind.{u_1, u_2} α β q f)) (Exists.{succ u_1} α (fun (a : α) => And (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a q) (Membership.mem.{u_2, u_2} β (Semiquot.{u_2} β) (Semiquot.instMembershipSemiquot.{u_2} β) b (f a))))
Case conversion may be inaccurate. Consider using '#align semiquot.mem_bind Semiquot.mem_bindₓ'. -/
@[simp]
theorem mem_bind (q : Semiquot α) (f : α → Semiquot β) (b : β) : b ∈ bind q f ↔ ∃ a ∈ q, b ∈ f a :=
  Set.mem_unionᵢ₂
#align semiquot.mem_bind Semiquot.mem_bind

instance : Monad Semiquot where
  pure := @Semiquot.pure
  map := @Semiquot.map
  bind := @Semiquot.bind

/- warning: semiquot.map_def -> Semiquot.map_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}}, Eq.{succ u_1} ((α -> β) -> (Semiquotₓ.{u_2, u_1} α) -> (Semiquotₓ.{u_2, u_1} β)) (Functor.map.{u_1, u_1} (fun {α : Type.{u_1}} => Semiquotₓ.{u_2, u_1} α) (Applicative.toFunctor.{u_1, u_1} (fun {α : Type.{u_1}} => Semiquotₓ.{u_2, u_1} α) (Monad.toApplicative.{u_1, u_1} (fun {α : Type.{u_1}} => Semiquotₓ.{u_2, u_1} α) Semiquotₓ.monad.{u_1, u_2})) α β) (Semiquot.map.{u_1, u_1, u_2, u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_1}}, Eq.{succ u_1} ((α -> β) -> (Semiquot.{u_1} α) -> (Semiquot.{u_1} β)) (fun (x._@.Mathlib.Data.Semiquot._hyg.993 : α -> β) (x._@.Mathlib.Data.Semiquot._hyg.995 : Semiquot.{u_1} α) => Functor.map.{u_1, u_1} Semiquot.{u_1} (Applicative.toFunctor.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α β x._@.Mathlib.Data.Semiquot._hyg.993 x._@.Mathlib.Data.Semiquot._hyg.995) (Semiquot.map.{u_1, u_1} α β)
Case conversion may be inaccurate. Consider using '#align semiquot.map_def Semiquot.map_defₓ'. -/
@[simp]
theorem map_def {β} : ((· <$> ·) : (α → β) → Semiquot α → Semiquot β) = map :=
  rfl
#align semiquot.map_def Semiquot.map_def

/- warning: semiquot.bind_def -> Semiquot.bind_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}}, Eq.{succ u_1} ((Semiquotₓ.{u_2, u_1} α) -> (α -> (Semiquotₓ.{u_2, u_1} β)) -> (Semiquotₓ.{u_2, u_1} β)) (Bind.bind.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Monad.toHasBind.{u_1, u_1} Semiquotₓ.{u_2, u_1} Semiquotₓ.monad.{u_1, u_2}) α β) (Semiquot.bind.{u_1, u_1, u_2, u_2, u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_1}}, Eq.{succ u_1} ((Semiquot.{u_1} α) -> (α -> (Semiquot.{u_1} β)) -> (Semiquot.{u_1} β)) (fun (x._@.Mathlib.Data.Semiquot._hyg.1033 : Semiquot.{u_1} α) (x._@.Mathlib.Data.Semiquot._hyg.1035 : α -> (Semiquot.{u_1} β)) => Bind.bind.{u_1, u_1} Semiquot.{u_1} (Monad.toBind.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1}) α β x._@.Mathlib.Data.Semiquot._hyg.1033 x._@.Mathlib.Data.Semiquot._hyg.1035) (Semiquot.bind.{u_1, u_1} α β)
Case conversion may be inaccurate. Consider using '#align semiquot.bind_def Semiquot.bind_defₓ'. -/
@[simp]
theorem bind_def {β} : ((· >>= ·) : Semiquot α → (α → Semiquot β) → Semiquot β) = bind :=
  rfl
#align semiquot.bind_def Semiquot.bind_def

/- warning: semiquot.mem_pure -> Semiquot.mem_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α}, Iff (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a (Pure.pure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Applicative.toHasPure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Monad.toApplicative.{u_1, u_1} Semiquotₓ.{u_2, u_1} Semiquotₓ.monad.{u_1, u_2})) α b)) (Eq.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α}, Iff (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a (Pure.pure.{u_1, u_1} Semiquot.{u_1} (Applicative.toPure.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α b)) (Eq.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align semiquot.mem_pure Semiquot.mem_pureₓ'. -/
@[simp]
theorem mem_pure {a b : α} : a ∈ (pure b : Semiquot α) ↔ a = b :=
  Set.mem_singleton_iff
#align semiquot.mem_pure Semiquot.mem_pure

/- warning: semiquot.mem_pure_self -> Semiquot.mem_pure_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (a : α), Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a (Pure.pure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Applicative.toHasPure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Monad.toApplicative.{u_1, u_1} Semiquotₓ.{u_2, u_1} Semiquotₓ.monad.{u_1, u_2})) α a)
but is expected to have type
  forall {α : Type.{u_1}} (a : α), Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a (Pure.pure.{u_1, u_1} Semiquot.{u_1} (Applicative.toPure.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α a)
Case conversion may be inaccurate. Consider using '#align semiquot.mem_pure_self Semiquot.mem_pure_selfₓ'. -/
theorem mem_pure_self (a : α) : a ∈ (pure a : Semiquot α) :=
  Set.mem_singleton a
#align semiquot.mem_pure_self Semiquot.mem_pure_self

/- warning: semiquot.pure_inj -> Semiquot.pure_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α}, Iff (Eq.{succ u_1} (Semiquotₓ.{u_2, u_1} α) (Pure.pure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Applicative.toHasPure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Monad.toApplicative.{u_1, u_1} Semiquotₓ.{u_2, u_1} Semiquotₓ.monad.{u_1, u_2})) α a) (Pure.pure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Applicative.toHasPure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Monad.toApplicative.{u_1, u_1} Semiquotₓ.{u_2, u_1} Semiquotₓ.monad.{u_1, u_2})) α b)) (Eq.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α}, Iff (Eq.{succ u_1} (Semiquot.{u_1} α) (Pure.pure.{u_1, u_1} Semiquot.{u_1} (Applicative.toPure.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α a) (Pure.pure.{u_1, u_1} Semiquot.{u_1} (Applicative.toPure.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α b)) (Eq.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align semiquot.pure_inj Semiquot.pure_injₓ'. -/
@[simp]
theorem pure_inj {a b : α} : (pure a : Semiquot α) = pure b ↔ a = b :=
  ext_s.trans Set.singleton_eq_singleton_iff
#align semiquot.pure_inj Semiquot.pure_inj

instance : LawfulMonad Semiquot
    where
  pure_bind α β x f := ext.2 <| by simp
  bind_assoc α β γ s f g :=
    ext.2 <| by
      simp <;>
        exact fun c =>
          ⟨fun ⟨b, ⟨a, as, bf⟩, cg⟩ => ⟨a, as, b, bf, cg⟩, fun ⟨a, as, b, bf, cg⟩ =>
            ⟨b, ⟨a, as, bf⟩, cg⟩⟩
  id_map α q := ext.2 <| by simp
  bind_pure_comp_eq_map α β f s := ext.2 <| by simp [eq_comm]

instance : LE (Semiquot α) :=
  ⟨fun s t => s.s ⊆ t.s⟩

instance : PartialOrder (Semiquot α)
    where
  le s t := ∀ ⦃x⦄, x ∈ s → x ∈ t
  le_refl s := Set.Subset.refl _
  le_trans s t u := Set.Subset.trans
  le_antisymm s t h₁ h₂ := ext_s.2 (Set.Subset.antisymm h₁ h₂)

instance : SemilatticeSup (Semiquot α) :=
  { Semiquot.partialOrder with
    sup := fun s => blur s.s
    le_sup_left := fun s t => Set.subset_union_left _ _
    le_sup_right := fun s t => Set.subset_union_right _ _
    sup_le := fun s t u => Set.union_subset }

/- warning: semiquot.pure_le -> Semiquot.pure_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {s : Semiquotₓ.{u_2, u_1} α}, Iff (LE.le.{u_1} (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasLe.{u_1, u_2} α) (Pure.pure.{u_1, u_1} (fun {α : Type.{u_1}} => Semiquotₓ.{u_2, u_1} α) (Applicative.toHasPure.{u_1, u_1} (fun {α : Type.{u_1}} => Semiquotₓ.{u_2, u_1} α) (Monad.toApplicative.{u_1, u_1} (fun {α : Type.{u_1}} => Semiquotₓ.{u_2, u_1} α) Semiquotₓ.monad.{u_1, u_2})) α a) s) (Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a s)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {s : Semiquot.{u_1} α}, Iff (LE.le.{u_1} (Semiquot.{u_1} α) (Semiquot.instLESemiquot.{u_1} α) (Pure.pure.{u_1, u_1} Semiquot.{u_1} (Applicative.toPure.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α a) s) (Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a s)
Case conversion may be inaccurate. Consider using '#align semiquot.pure_le Semiquot.pure_leₓ'. -/
@[simp]
theorem pure_le {a : α} {s : Semiquot α} : pure a ≤ s ↔ a ∈ s :=
  Set.singleton_subset_iff
#align semiquot.pure_le Semiquot.pure_le

/- warning: semiquot.is_pure -> Semiquot.IsPure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, (Semiquotₓ.{u_2, u_1} α) -> Prop
but is expected to have type
  forall {α : Type.{u_1}}, (Semiquot.{u_1} α) -> Prop
Case conversion may be inaccurate. Consider using '#align semiquot.is_pure Semiquot.IsPureₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a b «expr ∈ » q) -/
/-- Assert that a `semiquot` contains only one possible value. -/
def IsPure (q : Semiquot α) : Prop :=
  ∀ (a) (_ : a ∈ q) (b) (_ : b ∈ q), a = b
#align semiquot.is_pure Semiquot.IsPure

/- warning: semiquot.get -> Semiquot.get is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (q : Semiquotₓ.{u_2, u_1} α), (Semiquot.IsPure.{u_1, u_2} α q) -> α
but is expected to have type
  forall {α : Type.{u_1}} (q : Semiquot.{u_1} α), (Semiquot.IsPure.{u_1} α q) -> α
Case conversion may be inaccurate. Consider using '#align semiquot.get Semiquot.getₓ'. -/
/-- Extract the value from a `is_pure` semiquotient. -/
def get (q : Semiquot α) (h : q.IsPure) : α :=
  liftOn q id h
#align semiquot.get Semiquot.get

/- warning: semiquot.get_mem -> Semiquot.get_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {q : Semiquotₓ.{u_2, u_1} α} (p : Semiquot.IsPure.{u_1, u_2} α q), Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) (Semiquot.get.{u_1, u_2} α q p) q
but is expected to have type
  forall {α : Type.{u_1}} {q : Semiquot.{u_1} α} (p : Semiquot.IsPure.{u_1} α q), Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) (Semiquot.get.{u_1} α q p) q
Case conversion may be inaccurate. Consider using '#align semiquot.get_mem Semiquot.get_memₓ'. -/
theorem get_mem {q : Semiquot α} (p) : get q p ∈ q :=
  by
  let ⟨a, h⟩ := exists_mem q
  unfold get <;> rw [lift_on_of_mem q _ _ a h] <;> exact h
#align semiquot.get_mem Semiquot.get_mem

/- warning: semiquot.eq_pure -> Semiquot.eq_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {q : Semiquotₓ.{u_2, u_1} α} (p : Semiquot.IsPure.{u_1, u_2} α q), Eq.{succ u_1} (Semiquotₓ.{u_2, u_1} α) q (Pure.pure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Applicative.toHasPure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Monad.toApplicative.{u_1, u_1} Semiquotₓ.{u_2, u_1} Semiquotₓ.monad.{u_1, u_2})) α (Semiquot.get.{u_1, u_2} α q p))
but is expected to have type
  forall {α : Type.{u_1}} {q : Semiquot.{u_1} α} (p : Semiquot.IsPure.{u_1} α q), Eq.{succ u_1} (Semiquot.{u_1} α) q (Pure.pure.{u_1, u_1} Semiquot.{u_1} (Applicative.toPure.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α (Semiquot.get.{u_1} α q p))
Case conversion may be inaccurate. Consider using '#align semiquot.eq_pure Semiquot.eq_pureₓ'. -/
theorem eq_pure {q : Semiquot α} (p) : q = pure (get q p) :=
  ext.2 fun a => by simp <;> exact ⟨fun h => p _ h _ (get_mem _), fun e => e.symm ▸ get_mem _⟩
#align semiquot.eq_pure Semiquot.eq_pure

/- warning: semiquot.pure_is_pure -> Semiquot.pure_isPure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (a : α), Semiquot.IsPure.{u_1, u_2} α (Pure.pure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Applicative.toHasPure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Monad.toApplicative.{u_1, u_1} Semiquotₓ.{u_2, u_1} Semiquotₓ.monad.{u_1, u_2})) α a)
but is expected to have type
  forall {α : Type.{u_1}} (a : α), Semiquot.IsPure.{u_1} α (Pure.pure.{u_1, u_1} Semiquot.{u_1} (Applicative.toPure.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α a)
Case conversion may be inaccurate. Consider using '#align semiquot.pure_is_pure Semiquot.pure_isPureₓ'. -/
@[simp]
theorem pure_isPure (a : α) : IsPure (pure a)
  | b, ab, c, ac => by
    rw [mem_pure] at ab ac
    cc
#align semiquot.pure_is_pure Semiquot.pure_isPure

/- warning: semiquot.is_pure_iff -> Semiquot.isPure_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {s : Semiquotₓ.{u_2, u_1} α}, Iff (Semiquot.IsPure.{u_1, u_2} α s) (Exists.{succ u_1} α (fun (a : α) => Eq.{succ u_1} (Semiquotₓ.{u_2, u_1} α) s (Pure.pure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Applicative.toHasPure.{u_1, u_1} Semiquotₓ.{u_2, u_1} (Monad.toApplicative.{u_1, u_1} Semiquotₓ.{u_2, u_1} Semiquotₓ.monad.{u_1, u_2})) α a)))
but is expected to have type
  forall {α : Type.{u_1}} {s : Semiquot.{u_1} α}, Iff (Semiquot.IsPure.{u_1} α s) (Exists.{succ u_1} α (fun (a : α) => Eq.{succ u_1} (Semiquot.{u_1} α) s (Pure.pure.{u_1, u_1} Semiquot.{u_1} (Applicative.toPure.{u_1, u_1} Semiquot.{u_1} (Monad.toApplicative.{u_1, u_1} Semiquot.{u_1} Semiquot.instMonadSemiquot.{u_1})) α a)))
Case conversion may be inaccurate. Consider using '#align semiquot.is_pure_iff Semiquot.isPure_iffₓ'. -/
theorem isPure_iff {s : Semiquot α} : IsPure s ↔ ∃ a, s = pure a :=
  ⟨fun h => ⟨_, eq_pure h⟩, fun ⟨a, e⟩ => e.symm ▸ pure_isPure _⟩
#align semiquot.is_pure_iff Semiquot.isPure_iff

/- warning: semiquot.is_pure.mono -> Semiquot.IsPure.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {s : Semiquotₓ.{u_2, u_1} α} {t : Semiquotₓ.{u_2, u_1} α}, (LE.le.{u_1} (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasLe.{u_1, u_2} α) s t) -> (Semiquot.IsPure.{u_1, u_2} α t) -> (Semiquot.IsPure.{u_1, u_2} α s)
but is expected to have type
  forall {α : Type.{u_1}} {s : Semiquot.{u_1} α} {t : Semiquot.{u_1} α}, (LE.le.{u_1} (Semiquot.{u_1} α) (Semiquot.instLESemiquot.{u_1} α) s t) -> (Semiquot.IsPure.{u_1} α t) -> (Semiquot.IsPure.{u_1} α s)
Case conversion may be inaccurate. Consider using '#align semiquot.is_pure.mono Semiquot.IsPure.monoₓ'. -/
theorem IsPure.mono {s t : Semiquot α} (st : s ≤ t) (h : IsPure t) : IsPure s
  | a, as, b, bs => h _ (st as) _ (st bs)
#align semiquot.is_pure.mono Semiquot.IsPure.mono

/- warning: semiquot.is_pure.min -> Semiquot.IsPure.min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {s : Semiquotₓ.{u_2, u_1} α} {t : Semiquotₓ.{u_2, u_1} α}, (Semiquot.IsPure.{u_1, u_2} α t) -> (Iff (LE.le.{u_1} (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasLe.{u_1, u_2} α) s t) (Eq.{succ u_1} (Semiquotₓ.{u_2, u_1} α) s t))
but is expected to have type
  forall {α : Type.{u_1}} {s : Semiquot.{u_1} α} {t : Semiquot.{u_1} α}, (Semiquot.IsPure.{u_1} α t) -> (Iff (LE.le.{u_1} (Semiquot.{u_1} α) (Semiquot.instLESemiquot.{u_1} α) s t) (Eq.{succ u_1} (Semiquot.{u_1} α) s t))
Case conversion may be inaccurate. Consider using '#align semiquot.is_pure.min Semiquot.IsPure.minₓ'. -/
theorem IsPure.min {s t : Semiquot α} (h : IsPure t) : s ≤ t ↔ s = t :=
  ⟨fun st =>
    le_antisymm st <| by
      rw [eq_pure h, eq_pure (h.mono st)] <;> simp <;> exact h _ (get_mem _) _ (st <| get_mem _),
    le_of_eq⟩
#align semiquot.is_pure.min Semiquot.IsPure.min

/- warning: semiquot.is_pure_of_subsingleton -> Semiquot.isPure_of_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Subsingleton.{succ u_1} α] (q : Semiquotₓ.{u_2, u_1} α), Semiquot.IsPure.{u_1, u_2} α q
but is expected to have type
  forall {α : Type.{u_1}} [_inst_1 : Subsingleton.{succ u_1} α] (q : Semiquot.{u_1} α), Semiquot.IsPure.{u_1} α q
Case conversion may be inaccurate. Consider using '#align semiquot.is_pure_of_subsingleton Semiquot.isPure_of_subsingletonₓ'. -/
theorem isPure_of_subsingleton [Subsingleton α] (q : Semiquot α) : IsPure q
  | a, b, aq, bq => Subsingleton.elim _ _
#align semiquot.is_pure_of_subsingleton Semiquot.isPure_of_subsingleton

/- warning: semiquot.univ -> Semiquot.univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Inhabited.{succ u_1} α], Semiquotₓ.{u_2, u_1} α
but is expected to have type
  forall {α : Type.{u_1}} [_inst_1 : Inhabited.{succ u_1} α], Semiquot.{u_1} α
Case conversion may be inaccurate. Consider using '#align semiquot.univ Semiquot.univₓ'. -/
/-- `univ : semiquot α` represents an unspecified element of `univ : set α`. -/
def univ [Inhabited α] : Semiquot α :=
  mk <| Set.mem_univ default
#align semiquot.univ Semiquot.univ

instance [Inhabited α] : Inhabited (Semiquot α) :=
  ⟨univ⟩

/- warning: semiquot.mem_univ -> Semiquot.mem_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Inhabited.{succ u_1} α] (a : α), Membership.Mem.{u_1, u_1} α (Semiquotₓ.{u_2, u_1} α) (Semiquotₓ.hasMem.{u_1, u_2} α) a (Semiquot.univ.{u_1, u_2} α _inst_1)
but is expected to have type
  forall {α : Type.{u_1}} [_inst_1 : Inhabited.{succ u_1} α] (a : α), Membership.mem.{u_1, u_1} α (Semiquot.{u_1} α) (Semiquot.instMembershipSemiquot.{u_1} α) a (Semiquot.univ.{u_1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align semiquot.mem_univ Semiquot.mem_univₓ'. -/
@[simp]
theorem mem_univ [Inhabited α] : ∀ a, a ∈ @univ α _ :=
  @Set.mem_univ α
#align semiquot.mem_univ Semiquot.mem_univ

/- warning: semiquot.univ_unique -> Semiquot.univ_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (I : Inhabited.{succ u_1} α) (J : Inhabited.{succ u_1} α), Eq.{succ u_1} (Semiquotₓ.{u_2, u_1} α) (Semiquot.univ.{u_1, u_2} α I) (Semiquot.univ.{u_1, u_2} α J)
but is expected to have type
  forall {α : Type.{u_1}} (I : Inhabited.{succ u_1} α) (J : Inhabited.{succ u_1} α), Eq.{succ u_1} (Semiquot.{u_1} α) (Semiquot.univ.{u_1} α I) (Semiquot.univ.{u_1} α J)
Case conversion may be inaccurate. Consider using '#align semiquot.univ_unique Semiquot.univ_uniqueₓ'. -/
@[congr]
theorem univ_unique (I J : Inhabited α) : @univ _ I = @univ _ J :=
  ext.2 <| by simp
#align semiquot.univ_unique Semiquot.univ_unique

/- warning: semiquot.is_pure_univ -> Semiquot.isPure_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Inhabited.{succ u_1} α], Iff (Semiquot.IsPure.{u_1, u_2} α (Semiquot.univ.{u_1, u_2} α _inst_1)) (Subsingleton.{succ u_1} α)
but is expected to have type
  forall {α : Type.{u_1}} [_inst_1 : Inhabited.{succ u_1} α], Iff (Semiquot.IsPure.{u_1} α (Semiquot.univ.{u_1} α _inst_1)) (Subsingleton.{succ u_1} α)
Case conversion may be inaccurate. Consider using '#align semiquot.is_pure_univ Semiquot.isPure_univₓ'. -/
@[simp]
theorem isPure_univ [Inhabited α] : @IsPure α univ ↔ Subsingleton α :=
  ⟨fun h => ⟨fun a b => h a trivial b trivial⟩, fun ⟨h⟩ a _ b _ => h a b⟩
#align semiquot.is_pure_univ Semiquot.isPure_univ

instance [Inhabited α] : OrderTop (Semiquot α)
    where
  top := univ
  le_top s := Set.subset_univ _

end Semiquot

