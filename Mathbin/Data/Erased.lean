/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.erased
! leanprover-community/mathlib commit a2d2e18906e2b62627646b5d5be856e6a642062f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Defs

/-!
# A type for VM-erased data

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a type `erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `erased α` is
represented as `0`, just like types and proofs.
-/


universe u

#print Erased /-
/-- `erased α` is the same as `α`, except that the elements
  of `erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
def Erased (α : Sort u) : Sort max 1 u :=
  Σ's : α → Prop, ∃ a, (fun b => a = b) = s
#align erased Erased
-/

namespace Erased

#print Erased.mk /-
/-- Erase a value. -/
@[inline]
def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩
#align erased.mk Erased.mk
-/

#print Erased.out /-
/-- Extracts the erased value, noncomputably. -/
noncomputable def out {α} : Erased α → α
  | ⟨s, h⟩ => Classical.choose h
#align erased.out Erased.out
-/

#print Erased.OutType /-
/-- Extracts the erased value, if it is a type.

Note: `(mk a).out_type` is not definitionally equal to `a`.
-/
@[reducible]
def OutType (a : Erased (Sort u)) : Sort u :=
  out a
#align erased.out_type Erased.OutType
-/

#print Erased.out_proof /-
/-- Extracts the erased value, if it is a proof. -/
theorem out_proof {p : Prop} (a : Erased p) : p :=
  out a
#align erased.out_proof Erased.out_proof
-/

#print Erased.out_mk /-
@[simp]
theorem out_mk {α} (a : α) : (mk a).out = a :=
  by
  let h; show Classical.choose h = a
  have := Classical.choose_spec h
  exact cast (congr_fun this a).symm rfl
#align erased.out_mk Erased.out_mk
-/

#print Erased.mk_out /-
@[simp]
theorem mk_out {α} : ∀ a : Erased α, mk (out a) = a
  | ⟨s, h⟩ => by simp [mk] <;> congr <;> exact Classical.choose_spec h
#align erased.mk_out Erased.mk_out
-/

#print Erased.out_inj /-
@[ext]
theorem out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b := by simpa using congr_arg mk h
#align erased.out_inj Erased.out_inj
-/

#print Erased.equiv /-
/-- Equivalence between `erased α` and `α`. -/
noncomputable def equiv (α) : Erased α ≃ α :=
  ⟨out, mk, mk_out, out_mk⟩
#align erased.equiv Erased.equiv
-/

instance (α : Type u) : Repr (Erased α) :=
  ⟨fun _ => "erased"⟩

instance (α : Type u) : ToString (Erased α) :=
  ⟨fun _ => "erased"⟩

unsafe instance (α : Type u) : has_to_format (Erased α) :=
  ⟨fun _ => ("erased" : format)⟩

#print Erased.choice /-
/-- Computably produce an erased value from a proof of nonemptiness. -/
def choice {α} (h : Nonempty α) : Erased α :=
  mk (Classical.choice h)
#align erased.choice Erased.choice
-/

#print Erased.nonempty_iff /-
@[simp]
theorem nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩
#align erased.nonempty_iff Erased.nonempty_iff
-/

instance {α} [h : Nonempty α] : Inhabited (Erased α) :=
  ⟨choice h⟩

#print Erased.bind /-
/-- `(>>=)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `monad`).
-/
def bind {α β} (a : Erased α) (f : α → Erased β) : Erased β :=
  ⟨fun b => (f a.out).1 b, (f a.out).2⟩
#align erased.bind Erased.bind
-/

/- warning: erased.bind_eq_out -> Erased.bind_eq_out is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (a : Erased.{u1} α) (f : α -> (Erased.{u2} β)), Eq.{max 1 u2} (Erased.{u2} β) (Erased.bind.{u1, u2} α β a f) (f (Erased.out.{u1} α a))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (a : Erased.{u2} α) (f : α -> (Erased.{u1} β)), Eq.{max 1 u1} (Erased.{u1} β) (Erased.bind.{u2, u1} α β a f) (f (Erased.out.{u2} α a))
Case conversion may be inaccurate. Consider using '#align erased.bind_eq_out Erased.bind_eq_outₓ'. -/
@[simp]
theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out := by
  delta bind bind._proof_1 <;> cases f a.out <;> rfl
#align erased.bind_eq_out Erased.bind_eq_out

#print Erased.join /-
/-- Collapses two levels of erasure.
-/
def join {α} (a : Erased (Erased α)) : Erased α :=
  bind a id
#align erased.join Erased.join
-/

#print Erased.join_eq_out /-
@[simp]
theorem join_eq_out {α} (a) : @join α a = a.out :=
  bind_eq_out _ _
#align erased.join_eq_out Erased.join_eq_out
-/

#print Erased.map /-
/-- `(<$>)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `functor`).
-/
def map {α β} (f : α → β) (a : Erased α) : Erased β :=
  bind a (mk ∘ f)
#align erased.map Erased.map
-/

/- warning: erased.map_out -> Erased.map_out is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : α -> β} (a : Erased.{u1} α), Eq.{u2} β (Erased.out.{u2} β (Erased.map.{u1, u2} α β f a)) (f (Erased.out.{u1} α a))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {f : α -> β} (a : Erased.{u2} α), Eq.{u1} β (Erased.out.{u1} β (Erased.map.{u2, u1} α β f a)) (f (Erased.out.{u2} α a))
Case conversion may be inaccurate. Consider using '#align erased.map_out Erased.map_outₓ'. -/
@[simp]
theorem map_out {α β} {f : α → β} (a : Erased α) : (a.map f).out = f a.out := by simp [map]
#align erased.map_out Erased.map_out

instance : Monad Erased where
  pure := @mk
  bind := @bind
  map := @map

#print Erased.pure_def /-
@[simp]
theorem pure_def {α} : (pure : α → Erased α) = @mk _ :=
  rfl
#align erased.pure_def Erased.pure_def
-/

#print Erased.bind_def /-
@[simp]
theorem bind_def {α β} : ((· >>= ·) : Erased α → (α → Erased β) → Erased β) = @bind _ _ :=
  rfl
#align erased.bind_def Erased.bind_def
-/

#print Erased.map_def /-
@[simp]
theorem map_def {α β} : ((· <$> ·) : (α → β) → Erased α → Erased β) = @map _ _ :=
  rfl
#align erased.map_def Erased.map_def
-/

instance : LawfulMonad Erased := by refine' { .. } <;> intros <;> ext <;> simp

end Erased

