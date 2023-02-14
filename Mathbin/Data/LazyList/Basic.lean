/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.lazy_list.basic
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Traversable.Equiv
import Mathbin.Control.Traversable.Instances
import Mathbin.Data.LazyList

/-!
## Definitions on lazy lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains various definitions and proofs on lazy lists.

TODO: move the `lazy_list.lean` file from core to mathlib.
-/


universe u

namespace Thunk

/- warning: thunk.mk -> Thunk.pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, α -> (Thunkₓ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, α -> (Thunk.{u1} α)
Case conversion may be inaccurate. Consider using '#align thunk.mk Thunk.pureₓ'. -/
/-- Creates a thunk with a (non-lazy) constant value. -/
def pure {α} (x : α) : Thunk α := fun _ => x
#align thunk.mk Thunk.pure

instance {α : Type u} [DecidableEq α] : DecidableEq (Thunk α)
  | a, b =>
    by
    have : a = b ↔ a () = b () := ⟨by cc, by intro <;> ext x <;> cases x <;> assumption⟩
    rw [this] <;> infer_instance

end Thunk

namespace LazyList

open Function

#print LazyList.listEquivLazyList /-
/-- Isomorphism between strict and lazy lists. -/
def listEquivLazyList (α : Type _) : List α ≃ LazyList α
    where
  toFun := LazyList.ofList
  invFun := LazyList.toList
  right_inv := by
    intro
    induction x
    rfl
    simp! [*]
    ext
    cases x
    rfl
  left_inv := by
    intro
    induction x
    rfl
    simp! [*]
#align lazy_list.list_equiv_lazy_list LazyList.listEquivLazyList
-/

instance {α : Type u} [DecidableEq α] : DecidableEq (LazyList α)
  | nil, nil => isTrue rfl
  | cons x xs, cons y ys =>
    if h : x = y then
      match DecidableEq (xs ()) (ys ()) with
      | is_false h2 => isFalse (by intro <;> cc)
      | is_true h2 =>
        have : xs = ys := by ext u <;> cases u <;> assumption
        isTrue (by cc)
    else isFalse (by intro <;> cc)
  | nil, cons _ _ => isFalse (by cc)
  | cons _ _, nil => isFalse (by cc)

#print LazyList.traverse /-
/-- Traversal of lazy lists using an applicative effect. -/
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (f : α → m β) :
    LazyList α → m (LazyList β)
  | LazyList.nil => pure LazyList.nil
  | LazyList.cons x xs => LazyList.cons <$> f x <*> Thunk.pure <$> traverse (xs ())
#align lazy_list.traverse LazyList.traverse
-/

instance : Traversable LazyList
    where
  map := @LazyList.traverse id _
  traverse := @LazyList.traverse

instance : IsLawfulTraversable LazyList :=
  by
  apply Equiv.isLawfulTraversable' list_equiv_lazy_list <;> intros <;> skip <;> ext
  · induction x
    rfl
    simp! [Equiv.map, Functor.map] at *
    simp [*]
    rfl
  · induction x
    rfl
    simp! [Equiv.map, Functor.mapConst] at *
    simp [*]
    rfl
  · induction x
    · simp! [Traversable.traverse, Equiv.traverse, functor_norm]
      rfl
    simp! [Equiv.map, Functor.mapConst, Traversable.traverse] at *
    rw [x_ih]
    dsimp [list_equiv_lazy_list, Equiv.traverse, to_list, Traversable.traverse, List.traverse]
    simp! [functor_norm]
    rfl

#print LazyList.init /-
/-- `init xs`, if `xs` non-empty, drops the last element of the list.
Otherwise, return the empty list. -/
def init {α} : LazyList α → LazyList α
  | LazyList.nil => LazyList.nil
  | LazyList.cons x xs =>
    let xs' := xs ()
    match xs' with
    | LazyList.nil => LazyList.nil
    | LazyList.cons _ _ => LazyList.cons x (init xs')
#align lazy_list.init LazyList.init
-/

#print LazyList.find /-
/-- Return the first object contained in the list that satisfies
predicate `p` -/
def find {α} (p : α → Prop) [DecidablePred p] : LazyList α → Option α
  | nil => none
  | cons h t => if p h then some h else find (t ())
#align lazy_list.find LazyList.find
-/

#print LazyList.interleave /-
/-- `interleave xs ys` creates a list where elements of `xs` and `ys` alternate. -/
def interleave {α} : LazyList α → LazyList α → LazyList α
  | LazyList.nil, xs => xs
  | a@(LazyList.cons x xs), LazyList.nil => a
  | LazyList.cons x xs, LazyList.cons y ys =>
    LazyList.cons x (LazyList.cons y (interleave (xs ()) (ys ())))
#align lazy_list.interleave LazyList.interleave
-/

#print LazyList.interleaveAll /-
/-- `interleave_all (xs::ys::zs::xss)` creates a list where elements of `xs`, `ys`
and `zs` and the rest alternate. Every other element of the resulting list is taken from
`xs`, every fourth is taken from `ys`, every eighth is taken from `zs` and so on. -/
def interleaveAll {α} : List (LazyList α) → LazyList α
  | [] => LazyList.nil
  | x :: xs => interleave x (interleave_all xs)
#align lazy_list.interleave_all LazyList.interleaveAll
-/

#print LazyList.bind /-
/-- Monadic bind operation for `lazy_list`. -/
protected def bind {α β} : LazyList α → (α → LazyList β) → LazyList β
  | LazyList.nil, _ => LazyList.nil
  | LazyList.cons x xs, f => LazyList.append (f x) (bind (xs ()) f)
#align lazy_list.bind LazyList.bind
-/

#print LazyList.reverse /-
/-- Reverse the order of a `lazy_list`.
It is done by converting to a `list` first because reversal involves evaluating all
the list and if the list is all evaluated, `list` is a better representation for
it than a series of thunks. -/
def reverse {α} (xs : LazyList α) : LazyList α :=
  ofList xs.toList.reverse
#align lazy_list.reverse LazyList.reverse
-/

instance : Monad LazyList where
  pure := @LazyList.singleton
  bind := @LazyList.bind

/- warning: lazy_list.append_nil -> LazyList.append_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (xs : LazyList.{u1} α), Eq.{succ u1} (LazyList.{u1} α) (LazyList.append.{u1} α xs (fun (_ : Unit) => LazyList.nil.{u1} α)) xs
but is expected to have type
  forall {α : Type.{u1}} (xs : LazyList.{u1} α), Eq.{succ u1} (LazyList.{u1} α) (LazyList.append.{u1} α xs (Thunk.pure.{u1} (LazyList.{u1} α) (LazyList.nil.{u1} α))) xs
Case conversion may be inaccurate. Consider using '#align lazy_list.append_nil LazyList.append_nilₓ'. -/
theorem append_nil {α} (xs : LazyList α) : xs.append LazyList.nil = xs :=
  by
  induction xs; rfl
  simp [LazyList.append, xs_ih]
  ext; congr
#align lazy_list.append_nil LazyList.append_nil

/- warning: lazy_list.append_assoc -> LazyList.append_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (xs : LazyList.{u1} α) (ys : LazyList.{u1} α) (zs : LazyList.{u1} α), Eq.{succ u1} (LazyList.{u1} α) (LazyList.append.{u1} α (LazyList.append.{u1} α xs (fun (_ : Unit) => ys)) (fun (_ : Unit) => zs)) (LazyList.append.{u1} α xs (fun (_ : Unit) => LazyList.append.{u1} α ys (fun (_ : Unit) => zs)))
but is expected to have type
  forall {α : Type.{u1}} (xs : LazyList.{u1} α) (ys : LazyList.{u1} α) (zs : LazyList.{u1} α), Eq.{succ u1} (LazyList.{u1} α) (LazyList.append.{u1} α (LazyList.append.{u1} α xs (Thunk.mk.{u1} (LazyList.{u1} α) (fun (x._@.Init.Core._hyg.266 : Unit) => ys))) (Thunk.mk.{u1} (LazyList.{u1} α) (fun (x._@.Init.Core._hyg.266 : Unit) => zs))) (LazyList.append.{u1} α xs (Thunk.mk.{u1} (LazyList.{u1} α) (fun (x._@.Init.Core._hyg.266 : Unit) => LazyList.append.{u1} α ys (Thunk.mk.{u1} (LazyList.{u1} α) (fun (x._@.Init.Core._hyg.266 : Unit) => zs)))))
Case conversion may be inaccurate. Consider using '#align lazy_list.append_assoc LazyList.append_assocₓ'. -/
theorem append_assoc {α} (xs ys zs : LazyList α) :
    (xs.append ys).append zs = xs.append (ys.append zs) := by induction xs <;> simp [append, *]
#align lazy_list.append_assoc LazyList.append_assoc

/- warning: lazy_list.append_bind -> LazyList.append_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (xs : LazyList.{u1} α) (ys : Thunkₓ.{u1} (LazyList.{u1} α)) (f : α -> (LazyList.{u2} β)), Eq.{succ u2} (LazyList.{u2} β) (LazyList.bind.{u1, u2} α β (LazyList.append.{u1} α xs ys) f) (LazyList.append.{u2} β (LazyList.bind.{u1, u2} α β xs f) (fun (_ : Unit) => LazyList.bind.{u1, u2} α β (ys Unit.unit) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (xs : LazyList.{u2} α) (ys : Thunk.{u2} (LazyList.{u2} α)) (f : α -> (LazyList.{u1} β)), Eq.{succ u1} (LazyList.{u1} β) (LazyList.bind.{u2, u1} α β (LazyList.append.{u2} α xs ys) f) (LazyList.append.{u1} β (LazyList.bind.{u2, u1} α β xs f) (Thunk.mk.{u1} (LazyList.{u1} β) (fun (x._@.Init.Core._hyg.266 : Unit) => LazyList.bind.{u2, u1} α β (Thunk.get.{u2} (LazyList.{u2} α) ys) f)))
Case conversion may be inaccurate. Consider using '#align lazy_list.append_bind LazyList.append_bindₓ'. -/
theorem append_bind {α β} (xs : LazyList α) (ys : Thunk (LazyList α)) (f : α → LazyList β) :
    (@LazyList.append _ xs ys).bind f = (xs.bind f).append ((ys ()).bind f) := by
  induction xs <;> simp [LazyList.bind, append, *, append_assoc, append, LazyList.bind]
#align lazy_list.append_bind LazyList.append_bind

instance : LawfulMonad LazyList
    where
  pure_bind := by
    intros
    apply append_nil
  bind_assoc := by
    intros
    dsimp [(· >>= ·)]
    induction x <;> simp [LazyList.bind, append_bind, *]
  id_map := by
    intros
    simp [(· <$> ·)]
    induction x <;> simp [LazyList.bind, *, singleton, append]
    ext ⟨⟩; rfl

/- warning: lazy_list.mfirst -> LazyList.mfirstₓ is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Alternative.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}}, (α -> (m β)) -> (LazyList.{u3} α) -> (m β)
but is expected to have type
  forall {m : Type.{u3} -> Type.{u2}} [_inst_1 : Alternative.{u3, u2} m] {α : Type.{u1}} {β : Type.{u3}}, (α -> (m β)) -> (LazyList.{u1} α) -> (m β)
Case conversion may be inaccurate. Consider using '#align lazy_list.mfirst LazyList.mfirstₓₓ'. -/
/-- Try applying function `f` to every element of a `lazy_list` and
return the result of the first attempt that succeeds. -/
def mfirst {m} [Alternative m] {α β} (f : α → m β) : LazyList α → m β
  | nil => failure
  | cons x xs => f x <|> mfirst (xs ())
#align lazy_list.mfirst LazyList.mfirstₓ

#print LazyList.Mem /-
/-- Membership in lazy lists -/
protected def Mem {α} (x : α) : LazyList α → Prop
  | LazyList.nil => False
  | LazyList.cons y ys => x = y ∨ mem (ys ())
#align lazy_list.mem LazyList.Mem
-/

instance {α} : Membership α (LazyList α) :=
  ⟨LazyList.Mem⟩

#print LazyList.Mem.decidable /-
instance Mem.decidable {α} [DecidableEq α] (x : α) : ∀ xs : LazyList α, Decidable (x ∈ xs)
  | LazyList.nil => Decidable.false
  | LazyList.cons y ys =>
    if h : x = y then Decidable.isTrue (Or.inl h)
    else decidable_of_decidable_of_iff (mem.decidable (ys ())) (by simp [*, (· ∈ ·), LazyList.Mem])
#align lazy_list.mem.decidable LazyList.Mem.decidable
-/

#print LazyList.mem_nil /-
@[simp]
theorem mem_nil {α} (x : α) : x ∈ @LazyList.nil α ↔ False :=
  Iff.rfl
#align lazy_list.mem_nil LazyList.mem_nil
-/

/- warning: lazy_list.mem_cons -> LazyList.mem_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (y : α) (ys : Thunkₓ.{u1} (LazyList.{u1} α)), Iff (Membership.Mem.{u1, u1} α (LazyList.{u1} α) (LazyList.hasMem.{u1} α) x (LazyList.cons.{u1} α y ys)) (Or (Eq.{succ u1} α x y) (Membership.Mem.{u1, u1} α (LazyList.{u1} α) (LazyList.hasMem.{u1} α) x (ys Unit.unit)))
but is expected to have type
  forall {α : Type.{u1}} (x : α) (y : α) (ys : Thunk.{u1} (LazyList.{u1} α)), Iff (Membership.mem.{u1, u1} α (LazyList.{u1} α) (LazyList.instMembershipLazyList.{u1} α) x (LazyList.cons.{u1} α y ys)) (Or (Eq.{succ u1} α x y) (Membership.mem.{u1, u1} α (LazyList.{u1} α) (LazyList.instMembershipLazyList.{u1} α) x (Thunk.get.{u1} (LazyList.{u1} α) ys)))
Case conversion may be inaccurate. Consider using '#align lazy_list.mem_cons LazyList.mem_consₓ'. -/
@[simp]
theorem mem_cons {α} (x y : α) (ys : Thunk (LazyList α)) :
    x ∈ @LazyList.cons α y ys ↔ x = y ∨ x ∈ ys () :=
  Iff.rfl
#align lazy_list.mem_cons LazyList.mem_cons

/- warning: lazy_list.forall_mem_cons -> LazyList.forall_mem_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {a : α} {l : Thunkₓ.{u1} (LazyList.{u1} α)}, Iff (forall (x : α), (Membership.Mem.{u1, u1} α (LazyList.{u1} α) (LazyList.hasMem.{u1} α) x (LazyList.cons.{u1} α a l)) -> (p x)) (And (p a) (forall (x : α), (Membership.Mem.{u1, u1} α (LazyList.{u1} α) (LazyList.hasMem.{u1} α) x (l Unit.unit)) -> (p x)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {a : α} {l : Thunk.{u1} (LazyList.{u1} α)}, Iff (forall (x : α), (Membership.mem.{u1, u1} α (LazyList.{u1} α) (LazyList.instMembershipLazyList.{u1} α) x (LazyList.cons.{u1} α a l)) -> (p x)) (And (p a) (forall (x : α), (Membership.mem.{u1, u1} α (LazyList.{u1} α) (LazyList.instMembershipLazyList.{u1} α) x (Thunk.get.{u1} (LazyList.{u1} α) l)) -> (p x)))
Case conversion may be inaccurate. Consider using '#align lazy_list.forall_mem_cons LazyList.forall_mem_consₓ'. -/
theorem forall_mem_cons {α} {p : α → Prop} {a : α} {l : Thunk (LazyList α)} :
    (∀ x ∈ @LazyList.cons _ a l, p x) ↔ p a ∧ ∀ x ∈ l (), p x := by
  simp only [Membership.Mem, LazyList.Mem, or_imp, forall_and, forall_eq]
#align lazy_list.forall_mem_cons LazyList.forall_mem_cons

/-! ### map for partial functions -/


#print LazyList.pmap /-
/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {α β} {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : LazyList α, (∀ a ∈ l, p a) → LazyList β
  | LazyList.nil, H => LazyList.nil
  | LazyList.cons x xs, H =>
    LazyList.cons (f x (forall_mem_cons.1 H).1) (pmap (xs ()) (forall_mem_cons.1 H).2)
#align lazy_list.pmap LazyList.pmap
-/

#print LazyList.attach /-
/-- "Attach" the proof that the elements of `l` are in `l` to produce a new `lazy_list`
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α} (l : LazyList α) : LazyList { x // x ∈ l } :=
  pmap Subtype.mk l fun a => id
#align lazy_list.attach LazyList.attach
-/

instance {α} [Repr α] : Repr (LazyList α) :=
  ⟨fun xs => repr xs.toList⟩

end LazyList

