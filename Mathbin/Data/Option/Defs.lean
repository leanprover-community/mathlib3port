/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.option.defs
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!
# Extra definitions on `option`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines more operations involving `option α`. Lemmas about them are located in other
files under `data.option.`.
Other basic operations on `option` are defined in the core library.
-/


namespace Option

variable {α : Type _} {β : Type _}

attribute [inline] Option.isSome Option.isNone

#print Option.elim' /-
/-- An elimination principle for `option`. It is a nondependent version of `option.rec`. -/
@[simp]
protected def elim' (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b
#align option.elim Option.elim'
-/

instance hasMem : Membership α (Option α) :=
  ⟨fun a b => b = some a⟩
#align option.has_mem Option.hasMem

#print Option.mem_def /-
@[simp]
theorem mem_def {a : α} {b : Option α} : a ∈ b ↔ b = some a :=
  Iff.rfl
#align option.mem_def Option.mem_def
-/

#print Option.mem_iff /-
theorem mem_iff {a : α} {b : Option α} : a ∈ b ↔ b = a :=
  Iff.rfl
#align option.mem_iff Option.mem_iff
-/

#print Option.isNone_iff_eq_none /-
theorem isNone_iff_eq_none {o : Option α} : o.isNone = tt ↔ o = none :=
  ⟨Option.eq_none_of_isNone, fun e => e.symm ▸ rfl⟩
#align option.is_none_iff_eq_none Option.isNone_iff_eq_none
-/

#print Option.some_inj /-
theorem some_inj {a b : α} : some a = some b ↔ a = b := by simp
#align option.some_inj Option.some_inj
-/

#print Option.mem_some_iff /-
theorem mem_some_iff {α : Type _} {a b : α} : a ∈ some b ↔ b = a := by simp
#align option.mem_some_iff Option.mem_some_iff
-/

#print Option.decidableEqNone /-
/-- `o = none` is decidable even if the wrapped type does not have decidable equality.

This is not an instance because it is not definitionally equal to `option.decidable_eq`.
Try to use `o.is_none` or `o.is_some` instead.
-/
@[inline]
def decidableEqNone {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff (Bool.decidableEq _ _) isNone_iff_eq_none
#align option.decidable_eq_none Option.decidableEqNone
-/

#print Option.decidableForallMem /-
instance decidableForallMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∀ a ∈ o, p a)
  | none => isTrue (by simp [false_imp_iff])
  | some a =>
    if h : p a then is_true fun o e => some_inj.1 e ▸ h else is_false <| mt (fun H => H _ rfl) h
#align option.decidable_forall_mem Option.decidableForallMem
-/

/- warning: option.decidable_exists_mem -> Option.decidableExistsMem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] (o : Option.{u1} α), Decidable (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a o) (fun (H : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a o) => p a)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] (o : Option.{u1} α), Decidable (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Option.{u1} α) (Option.instMembershipOption.{u1} α) a o) (p a)))
Case conversion may be inaccurate. Consider using '#align option.decidable_exists_mem Option.decidableExistsMemₓ'. -/
instance decidableExistsMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∃ a ∈ o, p a)
  | none => isFalse fun ⟨a, ⟨h, _⟩⟩ => by cases h
  | some a => if h : p a then is_true <| ⟨_, rfl, h⟩ else is_false fun ⟨_, ⟨rfl, hn⟩⟩ => h hn
#align option.decidable_exists_mem Option.decidableExistsMem

#print Option.iget /-
/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[reducible]
def iget [Inhabited α] : Option α → α
  | some x => x
  | none => default
#align option.iget Option.iget
-/

#print Option.iget_some /-
@[simp]
theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl
#align option.iget_some Option.iget_some
-/

#print Option.guard /-
/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
def guard (p : α → Prop) [DecidablePred p] (a : α) : Option α :=
  if p a then some a else none
#align option.guard Option.guard
-/

/- warning: option.filter -> Option.filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], (Option.{u1} α) -> (Option.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, (α -> Bool) -> (Option.{u1} α) -> (Option.{u1} α)
Case conversion may be inaccurate. Consider using '#align option.filter Option.filterₓ'. -/
/-- `filter p o` returns `some a` if `o` is `some a` and `p a` holds, otherwise `none`. -/
def filter (p : α → Prop) [DecidablePred p] (o : Option α) : Option α :=
  o.bind (guard p)
#align option.filter Option.filter

#print Option.toList /-
/-- Cast of `option` to `list `. Returns `[a]` if the input is `some a`, and `[]` if it is
`none`. -/
def toList : Option α → List α
  | none => []
  | some a => [a]
#align option.to_list Option.toList
-/

#print Option.mem_toList /-
@[simp]
theorem mem_toList {a : α} {o : Option α} : a ∈ toList o ↔ a ∈ o := by
  cases o <;> simp [to_list, eq_comm]
#align option.mem_to_list Option.mem_toList
-/

#print Option.liftOrGet /-
/-- Two arguments failsafe function. Returns `f a b` if the inputs are `some a` and `some b`, and
"does nothing" otherwise. -/
def liftOrGet (f : α → α → α) : Option α → Option α → Option α
  | none, none => none
  | some a, none => some a
  |-- get a
    none,
    some b => some b
  |-- get b
      some
      a,
    some b => some (f a b)
#align option.lift_or_get Option.liftOrGet
-/

#print Option.liftOrGet_isCommutative /-
-- lift f
instance liftOrGet_isCommutative (f : α → α → α) [h : IsCommutative α f] :
    IsCommutative (Option α) (liftOrGet f) :=
  ⟨fun a b => by cases a <;> cases b <;> simp [lift_or_get, h.comm]⟩
#align option.lift_or_get_comm Option.liftOrGet_isCommutative
-/

#print Option.liftOrGet_isAssociative /-
instance liftOrGet_isAssociative (f : α → α → α) [h : IsAssociative α f] :
    IsAssociative (Option α) (liftOrGet f) :=
  ⟨fun a b c => by cases a <;> cases b <;> cases c <;> simp [lift_or_get, h.assoc]⟩
#align option.lift_or_get_assoc Option.liftOrGet_isAssociative
-/

#print Option.liftOrGet_isIdempotent /-
instance liftOrGet_isIdempotent (f : α → α → α) [h : IsIdempotent α f] :
    IsIdempotent (Option α) (liftOrGet f) :=
  ⟨fun a => by cases a <;> simp [lift_or_get, h.idempotent]⟩
#align option.lift_or_get_idem Option.liftOrGet_isIdempotent
-/

#print Option.liftOrGet_isLeftId /-
instance liftOrGet_isLeftId (f : α → α → α) : IsLeftId (Option α) (liftOrGet f) none :=
  ⟨fun a => by cases a <;> simp [lift_or_get]⟩
#align option.lift_or_get_is_left_id Option.liftOrGet_isLeftId
-/

#print Option.liftOrGet_isRightId /-
instance liftOrGet_isRightId (f : α → α → α) : IsRightId (Option α) (liftOrGet f) none :=
  ⟨fun a => by cases a <;> simp [lift_or_get]⟩
#align option.lift_or_get_is_right_id Option.liftOrGet_isRightId
-/

#print Option.Rel /-
/-- Lifts a relation `α → β → Prop` to a relation `option α → option β → Prop` by just adding
`none ~ none`. -/
inductive Rel (r : α → β → Prop) : Option α → Option β → Prop/--
If `a ~ b`, then `some a ~ some b` -/

  | some {a b} : r a b → Rel (some a) (some b)/-- `none ~ none` -/

  | none : Rel none none
#align option.rel Option.Rel
-/

#print Option.pbind /-
/-- Partial bind. If for some `x : option α`, `f : Π (a : α), a ∈ x → option β` is a
  partial function defined on `a : α` giving an `option β`, where `some a = x`,
  then `pbind x f h` is essentially the same as `bind x f`
  but is defined only when all `x = some a`, using the proof to apply `f`. -/
@[simp]
def pbind : ∀ x : Option α, (∀ a : α, a ∈ x → Option β) → Option β
  | none, _ => none
  | some a, f => f a rfl
#align option.pbind Option.pbind
-/

#print Option.pmap /-
/-- Partial map. If `f : Π a, p a → β` is a partial function defined on `a : α` satisfying `p`,
then `pmap f x h` is essentially the same as `map f x` but is defined only when all members of `x`
satisfy `p`, using the proof to apply `f`. -/
@[simp]
def pmap {p : α → Prop} (f : ∀ a : α, p a → β) : ∀ x : Option α, (∀ a ∈ x, p a) → Option β
  | none, _ => none
  | some a, H => some (f a (H a (mem_def.mpr rfl)))
#align option.pmap Option.pmap
-/

#print Option.join /-
/-- Flatten an `option` of `option`, a specialization of `mjoin`. -/
@[simp]
def join : Option (Option α) → Option α := fun x => bind x id
#align option.join Option.join
-/

#print Option.traverse /-
protected def traverse.{u, v} {F : Type u → Type v} [Applicative F] {α β : Type _} (f : α → F β) :
    Option α → F (Option β)
  | none => pure none
  | some x => some <$> f x
#align option.traverse Option.traverse
-/

#print Option.maybe /-
-- By analogy with `monad.sequence` in `init/category/combinators.lean`.
/-- If you maybe have a monadic computation in a `[monad m]` which produces a term of type `α`, then
there is a naturally associated way to always perform a computation in `m` which maybe produces a
result. -/
def maybe.{u, v} {m : Type u → Type v} [Monad m] {α : Type u} : Option (m α) → m (Option α)
  | none => return none
  | some fn => some <$> fn
#align option.maybe Option.maybe
-/

/- warning: option.mmap -> Option.mapM is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}}, (α -> (m β)) -> (Option.{u3} α) -> (m (Option.{u1} β))
but is expected to have type
  forall {m : Type.{u1} -> Type.{u2}} {_inst_1 : Type.{u3}} {α : Type.{u1}} [β : Monad.{u1, u2} m], (_inst_1 -> (m α)) -> (Option.{u3} _inst_1) -> (m (Option.{u1} α))
Case conversion may be inaccurate. Consider using '#align option.mmap Option.mapMₓ'. -/
/-- Map a monadic function `f : α → m β` over an `o : option α`, maybe producing a result. -/
def mapM.{u, v, w} {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β)
    (o : Option α) : m (Option β) :=
  (o.map f).maybe
#align option.mmap Option.mapM

/- warning: option.melim -> Option.elimM is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m], (m β) -> (α -> (m β)) -> (m (Option.{u1} α)) -> (m β)
but is expected to have type
  forall {α : Type.{u1} -> Type.{u2}} {β : Type.{u1}} {m : Type.{u1}} [_inst_1 : Monad.{u1, u2} α], (α (Option.{u1} β)) -> (α m) -> (β -> (α m)) -> (α m)
Case conversion may be inaccurate. Consider using '#align option.melim Option.elimMₓ'. -/
/-- A monadic analogue of `option.elim`. -/
def elimM {α β : Type _} {m : Type _ → Type _} [Monad m] (y : m β) (z : α → m β)
    (x : m (Option α)) : m β :=
  x >>= Option.elim' y z
#align option.melim Option.elimM

/- warning: option.mget_or_else -> Option.getDM is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m], (m (Option.{u1} α)) -> (m α) -> (m α)
but is expected to have type
  forall {α : Type.{u1} -> Type.{u2}} {m : Type.{u1}} [_inst_1 : Monad.{u1, u2} α], (α (Option.{u1} m)) -> (α m) -> (α m)
Case conversion may be inaccurate. Consider using '#align option.mget_or_else Option.getDMₓ'. -/
/-- A monadic analogue of `option.get_or_else`. -/
def getDM {α : Type _} {m : Type _ → Type _} [Monad m] (x : m (Option α)) (y : m α) : m α :=
  elimM y pure x
#align option.mget_or_else Option.getDM

end Option

