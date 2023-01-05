/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jannis Limperg

! This file was ported from Lean 3 source module control.ulift
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!
# Monadic instances for `ulift` and `plift`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `monad` and `is_lawful_monad` instances on `plift` and `ulift`. -/


universe u v

namespace PLift

variable {α : Sort u} {β : Sort v}

#print PLift.map /-
/-- Functorial action. -/
protected def map (f : α → β) (a : PLift α) : PLift β :=
  PLift.up (f a.down)
#align plift.map PLift.map
-/

#print PLift.map_up /-
@[simp]
theorem map_up (f : α → β) (a : α) : (PLift.up a).map f = PLift.up (f a) :=
  rfl
#align plift.map_up PLift.map_up
-/

#print PLift.pure /-
/-- Embedding of pure values. -/
@[simp]
protected def pure : α → PLift α :=
  up
#align plift.pure PLift.pure
-/

/- warning: plift.seq -> PLift.seq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, (PLift.{imax u1 u2} (α -> β)) -> (PLift.{u1} α) -> (PLift.{u2} β)
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}}, (PLift.{imax u1 u2} (α -> β)) -> (Unit -> (PLift.{u1} α)) -> (PLift.{u2} β)
Case conversion may be inaccurate. Consider using '#align plift.seq PLift.seqₓ'. -/
/-- Applicative sequencing. -/
protected def seq (f : PLift (α → β)) (x : PLift α) : PLift β :=
  PLift.up (f.down x.down)
#align plift.seq PLift.seq

#print PLift.seq_up /-
@[simp]
theorem seq_up (f : α → β) (x : α) : (PLift.up f).seq (PLift.up x) = PLift.up (f x) :=
  rfl
#align plift.seq_up PLift.seq_up
-/

#print PLift.bind /-
/-- Monadic bind. -/
protected def bind (a : PLift α) (f : α → PLift β) : PLift β :=
  f a.down
#align plift.bind PLift.bind
-/

#print PLift.bind_up /-
@[simp]
theorem bind_up (a : α) (f : α → PLift β) : (PLift.up a).bind f = f a :=
  rfl
#align plift.bind_up PLift.bind_up
-/

instance : Monad PLift where
  map := @PLift.map
  pure := @PLift.pure
  seq := @PLift.seq
  bind := @PLift.bind

instance : LawfulFunctor PLift where
  id_map := fun α ⟨x⟩ => rfl
  comp_map := fun α β γ g h ⟨x⟩ => rfl

instance : LawfulApplicative PLift
    where
  pure_seq_eq_map := fun α β g ⟨x⟩ => rfl
  map_pure α β g x := rfl
  seq_pure := fun α β ⟨g⟩ x => rfl
  seq_assoc := fun α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩ => rfl

instance : LawfulMonad PLift
    where
  bind_pure_comp_eq_map := fun α β f ⟨x⟩ => rfl
  bind_map_eq_seq := fun α β ⟨a⟩ ⟨b⟩ => rfl
  pure_bind α β x f := rfl
  bind_assoc := fun α β γ ⟨x⟩ f g => rfl

#print PLift.rec.constant /-
@[simp]
theorem rec.constant {α : Sort u} {β : Type v} (b : β) :
    (@PLift.rec α (fun _ => β) fun _ => b) = fun _ => b :=
  funext fun x => PLift.casesOn x fun a => Eq.refl (PLift.rec (fun a' => b) { down := a })
#align plift.rec.constant PLift.rec.constant
-/

end PLift

namespace ULift

variable {α : Type u} {β : Type v}

/- warning: ulift.map -> ULift.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}}, (α -> β) -> (ULift.{u_1, u} α) -> (ULift.{u_2, v} β)
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}}, (α -> β) -> (ULift.{u_1, u} α) -> (ULift.{u, v} β)
Case conversion may be inaccurate. Consider using '#align ulift.map ULift.mapₓ'. -/
/-- Functorial action. -/
protected def map (f : α → β) (a : ULift α) : ULift β :=
  ULift.up (f a.down)
#align ulift.map ULift.map

/- warning: ulift.map_up -> ULift.map_up is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (f : α -> β) (a : α), Eq.{succ (max v u_1)} (ULift.{u_1, v} β) (ULift.map.{u, v, u_2, u_1} α β f (ULift.up.{u_2, u} α a)) (ULift.up.{u_1, v} β (f a))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} (f : α -> β) (a : α), Eq.{max (succ u) (succ v)} (ULift.{u, v} β) (ULift.map.{u, v, u} α β f (ULift.up.{u, u} α a)) (ULift.up.{u, v} β (f a))
Case conversion may be inaccurate. Consider using '#align ulift.map_up ULift.map_upₓ'. -/
@[simp]
theorem map_up (f : α → β) (a : α) : (ULift.up a).map f = ULift.up (f a) :=
  rfl
#align ulift.map_up ULift.map_up

#print ULift.pure /-
/-- Embedding of pure values. -/
@[simp]
protected def pure : α → ULift α :=
  up
#align ulift.pure ULift.pure
-/

/- warning: ulift.seq -> ULift.seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (ULift.{u3, max u1 u2} (α -> β)) -> (ULift.{u4, u1} α) -> (ULift.{u5, u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}}, (ULift.{u4, max u2 u3} (α -> β)) -> (Unit -> (ULift.{u5, u2} α)) -> (ULift.{u1, u3} β)
Case conversion may be inaccurate. Consider using '#align ulift.seq ULift.seqₓ'. -/
/-- Applicative sequencing. -/
protected def seq (f : ULift (α → β)) (x : ULift α) : ULift β :=
  ULift.up (f.down x.down)
#align ulift.seq ULift.seq

/- warning: ulift.seq_up clashes with ULift.seq_up -> ULift.seq_up
warning: ulift.seq_up -> ULift.seq_up is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (x : α), Eq.{succ (max u2 u3)} (ULift.{u3, u2} β) (ULift.seq.{u1, u2, u4, u5, u3} α β (ULift.up.{u4, max u1 u2} (α -> β) f) (ULift.up.{u5, u1} α x)) (ULift.up.{u3, u2} β (f x))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u5}} (f : α -> β) (x : α), Eq.{max (succ u5) (succ u3)} (ULift.{u3, u5} β) (ULift.seq.{u3, u4, u5, u2, u1} α β (ULift.up.{u2, max u4 u5} (α -> β) f) (fun (x._@.Mathlib.Control.ULift._hyg.808 : Unit) => ULift.up.{u1, u4} α x)) (ULift.up.{u3, u5} β (f x))
Case conversion may be inaccurate. Consider using '#align ulift.seq_up ULift.seq_upₓ'. -/
@[simp]
theorem seq_up (f : α → β) (x : α) : (ULift.up f).seq (ULift.up x) = ULift.up (f x) :=
  rfl
#align ulift.seq_up ULift.seq_up

/- warning: ulift.bind clashes with ULift.bind -> ULift.bind
Case conversion may be inaccurate. Consider using '#align ulift.bind ULift.bindₓ'. -/
#print ULift.bind /-
/-- Monadic bind. -/
protected def bind (a : ULift α) (f : α → ULift β) : ULift β :=
  f a.down
#align ulift.bind ULift.bind
-/

/- warning: ulift.bind_up clashes with ULift.bind_up -> ULift.bind_up
warning: ulift.bind_up -> ULift.bind_up is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (f : α -> (ULift.{u3, u2} β)), Eq.{succ (max u2 u3)} (ULift.{u3, u2} β) (ULift.bind.{u1, u2, u4, u3} α β (ULift.up.{u4, u1} α a) f) (f a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} (a : α) (f : α -> (ULift.{u2, u4} β)), Eq.{max (succ u4) (succ u2)} (ULift.{u2, u4} β) (ULift.bind.{u3, u4, u1, u2} α β (ULift.up.{u1, u3} α a) f) (f a)
Case conversion may be inaccurate. Consider using '#align ulift.bind_up ULift.bind_upₓ'. -/
@[simp]
theorem bind_up (a : α) (f : α → ULift β) : (ULift.up a).bind f = f a :=
  rfl
#align ulift.bind_up ULift.bind_up

instance : Monad ULift where
  map := @ULift.map
  pure := @ULift.pure
  seq := @ULift.seq
  bind := @ULift.bind

instance : LawfulFunctor ULift where
  id_map := fun α ⟨x⟩ => rfl
  comp_map := fun α β γ g h ⟨x⟩ => rfl

instance : LawfulApplicative ULift
    where
  to_is_lawful_functor := ULift.is_lawful_functor
  pure_seq_eq_map := fun α β g ⟨x⟩ => rfl
  map_pure α β g x := rfl
  seq_pure := fun α β ⟨g⟩ x => rfl
  seq_assoc := fun α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩ => rfl

instance : LawfulMonad ULift
    where
  bind_pure_comp_eq_map := fun α β f ⟨x⟩ => rfl
  bind_map_eq_seq := fun α β ⟨a⟩ ⟨b⟩ => rfl
  pure_bind α β x f := by
    dsimp only [bind, pure, ULift.pure, ULift.bind]
    cases f x
    rfl
  bind_assoc := fun α β γ ⟨x⟩ f g =>
    by
    dsimp only [bind, pure, ULift.pure, ULift.bind]
    cases f x
    rfl

/- warning: ulift.rec.constant clashes with ULift.rec.constant -> ULift.rec.constant
warning: ulift.rec.constant -> ULift.rec.constant is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Sort.{u2}} (b : β), Eq.{imax (succ (max u1 u3)) u2} (forall (n : ULift.{u3, u1} α), (fun (_x : ULift.{u3, u1} α) => β) n) (ULift.rec.{u2, u3, u1} α (fun (_x : ULift.{u3, u1} α) => β) (fun (_x : α) => b)) (fun (_x : ULift.{u3, u1} α) => b)
but is expected to have type
  forall {α : Type.{u2}} {β : Sort.{u3}} (b : β), Eq.{imax (max (succ u2) (succ u1)) u3} ((ULift.{u1, u2} α) -> β) (ULift.rec.{u3, u1, u2} α (fun (_x : ULift.{u1, u2} α) => β) (fun (_x : α) => b)) (fun (_x : ULift.{u1, u2} α) => b)
Case conversion may be inaccurate. Consider using '#align ulift.rec.constant ULift.rec.constantₓ'. -/
@[simp]
theorem rec.constant {α : Type u} {β : Sort v} (b : β) :
    (@ULift.rec α (fun _ => β) fun _ => b) = fun _ => b :=
  funext fun x => ULift.casesOn x fun a => Eq.refl (ULift.rec (fun a' => b) { down := a })
#align ulift.rec.constant ULift.rec.constant

end ULift

