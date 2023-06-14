/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jannis Limperg

! This file was ported from Lean 3 source module control.ulift
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
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

#print PLift.seq /-
/-- Applicative sequencing. -/
protected def seq (f : PLift (α → β)) (x : PLift α) : PLift β :=
  PLift.up (f.down x.down)
#align plift.seq PLift.seq
-/

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
  pure_seq := fun α β g ⟨x⟩ => rfl
  map_pure α β g x := rfl
  seq_pure := fun α β ⟨g⟩ x => rfl
  seq_assoc := fun α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩ => rfl

instance : LawfulMonad PLift
    where
  bind_pure_comp := fun α β f ⟨x⟩ => rfl
  bind_map := fun α β ⟨a⟩ ⟨b⟩ => rfl
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

#print ULift.map /-
/-- Functorial action. -/
protected def map (f : α → β) (a : ULift α) : ULift β :=
  ULift.up (f a.down)
#align ulift.map ULift.map
-/

#print ULift.map_up /-
@[simp]
theorem map_up (f : α → β) (a : α) : (ULift.up a).map f = ULift.up (f a) :=
  rfl
#align ulift.map_up ULift.map_up
-/

#print ULift.pure /-
/-- Embedding of pure values. -/
@[simp]
protected def pure : α → ULift α :=
  up
#align ulift.pure ULift.pure
-/

#print ULift.seq /-
/-- Applicative sequencing. -/
protected def seq (f : ULift (α → β)) (x : ULift α) : ULift β :=
  ULift.up (f.down x.down)
#align ulift.seq ULift.seq
-/

#print ULift.seq_up /-
@[simp]
theorem seq_up (f : α → β) (x : α) : (ULift.up f).seq (ULift.up x) = ULift.up (f x) :=
  rfl
#align ulift.seq_up ULift.seq_up
-/

#print ULift.bind /-
/-- Monadic bind. -/
protected def bind (a : ULift α) (f : α → ULift β) : ULift β :=
  f a.down
#align ulift.bind ULift.bind
-/

#print ULift.bind_up /-
@[simp]
theorem bind_up (a : α) (f : α → ULift β) : (ULift.up a).bind f = f a :=
  rfl
#align ulift.bind_up ULift.bind_up
-/

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
  to_lawfulFunctor := ULift.lawfulFunctor
  pure_seq := fun α β g ⟨x⟩ => rfl
  map_pure α β g x := rfl
  seq_pure := fun α β ⟨g⟩ x => rfl
  seq_assoc := fun α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩ => rfl

instance : LawfulMonad ULift
    where
  bind_pure_comp := fun α β f ⟨x⟩ => rfl
  bind_map := fun α β ⟨a⟩ ⟨b⟩ => rfl
  pure_bind α β x f := by dsimp only [bind, pure, ULift.pure, ULift.bind]; cases f x; rfl
  bind_assoc := fun α β γ ⟨x⟩ f g => by dsimp only [bind, pure, ULift.pure, ULift.bind]; cases f x;
    rfl

#print ULift.rec.constant /-
@[simp]
theorem rec.constant {α : Type u} {β : Sort v} (b : β) :
    (@ULift.rec α (fun _ => β) fun _ => b) = fun _ => b :=
  funext fun x => ULift.casesOn x fun a => Eq.refl (ULift.rec (fun a' => b) { down := a })
#align ulift.rec.constant ULift.rec.constant
-/

end ULift

