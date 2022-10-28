/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jannis Limperg
-/

/-!
# Monadic instances for `ulift` and `plift`

In this file we define `monad` and `is_lawful_monad` instances on `plift` and `ulift`. -/


universe u v

namespace PLift

variable {α : Sort u} {β : Sort v}

/-- Functorial action. -/
protected def map (f : α → β) (a : PLift α) : PLift β :=
  PLift.up (f a.down)

@[simp]
theorem map_up (f : α → β) (a : α) : (PLift.up a).map f = PLift.up (f a) :=
  rfl

/-- Embedding of pure values. -/
@[simp]
protected def pure : α → PLift α :=
  up

/-- Applicative sequencing. -/
protected def seq (f : PLift (α → β)) (x : PLift α) : PLift β :=
  PLift.up (f.down x.down)

@[simp]
theorem seq_up (f : α → β) (x : α) : (PLift.up f).seq (PLift.up x) = PLift.up (f x) :=
  rfl

/-- Monadic bind. -/
protected def bind (a : PLift α) (f : α → PLift β) : PLift β :=
  f a.down

@[simp]
theorem bind_up (a : α) (f : α → PLift β) : (PLift.up a).bind f = f a :=
  rfl

instance : Monad PLift where
  map := @PLift.map
  pure := @PLift.pure
  seq := @PLift.seq
  bind := @PLift.bind

instance : IsLawfulFunctor PLift where
  id_map := fun α ⟨x⟩ => rfl
  comp_map := fun α β γ g h ⟨x⟩ => rfl

instance : LawfulApplicative PLift where
  pure_seq_eq_map := fun α β g ⟨x⟩ => rfl
  map_pure α β g x := rfl
  seq_pure := fun α β ⟨g⟩ x => rfl
  seq_assoc := fun α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩ => rfl

instance : LawfulMonad PLift where
  bind_pure_comp_eq_map := fun α β f ⟨x⟩ => rfl
  bind_map_eq_seq := fun α β ⟨a⟩ ⟨b⟩ => rfl
  pure_bind α β x f := rfl
  bind_assoc := fun α β γ ⟨x⟩ f g => rfl

@[simp]
theorem rec.constant {α : Sort u} {β : Type v} (b : β) : (@PLift.rec α (fun _ => β) fun _ => b) = fun _ => b :=
  funext fun x => PLift.casesOn x fun a => Eq.refl (PLift.rec (fun a' => b) { down := a })

end PLift

namespace ULift

variable {α : Type u} {β : Type v}

/-- Functorial action. -/
protected def map (f : α → β) (a : ULift α) : ULift β :=
  ULift.up (f a.down)

@[simp]
theorem map_up (f : α → β) (a : α) : (ULift.up a).map f = ULift.up (f a) :=
  rfl

/-- Embedding of pure values. -/
@[simp]
protected def pure : α → ULift α :=
  up

/-- Applicative sequencing. -/
protected def seq (f : ULift (α → β)) (x : ULift α) : ULift β :=
  ULift.up (f.down x.down)

@[simp]
theorem seq_up (f : α → β) (x : α) : (ULift.up f).seq (ULift.up x) = ULift.up (f x) :=
  rfl

/-- Monadic bind. -/
protected def bind (a : ULift α) (f : α → ULift β) : ULift β :=
  f a.down

@[simp]
theorem bind_up (a : α) (f : α → ULift β) : (ULift.up a).bind f = f a :=
  rfl

instance : Monad ULift where
  map := @ULift.map
  pure := @ULift.pure
  seq := @ULift.seq
  bind := @ULift.bind

instance : IsLawfulFunctor ULift where
  id_map := fun α ⟨x⟩ => rfl
  comp_map := fun α β γ g h ⟨x⟩ => rfl

instance : LawfulApplicative ULift where
  to_is_lawful_functor := ULift.is_lawful_functor
  pure_seq_eq_map := fun α β g ⟨x⟩ => rfl
  map_pure α β g x := rfl
  seq_pure := fun α β ⟨g⟩ x => rfl
  seq_assoc := fun α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩ => rfl

instance : LawfulMonad ULift where
  bind_pure_comp_eq_map := fun α β f ⟨x⟩ => rfl
  bind_map_eq_seq := fun α β ⟨a⟩ ⟨b⟩ => rfl
  pure_bind α β x f := by
    dsimp only [bind, pure, ULift.pure, ULift.bind]
    cases f x
    rfl
  bind_assoc := fun α β γ ⟨x⟩ f g => by
    dsimp only [bind, pure, ULift.pure, ULift.bind]
    cases f x
    rfl

@[simp]
theorem rec.constant {α : Type u} {β : Sort v} (b : β) : (@ULift.rec α (fun _ => β) fun _ => b) = fun _ => b :=
  funext fun x => ULift.casesOn x fun a => Eq.refl (ULift.rec (fun a' => b) { down := a })

end ULift

