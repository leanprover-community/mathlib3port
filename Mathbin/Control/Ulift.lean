
/-!
# Monadic instances for `ulift` and `plift`

In this file we define `monad` and `is_lawful_monad` instances on `plift` and `ulift`. -/


universe u v

namespace Plift

variable {α : Sort u} {β : Sort v}

/-- Functorial action. -/
protected def map (f : α → β) (a : Plift α) : Plift β :=
  Plift.up (f a.down)

@[simp]
theorem map_up (f : α → β) (a : α) : (Plift.up a).map f = Plift.up (f a) :=
  rfl

/-- Embedding of pure values. -/
@[simp]
protected def pure : α → Plift α :=
  up

/-- Applicative sequencing. -/
protected def seq (f : Plift (α → β)) (x : Plift α) : Plift β :=
  Plift.up (f.down x.down)

@[simp]
theorem seq_up (f : α → β) (x : α) : (Plift.up f).seq (Plift.up x) = Plift.up (f x) :=
  rfl

/-- Monadic bind. -/
protected def bind (a : Plift α) (f : α → Plift β) : Plift β :=
  f a.down

@[simp]
theorem bind_up (a : α) (f : α → Plift β) : (Plift.up a).bind f = f a :=
  rfl

instance : Monadₓ Plift where
  map := @Plift.map
  pure := @Plift.pure
  seq := @Plift.seq
  bind := @Plift.bind

instance : IsLawfulFunctor Plift where
  id_map := fun α ⟨x⟩ => rfl
  comp_map := fun α β γ g h ⟨x⟩ => rfl

instance : IsLawfulApplicative Plift where
  pure_seq_eq_map := fun α β g ⟨x⟩ => rfl
  map_pure := fun α β g x => rfl
  seq_pure := fun α β ⟨g⟩ x => rfl
  seq_assoc := fun α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩ => rfl

instance : IsLawfulMonad Plift where
  bind_pure_comp_eq_map := fun α β f ⟨x⟩ => rfl
  bind_map_eq_seq := fun α β ⟨a⟩ ⟨b⟩ => rfl
  pure_bind := fun α β x f => rfl
  bind_assoc := fun α β γ ⟨x⟩ f g => rfl

@[simp]
theorem rec.constant {α : Sort u} {β : Type v} (b : β) : (@Plift.rec α (fun _ => β) fun _ => b) = fun _ => b :=
  funext fun x => Plift.casesOn x fun a => Eq.refl (Plift.rec (fun a' => b) { down := a })

end Plift

namespace Ulift

variable {α : Type u} {β : Type v}

/-- Functorial action. -/
protected def map (f : α → β) (a : Ulift α) : Ulift β :=
  Ulift.up (f a.down)

@[simp]
theorem map_up (f : α → β) (a : α) : (Ulift.up a).map f = Ulift.up (f a) :=
  rfl

/-- Embedding of pure values. -/
@[simp]
protected def pure : α → Ulift α :=
  up

/-- Applicative sequencing. -/
protected def seq (f : Ulift (α → β)) (x : Ulift α) : Ulift β :=
  Ulift.up (f.down x.down)

@[simp]
theorem seq_up (f : α → β) (x : α) : (Ulift.up f).seq (Ulift.up x) = Ulift.up (f x) :=
  rfl

/-- Monadic bind. -/
protected def bind (a : Ulift α) (f : α → Ulift β) : Ulift β :=
  f a.down

@[simp]
theorem bind_up (a : α) (f : α → Ulift β) : (Ulift.up a).bind f = f a :=
  rfl

instance : Monadₓ Ulift where
  map := @Ulift.map
  pure := @Ulift.pure
  seq := @Ulift.seq
  bind := @Ulift.bind

instance : IsLawfulFunctor Ulift where
  id_map := fun α ⟨x⟩ => rfl
  comp_map := fun α β γ g h ⟨x⟩ => rfl

instance : IsLawfulApplicative Ulift where
  to_is_lawful_functor := Ulift.is_lawful_functor
  pure_seq_eq_map := fun α β g ⟨x⟩ => rfl
  map_pure := fun α β g x => rfl
  seq_pure := fun α β ⟨g⟩ x => rfl
  seq_assoc := fun α β γ ⟨x⟩ ⟨g⟩ ⟨h⟩ => rfl

instance : IsLawfulMonad Ulift where
  bind_pure_comp_eq_map := fun α β f ⟨x⟩ => rfl
  bind_map_eq_seq := fun α β ⟨a⟩ ⟨b⟩ => rfl
  pure_bind := fun α β x f => by
    dsimp only [bind, pure, Ulift.pure, Ulift.bind]
    cases f x
    rfl
  bind_assoc := fun α β γ ⟨x⟩ f g => by
    dsimp only [bind, pure, Ulift.pure, Ulift.bind]
    cases f x
    rfl

@[simp]
theorem rec.constant {α : Type u} {β : Sort v} (b : β) : (@Ulift.rec α (fun _ => β) fun _ => b) = fun _ => b :=
  funext fun x => Ulift.casesOn x fun a => Eq.refl (Ulift.rec (fun a' => b) { down := a })

end Ulift

