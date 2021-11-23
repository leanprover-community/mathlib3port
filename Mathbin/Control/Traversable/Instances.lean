import Mathbin.Control.Applicative 
import Mathbin.Data.List.Forall2 
import Mathbin.Data.Set.Lattice

/-!
# Traversable instances

This file provides instances of `traversable` for types from the core library: `option`, `list` and
`sum`.
-/


universe u v

section Option

open Functor

variable{F G : Type u → Type u}

variable[Applicativeₓ F][Applicativeₓ G]

variable[IsLawfulApplicative F][IsLawfulApplicative G]

theorem Option.id_traverse {α} (x : Option α) : Option.traverseₓ id.mk x = x :=
  by 
    cases x <;> rfl

@[nolint unused_arguments]
theorem Option.comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : Option α) :
  Option.traverseₓ (comp.mk ∘ (· <$> ·) f ∘ g) x = comp.mk (Option.traverseₓ f <$> Option.traverseₓ g x) :=
  by 
    cases x <;> simp' with functor_norm <;> rfl

theorem Option.traverse_eq_map_id {α β} (f : α → β) (x : Option α) : traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
  by 
    cases x <;> rfl

variable(η : ApplicativeTransformation F G)

theorem Option.naturality {α β} (f : α → F β) (x : Option α) :
  η (Option.traverseₓ f x) = Option.traverseₓ (@η _ ∘ f) x :=
  by 
    cases' x with x <;> simp' with functor_norm

end Option

instance  : IsLawfulTraversable Option :=
  { Option.is_lawful_monad with id_traverse := @Option.id_traverse, comp_traverse := @Option.comp_traverse,
    traverse_eq_map_id := @Option.traverse_eq_map_id, naturality := @Option.naturality }

namespace List

variable{F G : Type u → Type u}

variable[Applicativeₓ F][Applicativeₓ G]

section 

variable[IsLawfulApplicative F][IsLawfulApplicative G]

open Applicativeₓ Functor

open list(cons)

protected theorem id_traverse {α} (xs : List α) : List.traverseₓ id.mk xs = xs :=
  by 
    induction xs <;> simp' with functor_norm <;> rfl

@[nolint unused_arguments]
protected theorem comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : List α) :
  List.traverseₓ (comp.mk ∘ (· <$> ·) f ∘ g) x = comp.mk (List.traverseₓ f <$> List.traverseₓ g x) :=
  by 
    induction x <;> simp' with functor_norm <;> rfl

protected theorem traverse_eq_map_id {α β} (f : α → β) (x : List α) : List.traverseₓ (id.mk ∘ f) x = id.mk (f <$> x) :=
  by 
    induction x <;> simp' with functor_norm <;> rfl

variable(η : ApplicativeTransformation F G)

protected theorem naturality {α β} (f : α → F β) (x : List α) : η (List.traverseₓ f x) = List.traverseₓ (@η _ ∘ f) x :=
  by 
    induction x <;> simp' with functor_norm

open Nat

instance  : IsLawfulTraversable.{u} List :=
  { List.is_lawful_monad with id_traverse := @List.id_traverse, comp_traverse := @List.comp_traverse,
    traverse_eq_map_id := @List.traverse_eq_map_id, naturality := @List.naturality }

end 

section Traverse

variable{α' β' : Type u}(f : α' → F β')

@[simp]
theorem traverse_nil : traverse f ([] : List α') = (pure [] : F (List β')) :=
  rfl

@[simp]
theorem traverse_cons (a : α') (l : List α') : traverse f (a :: l) = ((· :: ·) <$> f a)<*>traverse f l :=
  rfl

variable[IsLawfulApplicative F]

@[simp]
theorem traverse_append : ∀ as bs : List α', traverse f (as ++ bs) = ((· ++ ·) <$> traverse f as)<*>traverse f bs
| [], bs =>
  have  : Append.append ([] : List β') = id :=
    by 
      funext  <;> rfl 
  by 
    simp' [this] with functor_norm
| a :: as, bs =>
  by 
    simp' [traverse_append as bs] with functor_norm <;> congr

theorem mem_traverse {f : α' → Set β'} : ∀ l : List α' n : List β', n ∈ traverse f l ↔ forall₂ (fun b a => b ∈ f a) n l
| [], [] =>
  by 
    simp 
| a :: as, [] =>
  by 
    simp 
| [], b :: bs =>
  by 
    simp 
| a :: as, b :: bs =>
  by 
    simp [mem_traverse as bs]

end Traverse

end List

namespace Sum

section Traverse

variable{σ : Type u}

variable{F G : Type u → Type u}

variable[Applicativeₓ F][Applicativeₓ G]

open Applicativeₓ Functor

open list(cons)

protected theorem traverse_map {α β γ : Type u} (g : α → β) (f : β → G γ) (x : Sum σ α) :
  Sum.traverseₓ f (g <$> x) = Sum.traverseₓ (f ∘ g) x :=
  by 
    cases x <;> simp' [Sum.traverseₓ, id_map] with functor_norm <;> rfl

variable[IsLawfulApplicative F][IsLawfulApplicative G]

protected theorem id_traverse {σ α} (x : Sum σ α) : Sum.traverseₓ id.mk x = x :=
  by 
    cases x <;> rfl

@[nolint unused_arguments]
protected theorem comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : Sum σ α) :
  Sum.traverseₓ (comp.mk ∘ (· <$> ·) f ∘ g) x = comp.mk (Sum.traverseₓ f <$> Sum.traverseₓ g x) :=
  by 
    cases x <;> simp' [Sum.traverseₓ, map_id] with functor_norm <;> rfl

protected theorem traverse_eq_map_id {α β} (f : α → β) (x : Sum σ α) : Sum.traverseₓ (id.mk ∘ f) x = id.mk (f <$> x) :=
  by 
    induction x <;> simp' with functor_norm <;> rfl

protected theorem map_traverse {α β γ} (g : α → G β) (f : β → γ) (x : Sum σ α) :
  (· <$> ·) f <$> Sum.traverseₓ g x = Sum.traverseₓ ((· <$> ·) f ∘ g) x :=
  by 
    cases x <;> simp' [Sum.traverseₓ, id_map] with functor_norm <;> congr <;> rfl

variable(η : ApplicativeTransformation F G)

protected theorem naturality {α β} (f : α → F β) (x : Sum σ α) : η (Sum.traverseₓ f x) = Sum.traverseₓ (@η _ ∘ f) x :=
  by 
    cases x <;> simp' [Sum.traverseₓ] with functor_norm

end Traverse

instance  {σ : Type u} : IsLawfulTraversable.{u} (Sum σ) :=
  { Sum.is_lawful_monad with id_traverse := @Sum.id_traverse σ, comp_traverse := @Sum.comp_traverse σ,
    traverse_eq_map_id := @Sum.traverse_eq_map_id σ, naturality := @Sum.naturality σ }

end Sum

