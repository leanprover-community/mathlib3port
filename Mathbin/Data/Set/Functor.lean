/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathbin.Data.Set.Lattice

/-!
# Functoriality of `set`

This file defines the functor structure of `set`.
-/


universe u

open Function

namespace Set

variable {α β : Type u} {s : Set α} {f : α → Set β} {g : Set (α → β)}

instance : Monad.{u} Set where
  pure α a := {a}
  bind α β s f := ⋃ i ∈ s, f i
  seq α β := Set.Seq
  map α β := Set.Image

@[simp]
theorem bind_def : s >>= f = ⋃ i ∈ s, f i :=
  rfl

@[simp]
theorem fmap_eq_image (f : α → β) : f <$> s = f '' s :=
  rfl

@[simp]
theorem seq_eq_set_seq (s : Set (α → β)) (t : Set α) : s <*> t = s.seq t :=
  rfl

@[simp]
theorem pure_def (a : α) : (pure a : Set α) = {a} :=
  rfl

/-- `set.image2` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem image2_def {α β γ : Type _} (f : α → β → γ) (s : Set α) (t : Set β) : Image2 f s t = f <$> s <*> t := by
  ext
  simp

instance : LawfulMonad Set where
  id_map α := image_id
  comp_map α β γ f g s := image_comp _ _ _
  pure_bind α β := bUnion_singleton
  bind_assoc α β γ s f g := by simp only [bind_def, bUnion_Union]
  bind_pure_comp_eq_map α β f s := (image_eq_Union _ _).symm
  bind_map_eq_seq α β s t := seq_def.symm

instance : IsCommApplicative (Set : Type u → Type u) :=
  ⟨fun α β s t => prod_image_seq_comm s t⟩

instance : Alternative Set :=
  { Set.monad with orelse := fun α => (· ∪ ·), failure := fun α => ∅ }

end Set

