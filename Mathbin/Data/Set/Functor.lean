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

instance : Monadₓ.{u} Set where
  pure := fun α a => {a}
  bind := fun α β s f => ⋃ i ∈ s, f i
  seq := fun α β => Set.Seq
  map := fun α β => Set.Image

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

instance : IsLawfulMonad Set where
  pure_bind := fun α β x f => by
    simp
  bind_assoc := fun α β γ s f g =>
    Set.ext fun a => by
      simp [exists_and_distrib_right.symm, -exists_and_distrib_right, exists_and_distrib_left.symm,
          -exists_and_distrib_left, and_assoc] <;>
        exact exists_swap
  id_map := fun α => id_map
  bind_pure_comp_eq_map := fun α β f s =>
    Set.ext <| by
      simp [Set.Image, eq_comm]
  bind_map_eq_seq := fun α β s t => by
    simp [seq_def]

instance : IsCommApplicative (Set : Type u → Type u) :=
  ⟨fun α β s t => prod_image_seq_comm s t⟩

instance : Alternativeₓ Set :=
  { Set.monad with orelse := fun α => (· ∪ ·), failure := fun α => ∅ }

end Set

