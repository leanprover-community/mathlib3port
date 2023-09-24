/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Data.Set.Lattice

#align_import data.set.functor from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Functoriality of `set`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the functor structure of `set`.
-/


universe u

open Function

namespace Set

variable {α β : Type u} {s : Set α} {f : α → Set β} {g : Set (α → β)}

instance : Monad.{u} Set where
  pure α a := {a}
  bind α β s f := ⋃ i ∈ s, f i
  seq α β := Set.seq
  map α β := Set.image

#print Set.bind_def /-
@[simp]
theorem bind_def : s >>= f = ⋃ i ∈ s, f i :=
  rfl
#align set.bind_def Set.bind_def
-/

#print Set.fmap_eq_image /-
@[simp]
theorem fmap_eq_image (f : α → β) : f <$> s = f '' s :=
  rfl
#align set.fmap_eq_image Set.fmap_eq_image
-/

#print Set.seq_eq_set_seq /-
@[simp]
theorem seq_eq_set_seq (s : Set (α → β)) (t : Set α) : s <*> t = s.seq t :=
  rfl
#align set.seq_eq_set_seq Set.seq_eq_set_seq
-/

#print Set.pure_def /-
@[simp]
theorem pure_def (a : α) : (pure a : Set α) = {a} :=
  rfl
#align set.pure_def Set.pure_def
-/

#print Set.image2_def /-
/-- `set.image2` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem image2_def {α β γ : Type _} (f : α → β → γ) (s : Set α) (t : Set β) :
    image2 f s t = f <$> s <*> t := by ext; simp
#align set.image2_def Set.image2_def
-/

instance : LawfulMonad Set where
  id_map α := image_id
  comp_map α β γ f g s := image_comp _ _ _
  pure_bind α β := biUnion_singleton
  bind_assoc α β γ s f g := by simp only [bind_def, bUnion_Union]
  bind_pure_comp α β f s := (image_eq_iUnion _ _).symm
  bind_map α β s t := seq_def.symm

instance : CommApplicative (Set : Type u → Type u) :=
  ⟨fun α β s t => prod_image_seq_comm s t⟩

instance : Alternative Set :=
  { Set.monad with
    orelse := fun α => (· ∪ ·)
    failure := fun α => ∅ }

end Set

