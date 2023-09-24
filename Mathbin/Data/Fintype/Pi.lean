/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Fintype.Basic
import Data.Finset.Pi

#align_import data.fintype.pi from "leanprover-community/mathlib"@"e04043d6bf7264a3c84bc69711dc354958ca4516"

/-!
# fintype instances for pi types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

open Finset

namespace Fintype

variable [DecidableEq α] [Fintype α] {δ : α → Type _}

#print Fintype.piFinset /-
/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `fintype.pi_finset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ finset.univ` in the `finset.pi` definition). -/
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ => by simp [Function.funext_iff]⟩
#align fintype.pi_finset Fintype.piFinset
-/

#print Fintype.mem_piFinset /-
@[simp]
theorem mem_piFinset {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a} : f ∈ piFinset t ↔ ∀ a, f a ∈ t a :=
  by
  constructor
  · simp only [pi_finset, mem_map, and_imp, forall_prop_of_true, exists_prop, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [pi_finset, mem_map, forall_prop_of_true, exists_prop, mem_univ, mem_pi]
    exact fun hf => ⟨fun a ha => f a, hf, rfl⟩
#align fintype.mem_pi_finset Fintype.mem_piFinset
-/

#print Fintype.coe_piFinset /-
@[simp]
theorem coe_piFinset (t : ∀ a, Finset (δ a)) :
    (piFinset t : Set (∀ a, δ a)) = Set.pi Set.univ fun a => t a :=
  Set.ext fun x => by rw [Set.mem_univ_pi]; exact Fintype.mem_piFinset
#align fintype.coe_pi_finset Fintype.coe_piFinset
-/

#print Fintype.piFinset_subset /-
theorem piFinset_subset (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) :
    piFinset t₁ ⊆ piFinset t₂ := fun g hg => mem_piFinset.2 fun a => h a <| mem_piFinset.1 hg a
#align fintype.pi_finset_subset Fintype.piFinset_subset
-/

#print Fintype.piFinset_empty /-
@[simp]
theorem piFinset_empty [Nonempty α] : piFinset (fun _ => ∅ : ∀ i, Finset (δ i)) = ∅ :=
  eq_empty_of_forall_not_mem fun _ => by simp
#align fintype.pi_finset_empty Fintype.piFinset_empty
-/

#print Fintype.piFinset_singleton /-
@[simp]
theorem piFinset_singleton (f : ∀ i, δ i) : piFinset (fun i => {f i} : ∀ i, Finset (δ i)) = {f} :=
  ext fun _ => by simp only [Function.funext_iff, Fintype.mem_piFinset, mem_singleton]
#align fintype.pi_finset_singleton Fintype.piFinset_singleton
-/

#print Fintype.piFinset_subsingleton /-
theorem piFinset_subsingleton {f : ∀ i, Finset (δ i)} (hf : ∀ i, (f i : Set (δ i)).Subsingleton) :
    (Fintype.piFinset f : Set (∀ i, δ i)).Subsingleton := fun a ha b hb =>
  funext fun i => hf _ (mem_piFinset.1 ha _) (mem_piFinset.1 hb _)
#align fintype.pi_finset_subsingleton Fintype.piFinset_subsingleton
-/

#print Fintype.piFinset_disjoint_of_disjoint /-
theorem piFinset_disjoint_of_disjoint (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (piFinset t₁) (piFinset t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_piFinset.1 hf₁ a) (f₂ a) (mem_piFinset.1 hf₂ a)
      (congr_fun eq₁₂ a)
#align fintype.pi_finset_disjoint_of_disjoint Fintype.piFinset_disjoint_of_disjoint
-/

end Fintype

/-! ### pi -/


#print Pi.fintype /-
/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance Pi.fintype {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
    Fintype (∀ a, β a) :=
  ⟨Fintype.piFinset fun _ => univ, by simp⟩
#align pi.fintype Pi.fintype
-/

#print Fintype.piFinset_univ /-
@[simp]
theorem Fintype.piFinset_univ {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) =
      (Finset.univ : Finset (∀ a, β a)) :=
  rfl
#align fintype.pi_finset_univ Fintype.piFinset_univ
-/

#print Function.Embedding.fintype /-
instance Function.Embedding.fintype {α β} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Fintype (α ↪ β) :=
  Fintype.ofEquiv _ (Equiv.subtypeInjectiveEquivEmbedding α β)
#align function.embedding.fintype Function.Embedding.fintype
-/

#print Finset.univ_pi_univ /-
@[simp]
theorem Finset.univ_pi_univ {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Finset.univ.pi fun a : α => (Finset.univ : Finset (β a))) = Finset.univ := by ext; simp
#align finset.univ_pi_univ Finset.univ_pi_univ
-/

