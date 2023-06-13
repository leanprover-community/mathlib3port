/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module data.set.constructions
! leanprover-community/mathlib commit e04043d6bf7264a3c84bc69711dc354958ca4516
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Basic

/-!
# Constructions involving sets of sets.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Finite Intersections

We define a structure `has_finite_inter` which asserts that a set `S` of subsets of `α` is
closed under finite intersections.

We define `finite_inter_closure` which, given a set `S` of subsets of `α`, is the smallest
set of subsets of `α` which is closed under finite intersections.

`finite_inter_closure S` is endowed with a term of type `has_finite_inter` using
`finite_inter_closure_has_finite_inter`.

-/


variable {α : Type _} (S : Set (Set α))

#print FiniteInter /-
/-- A structure encapsulating the fact that a set of sets is closed under finite intersection. -/
structure FiniteInter : Prop where
  univ_mem : Set.univ ∈ S
  inter_mem : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → s ∩ t ∈ S
#align has_finite_inter FiniteInter
-/

namespace FiniteInter

#print FiniteInter.finiteInterClosure /-
/-- The smallest set of sets containing `S` which is closed under finite intersections. -/
inductive finiteInterClosure : Set (Set α)
  | basic {s} : s ∈ S → finite_inter_closure s
  | univ : finite_inter_closure Set.univ
  | inter {s t} : finite_inter_closure s → finite_inter_closure t → finite_inter_closure (s ∩ t)
#align has_finite_inter.finite_inter_closure FiniteInter.finiteInterClosure
-/

#print FiniteInter.finiteInterClosure_finiteInter /-
theorem finiteInterClosure_finiteInter : FiniteInter (finiteInterClosure S) :=
  { univ_mem := finiteInterClosure.univ
    inter_mem := fun _ h _ => finiteInterClosure.inter h }
#align has_finite_inter.finite_inter_closure_has_finite_inter FiniteInter.finiteInterClosure_finiteInter
-/

variable {S}

#print FiniteInter.finiteInter_mem /-
theorem finiteInter_mem (cond : FiniteInter S) (F : Finset (Set α)) :
    ↑F ⊆ S → ⋂₀ (↑F : Set (Set α)) ∈ S := by
  classical
  refine' Finset.induction_on F (fun _ => _) _
  · simp [cond.univ_mem]
  · intro a s h1 h2 h3
    suffices a ∩ ⋂₀ ↑s ∈ S by simpa
    exact
      cond.inter_mem (h3 (Finset.mem_insert_self a s))
        (h2 fun x hx => h3 <| Finset.mem_insert_of_mem hx)
#align has_finite_inter.finite_inter_mem FiniteInter.finiteInter_mem
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (P «expr ∈ » finite_inter_closure[has_finite_inter.finite_inter_closure] (insert[has_insert.insert] A S)) -/
#print FiniteInter.finiteInterClosure_insert /-
theorem finiteInterClosure_insert {A : Set α} (cond : FiniteInter S) (P)
    (_ : P ∈ finiteInterClosure (insert A S)) : P ∈ S ∨ ∃ Q ∈ S, P = A ∩ Q :=
  by
  induction' H with S h T1 T2 _ _ h1 h2
  · cases h
    · exact Or.inr ⟨Set.univ, cond.univ_mem, by simpa⟩
    · exact Or.inl h
  · exact Or.inl cond.univ_mem
  · rcases h1 with (h | ⟨Q, hQ, rfl⟩) <;> rcases h2 with (i | ⟨R, hR, rfl⟩)
    · exact Or.inl (cond.inter_mem h i)
    ·
      exact
        Or.inr ⟨T1 ∩ R, cond.inter_mem h hR, by simp only [← Set.inter_assoc, Set.inter_comm _ A]⟩
    · exact Or.inr ⟨Q ∩ T2, cond.inter_mem hQ i, by simp only [Set.inter_assoc]⟩
    ·
      exact
        Or.inr
          ⟨Q ∩ R, cond.inter_mem hQ hR, by ext x;
            constructor <;> simp (config := { contextual := true })⟩
#align has_finite_inter.finite_inter_closure_insert FiniteInter.finiteInterClosure_insert
-/

end FiniteInter

