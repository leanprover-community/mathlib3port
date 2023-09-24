/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Logic.Basic

#align_import logic.relator from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Relator for functions, pairs, sums, and lists.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Relator

universe u₁ u₂ v₁ v₂

/- TODO(johoelzl):
 * should we introduce relators of datatypes as recursive function or as inductive
predicate? For now we stick to the recursor approach.
 * relation lift for datatypes, Π, Σ, set, and subtype types
 * proof composition and identity laws
 * implement method to derive relators from datatype
-/
section

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}

variable (R : α → β → Prop) (S : γ → δ → Prop)

#print Relator.LiftFun /-
def LiftFun (f : α → γ) (g : β → δ) : Prop :=
  ∀ ⦃a b⦄, R a b → S (f a) (g b)
#align relator.lift_fun Relator.LiftFun
-/

infixr:40 " ⇒ " => LiftFun

end

section

variable {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

#print Relator.RightTotal /-
def RightTotal : Prop :=
  ∀ b, ∃ a, R a b
#align relator.right_total Relator.RightTotal
-/

#print Relator.LeftTotal /-
def LeftTotal : Prop :=
  ∀ a, ∃ b, R a b
#align relator.left_total Relator.LeftTotal
-/

#print Relator.BiTotal /-
def BiTotal : Prop :=
  LeftTotal R ∧ RightTotal R
#align relator.bi_total Relator.BiTotal
-/

#print Relator.LeftUnique /-
def LeftUnique : Prop :=
  ∀ ⦃a b c⦄, R a c → R b c → a = b
#align relator.left_unique Relator.LeftUnique
-/

#print Relator.RightUnique /-
def RightUnique : Prop :=
  ∀ ⦃a b c⦄, R a b → R a c → b = c
#align relator.right_unique Relator.RightUnique
-/

#print Relator.BiUnique /-
def BiUnique : Prop :=
  LeftUnique R ∧ RightUnique R
#align relator.bi_unique Relator.BiUnique
-/

variable {R}

#print Relator.RightTotal.rel_forall /-
theorem RightTotal.rel_forall (h : RightTotal R) :
    ((R ⇒ Implies) ⇒ Implies) (fun p => ∀ i, p i) fun q => ∀ i, q i := fun p q Hrel H b =>
  Exists.elim (h b) fun a Rab => Hrel Rab (H _)
#align relator.right_total.rel_forall Relator.RightTotal.rel_forall
-/

#print Relator.LeftTotal.rel_exists /-
theorem LeftTotal.rel_exists (h : LeftTotal R) :
    ((R ⇒ Implies) ⇒ Implies) (fun p => ∃ i, p i) fun q => ∃ i, q i := fun p q Hrel ⟨a, pa⟩ =>
  (h a).imp fun b Rab => Hrel Rab pa
#align relator.left_total.rel_exists Relator.LeftTotal.rel_exists
-/

#print Relator.BiTotal.rel_forall /-
theorem BiTotal.rel_forall (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => ∀ i, p i) fun q => ∀ i, q i := fun p q Hrel =>
  ⟨fun H b => Exists.elim (h.right b) fun a Rab => (Hrel Rab).mp (H _), fun H a =>
    Exists.elim (h.left a) fun b Rab => (Hrel Rab).mpr (H _)⟩
#align relator.bi_total.rel_forall Relator.BiTotal.rel_forall
-/

#print Relator.BiTotal.rel_exists /-
theorem BiTotal.rel_exists (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => ∃ i, p i) fun q => ∃ i, q i := fun p q Hrel =>
  ⟨fun ⟨a, pa⟩ => (h.left a).imp fun b Rab => (Hrel Rab).1 pa, fun ⟨b, qb⟩ =>
    (h.right b).imp fun a Rab => (Hrel Rab).2 qb⟩
#align relator.bi_total.rel_exists Relator.BiTotal.rel_exists
-/

#print Relator.left_unique_of_rel_eq /-
theorem left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ R ⇒ Iff) Eq eq') : LeftUnique R :=
  fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)
#align relator.left_unique_of_rel_eq Relator.left_unique_of_rel_eq
-/

end

#print Relator.rel_imp /-
theorem rel_imp : (Iff ⇒ Iff ⇒ Iff) Implies Implies := fun p q h r s l => imp_congr h l
#align relator.rel_imp Relator.rel_imp
-/

#print Relator.rel_not /-
theorem rel_not : (Iff ⇒ Iff) Not Not := fun p q h => not_congr h
#align relator.rel_not Relator.rel_not
-/

#print Relator.bi_total_eq /-
theorem bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
  { left := fun a => ⟨a, rfl⟩
    right := fun a => ⟨a, rfl⟩ }
#align relator.bi_total_eq Relator.bi_total_eq
-/

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

#print Relator.LeftUnique.flip /-
theorem LeftUnique.flip (h : LeftUnique r) : RightUnique (flip r) := fun a b c h₁ h₂ => h h₁ h₂
#align relator.left_unique.flip Relator.LeftUnique.flip
-/

#print Relator.rel_and /-
theorem rel_and : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∧ ·) (· ∧ ·) := fun a b h₁ c d h₂ =>
  and_congr h₁ h₂
#align relator.rel_and Relator.rel_and
-/

#print Relator.rel_or /-
theorem rel_or : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∨ ·) (· ∨ ·) := fun a b h₁ c d h₂ =>
  or_congr h₁ h₂
#align relator.rel_or Relator.rel_or
-/

#print Relator.rel_iff /-
theorem rel_iff : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ↔ ·) (· ↔ ·) := fun a b h₁ c d h₂ =>
  iff_congr h₁ h₂
#align relator.rel_iff Relator.rel_iff
-/

#print Relator.rel_eq /-
theorem rel_eq {r : α → β → Prop} (hr : BiUnique r) : (r ⇒ r ⇒ (· ↔ ·)) (· = ·) (· = ·) :=
  fun a b h₁ c d h₂ => ⟨fun h => hr.right h₁ <| h.symm ▸ h₂, fun h => hr.left h₁ <| h.symm ▸ h₂⟩
#align relator.rel_eq Relator.rel_eq
-/

end Relator

