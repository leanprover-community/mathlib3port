/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Logic.Basic

/-!
# Relator for functions, pairs, sums, and lists.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/385
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

def LiftFun (f : α → γ) (g : β → δ) : Prop :=
  ∀ ⦃a b⦄, R a b → S (f a) (g b)

-- mathport name: «expr ⇒ »
infixr:40 " ⇒ " => LiftFun

end

section

variable {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

def RightTotal : Prop :=
  ∀ b, ∃ a, R a b

def LeftTotal : Prop :=
  ∀ a, ∃ b, R a b

def BiTotal : Prop :=
  LeftTotal R ∧ RightTotal R

def LeftUnique : Prop :=
  ∀ ⦃a b c⦄, R a c → R b c → a = b

def RightUnique : Prop :=
  ∀ ⦃a b c⦄, R a b → R a c → b = c

def BiUnique : Prop :=
  LeftUnique R ∧ RightUnique R

variable {R}

/- warning: relator.right_total.rel_forall -> Relator.RightTotal.rel_forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u₁}} {β : Type.{u₂}} {R : α -> β -> Prop}, (Relator.RightTotal.{u₁ u₂} α β R) -> (Relator.LiftFun.{(max (succ u₁) 1) (max (succ u₂) 1) 1 1} (α -> Prop) (β -> Prop) Prop Prop (Relator.LiftFun.{succ u₁ succ u₂ 1 1} α β Prop Prop R Implies) Implies (fun (p : α -> Prop) => forall (i : α), p i) (fun (q : β -> Prop) => forall (i : β), q i))
but is expected to have type
  forall {α : Type.{u₁}} {β : Type.{u₂}} {R : α -> β -> Prop}, (Relator.RightTotal.{u₁ u₂} α β R) -> (Relator.LiftFun.{(max (succ u₁) (succ u_1)) succ u₂ succ (imax (succ u₁) u_1) 1} (α -> Sort.{u_1}) (β -> Prop) Sort.{imax (succ u₁) u_1} Prop (Relator.LiftFun.{succ u₁ succ u₂ succ u_1 1} α β Sort.{u_1} Prop R (fun (a._@.Mathlib.Logic.Relator._hyg.939 : Sort.{u_1}) (a._@.Mathlib.Logic.Relator._hyg.940 : Prop) => a._@.Mathlib.Logic.Relator._hyg.939 -> a._@.Mathlib.Logic.Relator._hyg.940)) (fun (a._@.Mathlib.Logic.Relator._hyg.950 : Sort.{imax (succ u₁) u_1}) (a._@.Mathlib.Logic.Relator._hyg.951 : Prop) => a._@.Mathlib.Logic.Relator._hyg.950 -> a._@.Mathlib.Logic.Relator._hyg.951) (fun (p : α -> Sort.{u_1}) => forall (i : α), p i) (fun (q : β -> Prop) => forall (i : β), q i))
Case conversion may be inaccurate. Consider using '#align relator.right_total.rel_forall Relator.RightTotal.rel_forallₓ'. -/
theorem RightTotal.rel_forall (h : RightTotal R) : ((R ⇒ Implies) ⇒ Implies) (fun p => ∀ i, p i) fun q => ∀ i, q i :=
  fun p q Hrel H b => Exists.elim (h b) fun a Rab => Hrel Rab (H _)

theorem LeftTotal.rel_exists (h : LeftTotal R) : ((R ⇒ Implies) ⇒ Implies) (fun p => ∃ i, p i) fun q => ∃ i, q i :=
  fun p q Hrel ⟨a, pa⟩ => (h a).imp fun b Rab => Hrel Rab pa

theorem BiTotal.rel_forall (h : BiTotal R) : ((R ⇒ Iff) ⇒ Iff) (fun p => ∀ i, p i) fun q => ∀ i, q i := fun p q Hrel =>
  ⟨fun H b => Exists.elim (h.right b) fun a Rab => (Hrel Rab).mp (H _), fun H a =>
    Exists.elim (h.left a) fun b Rab => (Hrel Rab).mpr (H _)⟩

theorem BiTotal.rel_exists (h : BiTotal R) : ((R ⇒ Iff) ⇒ Iff) (fun p => ∃ i, p i) fun q => ∃ i, q i := fun p q Hrel =>
  ⟨fun ⟨a, pa⟩ => (h.left a).imp fun b Rab => (Hrel Rab).1 pa, fun ⟨b, qb⟩ =>
    (h.right b).imp fun a Rab => (Hrel Rab).2 qb⟩

theorem left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ R ⇒ Iff) Eq eq') : LeftUnique R :=
  fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)

end

theorem rel_imp : (Iff ⇒ Iff ⇒ Iff) Implies Implies := fun p q h r s l => imp_congr h l

theorem rel_not : (Iff ⇒ Iff) Not Not := fun p q h => not_congr h

theorem bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
  { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

/- warning: relator.left_unique.flip -> Relator.LeftUnique.flip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {r : α -> β -> Prop}, (Relator.LeftUnique.{u_1 u_2} α β r) -> (Relator.RightUnique.{u_2 u_1} β α (flip.{succ u_1 succ u_2 1} α β Prop r))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {r : α -> β -> Prop}, (Relator.LeftUnique.{u_1 u_2} α β r) -> (Relator.RightUnique.{u_2 u_1} β α (flip.{succ u_1 succ u_2 1} α β Prop r))
Case conversion may be inaccurate. Consider using '#align relator.left_unique.flip Relator.LeftUnique.flipₓ'. -/
theorem LeftUnique.flip (h : LeftUnique r) : RightUnique (flip r) := fun a b c h₁ h₂ => h h₁ h₂

theorem rel_and : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∧ ·) (· ∧ ·) := fun a b h₁ c d h₂ => and_congr h₁ h₂

theorem rel_or : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∨ ·) (· ∨ ·) := fun a b h₁ c d h₂ => or_congr h₁ h₂

theorem rel_iff : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ↔ ·) (· ↔ ·) := fun a b h₁ c d h₂ => iff_congr h₁ h₂

/- warning: relator.rel_eq -> Relator.rel_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {r : α -> β -> Prop}, (Relator.BiUnique.{u_1 u_2} α β r) -> (Relator.LiftFun.{succ u_1 succ u_2 (max (succ u_1) 1) (max (succ u_2) 1)} α β (α -> Prop) (β -> Prop) r (Relator.LiftFun.{succ u_1 succ u_2 1 1} α β Prop Prop r Iff) (Eq.{succ u_1} α) (Eq.{succ u_2} β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {r : α -> β -> Prop}, (Relator.BiUnique.{u_1 u_2} α β r) -> (Relator.LiftFun.{succ u_1 succ u_2 succ u_1 succ u_2} α β (α -> Prop) (β -> Prop) r (Relator.LiftFun.{succ u_1 succ u_2 1 1} α β Prop Prop r (fun (a._@.Mathlib.Logic.Relator._hyg.1985 : Prop) (a._@.Mathlib.Logic.Relator._hyg.1986 : Prop) => Iff a._@.Mathlib.Logic.Relator._hyg.1985 a._@.Mathlib.Logic.Relator._hyg.1986)) (fun (a._@.Mathlib.Logic.Relator._hyg.1998 : α) (a._@.Mathlib.Logic.Relator._hyg.1999 : α) => Eq.{succ u_1} α a._@.Mathlib.Logic.Relator._hyg.1998 a._@.Mathlib.Logic.Relator._hyg.1999) (fun (a._@.Mathlib.Logic.Relator._hyg.2011 : β) (a._@.Mathlib.Logic.Relator._hyg.2012 : β) => Eq.{succ u_2} β a._@.Mathlib.Logic.Relator._hyg.2011 a._@.Mathlib.Logic.Relator._hyg.2012))
Case conversion may be inaccurate. Consider using '#align relator.rel_eq Relator.rel_eqₓ'. -/
theorem rel_eq {r : α → β → Prop} (hr : BiUnique r) : (r ⇒ r ⇒ (· ↔ ·)) (· = ·) (· = ·) := fun a b h₁ c d h₂ =>
  ⟨fun h => hr.right h₁ <| h.symm ▸ h₂, fun h => hr.left h₁ <| h.symm ▸ h₂⟩

end Relator

