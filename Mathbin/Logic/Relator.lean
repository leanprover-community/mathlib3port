import Mathbin.Logic.Basic

namespace Relator

universe u₁ u₂ v₁ v₂

section

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}

variable (R : α → β → Prop) (S : γ → δ → Prop)

def lift_fun (f : α → γ) (g : β → δ) : Prop :=
  ∀ ⦃a b⦄, R a b → S (f a) (g b)

infixr:40 "⇒" => lift_fun

end

section

variable {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

def right_total : Prop :=
  ∀ b, ∃ a, R a b

def left_total : Prop :=
  ∀ a, ∃ b, R a b

def bi_total : Prop :=
  left_total R ∧ right_total R

def left_unique : Prop :=
  ∀ ⦃a b c⦄, R a c → R b c → a = b

def right_unique : Prop :=
  ∀ ⦃a b c⦄, R a b → R a c → b = c

def bi_unique : Prop :=
  left_unique R ∧ right_unique R

variable {R}

theorem right_total.rel_forall (h : right_total R) : ((R⇒Implies)⇒Implies) (fun p => ∀ i, p i) fun q => ∀ i, q i :=
  fun p q Hrel H b => Exists.elim (h b) fun a Rab => Hrel Rab (H _)

theorem left_total.rel_exists (h : left_total R) : ((R⇒Implies)⇒Implies) (fun p => ∃ i, p i) fun q => ∃ i, q i :=
  fun p q Hrel ⟨a, pa⟩ => (h a).imp $ fun b Rab => Hrel Rab pa

theorem bi_total.rel_forall (h : bi_total R) : ((R⇒Iff)⇒Iff) (fun p => ∀ i, p i) fun q => ∀ i, q i := fun p q Hrel =>
  ⟨fun H b => Exists.elim (h.right b) fun a Rab => (Hrel Rab).mp (H _), fun H a =>
    Exists.elim (h.left a) fun b Rab => (Hrel Rab).mpr (H _)⟩

theorem bi_total.rel_exists (h : bi_total R) : ((R⇒Iff)⇒Iff) (fun p => ∃ i, p i) fun q => ∃ i, q i := fun p q Hrel =>
  ⟨fun ⟨a, pa⟩ => (h.left a).imp $ fun b Rab => (Hrel Rab).1 pa, fun ⟨b, qb⟩ =>
    (h.right b).imp $ fun a Rab => (Hrel Rab).2 qb⟩

theorem left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R⇒R⇒Iff) Eq eq') : left_unique R :=
  fun a b c ac : R a c bc : R b c => (he ac bc).mpr ((he bc bc).mp rfl)

end

theorem rel_imp : (Iff⇒Iff⇒Iff) Implies Implies := fun p q h r s l => imp_congr h l

theorem rel_not : (Iff⇒Iff) Not Not := fun p q h => not_congr h

theorem bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
  { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

theorem left_unique.flip (h : left_unique r) : right_unique (flip r) := fun a b c h₁ h₂ => h h₁ h₂

theorem rel_and : ((· ↔ ·)⇒(· ↔ ·)⇒(· ↔ ·)) (· ∧ ·) (· ∧ ·) := fun a b h₁ c d h₂ => and_congr h₁ h₂

theorem rel_or : ((· ↔ ·)⇒(· ↔ ·)⇒(· ↔ ·)) (· ∨ ·) (· ∨ ·) := fun a b h₁ c d h₂ => or_congr h₁ h₂

theorem rel_iff : ((· ↔ ·)⇒(· ↔ ·)⇒(· ↔ ·)) (· ↔ ·) (· ↔ ·) := fun a b h₁ c d h₂ => iff_congr h₁ h₂

theorem rel_eq {r : α → β → Prop} (hr : bi_unique r) : (r⇒r⇒(· ↔ ·)) (· = ·) (· = ·) := fun a b h₁ c d h₂ =>
  Iff.intro
    (by
      intro h
      subst h
      exact hr.right h₁ h₂)
    (by
      intro h
      subst h
      exact hr.left h₁ h₂)

end Relator

