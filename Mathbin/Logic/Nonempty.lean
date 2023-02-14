/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module logic.nonempty
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Basic

/-!
# Nonempty types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves a few extra facts about `nonempty`, which is defined in core Lean.

## Main declarations

* `nonempty.some`: Extracts a witness of nonemptiness using choice. Takes `nonempty α` explicitly.
* `classical.arbitrary`: Extracts a witness of nonemptiness using choice. Takes `nonempty α` as an
  instance.
-/


variable {α β : Type _} {γ : α → Type _}

attribute [simp] instNonempty

#print Zero.nonempty /-
instance (priority := 20) Zero.nonempty [Zero α] : Nonempty α :=
  ⟨0⟩
#align has_zero.nonempty Zero.nonempty
-/

#print One.nonempty /-
instance (priority := 20) One.nonempty [One α] : Nonempty α :=
  ⟨1⟩
#align has_one.nonempty One.nonempty
-/

#print exists_true_iff_nonempty /-
theorem exists_true_iff_nonempty {α : Sort _} : (∃ a : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨a, trivial⟩
#align exists_true_iff_nonempty exists_true_iff_nonempty
-/

#print nonempty_Prop /-
@[simp]
theorem nonempty_Prop {p : Prop} : Nonempty p ↔ p :=
  Iff.intro (fun ⟨h⟩ => h) fun h => ⟨h⟩
#align nonempty_Prop nonempty_Prop
-/

#print not_nonempty_iff_imp_false /-
theorem not_nonempty_iff_imp_false {α : Sort _} : ¬Nonempty α ↔ α → False :=
  ⟨fun h a => h ⟨a⟩, fun h ⟨a⟩ => h a⟩
#align not_nonempty_iff_imp_false not_nonempty_iff_imp_false
-/

#print nonempty_sigma /-
@[simp]
theorem nonempty_sigma : Nonempty (Σa : α, γ a) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩
#align nonempty_sigma nonempty_sigma
-/

/- warning: nonempty_psigma -> nonempty_psigma is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}}, Iff (Nonempty.{max 1 u1 u2} (PSigma.{u1, u2} α β)) (Exists.{u1} α (fun (a : α) => Nonempty.{u2} (β a)))
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}}, Iff (Nonempty.{max (max 1 u1) u2} (PSigma.{u2, u1} α β)) (Exists.{u2} α (fun (a : α) => Nonempty.{u1} (β a)))
Case conversion may be inaccurate. Consider using '#align nonempty_psigma nonempty_psigmaₓ'. -/
@[simp]
theorem nonempty_psigma {α} {β : α → Sort _} : Nonempty (PSigma β) ↔ ∃ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩
#align nonempty_psigma nonempty_psigma

#print nonempty_subtype /-
@[simp]
theorem nonempty_subtype {α} {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ a : α, p a :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩
#align nonempty_subtype nonempty_subtype
-/

#print nonempty_prod /-
@[simp]
theorem nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩
#align nonempty_prod nonempty_prod
-/

/- warning: nonempty_pprod -> nonempty_pprod is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, Iff (Nonempty.{max 1 u1 u2} (PProd.{u1, u2} α β)) (And (Nonempty.{u1} α) (Nonempty.{u2} β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, Iff (Nonempty.{max (max 1 u1) u2} (PProd.{u2, u1} α β)) (And (Nonempty.{u2} α) (Nonempty.{u1} β))
Case conversion may be inaccurate. Consider using '#align nonempty_pprod nonempty_pprodₓ'. -/
@[simp]
theorem nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩
#align nonempty_pprod nonempty_pprod

#print nonempty_sum /-
@[simp]
theorem nonempty_sum : Nonempty (Sum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩
#align nonempty_sum nonempty_sum
-/

/- warning: nonempty_psum -> nonempty_psum is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, Iff (Nonempty.{max 1 u1 u2} (PSum.{u1, u2} α β)) (Or (Nonempty.{u1} α) (Nonempty.{u2} β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, Iff (Nonempty.{max (max 1 u1) u2} (PSum.{u2, u1} α β)) (Or (Nonempty.{u2} α) (Nonempty.{u1} β))
Case conversion may be inaccurate. Consider using '#align nonempty_psum nonempty_psumₓ'. -/
@[simp]
theorem nonempty_psum {α β} : Nonempty (PSum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩
#align nonempty_psum nonempty_psum

@[simp]
theorem nonempty_empty : ¬Nonempty Empty := fun ⟨h⟩ => h.elim
#align nonempty_empty nonempty_empty

/- warning: nonempty_ulift -> nonempty_ulift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Iff (Nonempty.{succ (max u1 u2)} (ULift.{u2, u1} α)) (Nonempty.{succ u1} α)
but is expected to have type
  forall {α : Type.{u2}}, Iff (Nonempty.{max (succ u2) (succ u1)} (ULift.{u1, u2} α)) (Nonempty.{succ u2} α)
Case conversion may be inaccurate. Consider using '#align nonempty_ulift nonempty_uliftₓ'. -/
@[simp]
theorem nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩
#align nonempty_ulift nonempty_ulift

#print nonempty_plift /-
@[simp]
theorem nonempty_plift {α} : Nonempty (PLift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩
#align nonempty_plift nonempty_plift
-/

#print Nonempty.forall /-
@[simp]
theorem Nonempty.forall {α} {p : Nonempty α → Prop} : (∀ h : Nonempty α, p h) ↔ ∀ a, p ⟨a⟩ :=
  Iff.intro (fun h a => h _) fun h ⟨a⟩ => h _
#align nonempty.forall Nonempty.forall
-/

#print Nonempty.exists /-
@[simp]
theorem Nonempty.exists {α} {p : Nonempty α → Prop} : (∃ h : Nonempty α, p h) ↔ ∃ a, p ⟨a⟩ :=
  Iff.intro (fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩
#align nonempty.exists Nonempty.exists
-/

#print Classical.inhabited_of_nonempty' /-
/-- Using `classical.choice`, lifts a (`Prop`-valued) `nonempty` instance to a (`Type`-valued)
  `inhabited` instance. `classical.inhabited_of_nonempty` already exists, in
  `core/init/classical.lean`, but the assumption is not a type class argument,
  which makes it unsuitable for some applications. -/
noncomputable def Classical.inhabited_of_nonempty' {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩
#align classical.inhabited_of_nonempty' Classical.inhabited_of_nonempty'
-/

#print Nonempty.some /-
/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
@[reducible]
protected noncomputable def Nonempty.some {α} (h : Nonempty α) : α :=
  Classical.choice h
#align nonempty.some Nonempty.some
-/

#print Classical.arbitrary /-
/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
@[reducible]
protected noncomputable def Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h
#align classical.arbitrary Classical.arbitrary
-/

/- warning: nonempty.map -> Nonempty.map is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, (α -> β) -> (Nonempty.{u1} α) -> (Nonempty.{u2} β)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, (α -> β) -> (Nonempty.{u2} α) -> (Nonempty.{u1} β)
Case conversion may be inaccurate. Consider using '#align nonempty.map Nonempty.mapₓ'. -/
/-- Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
  `nonempty` cannot be a `functor`, because `functor` is restricted to `Type`. -/
theorem Nonempty.map {α β} (f : α → β) : Nonempty α → Nonempty β
  | ⟨h⟩ => ⟨f h⟩
#align nonempty.map Nonempty.map

/- warning: nonempty.map2 -> Nonempty.map2 is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}}, (α -> β -> γ) -> (Nonempty.{u1} α) -> (Nonempty.{u2} β) -> (Nonempty.{u3} γ)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}}, (α -> β -> γ) -> (Nonempty.{u3} α) -> (Nonempty.{u2} β) -> (Nonempty.{u1} γ)
Case conversion may be inaccurate. Consider using '#align nonempty.map2 Nonempty.map2ₓ'. -/
protected theorem Nonempty.map2 {α β γ : Sort _} (f : α → β → γ) :
    Nonempty α → Nonempty β → Nonempty γ
  | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩
#align nonempty.map2 Nonempty.map2

/- warning: nonempty.congr -> Nonempty.congr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, (α -> β) -> (β -> α) -> (Iff (Nonempty.{u1} α) (Nonempty.{u2} β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, (α -> β) -> (β -> α) -> (Iff (Nonempty.{u2} α) (Nonempty.{u1} β))
Case conversion may be inaccurate. Consider using '#align nonempty.congr Nonempty.congrₓ'. -/
protected theorem Nonempty.congr {α β} (f : α → β) (g : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map f, Nonempty.map g⟩
#align nonempty.congr Nonempty.congr

#print Nonempty.elim_to_inhabited /-
theorem Nonempty.elim_to_inhabited {α : Sort _} [h : Nonempty α] {p : Prop} (f : Inhabited α → p) :
    p :=
  h.elim <| f ∘ Inhabited.mk
#align nonempty.elim_to_inhabited Nonempty.elim_to_inhabited
-/

instance {α β} [h : Nonempty α] [h2 : Nonempty β] : Nonempty (α × β) :=
  h.elim fun g => h2.elim fun g2 => ⟨⟨g, g2⟩⟩

instance {ι : Sort _} {α : ι → Sort _} [∀ i, Nonempty (α i)] : Nonempty (∀ i, α i) :=
  ⟨fun _ => Classical.arbitrary _⟩

/- warning: classical.nonempty_pi -> Classical.nonempty_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : ι -> Sort.{u2}}, Iff (Nonempty.{imax u1 u2} (forall (i : ι), α i)) (forall (i : ι), Nonempty.{u2} (α i))
but is expected to have type
  forall {ι : Sort.{u2}} {α : ι -> Sort.{u1}}, Iff (Nonempty.{imax u2 u1} (forall (i : ι), α i)) (forall (i : ι), Nonempty.{u1} (α i))
Case conversion may be inaccurate. Consider using '#align classical.nonempty_pi Classical.nonempty_piₓ'. -/
theorem Classical.nonempty_pi {ι} {α : ι → Sort _} : Nonempty (∀ i, α i) ↔ ∀ i, Nonempty (α i) :=
  ⟨fun ⟨f⟩ a => ⟨f a⟩, @Pi.nonempty _ _⟩
#align classical.nonempty_pi Classical.nonempty_pi

#print subsingleton_of_not_nonempty /-
theorem subsingleton_of_not_nonempty {α : Sort _} (h : ¬Nonempty α) : Subsingleton α :=
  ⟨fun x => False.elim <| not_nonempty_iff_imp_false.mp h x⟩
#align subsingleton_of_not_nonempty subsingleton_of_not_nonempty
-/

/- warning: function.surjective.nonempty -> Function.Surjective.nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [h : Nonempty.{succ u2} β] {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (Nonempty.{succ u1} α)
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} [h : Nonempty.{u2} β] {f : α -> β}, (Function.Surjective.{u1, u2} α β f) -> (Nonempty.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.surjective.nonempty Function.Surjective.nonemptyₓ'. -/
theorem Function.Surjective.nonempty [h : Nonempty β] {f : α → β} (hf : Function.Surjective f) :
    Nonempty α :=
  let ⟨y⟩ := h
  let ⟨x, hx⟩ := hf y
  ⟨x⟩
#align function.surjective.nonempty Function.Surjective.nonempty

