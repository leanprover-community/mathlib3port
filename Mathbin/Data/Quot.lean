/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.quot
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Relator

/-!
# Quotient types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module extends the core library's treatment of quotient types (`init.data.quot`).

## Tags

quotient
-/


variable {α : Sort _} {β : Sort _}

open Function

namespace Setoid

#print Setoid.ext /-
theorem ext {α : Sort _} :
    ∀ {s t : Setoid α}, (∀ a b, @Setoid.r α s a b ↔ @Setoid.r α t a b) → s = t
  | ⟨r, _⟩, ⟨p, _⟩, Eq =>
    by
    have : r = p := funext fun a => funext fun b => propext <| Eq a b
    subst this
#align setoid.ext Setoid.ext
-/

end Setoid

namespace Quot

variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort _}

-- mathport name: mk
local notation:arg "⟦" a "⟧" => Quot.mk _ a

instance (r : α → α → Prop) [Inhabited α] : Inhabited (Quot r) :=
  ⟨⟦default⟧⟩

instance [Subsingleton α] : Subsingleton (Quot ra) :=
  ⟨fun x => Quot.inductionOn x fun y => Quot.ind fun b => congr_arg _ (Subsingleton.elim _ _)⟩

#print Quot.hrecOn₂ /-
/-- Recursion on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂ (qa : Quot ra) (qb : Quot rb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (ca : ∀ {b a₁ a₂}, ra a₁ a₂ → HEq (f a₁ b) (f a₂ b))
    (cb : ∀ {a b₁ b₂}, rb b₁ b₂ → HEq (f a b₁) (f a b₂)) : φ qa qb :=
  Quot.hrecOn qa (fun a => Quot.hrecOn qb (f a) fun b₁ b₂ pb => cb pb) fun a₁ a₂ pa =>
    Quot.inductionOn qb fun b =>
      calc
        HEq (@Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₁) (@cb _)) (f a₁ b) := by simp [hEq_self_iff_true]
        HEq _ (f a₂ b) := ca pa
        HEq _ (@Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₂) (@cb _)) := by simp [hEq_self_iff_true]
        
#align quot.hrec_on₂ Quot.hrecOn₂
-/

#print Quot.map /-
/-- Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `quot ra → quot rb`. -/
protected def map (f : α → β) (h : (ra ⇒ rb) f f) : Quot ra → Quot rb :=
  Quot.lift (fun x => ⟦f x⟧) fun x y (h₁ : ra x y) => Quot.sound <| h h₁
#align quot.map Quot.map
-/

#print Quot.mapRight /-
/-- If `ra` is a subrelation of `ra'`, then we have a natural map `quot ra → quot ra'`. -/
protected def mapRight {ra' : α → α → Prop} (h : ∀ a₁ a₂, ra a₁ a₂ → ra' a₁ a₂) :
    Quot ra → Quot ra' :=
  Quot.map id h
#align quot.map_right Quot.mapRight
-/

#print Quot.factor /-
/-- Weaken the relation of a quotient. This is the same as `quot.map id`. -/
def factor {α : Type _} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) : Quot r → Quot s :=
  Quot.lift (Quot.mk s) fun x y rxy => Quot.sound (h x y rxy)
#align quot.factor Quot.factor
-/

#print Quot.factor_mk_eq /-
theorem factor_mk_eq {α : Type _} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
    factor r s h ∘ Quot.mk _ = Quot.mk _ :=
  rfl
#align quot.factor_mk_eq Quot.factor_mk_eq
-/

variable {γ : Sort _} {r : α → α → Prop} {s : β → β → Prop}

/- warning: quot.lift_mk clashes with quot.lift_beta -> Quot.lift_mk
Case conversion may be inaccurate. Consider using '#align quot.lift_mk Quot.lift_mkₓ'. -/
#print Quot.lift_mk /-
/-- **Alias** of `quot.lift_beta`. -/
theorem lift_mk (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) :
    Quot.lift f h (Quot.mk r a) = f a :=
  rfl
#align quot.lift_mk Quot.lift_mk
-/

#print Quot.liftOn_mk /-
@[simp]
theorem liftOn_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Quot.liftOn (Quot.mk r a) f h = f a :=
  rfl
#align quot.lift_on_mk Quot.liftOn_mk
-/

#print Quot.surjective_lift /-
@[simp]
theorem surjective_lift {f : α → γ} (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Surjective (lift f h) ↔ Surjective f :=
  ⟨fun hf => hf.comp Quot.exists_rep, fun hf y =>
    let ⟨x, hx⟩ := hf y
    ⟨Quot.mk _ x, hx⟩⟩
#align quot.surjective_lift Quot.surjective_lift
-/

#print Quot.lift₂ /-
/-- Descends a function `f : α → β → γ` to quotients of `α` and `β`. -/
@[reducible, elab_as_elim]
protected def lift₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun a => Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha => funext fun q => Quot.inductionOn q fun b => hs a₁ a₂ b ha) q₁ q₂
#align quot.lift₂ Quot.lift₂
-/

/- warning: quot.lift₂_mk -> Quot.lift₂_mk is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : α -> β -> γ) (hr : forall (a : α) (b₁ : β) (b₂ : β), (s b₁ b₂) -> (Eq.{u3} γ (f a b₁) (f a b₂))) (hs : forall (a₁ : α) (a₂ : α) (b : β), (r a₁ a₂) -> (Eq.{u3} γ (f a₁ b) (f a₂ b))) (a : α) (b : β), Eq.{u3} γ (Quot.lift₂.{u1, u2, u3} α β γ (fun (a₁ : α) (a₂ : α) => r a₁ a₂) (fun (b₁ : β) (b₂ : β) => s b₁ b₂) f hr hs (Quot.mk.{u1} α r a) (Quot.mk.{u2} β s b)) (f a b)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {γ : Sort.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : α -> β -> γ) (hr : forall (a : α) (b₁ : β) (b₂ : β), (s b₁ b₂) -> (Eq.{u3} γ (f a b₁) (f a b₂))) (hs : forall (a₁ : α) (a₂ : α) (b : β), (r a₁ a₂) -> (Eq.{u3} γ (f a₁ b) (f a₂ b))) (a : α) (b : β), Eq.{u3} γ (Quot.lift₂.{u2, u1, u3} α β γ (fun (a₁ : α) (a₂ : α) => r a₁ a₂) (fun (b₁ : β) (b₂ : β) => s b₁ b₂) f hr hs (Quot.mk.{u2} α r a) (Quot.mk.{u1} β s b)) (f a b)
Case conversion may be inaccurate. Consider using '#align quot.lift₂_mk Quot.lift₂_mkₓ'. -/
@[simp]
theorem lift₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (a : α) (b : β) :
    Quot.lift₂ f hr hs (Quot.mk r a) (Quot.mk s b) = f a b :=
  rfl
#align quot.lift₂_mk Quot.lift₂_mk

#print Quot.liftOn₂ /-
/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` and applies it. -/
@[reducible, elab_as_elim]
protected def liftOn₂ (p : Quot r) (q : Quot s) (f : α → β → γ)
    (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : γ :=
  Quot.lift₂ f hr hs p q
#align quot.lift_on₂ Quot.liftOn₂
-/

/- warning: quot.lift_on₂_mk -> Quot.liftOn₂_mk is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} (a : α) (b : β) (f : α -> β -> γ) (hr : forall (a : α) (b₁ : β) (b₂ : β), (s b₁ b₂) -> (Eq.{u3} γ (f a b₁) (f a b₂))) (hs : forall (a₁ : α) (a₂ : α) (b : β), (r a₁ a₂) -> (Eq.{u3} γ (f a₁ b) (f a₂ b))), Eq.{u3} γ (Quot.liftOn₂.{u1, u2, u3} α β γ r s (Quot.mk.{u1} α r a) (Quot.mk.{u2} β s b) f hr hs) (f a b)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {γ : Sort.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} (a : α) (b : β) (f : α -> β -> γ) (hr : forall (a : α) (b₁ : β) (b₂ : β), (s b₁ b₂) -> (Eq.{u3} γ (f a b₁) (f a b₂))) (hs : forall (a₁ : α) (a₂ : α) (b : β), (r a₁ a₂) -> (Eq.{u3} γ (f a₁ b) (f a₂ b))), Eq.{u3} γ (Quot.liftOn₂.{u2, u1, u3} α β γ r s (Quot.mk.{u2} α r a) (Quot.mk.{u1} β s b) f hr hs) (f a b)
Case conversion may be inaccurate. Consider using '#align quot.lift_on₂_mk Quot.liftOn₂_mkₓ'. -/
@[simp]
theorem liftOn₂_mk (a : α) (b : β) (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) :
    Quot.liftOn₂ (Quot.mk r a) (Quot.mk s b) f hr hs = f a b :=
  rfl
#align quot.lift_on₂_mk Quot.liftOn₂_mk

variable {t : γ → γ → Prop}

#print Quot.map₂ /-
/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` wih values in a quotient of
`γ`. -/
protected def map₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) : Quot t :=
  Quot.lift₂ (fun a b => Quot.mk t <| f a b) (fun a b₁ b₂ hb => Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha => Quot.sound (hs a₁ a₂ b ha)) q₁ q₂
#align quot.map₂ Quot.map₂
-/

/- warning: quot.map₂_mk -> Quot.map₂_mk is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : α -> β -> γ) (hr : forall (a : α) (b₁ : β) (b₂ : β), (s b₁ b₂) -> (t (f a b₁) (f a b₂))) (hs : forall (a₁ : α) (a₂ : α) (b : β), (r a₁ a₂) -> (t (f a₁ b) (f a₂ b))) (a : α) (b : β), Eq.{u3} (Quot.{u3} γ t) (Quot.map₂.{u1, u2, u3} α β γ (fun (a₁ : α) (a₂ : α) => r a₁ a₂) (fun (b₁ : β) (b₂ : β) => s b₁ b₂) t f hr hs (Quot.mk.{u1} α r a) (Quot.mk.{u2} β s b)) (Quot.mk.{u3} γ t (f a b))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {γ : Sort.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : α -> β -> γ) (hr : forall (a : α) (b₁ : β) (b₂ : β), (s b₁ b₂) -> (t (f a b₁) (f a b₂))) (hs : forall (a₁ : α) (a₂ : α) (b : β), (r a₁ a₂) -> (t (f a₁ b) (f a₂ b))) (a : α) (b : β), Eq.{u3} (Quot.{u3} γ t) (Quot.map₂.{u2, u1, u3} α β γ (fun (a₁ : α) (a₂ : α) => r a₁ a₂) (fun (b₁ : β) (b₂ : β) => s b₁ b₂) t f hr hs (Quot.mk.{u2} α r a) (Quot.mk.{u1} β s b)) (Quot.mk.{u3} γ t (f a b))
Case conversion may be inaccurate. Consider using '#align quot.map₂_mk Quot.map₂_mkₓ'. -/
@[simp]
theorem map₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (a : α) (b : β) :
    Quot.map₂ f hr hs (Quot.mk r a) (Quot.mk s b) = Quot.mk t (f a b) :=
  rfl
#align quot.map₂_mk Quot.map₂_mk

#print Quot.recOnSubsingleton₂ /-
/-- A binary version of `quot.rec_on_subsingleton`. -/
@[reducible, elab_as_elim]
protected def recOnSubsingleton₂ {φ : Quot r → Quot s → Sort _}
    [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quot r) (q₂ : Quot s) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) :
    φ q₁ q₂ :=
  @Quot.recOnSubsingleton' _ r (fun q => φ q q₂) (fun a => Quot.ind (h a) q₂) q₁ fun a =>
    Quot.recOnSubsingleton' q₂ fun b => f a b
#align quot.rec_on_subsingleton₂ Quot.recOnSubsingleton₂
-/

/- warning: quot.induction_on₂ -> Quot.induction_on₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {δ : (Quot.{u1} α r) -> (Quot.{u2} β s) -> Prop} (q₁ : Quot.{u1} α r) (q₂ : Quot.{u2} β s), (forall (a : α) (b : β), δ (Quot.mk.{u1} α r a) (Quot.mk.{u2} β s b)) -> (δ q₁ q₂)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {δ : (Quot.{u2} α r) -> (Quot.{u1} β s) -> Prop} (q₁ : Quot.{u2} α r) (q₂ : Quot.{u1} β s), (forall (a : α) (b : β), δ (Quot.mk.{u2} α r a) (Quot.mk.{u1} β s b)) -> (δ q₁ q₂)
Case conversion may be inaccurate. Consider using '#align quot.induction_on₂ Quot.induction_on₂ₓ'. -/
@[elab_as_elim]
protected theorem induction_on₂ {δ : Quot r → Quot s → Prop} (q₁ : Quot r) (q₂ : Quot s)
    (h : ∀ a b, δ (Quot.mk r a) (Quot.mk s b)) : δ q₁ q₂ :=
  Quot.ind (fun a₁ => Quot.ind (fun a₂ => h a₁ a₂) q₂) q₁
#align quot.induction_on₂ Quot.induction_on₂

/- warning: quot.induction_on₃ -> Quot.induction_on₃ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} {δ : (Quot.{u1} α r) -> (Quot.{u2} β s) -> (Quot.{u3} γ t) -> Prop} (q₁ : Quot.{u1} α r) (q₂ : Quot.{u2} β s) (q₃ : Quot.{u3} γ t), (forall (a : α) (b : β) (c : γ), δ (Quot.mk.{u1} α r a) (Quot.mk.{u2} β s b) (Quot.mk.{u3} γ t c)) -> (δ q₁ q₂ q₃)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} {δ : (Quot.{u3} α r) -> (Quot.{u2} β s) -> (Quot.{u1} γ t) -> Prop} (q₁ : Quot.{u3} α r) (q₂ : Quot.{u2} β s) (q₃ : Quot.{u1} γ t), (forall (a : α) (b : β) (c : γ), δ (Quot.mk.{u3} α r a) (Quot.mk.{u2} β s b) (Quot.mk.{u1} γ t c)) -> (δ q₁ q₂ q₃)
Case conversion may be inaccurate. Consider using '#align quot.induction_on₃ Quot.induction_on₃ₓ'. -/
@[elab_as_elim]
protected theorem induction_on₃ {δ : Quot r → Quot s → Quot t → Prop} (q₁ : Quot r) (q₂ : Quot s)
    (q₃ : Quot t) (h : ∀ a b c, δ (Quot.mk r a) (Quot.mk s b) (Quot.mk t c)) : δ q₁ q₂ q₃ :=
  Quot.ind (fun a₁ => Quot.ind (fun a₂ => Quot.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁
#align quot.induction_on₃ Quot.induction_on₃

instance (r : α → α → Prop) (f : α → Prop) (h : ∀ a b, r a b → f a = f b) [hf : DecidablePred f] :
    DecidablePred (Quot.lift f h) := fun q => Quot.recOnSubsingleton' q hf

/-- Note that this provides `decidable_rel (quot.lift₂ f ha hb)` when `α = β`. -/
instance (r : α → α → Prop) (s : β → β → Prop) (f : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    [hf : ∀ a, DecidablePred (f a)] (q₁ : Quot r) : DecidablePred (Quot.lift₂ f ha hb q₁) :=
  fun q₂ => Quot.recOnSubsingleton₂ q₁ q₂ hf

instance (r : α → α → Prop) (q : Quot r) (f : α → Prop) (h : ∀ a b, r a b → f a = f b)
    [DecidablePred f] : Decidable (Quot.liftOn q f h) :=
  Quot.lift.decidablePred _ _ _ _

instance (r : α → α → Prop) (s : β → β → Prop) (q₁ : Quot r) (q₂ : Quot s) (f : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    [∀ a, DecidablePred (f a)] : Decidable (Quot.liftOn₂ q₁ q₂ f ha hb) :=
  Quot.lift₂.decidablePred _ _ _ _ _ _ _

end Quot

namespace Quotient

variable [sa : Setoid α] [sb : Setoid β]

variable {φ : Quotient sa → Quotient sb → Sort _}

instance (s : Setoid α) [Inhabited α] : Inhabited (Quotient s) :=
  ⟨⟦default⟧⟩

instance (s : Setoid α) [Subsingleton α] : Subsingleton (Quotient s) :=
  Quot.Subsingleton

instance {α : Type _} [Setoid α] : IsEquiv α (· ≈ ·)
    where
  refl := Setoid.refl
  symm a b := Setoid.symm
  trans a b c := Setoid.trans

#print Quotient.hrecOn₂ /-
/-- Induction on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂ (qa : Quotient sa) (qb : Quotient sb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) : φ qa qb :=
  Quot.hrecOn₂ qa qb f (fun _ _ _ p => c _ _ _ _ p (Setoid.refl _)) fun _ _ _ p =>
    c _ _ _ _ (Setoid.refl _) p
#align quotient.hrec_on₂ Quotient.hrecOn₂
-/

#print Quotient.map /-
/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map (f : α → β) (h : ((· ≈ ·) ⇒ (· ≈ ·)) f f) : Quotient sa → Quotient sb :=
  Quot.map f h
#align quotient.map Quotient.map
-/

@[simp]
theorem map_mk'' (f : α → β) (h : ((· ≈ ·) ⇒ (· ≈ ·)) f f) (x : α) :
    Quotient.map f h (⟦x⟧ : Quotient sa) = (⟦f x⟧ : Quotient sb) :=
  rfl
#align quotient.map_mk Quotient.map_mk''

variable {γ : Sort _} [sc : Setoid γ]

#print Quotient.map₂ /-
/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : quotient sa → quotient sb → quotient sc`.
Useful to define binary operations on quotients. -/
protected def map₂ (f : α → β → γ) (h : ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f) :
    Quotient sa → Quotient sb → Quotient sc :=
  Quotient.lift₂ (fun x y => ⟦f x y⟧) fun x₁ y₁ x₂ y₂ h₁ h₂ => Quot.sound <| h h₁ h₂
#align quotient.map₂ Quotient.map₂
-/

@[simp]
theorem map₂_mk'' (f : α → β → γ) (h : ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f) (x : α) (y : β) :
    Quotient.map₂ f h (⟦x⟧ : Quotient sa) (⟦y⟧ : Quotient sb) = (⟦f x y⟧ : Quotient sc) :=
  rfl
#align quotient.map₂_mk Quotient.map₂_mk''

include sa

instance (f : α → Prop) (h : ∀ a b, a ≈ b → f a = f b) [DecidablePred f] :
    DecidablePred (Quotient.lift f h) :=
  Quot.lift.decidablePred _ _ _

include sb

/-- Note that this provides `decidable_rel (quotient.lift₂ f h)` when `α = β`. -/
instance (f : α → β → Prop) (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    [hf : ∀ a, DecidablePred (f a)] (q₁ : Quotient sa) : DecidablePred (Quotient.lift₂ f h q₁) :=
  fun q₂ => Quotient.recOnSubsingleton₂ q₁ q₂ hf

omit sb

instance (q : Quotient sa) (f : α → Prop) (h : ∀ a b, a ≈ b → f a = f b) [DecidablePred f] :
    Decidable (Quotient.liftOn q f h) :=
  Quotient.lift.decidablePred _ _ _

instance (q₁ : Quotient sa) (q₂ : Quotient sb) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) [∀ a, DecidablePred (f a)] :
    Decidable (Quotient.liftOn₂ q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ _ _ _

end Quotient

#print Quot.eq /-
theorem Quot.eq {α : Type _} {r : α → α → Prop} {x y : α} :
    Quot.mk r x = Quot.mk r y ↔ EqvGen r x y :=
  ⟨Quot.exact r, Quot.EqvGen_sound⟩
#align quot.eq Quot.eq
-/

#print Quotient.eq /-
@[simp]
theorem Quotient.eq [r : Setoid α] {x y : α} : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
  ⟨Quotient.exact, Quotient.sound⟩
#align quotient.eq Quotient.eq
-/

#print forall_quotient_iff /-
theorem forall_quotient_iff {α : Type _} [r : Setoid α] {p : Quotient r → Prop} :
    (∀ a : Quotient r, p a) ↔ ∀ a : α, p ⟦a⟧ :=
  ⟨fun h x => h _, fun h a => a.inductionOn h⟩
#align forall_quotient_iff forall_quotient_iff
-/

@[simp]
theorem Quotient.lift_mk'' [s : Setoid α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.lift f h (Quotient.mk'' x) = f x :=
  rfl
#align quotient.lift_mk Quotient.lift_mk''

@[simp]
theorem Quotient.lift_comp_mk'' [Setoid α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) :
    Quotient.lift f h ∘ Quotient.mk'' = f :=
  rfl
#align quotient.lift_comp_mk Quotient.lift_comp_mk''

@[simp]
theorem Quotient.lift₂_mk'' {α : Sort _} {β : Sort _} {γ : Sort _} [Setoid α] [Setoid β]
    (f : α → β → γ)
    (h : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (a : α)
    (b : β) : Quotient.lift₂ f h (Quotient.mk'' a) (Quotient.mk'' b) = f a b :=
  rfl
#align quotient.lift₂_mk Quotient.lift₂_mk''

@[simp]
theorem Quotient.liftOn_mk'' [s : Setoid α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.liftOn (Quotient.mk'' x) f h = f x :=
  rfl
#align quotient.lift_on_mk Quotient.liftOn_mk''

@[simp]
theorem Quotient.liftOn₂_mk'' {α : Sort _} {β : Sort _} [Setoid α] (f : α → α → β)
    (h : ∀ a₁ a₂ b₁ b₂ : α, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (x y : α) :
    Quotient.liftOn₂ (Quotient.mk'' x) (Quotient.mk'' y) f h = f x y :=
  rfl
#align quotient.lift_on₂_mk Quotient.liftOn₂_mk''

#print surjective_quot_mk /-
/-- `quot.mk r` is a surjective function. -/
theorem surjective_quot_mk (r : α → α → Prop) : Surjective (Quot.mk r) :=
  Quot.exists_rep
#align surjective_quot_mk surjective_quot_mk
-/

/-- `quotient.mk` is a surjective function. -/
theorem surjective_quotient_mk'' (α : Sort _) [s : Setoid α] :
    Surjective (Quotient.mk'' : α → Quotient s) :=
  Quot.exists_rep
#align surjective_quotient_mk surjective_quotient_mk''

#print Quot.out /-
/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def Quot.out {r : α → α → Prop} (q : Quot r) : α :=
  Classical.choose (Quot.exists_rep q)
#align quot.out Quot.out
-/

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
unsafe def quot.unquot {r : α → α → Prop} : Quot r → α :=
  unchecked_cast
#align quot.unquot quot.unquot

#print Quot.out_eq /-
@[simp]
theorem Quot.out_eq {r : α → α → Prop} (q : Quot r) : Quot.mk r q.out = q :=
  Classical.choose_spec (Quot.exists_rep q)
#align quot.out_eq Quot.out_eq
-/

#print Quotient.out /-
/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def Quotient.out [s : Setoid α] : Quotient s → α :=
  Quot.out
#align quotient.out Quotient.out
-/

#print Quotient.out_eq /-
@[simp]
theorem Quotient.out_eq [s : Setoid α] (q : Quotient s) : ⟦q.out⟧ = q :=
  q.out_eq
#align quotient.out_eq Quotient.out_eq
-/

theorem Quotient.mk''_out [s : Setoid α] (a : α) : ⟦a⟧.out ≈ a :=
  Quotient.exact (Quotient.out_eq _)
#align quotient.mk_out Quotient.mk''_out

theorem Quotient.mk''_eq_iff_out [s : Setoid α] {x : α} {y : Quotient s} :
    ⟦x⟧ = y ↔ x ≈ Quotient.out y :=
  by
  refine' Iff.trans _ Quotient.eq
  rw [Quotient.out_eq y]
#align quotient.mk_eq_iff_out Quotient.mk''_eq_iff_out

theorem Quotient.eq_mk''_iff_out [s : Setoid α] {x : Quotient s} {y : α} :
    x = ⟦y⟧ ↔ Quotient.out x ≈ y :=
  by
  refine' Iff.trans _ Quotient.eq
  rw [Quotient.out_eq x]
#align quotient.eq_mk_iff_out Quotient.eq_mk''_iff_out

#print Quotient.out_equiv_out /-
@[simp]
theorem Quotient.out_equiv_out {s : Setoid α} {x y : Quotient s} : x.out ≈ y.out ↔ x = y := by
  rw [← Quotient.eq_mk''_iff_out, Quotient.out_eq]
#align quotient.out_equiv_out Quotient.out_equiv_out
-/

#print Quotient.out_injective /-
theorem Quotient.out_injective {s : Setoid α} : Injective (@Quotient.out α s) := fun a b h =>
  Quotient.out_equiv_out.1 <| h ▸ Setoid.refl _
#align quotient.out_injective Quotient.out_injective
-/

#print Quotient.out_inj /-
@[simp]
theorem Quotient.out_inj {s : Setoid α} {x y : Quotient s} : x.out = y.out ↔ x = y :=
  ⟨fun h => Quotient.out_injective h, fun h => h ▸ rfl⟩
#align quotient.out_inj Quotient.out_inj
-/

section Pi

#print piSetoid /-
instance piSetoid {ι : Sort _} {α : ι → Sort _} [∀ i, Setoid (α i)] : Setoid (∀ i, α i)
    where
  R a b := ∀ i, a i ≈ b i
  iseqv :=
    ⟨fun a i => Setoid.refl _, fun a b h i => Setoid.symm (h _), fun a b c h₁ h₂ i =>
      Setoid.trans (h₁ _) (h₂ _)⟩
#align pi_setoid piSetoid
-/

#print Quotient.choice /-
/-- Given a function `f : Π i, quotient (S i)`, returns the class of functions `Π i, α i` sending
each `i` to an element of the class `f i`. -/
noncomputable def Quotient.choice {ι : Type _} {α : ι → Type _} [S : ∀ i, Setoid (α i)]
    (f : ∀ i, Quotient (S i)) : @Quotient (∀ i, α i) (by infer_instance) :=
  ⟦fun i => (f i).out⟧
#align quotient.choice Quotient.choice
-/

/- warning: quotient.choice_eq -> Quotient.choice_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Setoid.{succ u2} (α i)] (f : forall (i : ι), α i), Eq.{max (succ u1) (succ u2)} (Quotient.{max (succ u1) (succ u2)} (forall (i : ι), α i) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i))) (Quotient.choice.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) (fun (i : ι) => Quotient.mk''.{succ u2} (α i) (_inst_1 i) (f i))) (Quotient.mk''.{max (succ u1) (succ u2)} (forall (i : ι), α i) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) f)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Setoid.{succ u1} (α i)] (f : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Quotient.{max (succ u2) (succ u1)} (forall (i : ι), α i) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), α i)) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)))) (Quotient.choice.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) (fun (i : ι) => Quotient.mk.{succ u1} (α i) (_inst_1 i) (f i))) (Quotient.mk.{max (succ u2) (succ u1)} (forall (i : ι), α i) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), α i)) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i))) f)
Case conversion may be inaccurate. Consider using '#align quotient.choice_eq Quotient.choice_eqₓ'. -/
@[simp]
theorem Quotient.choice_eq {ι : Type _} {α : ι → Type _} [∀ i, Setoid (α i)] (f : ∀ i, α i) :
    (Quotient.choice fun i => ⟦f i⟧) = ⟦f⟧ :=
  Quotient.sound fun i => Quotient.mk''_out _
#align quotient.choice_eq Quotient.choice_eq

/- warning: quotient.induction_on_pi -> Quotient.induction_on_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Sort.{u2}} [s : forall (i : ι), Setoid.{u2} (α i)] {p : (forall (i : ι), Quotient.{u2} (α i) (s i)) -> Prop} (f : forall (i : ι), Quotient.{u2} (α i) (s i)), (forall (a : forall (i : ι), α i), p (fun (i : ι) => Quotient.mk''.{u2} (α i) (s i) (a i))) -> (p f)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Sort.{u1}} [s : forall (i : ι), Setoid.{u1} (α i)] {p : (forall (i : ι), Quotient.{u1} (α i) (s i)) -> Prop} (f : forall (i : ι), Quotient.{u1} (α i) (s i)), (forall (a : forall (i : ι), α i), p (fun (i : ι) => Quotient.mk.{u1} (α i) (s i) (a i))) -> (p f)
Case conversion may be inaccurate. Consider using '#align quotient.induction_on_pi Quotient.induction_on_piₓ'. -/
@[elab_as_elim]
theorem Quotient.induction_on_pi {ι : Type _} {α : ι → Sort _} [s : ∀ i, Setoid (α i)]
    {p : (∀ i, Quotient (s i)) → Prop} (f : ∀ i, Quotient (s i))
    (h : ∀ a : ∀ i, α i, p fun i => ⟦a i⟧) : p f :=
  by
  rw [← (funext fun i => Quotient.out_eq (f i) : (fun i => ⟦(f i).out⟧) = f)]
  apply h
#align quotient.induction_on_pi Quotient.induction_on_pi

end Pi

#print nonempty_quotient_iff /-
theorem nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ => ⟨⟦a⟧⟩⟩
#align nonempty_quotient_iff nonempty_quotient_iff
-/

/-! ### Truncation -/


#print Trunc /-
/-- `trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `nonempty α`, but unlike `nonempty α`, `trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
def Trunc.{u} (α : Sort u) : Sort u :=
  @Quot α fun _ _ => True
#align trunc Trunc
-/

#print true_equivalence /-
theorem true_equivalence : @Equivalence α fun _ _ => True :=
  ⟨fun _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩
#align true_equivalence true_equivalence
-/

namespace Trunc

#print Trunc.mk /-
/-- Constructor for `trunc α` -/
def mk (a : α) : Trunc α :=
  Quot.mk _ a
#align trunc.mk Trunc.mk
-/

instance [Inhabited α] : Inhabited (Trunc α) :=
  ⟨mk default⟩

#print Trunc.lift /-
/-- Any constant function lifts to a function out of the truncation -/
def lift (f : α → β) (c : ∀ a b : α, f a = f b) : Trunc α → β :=
  Quot.lift f fun a b _ => c a b
#align trunc.lift Trunc.lift
-/

#print Trunc.ind /-
theorem ind {β : Trunc α → Prop} : (∀ a : α, β (mk a)) → ∀ q : Trunc α, β q :=
  Quot.ind
#align trunc.ind Trunc.ind
-/

#print Trunc.lift_mk /-
protected theorem lift_mk (f : α → β) (c) (a : α) : lift f c (mk a) = f a :=
  rfl
#align trunc.lift_mk Trunc.lift_mk
-/

#print Trunc.liftOn /-
/-- Lift a constant function on `q : trunc α`. -/
@[reducible, elab_as_elim]
protected def liftOn (q : Trunc α) (f : α → β) (c : ∀ a b : α, f a = f b) : β :=
  lift f c q
#align trunc.lift_on Trunc.liftOn
-/

#print Trunc.induction_on /-
@[elab_as_elim]
protected theorem induction_on {β : Trunc α → Prop} (q : Trunc α) (h : ∀ a, β (mk a)) : β q :=
  ind h q
#align trunc.induction_on Trunc.induction_on
-/

#print Trunc.exists_rep /-
theorem exists_rep (q : Trunc α) : ∃ a : α, mk a = q :=
  Quot.exists_rep q
#align trunc.exists_rep Trunc.exists_rep
-/

/- warning: trunc.induction_on₂ -> Trunc.induction_on₂ is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {C : (Trunc.{u1} α) -> (Trunc.{u2} β) -> Prop} (q₁ : Trunc.{u1} α) (q₂ : Trunc.{u2} β), (forall (a : α) (b : β), C (Trunc.mk.{u1} α a) (Trunc.mk.{u2} β b)) -> (C q₁ q₂)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {C : (Trunc.{u2} α) -> (Trunc.{u1} β) -> Prop} (q₁ : Trunc.{u2} α) (q₂ : Trunc.{u1} β), (forall (a : α) (b : β), C (Trunc.mk.{u2} α a) (Trunc.mk.{u1} β b)) -> (C q₁ q₂)
Case conversion may be inaccurate. Consider using '#align trunc.induction_on₂ Trunc.induction_on₂ₓ'. -/
@[elab_as_elim]
protected theorem induction_on₂ {C : Trunc α → Trunc β → Prop} (q₁ : Trunc α) (q₂ : Trunc β)
    (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
  Trunc.induction_on q₁ fun a₁ => Trunc.induction_on q₂ (h a₁)
#align trunc.induction_on₂ Trunc.induction_on₂

#print Trunc.eq /-
protected theorem eq (a b : Trunc α) : a = b :=
  Trunc.induction_on₂ a b fun x y => Quot.sound trivial
#align trunc.eq Trunc.eq
-/

instance : Subsingleton (Trunc α) :=
  ⟨Trunc.eq⟩

#print Trunc.bind /-
/-- The `bind` operator for the `trunc` monad. -/
def bind (q : Trunc α) (f : α → Trunc β) : Trunc β :=
  Trunc.liftOn q f fun a b => Trunc.eq _ _
#align trunc.bind Trunc.bind
-/

#print Trunc.map /-
/-- A function `f : α → β` defines a function `map f : trunc α → trunc β`. -/
def map (f : α → β) (q : Trunc α) : Trunc β :=
  bind q (Trunc.mk ∘ f)
#align trunc.map Trunc.map
-/

instance : Monad Trunc where
  pure := @Trunc.mk
  bind := @Trunc.bind

instance : LawfulMonad Trunc where
  id_map α q := Trunc.eq _ _
  pure_bind α β q f := rfl
  bind_assoc α β γ x f g := Trunc.eq _ _

variable {C : Trunc α → Sort _}

#print Trunc.rec /-
/-- Recursion/induction principle for `trunc`. -/
@[reducible, elab_as_elim]
protected def rec (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b) (q : Trunc α) :
    C q :=
  Quot.rec f (fun a b _ => h a b) q
#align trunc.rec Trunc.rec
-/

#print Trunc.recOn /-
/-- A version of `trunc.rec` taking `q : trunc α` as the first argument. -/
@[reducible, elab_as_elim]
protected def recOn (q : Trunc α) (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
  Trunc.rec f h q
#align trunc.rec_on Trunc.recOn
-/

#print Trunc.recOnSubsingleton /-
/-- A version of `trunc.rec_on` assuming the codomain is a `subsingleton`. -/
@[reducible, elab_as_elim]
protected def recOnSubsingleton [∀ a, Subsingleton (C (mk a))] (q : Trunc α) (f : ∀ a, C (mk a)) :
    C q :=
  Trunc.rec f (fun a b => Subsingleton.elim _ (f b)) q
#align trunc.rec_on_subsingleton Trunc.recOnSubsingleton
-/

#print Trunc.out /-
/-- Noncomputably extract a representative of `trunc α` (using the axiom of choice). -/
noncomputable def out : Trunc α → α :=
  Quot.out
#align trunc.out Trunc.out
-/

#print Trunc.out_eq /-
@[simp]
theorem out_eq (q : Trunc α) : mk q.out = q :=
  Trunc.eq _ _
#align trunc.out_eq Trunc.out_eq
-/

#print Trunc.nonempty /-
protected theorem nonempty (q : Trunc α) : Nonempty α :=
  nonempty_of_exists q.exists_rep
#align trunc.nonempty Trunc.nonempty
-/

end Trunc

/-! ### `quotient` with implicit `setoid` -/


namespace Quotient

variable {γ : Sort _} {φ : Sort _} {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

/-! Versions of quotient definitions and lemmas ending in `'` use unification instead
of typeclass inference for inferring the `setoid` argument. This is useful when there are
several different quotient relations on a type, for example quotient groups, rings and modules. -/


#print Quotient.mk' /-
/-- A version of `quotient.mk` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
protected def mk' (a : α) : Quotient s₁ :=
  Quot.mk s₁.1 a
#align quotient.mk' Quotient.mk'
-/

#print Quotient.surjective_Quotient_mk'' /-
/-- `quotient.mk'` is a surjective function. -/
theorem surjective_Quotient_mk'' : Surjective (Quotient.mk' : α → Quotient s₁) :=
  Quot.exists_rep
#align quotient.surjective_quotient_mk' Quotient.surjective_Quotient_mk''
-/

#print Quotient.liftOn' /-
/-- A version of `quotient.lift_on` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
@[elab_as_elim, reducible]
protected def liftOn' (q : Quotient s₁) (f : α → φ) (h : ∀ a b, @Setoid.r α s₁ a b → f a = f b) :
    φ :=
  Quotient.liftOn q f h
#align quotient.lift_on' Quotient.liftOn'
-/

@[simp]
protected theorem liftOn'_mk' (f : α → φ) (h) (x : α) :
    Quotient.liftOn' (@Quotient.mk' _ s₁ x) f h = f x :=
  rfl
#align quotient.lift_on'_mk' Quotient.liftOn'_mk'

/- warning: quotient.surjective_lift_on' -> Quotient.surjective_liftOn' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {φ : Sort.{u2}} {s₁ : Setoid.{u1} α} {f : α -> φ} (h : forall (a : α) (b : α), (Setoid.r.{u1} α s₁ a b) -> (Eq.{u2} φ (f a) (f b))), Iff (Function.Surjective.{u1, u2} (Quotient.{u1} α s₁) φ (fun (x : Quotient.{u1} α s₁) => Quotient.liftOn'.{u1, u2} α φ s₁ x f h)) (Function.Surjective.{u1, u2} α φ f)
but is expected to have type
  forall {α : Sort.{u2}} {φ : Sort.{u1}} {s₁ : Setoid.{u2} α} {f : α -> φ} (h : forall (a : α) (b : α), (Setoid.r.{u2} α s₁ a b) -> (Eq.{u1} φ (f a) (f b))), Iff (Function.Surjective.{u2, u1} (Quotient.{u2} α s₁) φ (fun (x : Quotient.{u2} α s₁) => Quotient.liftOn'.{u2, u1} α φ s₁ x f h)) (Function.Surjective.{u2, u1} α φ f)
Case conversion may be inaccurate. Consider using '#align quotient.surjective_lift_on' Quotient.surjective_liftOn'ₓ'. -/
@[simp]
theorem surjective_liftOn' {f : α → φ} (h : ∀ a b, @Setoid.r α s₁ a b → f a = f b) :
    (Surjective fun x => Quotient.liftOn' x f h) ↔ Surjective f :=
  Quot.surjective_lift _
#align quotient.surjective_lift_on' Quotient.surjective_liftOn'

#print Quotient.liftOn₂' /-
/-- A version of `quotient.lift_on₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_elim, reducible]
protected def liftOn₂' (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α → β → γ)
    (h : ∀ a₁ a₂ b₁ b₂, @Setoid.r α s₁ a₁ b₁ → @Setoid.r β s₂ a₂ b₂ → f a₁ a₂ = f b₁ b₂) : γ :=
  Quotient.liftOn₂ q₁ q₂ f h
#align quotient.lift_on₂' Quotient.liftOn₂'
-/

@[simp]
protected theorem liftOn₂'_mk' (f : α → β → γ) (h) (a : α) (b : β) :
    Quotient.liftOn₂' (@Quotient.mk' _ s₁ a) (@Quotient.mk' _ s₂ b) f h = f a b :=
  rfl
#align quotient.lift_on₂'_mk' Quotient.liftOn₂'_mk'

#print Quotient.ind' /-
/-- A version of `quotient.ind` taking `{s : setoid α}` as an implicit argument instead of an
instance argument. -/
@[elab_as_elim]
protected theorem ind' {p : Quotient s₁ → Prop} (h : ∀ a, p (Quotient.mk' a)) (q : Quotient s₁) :
    p q :=
  Quotient.ind h q
#align quotient.ind' Quotient.ind'
-/

/- warning: quotient.ind₂' -> Quotient.ind₂' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {s₁ : Setoid.{u1} α} {s₂ : Setoid.{u2} β} {p : (Quotient.{u1} α s₁) -> (Quotient.{u2} β s₂) -> Prop}, (forall (a₁ : α) (a₂ : β), p (Quotient.mk'.{u1} α s₁ a₁) (Quotient.mk'.{u2} β s₂ a₂)) -> (forall (q₁ : Quotient.{u1} α s₁) (q₂ : Quotient.{u2} β s₂), p q₁ q₂)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {s₁ : Setoid.{u2} α} {s₂ : Setoid.{u1} β} {p : (Quotient.{u2} α s₁) -> (Quotient.{u1} β s₂) -> Prop}, (forall (a₁ : α) (a₂ : β), p (Quotient.mk''.{u2} α s₁ a₁) (Quotient.mk''.{u1} β s₂ a₂)) -> (forall (q₁ : Quotient.{u2} α s₁) (q₂ : Quotient.{u1} β s₂), p q₁ q₂)
Case conversion may be inaccurate. Consider using '#align quotient.ind₂' Quotient.ind₂'ₓ'. -/
/-- A version of `quotient.ind₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_elim]
protected theorem ind₂' {p : Quotient s₁ → Quotient s₂ → Prop}
    (h : ∀ a₁ a₂, p (Quotient.mk' a₁) (Quotient.mk' a₂)) (q₁ : Quotient s₁) (q₂ : Quotient s₂) :
    p q₁ q₂ :=
  Quotient.ind₂ h q₁ q₂
#align quotient.ind₂' Quotient.ind₂'

#print Quotient.inductionOn' /-
/-- A version of `quotient.induction_on` taking `{s : setoid α}` as an implicit argument instead
of an instance argument. -/
@[elab_as_elim]
protected theorem inductionOn' {p : Quotient s₁ → Prop} (q : Quotient s₁)
    (h : ∀ a, p (Quotient.mk' a)) : p q :=
  Quotient.inductionOn q h
#align quotient.induction_on' Quotient.inductionOn'
-/

/- warning: quotient.induction_on₂' -> Quotient.inductionOn₂' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {s₁ : Setoid.{u1} α} {s₂ : Setoid.{u2} β} {p : (Quotient.{u1} α s₁) -> (Quotient.{u2} β s₂) -> Prop} (q₁ : Quotient.{u1} α s₁) (q₂ : Quotient.{u2} β s₂), (forall (a₁ : α) (a₂ : β), p (Quotient.mk'.{u1} α s₁ a₁) (Quotient.mk'.{u2} β s₂ a₂)) -> (p q₁ q₂)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {s₁ : Setoid.{u2} α} {s₂ : Setoid.{u1} β} {p : (Quotient.{u2} α s₁) -> (Quotient.{u1} β s₂) -> Prop} (q₁ : Quotient.{u2} α s₁) (q₂ : Quotient.{u1} β s₂), (forall (a₁ : α) (a₂ : β), p (Quotient.mk''.{u2} α s₁ a₁) (Quotient.mk''.{u1} β s₂ a₂)) -> (p q₁ q₂)
Case conversion may be inaccurate. Consider using '#align quotient.induction_on₂' Quotient.inductionOn₂'ₓ'. -/
/-- A version of `quotient.induction_on₂` taking `{s₁ : setoid α} {s₂ : setoid β}` as implicit
arguments instead of instance arguments. -/
@[elab_as_elim]
protected theorem inductionOn₂' {p : Quotient s₁ → Quotient s₂ → Prop} (q₁ : Quotient s₁)
    (q₂ : Quotient s₂) (h : ∀ a₁ a₂, p (Quotient.mk' a₁) (Quotient.mk' a₂)) : p q₁ q₂ :=
  Quotient.induction_on₂ q₁ q₂ h
#align quotient.induction_on₂' Quotient.inductionOn₂'

/- warning: quotient.induction_on₃' -> Quotient.inductionOn₃' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {s₁ : Setoid.{u1} α} {s₂ : Setoid.{u2} β} {s₃ : Setoid.{u3} γ} {p : (Quotient.{u1} α s₁) -> (Quotient.{u2} β s₂) -> (Quotient.{u3} γ s₃) -> Prop} (q₁ : Quotient.{u1} α s₁) (q₂ : Quotient.{u2} β s₂) (q₃ : Quotient.{u3} γ s₃), (forall (a₁ : α) (a₂ : β) (a₃ : γ), p (Quotient.mk'.{u1} α s₁ a₁) (Quotient.mk'.{u2} β s₂ a₂) (Quotient.mk'.{u3} γ s₃ a₃)) -> (p q₁ q₂ q₃)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} {s₁ : Setoid.{u3} α} {s₂ : Setoid.{u2} β} {s₃ : Setoid.{u1} γ} {p : (Quotient.{u3} α s₁) -> (Quotient.{u2} β s₂) -> (Quotient.{u1} γ s₃) -> Prop} (q₁ : Quotient.{u3} α s₁) (q₂ : Quotient.{u2} β s₂) (q₃ : Quotient.{u1} γ s₃), (forall (a₁ : α) (a₂ : β) (a₃ : γ), p (Quotient.mk''.{u3} α s₁ a₁) (Quotient.mk''.{u2} β s₂ a₂) (Quotient.mk''.{u1} γ s₃ a₃)) -> (p q₁ q₂ q₃)
Case conversion may be inaccurate. Consider using '#align quotient.induction_on₃' Quotient.inductionOn₃'ₓ'. -/
/-- A version of `quotient.induction_on₃` taking `{s₁ : setoid α} {s₂ : setoid β} {s₃ : setoid γ}`
as implicit arguments instead of instance arguments. -/
@[elab_as_elim]
protected theorem inductionOn₃' {p : Quotient s₁ → Quotient s₂ → Quotient s₃ → Prop}
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (q₃ : Quotient s₃)
    (h : ∀ a₁ a₂ a₃, p (Quotient.mk' a₁) (Quotient.mk' a₂) (Quotient.mk' a₃)) : p q₁ q₂ q₃ :=
  Quotient.induction_on₃ q₁ q₂ q₃ h
#align quotient.induction_on₃' Quotient.inductionOn₃'

#print Quotient.recOnSubsingleton' /-
/-- A version of `quotient.rec_on_subsingleton` taking `{s₁ : setoid α}` as an implicit argument
instead of an instance argument. -/
@[elab_as_elim]
protected def recOnSubsingleton' {φ : Quotient s₁ → Sort _} [h : ∀ a, Subsingleton (φ ⟦a⟧)]
    (q : Quotient s₁) (f : ∀ a, φ (Quotient.mk' a)) : φ q :=
  Quotient.recOnSubsingleton q f
#align quotient.rec_on_subsingleton' Quotient.recOnSubsingleton'
-/

#print Quotient.recOnSubsingleton₂' /-
/-- A version of `quotient.rec_on_subsingleton₂` taking `{s₁ : setoid α} {s₂ : setoid α}`
as implicit arguments instead of instance arguments. -/
@[reducible, elab_as_elim]
protected def recOnSubsingleton₂' {φ : Quotient s₁ → Quotient s₂ → Sort _}
    [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quotient s₁) (q₂ : Quotient s₂)
    (f : ∀ a₁ a₂, φ (Quotient.mk' a₁) (Quotient.mk' a₂)) : φ q₁ q₂ :=
  Quotient.recOnSubsingleton₂ q₁ q₂ f
#align quotient.rec_on_subsingleton₂' Quotient.recOnSubsingleton₂'
-/

#print Quotient.hrecOn' /-
/-- Recursion on a `quotient` argument `a`, result type depends on `⟦a⟧`. -/
protected def hrecOn' {φ : Quotient s₁ → Sort _} (qa : Quotient s₁) (f : ∀ a, φ (Quotient.mk' a))
    (c : ∀ a₁ a₂, a₁ ≈ a₂ → HEq (f a₁) (f a₂)) : φ qa :=
  Quot.hrecOn qa f c
#align quotient.hrec_on' Quotient.hrecOn'
-/

@[simp]
theorem hrecOn'_mk' {φ : Quotient s₁ → Sort _} (f : ∀ a, φ (Quotient.mk' a))
    (c : ∀ a₁ a₂, a₁ ≈ a₂ → HEq (f a₁) (f a₂)) (x : α) : (Quotient.mk' x).hrecOn' f c = f x :=
  rfl
#align quotient.hrec_on'_mk' Quotient.hrecOn'_mk'

#print Quotient.hrecOn₂' /-
/-- Recursion on two `quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂' {φ : Quotient s₁ → Quotient s₂ → Sort _} (qa : Quotient s₁)
    (qb : Quotient s₂) (f : ∀ a b, φ (Quotient.mk' a) (Quotient.mk' b))
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) : φ qa qb :=
  Quotient.hrecOn₂ qa qb f c
#align quotient.hrec_on₂' Quotient.hrecOn₂'
-/

@[simp]
theorem hrecOn₂'_mk' {φ : Quotient s₁ → Quotient s₂ → Sort _}
    (f : ∀ a b, φ (Quotient.mk' a) (Quotient.mk' b))
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) (x : α) (qb : Quotient s₂) :
    (Quotient.mk' x).hrecOn₂' qb f c = qb.hrecOn' (f x) fun b₁ b₂ => c _ _ _ _ (Setoid.refl _) :=
  rfl
#align quotient.hrec_on₂'_mk' Quotient.hrecOn₂'_mk'

#print Quotient.map' /-
/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `quotient sa → quotient sb`. Useful to define unary operations on quotients. -/
protected def map' (f : α → β) (h : (s₁.R ⇒ s₂.R) f f) : Quotient s₁ → Quotient s₂ :=
  Quot.map f h
#align quotient.map' Quotient.map'
-/

@[simp]
theorem map'_mk' (f : α → β) (h) (x : α) :
    (Quotient.mk' x : Quotient s₁).map' f h = (Quotient.mk' (f x) : Quotient s₂) :=
  rfl
#align quotient.map'_mk' Quotient.map'_mk'

#print Quotient.map₂' /-
/-- A version of `quotient.map₂` using curly braces and unification. -/
protected def map₂' (f : α → β → γ) (h : (s₁.R ⇒ s₂.R ⇒ s₃.R) f f) :
    Quotient s₁ → Quotient s₂ → Quotient s₃ :=
  Quotient.map₂ f h
#align quotient.map₂' Quotient.map₂'
-/

@[simp]
theorem map₂'_mk' (f : α → β → γ) (h) (x : α) :
    (Quotient.mk' x : Quotient s₁).map₂' f h =
      (Quotient.map' (f x) (h (Setoid.refl x)) : Quotient s₂ → Quotient s₃) :=
  rfl
#align quotient.map₂'_mk' Quotient.map₂'_mk'

#print Quotient.exact' /-
theorem exact' {a b : α} : (Quotient.mk' a : Quotient s₁) = Quotient.mk' b → @Setoid.r _ s₁ a b :=
  Quotient.exact
#align quotient.exact' Quotient.exact'
-/

#print Quotient.sound' /-
theorem sound' {a b : α} : @Setoid.r _ s₁ a b → @Quotient.mk' α s₁ a = Quotient.mk' b :=
  Quotient.sound
#align quotient.sound' Quotient.sound'
-/

#print Quotient.eq' /-
@[simp]
protected theorem eq' {a b : α} : @Quotient.mk' α s₁ a = Quotient.mk' b ↔ @Setoid.r _ s₁ a b :=
  Quotient.eq
#align quotient.eq' Quotient.eq'
-/

#print Quotient.out' /-
/-- A version of `quotient.out` taking `{s₁ : setoid α}` as an implicit argument instead of an
instance argument. -/
noncomputable def out' (a : Quotient s₁) : α :=
  Quotient.out a
#align quotient.out' Quotient.out'
-/

#print Quotient.out_eq' /-
@[simp]
theorem out_eq' (q : Quotient s₁) : Quotient.mk' q.out' = q :=
  q.out_eq
#align quotient.out_eq' Quotient.out_eq'
-/

#print Quotient.mk_out' /-
theorem mk_out' (a : α) : @Setoid.r α s₁ (Quotient.mk' a : Quotient s₁).out' a :=
  Quotient.exact (Quotient.out_eq _)
#align quotient.mk_out' Quotient.mk_out'
-/

section

variable [Setoid α]

protected theorem mk'_eq_mk'' (x : α) : Quotient.mk' x = ⟦x⟧ :=
  rfl
#align quotient.mk'_eq_mk Quotient.mk'_eq_mk''

/- warning: quotient.lift_on'_mk -> Quotient.liftOn'_mk is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Setoid.{u1} α] (x : α) (f : α -> β) (h : forall (a : α) (b : α), (Setoid.r.{u1} α _inst_1 a b) -> (Eq.{u2} β (f a) (f b))), Eq.{u2} β (Quotient.liftOn'.{u1, u2} α β _inst_1 (Quotient.mk''.{u1} α _inst_1 x) f h) (f x)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Setoid.{u2} α] (x : α) (f : α -> β) (h : forall (a : α) (b : α), (Setoid.r.{u2} α _inst_1 a b) -> (Eq.{u1} β (f a) (f b))), Eq.{u1} β (Quotient.liftOn'.{u2, u1} α β _inst_1 (Quotient.mk.{u2} α _inst_1 x) f h) (f x)
Case conversion may be inaccurate. Consider using '#align quotient.lift_on'_mk Quotient.liftOn'_mkₓ'. -/
@[simp]
protected theorem liftOn'_mk (x : α) (f : α → β) (h) : ⟦x⟧.liftOn' f h = f x :=
  rfl
#align quotient.lift_on'_mk Quotient.liftOn'_mk

/- warning: quotient.lift_on₂'_mk -> Quotient.liftOn₂'_mk is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} [_inst_1 : Setoid.{u1} α] [_inst_2 : Setoid.{u2} β] (f : α -> β -> γ) (h : forall (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), (Setoid.r.{u1} α _inst_1 a₁ b₁) -> (Setoid.r.{u2} β _inst_2 a₂ b₂) -> (Eq.{u3} γ (f a₁ a₂) (f b₁ b₂))) (a : α) (b : β), Eq.{u3} γ (Quotient.liftOn₂'.{u1, u2, u3} α β γ _inst_1 _inst_2 (Quotient.mk''.{u1} α _inst_1 a) (Quotient.mk''.{u2} β _inst_2 b) f h) (f a b)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u3}} {γ : Sort.{u1}} [_inst_1 : Setoid.{u2} α] [_inst_2 : Setoid.{u3} β] (f : α -> β -> γ) (h : forall (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), (Setoid.r.{u2} α _inst_1 a₁ b₁) -> (Setoid.r.{u3} β _inst_2 a₂ b₂) -> (Eq.{u1} γ (f a₁ a₂) (f b₁ b₂))) (a : α) (b : β), Eq.{u1} γ (Quotient.liftOn₂'.{u2, u3, u1} α β γ _inst_1 _inst_2 (Quotient.mk.{u2} α _inst_1 a) (Quotient.mk.{u3} β _inst_2 b) f h) (f a b)
Case conversion may be inaccurate. Consider using '#align quotient.lift_on₂'_mk Quotient.liftOn₂'_mkₓ'. -/
@[simp]
protected theorem liftOn₂'_mk [Setoid β] (f : α → β → γ) (h) (a : α) (b : β) :
    Quotient.liftOn₂' ⟦a⟧ ⟦b⟧ f h = f a b :=
  Quotient.liftOn₂'_mk' _ _ _ _
#align quotient.lift_on₂'_mk Quotient.liftOn₂'_mk

/- warning: quotient.map'_mk -> Quotient.map'_mk'' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Setoid.{u1} α] [_inst_2 : Setoid.{u2} β] (f : α -> β) (h : Relator.LiftFun.{u1, u1, u2, u2} α α β β (Setoid.r.{u1} α _inst_1) (Setoid.r.{u2} β _inst_2) f f) (x : α), Eq.{u2} (Quotient.{u2} β _inst_2) (Quotient.map'.{u1, u2} α β _inst_1 _inst_2 f h (Quotient.mk''.{u1} α _inst_1 x)) (Quotient.mk''.{u2} β _inst_2 (f x))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {_inst_1 : Setoid.{u2} α} {_inst_2 : Setoid.{u1} β} (f : α -> β) (h : Relator.LiftFun.{u2, u2, u1, u1} α α β β (Setoid.r.{u2} α _inst_1) (Setoid.r.{u1} β _inst_2) f f) (x : α), Eq.{u1} (Quotient.{u1} β _inst_2) (Quotient.map'.{u2, u1} α β _inst_1 _inst_2 f h (Quotient.mk''.{u2} α _inst_1 x)) (Quotient.mk''.{u1} β _inst_2 (f x))
Case conversion may be inaccurate. Consider using '#align quotient.map'_mk Quotient.map'_mk''ₓ'. -/
@[simp]
theorem map'_mk'' [Setoid β] (f : α → β) (h) (x : α) : ⟦x⟧.map' f h = ⟦f x⟧ :=
  rfl
#align quotient.map'_mk Quotient.map'_mk''

end

instance (q : Quotient s₁) (f : α → Prop) (h : ∀ a b, @Setoid.r α s₁ a b → f a = f b)
    [DecidablePred f] : Decidable (Quotient.liftOn' q f h) :=
  Quotient.lift.decidablePred _ _ q

instance (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, @Setoid.r α s₁ a₁ a₂ → @Setoid.r β s₂ b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    [∀ a, DecidablePred (f a)] : Decidable (Quotient.liftOn₂' q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ _ _ _

end Quotient

