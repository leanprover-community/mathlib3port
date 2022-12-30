/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.option.basic
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.IsEmpty
import Mathbin.Control.Traversable.Basic
import Mathbin.Tactic.Basic

/-!
# Option of a type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/493
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the basic theory of option types.

If `α` is a type, then `option α` can be understood as the type with one more element than `α`.
`option α` has terms `some a`, where `a : α`, and `none`, which is the added element.
This is useful in multiple ways:
* It is the prototype of addition of terms to a type. See for example `with_bot α` which uses
  `none` as an element smaller than all others.
* It can be used to define failsafe partial functions, which return `some the_result_we_expect`
  if we can find `the_result_we_expect`, and `none` if there is no meaningful result. This forces
  any subsequent use of the partial function to explicitly deal with the exceptions that make it
  return `none`.
* `option` is a monad. We love monads.

`part` is an alternative to `option` that can be seen as the type of `true`/`false` values
along with a term `a : α` if the value is `true`.

## Implementation notes

`option` is currently defined in core Lean, but this will change in Lean 4.
-/


namespace Option

variable {α β γ δ : Type _}

#print Option.coe_def /-
theorem coe_def : (coe : α → Option α) = some :=
  rfl
#align option.coe_def Option.coe_def
-/

theorem some_eq_coe (a : α) : some a = a :=
  rfl
#align option.some_eq_coe Option.some_eq_coe

#print Option.some_ne_none /-
theorem some_ne_none (x : α) : some x ≠ none := fun h => Option.noConfusion h
#align option.some_ne_none Option.some_ne_none
-/

@[simp]
theorem coe_ne_none (a : α) : (a : Option α) ≠ none :=
  fun.
#align option.coe_ne_none Option.coe_ne_none

#print Option.forall /-
protected theorem forall {p : Option α → Prop} : (∀ x, p x) ↔ p none ∧ ∀ x, p (some x) :=
  ⟨fun h => ⟨h _, fun x => h _⟩, fun h x => Option.casesOn x h.1 h.2⟩
#align option.forall Option.forall
-/

#print Option.exists /-
protected theorem exists {p : Option α → Prop} : (∃ x, p x) ↔ p none ∨ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx⟩ => ((Option.casesOn x Or.inl) fun x hx => Or.inr ⟨x, hx⟩) hx, fun h =>
    h.elim (fun h => ⟨_, h⟩) fun ⟨x, hx⟩ => ⟨_, hx⟩⟩
#align option.exists Option.exists
-/

#print Option.get_mem /-
@[simp]
theorem get_mem : ∀ {o : Option α} (h : isSome o), Option.get h ∈ o
  | some a, _ => rfl
#align option.get_mem Option.get_mem
-/

#print Option.get_of_mem /-
theorem get_of_mem {a : α} : ∀ {o : Option α} (h : isSome o), a ∈ o → Option.get h = a
  | _, _, rfl => rfl
#align option.get_of_mem Option.get_of_mem
-/

#print Option.not_mem_none /-
@[simp]
theorem not_mem_none (a : α) : a ∉ (none : Option α) := fun h => Option.noConfusion h
#align option.not_mem_none Option.not_mem_none
-/

#print Option.some_get /-
@[simp]
theorem some_get : ∀ {x : Option α} (h : isSome x), some (Option.get h) = x
  | some x, hx => rfl
#align option.some_get Option.some_get
-/

#print Option.get_some /-
@[simp]
theorem get_some (x : α) (h : isSome (some x)) : Option.get h = x :=
  rfl
#align option.get_some Option.get_some
-/

@[simp]
theorem get_or_else_some (x y : α) : Option.getD (some x) y = x :=
  rfl
#align option.get_or_else_some Option.get_or_else_some

@[simp]
theorem get_or_else_none (x : α) : Option.getD none x = x :=
  rfl
#align option.get_or_else_none Option.get_or_else_none

#print Option.getD_coe /-
@[simp]
theorem getD_coe (x y : α) : Option.getD (↑x) y = x :=
  rfl
#align option.get_or_else_coe Option.getD_coe
-/

theorem get_or_else_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) : some (x.getOrElse y) = x :=
  by cases x <;> [contradiction, rw [get_or_else_some]]
#align option.get_or_else_of_ne_none Option.get_or_else_of_ne_none

#print Option.coe_get /-
@[simp]
theorem coe_get {o : Option α} (h : o.isSome) : ((Option.get h : α) : Option α) = o :=
  Option.some_get h
#align option.coe_get Option.coe_get
-/

#print Option.mem_unique /-
theorem mem_unique {o : Option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
  Option.some.inj <| ha.symm.trans hb
#align option.mem_unique Option.mem_unique
-/

#print Option.eq_of_mem_of_mem /-
theorem eq_of_mem_of_mem {a : α} {o1 o2 : Option α} (h1 : a ∈ o1) (h2 : a ∈ o2) : o1 = o2 :=
  h1.trans h2.symm
#align option.eq_of_mem_of_mem Option.eq_of_mem_of_mem
-/

#print Option.Mem.leftUnique /-
theorem Mem.leftUnique : Relator.LeftUnique ((· ∈ ·) : α → Option α → Prop) := fun a o b =>
  mem_unique
#align option.mem.left_unique Option.Mem.leftUnique
-/

#print Option.some_injective /-
theorem some_injective (α : Type _) : Function.Injective (@some α) := fun _ _ => some_inj.mp
#align option.some_injective Option.some_injective
-/

/- warning: option.map_injective -> Option.map_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Function.Injective.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β) (Option.map.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Function.Injective.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β) (Option.map.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align option.map_injective Option.map_injectiveₓ'. -/
/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.Injective f) : Function.Injective (Option.map f)
  | none, none, H => rfl
  | some a₁, some a₂, H => by rw [Hf (Option.some.inj H)]
#align option.map_injective Option.map_injective

/- warning: option.map_comp_some -> Option.map_comp_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{max (succ u1) (succ u2)} (α -> (Option.{u2} β)) (Function.comp.{succ u1, succ u1, succ u2} α (Option.{u1} α) (Option.{u2} β) (Option.map.{u1, u2} α β f) (Option.some.{u1} α)) (Function.comp.{succ u1, succ u2, succ u2} α β (Option.{u2} β) (Option.some.{u2} β) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{max (succ u2) (succ u1)} (α -> (Option.{u1} β)) (Function.comp.{succ u2, succ u2, succ u1} α (Option.{u2} α) (Option.{u1} β) (Option.map.{u2, u1} α β f) (Option.some.{u2} α)) (Function.comp.{succ u2, succ u1, succ u1} α β (Option.{u1} β) (Option.some.{u1} β) f)
Case conversion may be inaccurate. Consider using '#align option.map_comp_some Option.map_comp_someₓ'. -/
@[simp]
theorem map_comp_some (f : α → β) : Option.map f ∘ some = some ∘ f :=
  rfl
#align option.map_comp_some Option.map_comp_some

#print Option.ext /-
@[ext]
theorem ext : ∀ {o₁ o₂ : Option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
  | none, none, H => rfl
  | some a, o, H => ((H _).1 rfl).symm
  | o, some b, H => (H _).2 rfl
#align option.ext Option.ext
-/

#print Option.eq_none_iff_forall_not_mem /-
theorem eq_none_iff_forall_not_mem {o : Option α} : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e a h => by rw [e] at h <;> cases h, fun h => ext <| by simpa⟩
#align option.eq_none_iff_forall_not_mem Option.eq_none_iff_forall_not_mem
-/

/- warning: option.none_bind -> Option.none_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} (f : α -> (Option.{u_1} β)), Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1, u_1} Option.{u_1} (Monad.toHasBind.{u_1, u_1} Option.{u_1} Option.monad.{u_1}) α β (Option.none.{u_1} α) f) (Option.none.{u_1} β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> (Option.{u_2} β)), Eq.{succ u_2} (Option.{u_2} β) (Option.bind.{u_1, u_2} α β (Option.none.{u_1} α) f) (Option.none.{u_2} β)
Case conversion may be inaccurate. Consider using '#align option.none_bind Option.none_bindₓ'. -/
@[simp]
theorem none_bind {α β} (f : α → Option β) : none >>= f = none :=
  rfl
#align option.none_bind Option.none_bind

/- warning: option.some_bind -> Option.some_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} (a : α) (f : α -> (Option.{u_1} β)), Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1, u_1} Option.{u_1} (Monad.toHasBind.{u_1, u_1} Option.{u_1} Option.monad.{u_1}) α β (Option.some.{u_1} α a) f) (f a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (a : α) (f : α -> (Option.{u_2} β)), Eq.{succ u_2} (Option.{u_2} β) (Option.bind.{u_1, u_2} α β (Option.some.{u_1} α a) f) (f a)
Case conversion may be inaccurate. Consider using '#align option.some_bind Option.some_bindₓ'. -/
@[simp]
theorem some_bind {α β} (a : α) (f : α → Option β) : some a >>= f = f a :=
  rfl
#align option.some_bind Option.some_bind

#print Option.none_bind' /-
@[simp]
theorem none_bind' (f : α → Option β) : none.bind f = none :=
  rfl
#align option.none_bind' Option.none_bind'
-/

#print Option.some_bind' /-
@[simp]
theorem some_bind' (a : α) (f : α → Option β) : (some a).bind f = f a :=
  rfl
#align option.some_bind' Option.some_bind'
-/

/- warning: option.bind_some -> Option.bind_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) α α x (Option.some.{u1} α)) x
but is expected to have type
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (Option.bind.{u1, u1} α α x (Option.some.{u1} α)) x
Case conversion may be inaccurate. Consider using '#align option.bind_some Option.bind_someₓ'. -/
@[simp]
theorem bind_some : ∀ x : Option α, x >>= some = x :=
  @bind_pure α Option _ _
#align option.bind_some Option.bind_some

@[simp]
theorem bind_some' : ∀ x : Option α, x.bind some = x :=
  bind_some
#align option.bind_some' Option.bind_some'

/- warning: option.bind_eq_some -> Option.bind_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {x : Option.{u_1} α} {f : α -> (Option.{u_1} β)} {b : β}, Iff (Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1, u_1} Option.{u_1} (Monad.toHasBind.{u_1, u_1} Option.{u_1} Option.monad.{u_1}) α β x f) (Option.some.{u_1} β b)) (Exists.{succ u_1} α (fun (a : α) => And (Eq.{succ u_1} (Option.{u_1} α) x (Option.some.{u_1} α a)) (Eq.{succ u_1} (Option.{u_1} β) (f a) (Option.some.{u_1} β b))))
but is expected to have type
  forall {α : Type.{u_1}} {β : α} {x : Type.{u_2}} {f : Option.{u_2} x} {b : x -> (Option.{u_1} α)}, Iff (Eq.{succ u_1} (Option.{u_1} α) (Option.bind.{u_2, u_1} x α f b) (Option.some.{u_1} α β)) (Exists.{succ u_2} x (fun (a : x) => And (Eq.{succ u_2} (Option.{u_2} x) f (Option.some.{u_2} x a)) (Eq.{succ u_1} (Option.{u_1} α) (b a) (Option.some.{u_1} α β))))
Case conversion may be inaccurate. Consider using '#align option.bind_eq_some Option.bind_eq_someₓ'. -/
@[simp]
theorem bind_eq_some {α β} {x : Option α} {f : α → Option β} {b : β} :
    x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b := by cases x <;> simp
#align option.bind_eq_some Option.bind_eq_some

/- warning: option.bind_eq_some' -> Option.bind_eq_some' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {x : Option.{u1} α} {f : α -> (Option.{u2} β)} {b : β}, Iff (Eq.{succ u2} (Option.{u2} β) (Option.bind.{u1, u2} α β x f) (Option.some.{u2} β b)) (Exists.{succ u1} α (fun (a : α) => And (Eq.{succ u1} (Option.{u1} α) x (Option.some.{u1} α a)) (Eq.{succ u2} (Option.{u2} β) (f a) (Option.some.{u2} β b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {x : Option.{u2} α} {f : α -> (Option.{u1} β)} {b : β}, Iff (Eq.{succ u1} (Option.{u1} β) (Option.bind.{u2, u1} α β x f) (Option.some.{u1} β b)) (Exists.{succ u2} α (fun (a : α) => And (Eq.{succ u2} (Option.{u2} α) x (Option.some.{u2} α a)) (Eq.{succ u1} (Option.{u1} β) (f a) (Option.some.{u1} β b))))
Case conversion may be inaccurate. Consider using '#align option.bind_eq_some' Option.bind_eq_some'ₓ'. -/
@[simp]
theorem bind_eq_some' {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by cases x <;> simp
#align option.bind_eq_some' Option.bind_eq_some'

/- warning: option.bind_eq_none' -> Option.bind_eq_none' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {o : Option.{u1} α} {f : α -> (Option.{u2} β)}, Iff (Eq.{succ u2} (Option.{u2} β) (Option.bind.{u1, u2} α β o f) (Option.none.{u2} β)) (forall (b : β) (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a o) -> (Not (Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (f a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {o : Option.{u2} α} {f : α -> (Option.{u1} β)}, Iff (Eq.{succ u1} (Option.{u1} β) (Option.bind.{u2, u1} α β o f) (Option.none.{u1} β)) (forall (b : β) (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a o) -> (Not (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (f a))))
Case conversion may be inaccurate. Consider using '#align option.bind_eq_none' Option.bind_eq_none'ₓ'. -/
@[simp]
theorem bind_eq_none' {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some']
#align option.bind_eq_none' Option.bind_eq_none'

/- warning: option.bind_eq_none -> Option.bind_eq_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {o : Option.{u_1} α} {f : α -> (Option.{u_1} β)}, Iff (Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1, u_1} Option.{u_1} (Monad.toHasBind.{u_1, u_1} Option.{u_1} Option.monad.{u_1}) α β o f) (Option.none.{u_1} β)) (forall (b : β) (a : α), (Membership.Mem.{u_1, u_1} α (Option.{u_1} α) (Option.hasMem.{u_1} α) a o) -> (Not (Membership.Mem.{u_1, u_1} β (Option.{u_1} β) (Option.hasMem.{u_1} β) b (f a))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {o : Option.{u_1} α} {f : α -> (Option.{u_2} β)}, Iff (Eq.{succ u_2} (Option.{u_2} β) (Option.bind.{u_1, u_2} α β o f) (Option.none.{u_2} β)) (forall (b : β) (a : α), (Membership.mem.{u_1, u_1} α (Option.{u_1} α) (Option.instMembershipOption.{u_1} α) a o) -> (Not (Membership.mem.{u_2, u_2} β (Option.{u_2} β) (Option.instMembershipOption.{u_2} β) b (f a))))
Case conversion may be inaccurate. Consider using '#align option.bind_eq_none Option.bind_eq_noneₓ'. -/
@[simp]
theorem bind_eq_none {α β} {o : Option α} {f : α → Option β} :
    o >>= f = none ↔ ∀ b a, a ∈ o → b ∉ f a :=
  bind_eq_none'
#align option.bind_eq_none Option.bind_eq_none

/- warning: option.bind_comm -> Option.bind_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> (Option.{u3} γ)} (a : Option.{u1} α) (b : Option.{u2} β), Eq.{succ u3} (Option.{u3} γ) (Option.bind.{u1, u3} α γ a (fun (x : α) => Option.bind.{u2, u3} β γ b (f x))) (Option.bind.{u2, u3} β γ b (fun (y : β) => Option.bind.{u1, u3} α γ a (fun (x : α) => f x y)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> (Option.{u1} γ)} (a : Option.{u3} α) (b : Option.{u2} β), Eq.{succ u1} (Option.{u1} γ) (Option.bind.{u3, u1} α γ a (fun (x : α) => Option.bind.{u2, u1} β γ b (f x))) (Option.bind.{u2, u1} β γ b (fun (y : β) => Option.bind.{u3, u1} α γ a (fun (x : α) => f x y)))
Case conversion may be inaccurate. Consider using '#align option.bind_comm Option.bind_commₓ'. -/
theorem bind_comm {α β γ} {f : α → β → Option γ} (a : Option α) (b : Option β) :
    (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by
  cases a <;> cases b <;> rfl
#align option.bind_comm Option.bind_comm

/- warning: option.bind_assoc -> Option.bind_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (x : Option.{u1} α) (f : α -> (Option.{u2} β)) (g : β -> (Option.{u3} γ)), Eq.{succ u3} (Option.{u3} γ) (Option.bind.{u2, u3} β γ (Option.bind.{u1, u2} α β x f) g) (Option.bind.{u1, u3} α γ x (fun (y : α) => Option.bind.{u2, u3} β γ (f y) g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (x : Option.{u3} α) (f : α -> (Option.{u2} β)) (g : β -> (Option.{u1} γ)), Eq.{succ u1} (Option.{u1} γ) (Option.bind.{u2, u1} β γ (Option.bind.{u3, u2} α β x f) g) (Option.bind.{u3, u1} α γ x (fun (y : α) => Option.bind.{u2, u1} β γ (f y) g))
Case conversion may be inaccurate. Consider using '#align option.bind_assoc Option.bind_assocₓ'. -/
theorem bind_assoc (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun y => (f y).bind g := by cases x <;> rfl
#align option.bind_assoc Option.bind_assoc

/- warning: option.join_eq_some -> Option.join_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : Option.{u1} (Option.{u1} α)} {a : α}, Iff (Eq.{succ u1} (Option.{u1} α) (Option.join.{u1} α x) (Option.some.{u1} α a)) (Eq.{succ u1} (Option.{u1} (Option.{u1} α)) x (Option.some.{u1} (Option.{u1} α) (Option.some.{u1} α a)))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {a : Option.{u1} (Option.{u1} α)}, Iff (Eq.{succ u1} (Option.{u1} α) (Option.join.{u1} α a) (Option.some.{u1} α x)) (Eq.{succ u1} (Option.{u1} (Option.{u1} α)) a (Option.some.{u1} (Option.{u1} α) (Option.some.{u1} α x)))
Case conversion may be inaccurate. Consider using '#align option.join_eq_some Option.join_eq_someₓ'. -/
theorem join_eq_some {x : Option (Option α)} {a : α} : x.join = some a ↔ x = some (some a) := by
  simp
#align option.join_eq_some Option.join_eq_some

#print Option.join_ne_none /-
theorem join_ne_none {x : Option (Option α)} : x.join ≠ none ↔ ∃ z, x = some (some z) := by simp
#align option.join_ne_none Option.join_ne_none
-/

#print Option.join_ne_none' /-
theorem join_ne_none' {x : Option (Option α)} : ¬x.join = none ↔ ∃ z, x = some (some z) := by simp
#align option.join_ne_none' Option.join_ne_none'
-/

#print Option.join_eq_none /-
theorem join_eq_none {o : Option (Option α)} : o.join = none ↔ o = none ∨ o = some none := by
  rcases o with (_ | _ | _) <;> simp
#align option.join_eq_none Option.join_eq_none
-/

/- warning: option.bind_id_eq_join -> Option.bind_id_eq_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : Option.{u1} (Option.{u1} α)}, Eq.{succ u1} (Option.{u1} α) (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) (Option.{u1} α) α x (id.{succ u1} (Option.{u1} α))) (Option.join.{u1} α x)
but is expected to have type
  forall {α : Type.{u1}} {x : Option.{u1} (Option.{u1} α)}, Eq.{succ u1} (Option.{u1} α) (Option.bind.{u1, u1} (Option.{u1} α) α x (id.{succ u1} (Option.{u1} α))) (Option.join.{u1} α x)
Case conversion may be inaccurate. Consider using '#align option.bind_id_eq_join Option.bind_id_eq_joinₓ'. -/
theorem bind_id_eq_join {x : Option (Option α)} : x >>= id = x.join := by simp
#align option.bind_id_eq_join Option.bind_id_eq_join

/- warning: option.join_eq_join -> Option.joinM_eq_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} ((Option.{u1} (Option.{u1} α)) -> (Option.{u1} α)) (joinM.{u1} Option.{u1} Option.monad.{u1} α) (Option.join.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} ((Option.{u1} (Option.{u1} α)) -> (Option.{u1} α)) (joinM.{u1} Option.{u1} instMonadOption.{u1} α) (Option.join.{u1} α)
Case conversion may be inaccurate. Consider using '#align option.join_eq_join Option.joinM_eq_joinₓ'. -/
theorem joinM_eq_join : joinM = @join α :=
  funext fun x => by rw [joinM, bind_id_eq_join]
#align option.join_eq_join Option.joinM_eq_join

/- warning: option.bind_eq_bind -> Option.bind_eq_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> (Option.{u1} β)} {x : Option.{u1} α}, Eq.{succ u1} (Option.{u1} β) (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) α β x f) (Option.bind.{u1, u1} α β x f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> (Option.{u1} β)} {x : Option.{u1} α}, Eq.{succ u1} (Option.{u1} β) (Bind.bind.{u1, u1} Option.{u1} (Monad.toBind.{u1, u1} Option.{u1} instMonadOption.{u1}) α β x f) (Option.bind.{u1, u1} α β x f)
Case conversion may be inaccurate. Consider using '#align option.bind_eq_bind Option.bind_eq_bindₓ'. -/
theorem bind_eq_bind {α β : Type _} {f : α → Option β} {x : Option α} : x >>= f = x.bind f :=
  rfl
#align option.bind_eq_bind Option.bind_eq_bind

/- warning: option.map_eq_map -> Option.map_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> β}, Eq.{succ u1} ((Option.{u1} α) -> (Option.{u1} β)) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α β f) (Option.map.{u1, u1} α β f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> β}, Eq.{succ u1} ((Option.{u1} α) -> (Option.{u1} β)) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α β f) (Option.map.{u1, u1} α β f)
Case conversion may be inaccurate. Consider using '#align option.map_eq_map Option.map_eq_mapₓ'. -/
@[simp]
theorem map_eq_map {α β} {f : α → β} : (· <$> ·) f = Option.map f :=
  rfl
#align option.map_eq_map Option.map_eq_map

/- warning: option.map_none -> Option.map_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> β}, Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α β f (Option.none.{u1} α)) (Option.none.{u1} β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> β}, Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α β f (Option.none.{u1} α)) (Option.none.{u1} β)
Case conversion may be inaccurate. Consider using '#align option.map_none Option.map_noneₓ'. -/
theorem map_none {α β} {f : α → β} : f <$> none = none :=
  rfl
#align option.map_none Option.map_none

/- warning: option.map_some -> Option.map_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {a : α} {f : α -> β}, Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α β f (Option.some.{u1} α a)) (Option.some.{u1} β (f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {a : α -> β} {f : α}, Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α β a (Option.some.{u1} α f)) (Option.some.{u1} β (a f))
Case conversion may be inaccurate. Consider using '#align option.map_some Option.map_someₓ'. -/
theorem map_some {α β} {a : α} {f : α → β} : f <$> some a = some (f a) :=
  rfl
#align option.map_some Option.map_some

/- warning: option.map_coe -> Option.map_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {a : α} {f : α -> β}, Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} (fun {α : Type.{u1}} => Option.{u1} α) (Traversable.toFunctor.{u1} (fun {α : Type.{u1}} => Option.{u1} α) Option.traversable.{u1}) α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) β (Option.{u1} β) (HasLiftT.mk.{succ u1, succ u1} β (Option.{u1} β) (CoeTCₓ.coe.{succ u1, succ u1} β (Option.{u1} β) (coeOption.{u1} β))) (f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {a : α} {f : α -> β}, Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α β f (Option.some.{u1} α a)) (Option.some.{u1} β (f a))
Case conversion may be inaccurate. Consider using '#align option.map_coe Option.map_coeₓ'. -/
theorem map_coe {α β} {a : α} {f : α → β} : f <$> (a : Option α) = ↑(f a) :=
  rfl
#align option.map_coe Option.map_coe

/- warning: option.map_none' -> Option.map_none' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Eq.{succ u2} (Option.{u2} β) (Option.map.{u1, u2} α β f (Option.none.{u1} α)) (Option.none.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{succ u1} (Option.{u1} β) (Option.map.{u2, u1} α β f (Option.none.{u2} α)) (Option.none.{u1} β)
Case conversion may be inaccurate. Consider using '#align option.map_none' Option.map_none'ₓ'. -/
@[simp]
theorem map_none' {f : α → β} : Option.map f none = none :=
  rfl
#align option.map_none' Option.map_none'

/- warning: option.map_some' -> Option.map_some' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {a : α} {f : α -> β}, Eq.{succ u2} (Option.{u2} β) (Option.map.{u1, u2} α β f (Option.some.{u1} α a)) (Option.some.{u2} β (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (f : α -> β), Eq.{succ u1} (Option.{u1} β) (Option.map.{u2, u1} α β f (Option.some.{u2} α a)) (Option.some.{u1} β (f a))
Case conversion may be inaccurate. Consider using '#align option.map_some' Option.map_some'ₓ'. -/
@[simp]
theorem map_some' {a : α} {f : α → β} : Option.map f (some a) = some (f a) :=
  rfl
#align option.map_some' Option.map_some'

#print Option.map_coe' /-
@[simp]
theorem map_coe' {a : α} {f : α → β} : Option.map f (a : Option α) = ↑(f a) :=
  rfl
#align option.map_coe' Option.map_coe'
-/

/- warning: option.map_eq_some -> Option.map_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {x : Option.{u1} α} {f : α -> β} {b : β}, Iff (Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} (fun {α : Type.{u1}} => Option.{u1} α) (Traversable.toFunctor.{u1} (fun {α : Type.{u1}} => Option.{u1} α) Option.traversable.{u1}) α β f x) (Option.some.{u1} β b)) (Exists.{succ u1} α (fun (a : α) => And (Eq.{succ u1} (Option.{u1} α) x (Option.some.{u1} α a)) (Eq.{succ u1} β (f a) b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {x : α -> β} {f : Option.{u1} α} {b : β}, Iff (Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α β x f) (Option.some.{u1} β b)) (Exists.{succ u1} α (fun (a : α) => And (Eq.{succ u1} (Option.{u1} α) f (Option.some.{u1} α a)) (Eq.{succ u1} β (x a) b)))
Case conversion may be inaccurate. Consider using '#align option.map_eq_some Option.map_eq_someₓ'. -/
theorem map_eq_some {α β} {x : Option α} {f : α → β} {b : β} :
    f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b := by cases x <;> simp
#align option.map_eq_some Option.map_eq_some

/- warning: option.map_eq_some' -> Option.map_eq_some' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {x : Option.{u1} α} {f : α -> β} {b : β}, Iff (Eq.{succ u2} (Option.{u2} β) (Option.map.{u1, u2} α β f x) (Option.some.{u2} β b)) (Exists.{succ u1} α (fun (a : α) => And (Eq.{succ u1} (Option.{u1} α) x (Option.some.{u1} α a)) (Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : α} {x : Type.{u1}} {f : Option.{u1} x} {b : x -> α}, Iff (Eq.{succ u2} (Option.{u2} α) (Option.map.{u1, u2} x α b f) (Option.some.{u2} α β)) (Exists.{succ u1} x (fun (a : x) => And (Eq.{succ u1} (Option.{u1} x) f (Option.some.{u1} x a)) (Eq.{succ u2} α (b a) β)))
Case conversion may be inaccurate. Consider using '#align option.map_eq_some' Option.map_eq_some'ₓ'. -/
@[simp]
theorem map_eq_some' {x : Option α} {f : α → β} {b : β} :
    x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by cases x <;> simp
#align option.map_eq_some' Option.map_eq_some'

/- warning: option.map_eq_none -> Option.map_eq_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {x : Option.{u1} α} {f : α -> β}, Iff (Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} (fun {α : Type.{u1}} => Option.{u1} α) (Traversable.toFunctor.{u1} (fun {α : Type.{u1}} => Option.{u1} α) Option.traversable.{u1}) α β f x) (Option.none.{u1} β)) (Eq.{succ u1} (Option.{u1} α) x (Option.none.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {x : α -> β} {f : Option.{u1} α}, Iff (Eq.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α β x f) (Option.none.{u1} β)) (Eq.{succ u1} (Option.{u1} α) f (Option.none.{u1} α))
Case conversion may be inaccurate. Consider using '#align option.map_eq_none Option.map_eq_noneₓ'. -/
theorem map_eq_none {α β} {x : Option α} {f : α → β} : f <$> x = none ↔ x = none := by
  cases x <;> simp only [map_none, map_some, eq_self_iff_true]
#align option.map_eq_none Option.map_eq_none

/- warning: option.map_eq_none' -> Option.map_eq_none' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {x : Option.{u1} α} {f : α -> β}, Iff (Eq.{succ u2} (Option.{u2} β) (Option.map.{u1, u2} α β f x) (Option.none.{u2} β)) (Eq.{succ u1} (Option.{u1} α) x (Option.none.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Option.{u2} α} {x : Type.{u1}} {f : α -> x}, Iff (Eq.{succ u1} (Option.{u1} x) (Option.map.{u2, u1} α x f β) (Option.none.{u1} x)) (Eq.{succ u2} (Option.{u2} α) β (Option.none.{u2} α))
Case conversion may be inaccurate. Consider using '#align option.map_eq_none' Option.map_eq_none'ₓ'. -/
@[simp]
theorem map_eq_none' {x : Option α} {f : α → β} : x.map f = none ↔ x = none := by
  cases x <;> simp only [map_none', map_some', eq_self_iff_true]
#align option.map_eq_none' Option.map_eq_none'

/- warning: option.map_injective' -> Option.map_injective' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) ((Option.{u1} α) -> (Option.{u2} β)) (Option.map.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> β) ((Option.{u2} α) -> (Option.{u1} β)) (Option.map.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align option.map_injective' Option.map_injective'ₓ'. -/
/-- `option.map` as a function between functions is injective. -/
theorem map_injective' : Function.Injective (@Option.map α β) := fun f g h =>
  funext fun x => some_injective _ <| by simp only [← map_some', h]
#align option.map_injective' Option.map_injective'

/- warning: option.map_inj -> Option.map_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β}, Iff (Eq.{max (succ u1) (succ u2)} ((Option.{u1} α) -> (Option.{u2} β)) (Option.map.{u1, u2} α β f) (Option.map.{u1, u2} α β g)) (Eq.{max (succ u1) (succ u2)} (α -> β) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β}, Iff (Eq.{max (succ u2) (succ u1)} ((Option.{u2} α) -> (Option.{u1} β)) (Option.map.{u2, u1} α β f) (Option.map.{u2, u1} α β g)) (Eq.{max (succ u2) (succ u1)} (α -> β) f g)
Case conversion may be inaccurate. Consider using '#align option.map_inj Option.map_injₓ'. -/
@[simp]
theorem map_inj {f g : α → β} : Option.map f = Option.map g ↔ f = g :=
  map_injective'.eq_iff
#align option.map_inj Option.map_inj

/- warning: option.map_congr -> Option.map_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {x : Option.{u1} α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (Eq.{succ u2} β (f a) (g a))) -> (Eq.{succ u2} (Option.{u2} β) (Option.map.{u1, u2} α β f x) (Option.map.{u1, u2} α β g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {x : Option.{u2} α}, (forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (Eq.{succ u1} β (f a) (g a))) -> (Eq.{succ u1} (Option.{u1} β) (Option.map.{u2, u1} α β f x) (Option.map.{u2, u1} α β g x))
Case conversion may be inaccurate. Consider using '#align option.map_congr Option.map_congrₓ'. -/
theorem map_congr {f g : α → β} {x : Option α} (h : ∀ a ∈ x, f a = g a) :
    Option.map f x = Option.map g x := by cases x <;> simp only [map_none', map_some', h, mem_def]
#align option.map_congr Option.map_congr

attribute [simp] map_id

#print Option.map_eq_id /-
@[simp]
theorem map_eq_id {f : α → α} : Option.map f = id ↔ f = id :=
  map_injective'.eq_iff' map_id
#align option.map_eq_id Option.map_eq_id
-/

/- warning: option.map_map -> Option.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (h : β -> γ) (g : α -> β) (x : Option.{u1} α), Eq.{succ u3} (Option.{u3} γ) (Option.map.{u2, u3} β γ h (Option.map.{u1, u2} α β g x)) (Option.map.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ h g) x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (h : α -> β) (g : γ -> α) (x : Option.{u1} γ), Eq.{succ u2} (Option.{u2} β) (Option.map.{u3, u2} α β h (Option.map.{u1, u3} γ α g x)) (Option.map.{u1, u2} γ β (Function.comp.{succ u1, succ u3, succ u2} γ α β h g) x)
Case conversion may be inaccurate. Consider using '#align option.map_map Option.map_mapₓ'. -/
@[simp]
theorem map_map (h : β → γ) (g : α → β) (x : Option α) :
    Option.map h (Option.map g x) = Option.map (h ∘ g) x := by
  cases x <;> simp only [map_none', map_some']
#align option.map_map Option.map_map

/- warning: option.map_comm -> Option.map_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}, (Eq.{max (succ u1) (succ u4)} (α -> δ) (Function.comp.{succ u1, succ u2, succ u4} α β δ g₁ f₁) (Function.comp.{succ u1, succ u3, succ u4} α γ δ g₂ f₂)) -> (forall (a : α), Eq.{succ u4} (Option.{u4} δ) (Option.map.{u2, u4} β δ g₁ (Option.map.{u1, u2} α β f₁ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a))) (Option.map.{u3, u4} γ δ g₂ (Option.map.{u1, u3} α γ f₂ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u3}} {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}, (Eq.{max (succ u4) (succ u3)} (α -> δ) (Function.comp.{succ u4, succ u2, succ u3} α β δ g₁ f₁) (Function.comp.{succ u4, succ u1, succ u3} α γ δ g₂ f₂)) -> (forall (a : α), Eq.{succ u3} (Option.{u3} δ) (Option.map.{u2, u3} β δ g₁ (Option.map.{u4, u2} α β f₁ (Option.some.{u4} α a))) (Option.map.{u1, u3} γ δ g₂ (Option.map.{u4, u1} α γ f₂ (Option.some.{u4} α a))))
Case conversion may be inaccurate. Consider using '#align option.map_comm Option.map_commₓ'. -/
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) : (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂ := by rw [map_map, h, ← map_map]
#align option.map_comm Option.map_comm

/- warning: option.comp_map -> Option.comp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (h : β -> γ) (g : α -> β) (x : Option.{u1} α), Eq.{succ u3} (Option.{u3} γ) (Option.map.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ h g) x) (Option.map.{u2, u3} β γ h (Option.map.{u1, u2} α β g x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (h : α -> β) (g : γ -> α) (x : Option.{u1} γ), Eq.{succ u2} (Option.{u2} β) (Option.map.{u1, u2} γ β (Function.comp.{succ u1, succ u3, succ u2} γ α β h g) x) (Option.map.{u3, u2} α β h (Option.map.{u1, u3} γ α g x))
Case conversion may be inaccurate. Consider using '#align option.comp_map Option.comp_mapₓ'. -/
theorem comp_map (h : β → γ) (g : α → β) (x : Option α) :
    Option.map (h ∘ g) x = Option.map h (Option.map g x) :=
  (map_map _ _ _).symm
#align option.comp_map Option.comp_map

/- warning: option.map_comp_map -> Option.map_comp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : β -> γ), Eq.{max (succ u1) (succ u3)} ((Option.{u1} α) -> (Option.{u3} γ)) (Function.comp.{succ u1, succ u2, succ u3} (Option.{u1} α) (Option.{u2} β) (Option.{u3} γ) (Option.map.{u2, u3} β γ g) (Option.map.{u1, u2} α β f)) (Option.map.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β) (g : β -> γ), Eq.{max (succ u1) (succ u3)} ((Option.{u3} α) -> (Option.{u1} γ)) (Function.comp.{succ u3, succ u2, succ u1} (Option.{u3} α) (Option.{u2} β) (Option.{u1} γ) (Option.map.{u2, u1} β γ g) (Option.map.{u3, u2} α β f)) (Option.map.{u3, u1} α γ (Function.comp.{succ u3, succ u2, succ u1} α β γ g f))
Case conversion may be inaccurate. Consider using '#align option.map_comp_map Option.map_comp_mapₓ'. -/
@[simp]
theorem map_comp_map (f : α → β) (g : β → γ) : Option.map g ∘ Option.map f = Option.map (g ∘ f) :=
  by
  ext x
  rw [comp_map]
#align option.map_comp_map Option.map_comp_map

/- warning: option.mem_map_of_mem -> Option.mem_map_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {a : α} {x : Option.{u1} α} (g : α -> β), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) (g a) (Option.map.{u1, u2} α β g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {a : α} {x : Option.{u2} α} (g : α -> β), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) (g a) (Option.map.{u2, u1} α β g x))
Case conversion may be inaccurate. Consider using '#align option.mem_map_of_mem Option.mem_map_of_memₓ'. -/
theorem mem_map_of_mem {a : α} {x : Option α} (g : α → β) (h : a ∈ x) : g a ∈ x.map g :=
  mem_def.mpr ((mem_def.mp h).symm ▸ map_some')
#align option.mem_map_of_mem Option.mem_map_of_mem

theorem mem_map {f : α → β} {y : β} {o : Option α} : y ∈ o.map f ↔ ∃ x ∈ o, f x = y := by simp
#align option.mem_map Option.mem_map

theorem forall_mem_map {f : α → β} {o : Option α} {p : β → Prop} :
    (∀ y ∈ o.map f, p y) ↔ ∀ x ∈ o, p (f x) := by simp
#align option.forall_mem_map Option.forall_mem_map

theorem exists_mem_map {f : α → β} {o : Option α} {p : β → Prop} :
    (∃ y ∈ o.map f, p y) ↔ ∃ x ∈ o, p (f x) := by simp
#align option.exists_mem_map Option.exists_mem_map

/- warning: option.bind_map_comm -> Option.bind_map_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {x : Option.{u_1} (Option.{u_1} α)} {f : α -> β}, Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1, u_1} Option.{u_1} (Monad.toHasBind.{u_1, u_1} Option.{u_1} Option.monad.{u_1}) (Option.{u_1} α) β x (Option.map.{u_1, u_1} α β f)) (Bind.bind.{u_1, u_1} Option.{u_1} (Monad.toHasBind.{u_1, u_1} Option.{u_1} Option.monad.{u_1}) (Option.{u_1} β) β (Option.map.{u_1, u_1} (Option.{u_1} α) (Option.{u_1} β) (Option.map.{u_1, u_1} α β f) x) (id.{succ u_1} (Option.{u_1} β)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {x : Option.{u_1} (Option.{u_1} α)} {f : α -> β}, Eq.{succ u_2} (Option.{u_2} β) (Option.bind.{u_1, u_2} (Option.{u_1} α) β x (Option.map.{u_1, u_2} α β f)) (Option.bind.{u_2, u_2} (Option.{u_2} β) β (Option.map.{u_1, u_2} (Option.{u_1} α) (Option.{u_2} β) (Option.map.{u_1, u_2} α β f) x) (id.{succ u_2} (Option.{u_2} β)))
Case conversion may be inaccurate. Consider using '#align option.bind_map_comm Option.bind_map_commₓ'. -/
theorem bind_map_comm {α β} {x : Option (Option α)} {f : α → β} :
    x >>= Option.map f = x.map (Option.map f) >>= id := by cases x <;> simp
#align option.bind_map_comm Option.bind_map_comm

/- warning: option.join_map_eq_map_join -> Option.join_map_eq_map_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : Option.{u1} (Option.{u1} α)}, Eq.{succ u2} (Option.{u2} β) (Option.join.{u2} β (Option.map.{u1, u2} (Option.{u1} α) (Option.{u2} β) (Option.map.{u1, u2} α β f) x)) (Option.map.{u1, u2} α β f (Option.join.{u1} α x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {x : Option.{u2} (Option.{u2} α)}, Eq.{succ u1} (Option.{u1} β) (Option.join.{u1} β (Option.map.{u2, u1} (Option.{u2} α) (Option.{u1} β) (Option.map.{u2, u1} α β f) x)) (Option.map.{u2, u1} α β f (Option.join.{u2} α x))
Case conversion may be inaccurate. Consider using '#align option.join_map_eq_map_join Option.join_map_eq_map_joinₓ'. -/
theorem join_map_eq_map_join {f : α → β} {x : Option (Option α)} :
    (x.map (Option.map f)).join = x.join.map f := by rcases x with (_ | _ | x) <;> simp
#align option.join_map_eq_map_join Option.join_map_eq_map_join

#print Option.join_join /-
theorem join_join {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  rcases x with (_ | _ | _ | x) <;> simp
#align option.join_join Option.join_join
-/

#print Option.mem_of_mem_join /-
theorem mem_of_mem_join {a : α} {x : Option (Option α)} (h : a ∈ x.join) : some a ∈ x :=
  mem_def.mpr ((mem_def.mp h).symm ▸ join_eq_some.mp h)
#align option.mem_of_mem_join Option.mem_of_mem_join
-/

section Pmap

variable {p : α → Prop} (f : ∀ a : α, p a → β) (x : Option α)

#print Option.pbind_eq_bind /-
@[simp]
theorem pbind_eq_bind (f : α → Option β) (x : Option α) : (x.pbind fun a _ => f a) = x.bind f := by
  cases x <;> simp only [pbind, none_bind', some_bind']
#align option.pbind_eq_bind Option.pbind_eq_bind
-/

/- warning: option.map_bind -> Option.map_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (f : β -> γ) (x : Option.{u1} α) (g : α -> (Option.{u1} β)), Eq.{succ u1} (Option.{u1} γ) (Option.map.{u1, u1} β γ f (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) α β x g)) (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) α γ x (fun (a : α) => Option.map.{u1, u1} β γ f (g a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (f : β -> γ) (x : Option.{u1} α) (g : α -> (Option.{u1} β)), Eq.{succ u1} (Option.{u1} γ) (Option.map.{u1, u1} β γ f (Bind.bind.{u1, u1} Option.{u1} (Monad.toBind.{u1, u1} Option.{u1} instMonadOption.{u1}) α β x g)) (Bind.bind.{u1, u1} Option.{u1} (Monad.toBind.{u1, u1} Option.{u1} instMonadOption.{u1}) α γ x (fun (a : α) => Option.map.{u1, u1} β γ f (g a)))
Case conversion may be inaccurate. Consider using '#align option.map_bind Option.map_bindₓ'. -/
theorem map_bind {α β γ} (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x >>= g) = x >>= fun a => Option.map f (g a) := by
  simp_rw [← map_eq_map, ← bind_pure_comp_eq_map, LawfulMonad.bind_assoc]
#align option.map_bind Option.map_bind

/- warning: option.map_bind' -> Option.map_bind' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : β -> γ) (x : Option.{u1} α) (g : α -> (Option.{u2} β)), Eq.{succ u3} (Option.{u3} γ) (Option.map.{u2, u3} β γ f (Option.bind.{u1, u2} α β x g)) (Option.bind.{u1, u3} α γ x (fun (a : α) => Option.map.{u2, u3} β γ f (g a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : β -> γ) (x : Option.{u3} α) (g : α -> (Option.{u2} β)), Eq.{succ u1} (Option.{u1} γ) (Option.map.{u2, u1} β γ f (Option.bind.{u3, u2} α β x g)) (Option.bind.{u3, u1} α γ x (fun (a : α) => Option.map.{u2, u1} β γ f (g a)))
Case conversion may be inaccurate. Consider using '#align option.map_bind' Option.map_bind'ₓ'. -/
theorem map_bind' (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x.bind g) = x.bind fun a => Option.map f (g a) := by cases x <;> simp
#align option.map_bind' Option.map_bind'

/- warning: option.map_pbind -> Option.map_pbind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : β -> γ) (x : Option.{u1} α) (g : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (Option.{u2} β)), Eq.{succ u3} (Option.{u3} γ) (Option.map.{u2, u3} β γ f (Option.pbind.{u1, u2} α β x g)) (Option.pbind.{u1, u3} α γ x (fun (a : α) (H : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) => Option.map.{u2, u3} β γ f (g a H)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : β -> γ) (x : Option.{u3} α) (g : forall (a : α), (Membership.mem.{u3, u3} α (Option.{u3} α) (Option.instMembershipOption.{u3} α) a x) -> (Option.{u2} β)), Eq.{succ u1} (Option.{u1} γ) (Option.map.{u2, u1} β γ f (Option.pbind.{u3, u2} α β x g)) (Option.pbind.{u3, u1} α γ x (fun (a : α) (H : Membership.mem.{u3, u3} α (Option.{u3} α) (Option.instMembershipOption.{u3} α) a x) => Option.map.{u2, u1} β γ f (g a H)))
Case conversion may be inaccurate. Consider using '#align option.map_pbind Option.map_pbindₓ'. -/
theorem map_pbind (f : β → γ) (x : Option α) (g : ∀ a, a ∈ x → Option β) :
    Option.map f (x.pbind g) = x.pbind fun a H => Option.map f (g a H) := by
  cases x <;> simp only [pbind, map_none']
#align option.map_pbind Option.map_pbind

/- warning: option.pbind_map -> Option.pbind_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (x : Option.{u1} α) (g : forall (b : β), (Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Option.map.{u1, u2} α β f x)) -> (Option.{u3} γ)), Eq.{succ u3} (Option.{u3} γ) (Option.pbind.{u2, u3} β γ (Option.map.{u1, u2} α β f x) g) (Option.pbind.{u1, u3} α γ x (fun (a : α) (h : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) => g (f a) (Option.mem_map_of_mem.{u1, u2} α β a x f h)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β) (x : Option.{u3} α) (g : forall (b : β), (Membership.mem.{u2, u2} β (Option.{u2} β) (Option.instMembershipOption.{u2} β) b (Option.map.{u3, u2} α β f x)) -> (Option.{u1} γ)), Eq.{succ u1} (Option.{u1} γ) (Option.pbind.{u2, u1} β γ (Option.map.{u3, u2} α β f x) g) (Option.pbind.{u3, u1} α γ x (fun (a : α) (h : Membership.mem.{u3, u3} α (Option.{u3} α) (Option.instMembershipOption.{u3} α) a x) => g (f a) (Option.mem_map_of_mem.{u2, u3} α β a x f h)))
Case conversion may be inaccurate. Consider using '#align option.pbind_map Option.pbind_mapₓ'. -/
theorem pbind_map (f : α → β) (x : Option α) (g : ∀ b : β, b ∈ x.map f → Option γ) :
    pbind (Option.map f x) g = x.pbind fun a h => g (f a) (mem_map_of_mem _ h) := by cases x <;> rfl
#align option.pbind_map Option.pbind_map

/- warning: option.pmap_none -> Option.pmap_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) {H : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a (Option.none.{u1} α)) -> (p a)}, Eq.{succ u2} (Option.{u2} β) (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f (Option.none.{u1} α) H) (Option.none.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) {H : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a (Option.none.{u2} α)) -> (p a)}, Eq.{succ u1} (Option.{u1} β) (Option.pmap.{u2, u1} α β (fun (a : α) => p a) f (Option.none.{u2} α) H) (Option.none.{u1} β)
Case conversion may be inaccurate. Consider using '#align option.pmap_none Option.pmap_noneₓ'. -/
@[simp]
theorem pmap_none (f : ∀ a : α, p a → β) {H} : pmap f (@none α) H = none :=
  rfl
#align option.pmap_none Option.pmap_none

#print Option.pmap_some /-
@[simp]
theorem pmap_some (f : ∀ a : α, p a → β) {x : α} (h : p x) :
    pmap f (some x) = fun _ => some (f x h) :=
  rfl
#align option.pmap_some Option.pmap_some
-/

/- warning: option.mem_pmem -> Option.mem_pmem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (x : Option.{u1} α) {a : α} (h : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (p a)) (ha : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x), Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) (f a (h a ha)) (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f x h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (x : Option.{u2} α) {a : α} (h : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (p a)) (ha : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x), Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) (f a (h a ha)) (Option.pmap.{u2, u1} α β (fun (a : α) => p a) f x h)
Case conversion may be inaccurate. Consider using '#align option.mem_pmem Option.mem_pmemₓ'. -/
theorem mem_pmem {a : α} (h : ∀ a ∈ x, p a) (ha : a ∈ x) : f a (h a ha) ∈ pmap f x h :=
  by
  rw [mem_def] at ha⊢
  subst ha
  rfl
#align option.mem_pmem Option.mem_pmem

/- warning: option.pmap_map -> Option.pmap_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (g : γ -> α) (x : Option.{u3} γ) (H : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a (Option.map.{u3, u1} γ α g x)) -> (p a)), Eq.{succ u2} (Option.{u2} β) (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f (Option.map.{u3, u1} γ α g x) H) (Option.pmap.{u3, u2} γ β (fun (a : γ) => p (g a)) (fun (a : γ) (h : p (g a)) => f (g a) h) x (fun (a : γ) (h : Membership.Mem.{u3, u3} γ (Option.{u3} γ) (Option.hasMem.{u3} γ) a x) => H (g a) (Option.mem_map_of_mem.{u3, u1} γ α a x g h)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (g : γ -> α) (x : Option.{u3} γ) (H : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a (Option.map.{u3, u2} γ α g x)) -> (p a)), Eq.{succ u1} (Option.{u1} β) (Option.pmap.{u2, u1} α β (fun (a : α) => p a) f (Option.map.{u3, u2} γ α g x) H) (Option.pmap.{u3, u1} γ β (fun (a : γ) => p (g a)) (fun (a : γ) (h : p (g a)) => f (g a) h) x (fun (a : γ) (h : Membership.mem.{u3, u3} γ (Option.{u3} γ) (Option.instMembershipOption.{u3} γ) a x) => H (g a) (Option.mem_map_of_mem.{u2, u3} γ α a x g h)))
Case conversion may be inaccurate. Consider using '#align option.pmap_map Option.pmap_mapₓ'. -/
theorem pmap_map (g : γ → α) (x : Option γ) (H) :
    pmap f (x.map g) H = pmap (fun a h => f (g a) h) x fun a h => H _ (mem_map_of_mem _ h) := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.pmap_map Option.pmap_map

/- warning: option.map_pmap -> Option.map_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {p : α -> Prop} (g : β -> γ) (f : forall (a : α), (p a) -> β) (x : Option.{u1} α) (H : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (p a)), Eq.{succ u3} (Option.{u3} γ) (Option.map.{u2, u3} β γ g (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f x H)) (Option.pmap.{u1, u3} α γ (fun (a : α) => p a) (fun (a : α) (h : p a) => g (f a h)) x H)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {p : α -> Prop} (g : β -> γ) (f : forall (a : α), (p a) -> β) (x : Option.{u3} α) (H : forall (a : α), (Membership.mem.{u3, u3} α (Option.{u3} α) (Option.instMembershipOption.{u3} α) a x) -> (p a)), Eq.{succ u2} (Option.{u2} γ) (Option.map.{u1, u2} β γ g (Option.pmap.{u3, u1} α β (fun (a : α) => p a) f x H)) (Option.pmap.{u3, u2} α γ (fun (a : α) => p a) (fun (a : α) (h : p a) => g (f a h)) x H)
Case conversion may be inaccurate. Consider using '#align option.map_pmap Option.map_pmapₓ'. -/
theorem map_pmap (g : β → γ) (f : ∀ a, p a → β) (x H) :
    Option.map g (pmap f x H) = pmap (fun a h => g (f a h)) x H := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.map_pmap Option.map_pmap

/- warning: option.pmap_eq_map -> Option.pmap_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Prop) (f : α -> β) (x : Option.{u1} α) (H : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (p a)), Eq.{succ u2} (Option.{u2} β) (Option.pmap.{u1, u2} α β p (fun (a : α) (_x : p a) => f a) x H) (Option.map.{u1, u2} α β f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : α -> Prop) (f : α -> β) (x : Option.{u2} α) (H : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (p a)), Eq.{succ u1} (Option.{u1} β) (Option.pmap.{u2, u1} α β p (fun (a : α) (_x : p a) => f a) x H) (Option.map.{u2, u1} α β f x)
Case conversion may be inaccurate. Consider using '#align option.pmap_eq_map Option.pmap_eq_mapₓ'. -/
@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (x H) :
    @pmap _ _ p (fun a _ => f a) x H = Option.map f x := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.pmap_eq_map Option.pmap_eq_map

/- warning: option.pmap_bind -> Option.pmap_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} {x : Option.{u1} α} {g : α -> (Option.{u1} β)} {p : β -> Prop} {f : forall (b : β), (p b) -> γ} (H : forall (a : β), (Membership.Mem.{u1, u1} β (Option.{u1} β) (Option.hasMem.{u1} β) a (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) α β x g)) -> (p a)) (H' : forall (a : α) (b : β), (Membership.Mem.{u1, u1} β (Option.{u1} β) (Option.hasMem.{u1} β) b (g a)) -> (Membership.Mem.{u1, u1} β (Option.{u1} β) (Option.hasMem.{u1} β) b (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) α β x g))), Eq.{succ u1} (Option.{u1} γ) (Option.pmap.{u1, u1} β γ (fun (b : β) => p b) f (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) α β x g) H) (Bind.bind.{u1, u1} Option.{u1} (Monad.toHasBind.{u1, u1} Option.{u1} Option.monad.{u1}) α γ x (fun (a : α) => Option.pmap.{u1, u1} β γ (fun (b : β) => p b) f (g a) (fun (b : β) (h : Membership.Mem.{u1, u1} β (Option.{u1} β) (Option.hasMem.{u1} β) b (g a)) => H b (H' a b h))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} {x : Option.{u1} α} {g : α -> (Option.{u1} β)} {p : β -> Prop} {f : forall (b : β), (p b) -> γ} (H : forall (a : β), (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) a (Bind.bind.{u1, u1} Option.{u1} (Monad.toBind.{u1, u1} Option.{u1} instMonadOption.{u1}) α β x g)) -> (p a)) (H' : forall (a : α) (b : β), (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (g a)) -> (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Bind.bind.{u1, u1} Option.{u1} (Monad.toBind.{u1, u1} Option.{u1} instMonadOption.{u1}) α β x g))), Eq.{succ u1} (Option.{u1} γ) (Option.pmap.{u1, u1} β γ (fun (b : β) => p b) f (Bind.bind.{u1, u1} Option.{u1} (Monad.toBind.{u1, u1} Option.{u1} instMonadOption.{u1}) α β x g) H) (Bind.bind.{u1, u1} Option.{u1} (Monad.toBind.{u1, u1} Option.{u1} instMonadOption.{u1}) α γ x (fun (a : α) => Option.pmap.{u1, u1} β γ (fun (b : β) => p b) f (g a) (fun (b : β) (h : Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (g a)) => H b (H' a b h))))
Case conversion may be inaccurate. Consider using '#align option.pmap_bind Option.pmap_bindₓ'. -/
theorem pmap_bind {α β γ} {x : Option α} {g : α → Option β} {p : β → Prop} {f : ∀ b, p b → γ} (H)
    (H' : ∀ (a : α), ∀ b ∈ g a, b ∈ x >>= g) :
    pmap f (x >>= g) H = x >>= fun a => pmap f (g a) fun b h => H _ (H' a _ h) := by
  cases x <;> simp only [pmap, none_bind, some_bind]
#align option.pmap_bind Option.pmap_bind

/- warning: option.bind_pmap -> Option.bind_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (x : Option.{u1} α) (g : β -> (Option.{u2} γ)) (H : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (p a)), Eq.{succ u2} (Option.{u2} γ) (Bind.bind.{u2, u2} Option.{u2} (Monad.toHasBind.{u2, u2} Option.{u2} Option.monad.{u2}) β γ (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f x H) g) (Option.pbind.{u1, u2} α γ x (fun (a : α) (h : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) => g (f a (H a h))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (x : Option.{u2} α) (g : β -> (Option.{u1} γ)) (H : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (p a)), Eq.{succ u1} (Option.{u1} γ) (Bind.bind.{u1, u1} Option.{u1} (Monad.toBind.{u1, u1} Option.{u1} instMonadOption.{u1}) β γ (Option.pmap.{u2, u1} α β (fun (a : α) => p a) f x H) g) (Option.pbind.{u2, u1} α γ x (fun (a : α) (h : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) => g (f a (H a h))))
Case conversion may be inaccurate. Consider using '#align option.bind_pmap Option.bind_pmapₓ'. -/
theorem bind_pmap {α β γ} {p : α → Prop} (f : ∀ a, p a → β) (x : Option α) (g : β → Option γ) (H) :
    pmap f x H >>= g = x.pbind fun a h => g (f a (H _ h)) := by
  cases x <;> simp only [pmap, none_bind, some_bind, pbind]
#align option.bind_pmap Option.bind_pmap

variable {f x}

/- warning: option.pbind_eq_none -> Option.pbind_eq_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {x : Option.{u1} α} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (Option.{u2} β)}, (forall (a : α) (H : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x), (Eq.{succ u2} (Option.{u2} β) (f a H) (Option.none.{u2} β)) -> (Eq.{succ u1} (Option.{u1} α) x (Option.none.{u1} α))) -> (Iff (Eq.{succ u2} (Option.{u2} β) (Option.pbind.{u1, u2} α β x f) (Option.none.{u2} β)) (Eq.{succ u1} (Option.{u1} α) x (Option.none.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {x : Option.{u2} α} {f : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (Option.{u1} β)}, (forall (a : α) (H : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x), (Eq.{succ u1} (Option.{u1} β) (f a H) (Option.none.{u1} β)) -> (Eq.{succ u2} (Option.{u2} α) x (Option.none.{u2} α))) -> (Iff (Eq.{succ u1} (Option.{u1} β) (Option.pbind.{u2, u1} α β x f) (Option.none.{u1} β)) (Eq.{succ u2} (Option.{u2} α) x (Option.none.{u2} α)))
Case conversion may be inaccurate. Consider using '#align option.pbind_eq_none Option.pbind_eq_noneₓ'. -/
theorem pbind_eq_none {f : ∀ a : α, a ∈ x → Option β} (h' : ∀ a ∈ x, f a H = none → x = none) :
    x.pbind f = none ↔ x = none := by
  cases x
  · simp
  · simp only [pbind, iff_false_iff]
    intro h
    cases h' x rfl h
#align option.pbind_eq_none Option.pbind_eq_none

/- warning: option.pbind_eq_some -> Option.pbind_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {x : Option.{u1} α} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (Option.{u2} β)} {y : β}, Iff (Eq.{succ u2} (Option.{u2} β) (Option.pbind.{u1, u2} α β x f) (Option.some.{u2} β y)) (Exists.{succ u1} α (fun (z : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) z x) (fun (H : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) z x) => Eq.{succ u2} (Option.{u2} β) (f z H) (Option.some.{u2} β y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {x : Option.{u2} α} {f : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (Option.{u1} β)} {y : β}, Iff (Eq.{succ u1} (Option.{u1} β) (Option.pbind.{u2, u1} α β x f) (Option.some.{u1} β y)) (Exists.{succ u2} α (fun (z : α) => Exists.{0} (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) z x) (fun (H : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) z x) => Eq.{succ u1} (Option.{u1} β) (f z H) (Option.some.{u1} β y))))
Case conversion may be inaccurate. Consider using '#align option.pbind_eq_some Option.pbind_eq_someₓ'. -/
theorem pbind_eq_some {f : ∀ a : α, a ∈ x → Option β} {y : β} :
    x.pbind f = some y ↔ ∃ z ∈ x, f z H = some y :=
  by
  cases x
  · simp
  · simp only [pbind]
    constructor
    · intro h
      use x
      simpa only [mem_def, exists_prop_of_true] using h
    · rintro ⟨z, H, hz⟩
      simp only [mem_def] at H
      simpa only [H] using hz
#align option.pbind_eq_some Option.pbind_eq_some

/- warning: option.pmap_eq_none_iff -> Option.pmap_eq_none_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {x : Option.{u1} α} {h : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (p a)}, Iff (Eq.{succ u2} (Option.{u2} β) (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f x h) (Option.none.{u2} β)) (Eq.{succ u1} (Option.{u1} α) x (Option.none.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {x : Option.{u2} α} {h : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (p a)}, Iff (Eq.{succ u1} (Option.{u1} β) (Option.pmap.{u2, u1} α β (fun (a : α) => p a) f x h) (Option.none.{u1} β)) (Eq.{succ u2} (Option.{u2} α) x (Option.none.{u2} α))
Case conversion may be inaccurate. Consider using '#align option.pmap_eq_none_iff Option.pmap_eq_none_iffₓ'. -/
@[simp]
theorem pmap_eq_none_iff {h} : pmap f x h = none ↔ x = none := by cases x <;> simp
#align option.pmap_eq_none_iff Option.pmap_eq_none_iff

/- warning: option.pmap_eq_some_iff -> Option.pmap_eq_some_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {x : Option.{u1} α} {hf : forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a x) -> (p a)} {y : β}, Iff (Eq.{succ u2} (Option.{u2} β) (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f x hf) (Option.some.{u2} β y)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Eq.{succ u1} (Option.{u1} α) x (Option.some.{u1} α a)) (fun (H : Eq.{succ u1} (Option.{u1} α) x (Option.some.{u1} α a)) => Eq.{succ u2} β (f a (hf a H)) y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {x : Option.{u2} α} {hf : forall (a : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a x) -> (p a)} {y : β}, Iff (Eq.{succ u1} (Option.{u1} β) (Option.pmap.{u2, u1} α β (fun (a : α) => p a) f x hf) (Option.some.{u1} β y)) (Exists.{succ u2} α (fun (a : α) => Exists.{0} (Eq.{succ u2} (Option.{u2} α) x (Option.some.{u2} α a)) (fun (H : Eq.{succ u2} (Option.{u2} α) x (Option.some.{u2} α a)) => Eq.{succ u1} β (f a (hf a H)) y)))
Case conversion may be inaccurate. Consider using '#align option.pmap_eq_some_iff Option.pmap_eq_some_iffₓ'. -/
@[simp]
theorem pmap_eq_some_iff {hf} {y : β} :
    pmap f x hf = some y ↔ ∃ (a : α)(H : x = some a), f a (hf a H) = y :=
  by
  cases x
  · simp only [not_mem_none, exists_false, pmap, not_false_iff, exists_prop_of_false]
  · constructor
    · intro h
      simp only [pmap] at h
      exact ⟨x, rfl, h⟩
    · rintro ⟨a, H, rfl⟩
      simp only [mem_def] at H
      simp only [H, pmap]
#align option.pmap_eq_some_iff Option.pmap_eq_some_iff

/- warning: option.join_pmap_eq_pmap_join -> Option.join_pmap_eq_pmap_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {x : Option.{u1} (Option.{u1} α)} (H : forall (a : Option.{u1} α), (Membership.Mem.{u1, u1} (Option.{u1} α) (Option.{u1} (Option.{u1} α)) (Option.hasMem.{u1} (Option.{u1} α)) a x) -> (forall (a_1 : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a_1 a) -> (p a_1))), Eq.{succ u2} (Option.{u2} β) (Option.join.{u2} β (Option.pmap.{u1, u2} (Option.{u1} α) (Option.{u2} β) (fun (a : Option.{u1} α) => forall (a_1 : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a_1 a) -> (p a_1)) (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f) x H)) (Option.pmap.{u1, u2} α β (fun (a : α) => p a) f (Option.join.{u1} α x) (fun (a : α) (h : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a (Option.join.{u1} α x)) => H (Option.some.{u1} α a) (Option.mem_of_mem_join.{u1} α a x h) a (rfl.{succ u1} (Option.{u1} α) (Option.some.{u1} α a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {x : Option.{u2} (Option.{u2} α)} (H : forall (a : Option.{u2} α), (Membership.mem.{u2, u2} (Option.{u2} α) (Option.{u2} (Option.{u2} α)) (Option.instMembershipOption.{u2} (Option.{u2} α)) a x) -> (forall (a_1 : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a_1 a) -> (p a_1))), Eq.{succ u1} (Option.{u1} β) (Option.join.{u1} β (Option.pmap.{u2, u1} (Option.{u2} α) (Option.{u1} β) (fun (a : Option.{u2} α) => forall (a_1 : α), (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a_1 a) -> (p a_1)) (Option.pmap.{u2, u1} α β (fun (a : α) => p a) f) x H)) (Option.pmap.{u2, u1} α β (fun (a : α) => p a) f (Option.join.{u2} α x) (fun (a : α) (h : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a (Option.join.{u2} α x)) => H (Option.some.{u2} α a) (Option.mem_of_mem_join.{u2} α a x h) a (rfl.{succ u2} (Option.{u2} α) (Option.some.{u2} α a))))
Case conversion may be inaccurate. Consider using '#align option.join_pmap_eq_pmap_join Option.join_pmap_eq_pmap_joinₓ'. -/
@[simp]
theorem join_pmap_eq_pmap_join {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h => H (some a) (mem_of_mem_join h) _ rfl := by
  rcases x with (_ | _ | x) <;> simp
#align option.join_pmap_eq_pmap_join Option.join_pmap_eq_pmap_join

end Pmap

/- warning: option.seq_some -> Option.seq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {a : α} {f : α -> β}, Eq.{succ u1} (Option.{u1} β) (Seq.seq.{u1, u1} Option.{u1} (Applicative.toHasSeq.{u1, u1} Option.{u1} (Monad.toApplicative.{u1, u1} Option.{u1} Option.monad.{u1})) α β (Option.some.{u1} (α -> β) f) (Option.some.{u1} α a)) (Option.some.{u1} β (f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {a : α} {f : α -> β}, Eq.{succ u1} (Option.{u1} β) (Seq.seq.{u1, u1} Option.{u1} (Applicative.toSeq.{u1, u1} Option.{u1} (Alternative.toApplicative.{u1, u1} Option.{u1} instAlternativeOption.{u1})) α β (Option.some.{u1} (α -> β) f) (fun (x._@.Mathlib.Data.Option.Basic._hyg.2283 : Unit) => Option.some.{u1} α a)) (Option.some.{u1} β (f a))
Case conversion may be inaccurate. Consider using '#align option.seq_some Option.seq_someₓ'. -/
@[simp]
theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) :=
  rfl
#align option.seq_some Option.seq_some

#print Option.some_orElse' /-
@[simp]
theorem some_orElse' (a : α) (x : Option α) : (some a).orelse x = some a :=
  rfl
#align option.some_orelse' Option.some_orElse'
-/

/- warning: option.some_orelse -> Option.some_orElse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (HasOrelse.orelse.{u1, u1} Option.{u1} (Alternative.toHasOrelse.{u1, u1} Option.{u1} Option.alternative.{u1}) α (Option.some.{u1} α a) x) (Option.some.{u1} α a)
but is expected to have type
  forall {α : Type.{u1}} (a : α) (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (HOrElse.hOrElse.{u1, u1, u1} (Option.{u1} α) (Option.{u1} α) (Option.{u1} α) (instHOrElse.{u1} (Option.{u1} α) (Option.instOrElseOption.{u1} α)) (Option.some.{u1} α a) (fun (x._@.Std.Data.Option.Lemmas._hyg.3067 : Unit) => x)) (Option.some.{u1} α a)
Case conversion may be inaccurate. Consider using '#align option.some_orelse Option.some_orElseₓ'. -/
@[simp]
theorem some_orElse (a : α) (x : Option α) : (some a <|> x) = some a :=
  rfl
#align option.some_orelse Option.some_orElse

/- warning: option.none_orelse' -> Option.none_orElse' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (Option.orelse.{u1} α (Option.none.{u1} α) x) x
but is expected to have type
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (Option.orElse.{u1} α (Option.none.{u1} α) (fun (x._@.Mathlib.Data.Option.Basic._hyg.2340 : Unit) => x)) x
Case conversion may be inaccurate. Consider using '#align option.none_orelse' Option.none_orElse'ₓ'. -/
@[simp]
theorem none_orElse' (x : Option α) : none.orelse x = x := by cases x <;> rfl
#align option.none_orelse' Option.none_orElse'

/- warning: option.none_orelse -> Option.none_orElse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (HasOrelse.orelse.{u1, u1} Option.{u1} (Alternative.toHasOrelse.{u1, u1} Option.{u1} Option.alternative.{u1}) α (Option.none.{u1} α) x) x
but is expected to have type
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (HOrElse.hOrElse.{u1, u1, u1} (Option.{u1} α) (Option.{u1} α) (Option.{u1} α) (instHOrElse.{u1} (Option.{u1} α) (Option.instOrElseOption.{u1} α)) (Option.none.{u1} α) (fun (x._@.Std.Data.Option.Lemmas._hyg.3081 : Unit) => x)) x
Case conversion may be inaccurate. Consider using '#align option.none_orelse Option.none_orElseₓ'. -/
@[simp]
theorem none_orElse (x : Option α) : (none <|> x) = x :=
  none_orElse' x
#align option.none_orelse Option.none_orElse

#print Option.orElse_none' /-
@[simp]
theorem orElse_none' (x : Option α) : x.orelse none = x := by cases x <;> rfl
#align option.orelse_none' Option.orElse_none'
-/

/- warning: option.orelse_none -> Option.orElse_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (HasOrelse.orelse.{u1, u1} Option.{u1} (Alternative.toHasOrelse.{u1, u1} Option.{u1} Option.alternative.{u1}) α x (Option.none.{u1} α)) x
but is expected to have type
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (HOrElse.hOrElse.{u1, u1, u1} (Option.{u1} α) (Option.{u1} α) (Option.{u1} α) (instHOrElse.{u1} (Option.{u1} α) (Option.instOrElseOption.{u1} α)) x (fun (x._@.Std.Data.Option.Lemmas._hyg.3095 : Unit) => Option.none.{u1} α)) x
Case conversion may be inaccurate. Consider using '#align option.orelse_none Option.orElse_noneₓ'. -/
@[simp]
theorem orElse_none (x : Option α) : (x <|> none) = x :=
  orElse_none' x
#align option.orelse_none Option.orElse_none

#print Option.isSome_none /-
@[simp]
theorem isSome_none : @isSome α none = ff :=
  rfl
#align option.is_some_none Option.isSome_none
-/

#print Option.isSome_some /-
@[simp]
theorem isSome_some {a : α} : isSome (some a) = tt :=
  rfl
#align option.is_some_some Option.isSome_some
-/

#print Option.isSome_iff_exists /-
theorem isSome_iff_exists {x : Option α} : isSome x ↔ ∃ a, x = some a := by
  cases x <;> simp [is_some] <;> exact ⟨_, rfl⟩
#align option.is_some_iff_exists Option.isSome_iff_exists
-/

#print Option.isNone_none /-
@[simp]
theorem isNone_none : @isNone α none = tt :=
  rfl
#align option.is_none_none Option.isNone_none
-/

#print Option.isNone_some /-
@[simp]
theorem isNone_some {a : α} : isNone (some a) = ff :=
  rfl
#align option.is_none_some Option.isNone_some
-/

#print Option.not_isSome /-
@[simp]
theorem not_isSome {a : Option α} : isSome a = ff ↔ a.isNone = tt := by cases a <;> simp
#align option.not_is_some Option.not_isSome
-/

#print Option.eq_some_iff_get_eq /-
theorem eq_some_iff_get_eq {o : Option α} {a : α} : o = some a ↔ ∃ h : o.isSome, Option.get h = a :=
  by cases o <;> simp
#align option.eq_some_iff_get_eq Option.eq_some_iff_get_eq
-/

#print Option.not_isSome_iff_eq_none /-
theorem not_isSome_iff_eq_none {o : Option α} : ¬o.isSome ↔ o = none := by cases o <;> simp
#align option.not_is_some_iff_eq_none Option.not_isSome_iff_eq_none
-/

#print Option.ne_none_iff_isSome /-
theorem ne_none_iff_isSome {o : Option α} : o ≠ none ↔ o.isSome := by cases o <;> simp
#align option.ne_none_iff_is_some Option.ne_none_iff_isSome
-/

#print Option.ne_none_iff_exists /-
theorem ne_none_iff_exists {o : Option α} : o ≠ none ↔ ∃ x : α, some x = o := by cases o <;> simp
#align option.ne_none_iff_exists Option.ne_none_iff_exists
-/

#print Option.ne_none_iff_exists' /-
theorem ne_none_iff_exists' {o : Option α} : o ≠ none ↔ ∃ x : α, o = some x :=
  ne_none_iff_exists.trans <| exists_congr fun _ => eq_comm
#align option.ne_none_iff_exists' Option.ne_none_iff_exists'
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ≠ » none[option.none]) -/
#print Option.bex_ne_none /-
theorem bex_ne_none {p : Option α → Prop} : (∃ (x : _)(_ : x ≠ none), p x) ↔ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx, hp⟩ => ⟨get <| ne_none_iff_isSome.1 hx, by rwa [some_get]⟩, fun ⟨x, hx⟩ =>
    ⟨some x, some_ne_none x, hx⟩⟩
#align option.bex_ne_none Option.bex_ne_none
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ≠ » none[option.none]) -/
#print Option.ball_ne_none /-
theorem ball_ne_none {p : Option α → Prop} : (∀ (x) (_ : x ≠ none), p x) ↔ ∀ x, p (some x) :=
  ⟨fun h x => h (some x) (some_ne_none x), fun h x hx => by
    simpa only [some_get] using h (get <| ne_none_iff_is_some.1 hx)⟩
#align option.ball_ne_none Option.ball_ne_none
-/

#print Option.iget_mem /-
theorem iget_mem [Inhabited α] : ∀ {o : Option α}, isSome o → o.iget ∈ o
  | some a, _ => rfl
#align option.iget_mem Option.iget_mem
-/

#print Option.iget_of_mem /-
theorem iget_of_mem [Inhabited α] {a : α} : ∀ {o : Option α}, a ∈ o → o.iget = a
  | _, rfl => rfl
#align option.iget_of_mem Option.iget_of_mem
-/

#print Option.getD_default_eq_iget /-
theorem getD_default_eq_iget [Inhabited α] (o : Option α) : o.getOrElse default = o.iget := by
  cases o <;> rfl
#align option.get_or_else_default_eq_iget Option.getD_default_eq_iget
-/

/- warning: option.guard_eq_some -> Option.guard_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {a : α} {b : α}, Iff (Eq.{succ u1} (Option.{u1} α) (Option.guard.{u1} α p (fun (a : α) => _inst_1 a) a) (Option.some.{u1} α b)) (And (Eq.{succ u1} α a b) (p a))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {_inst_1 : α} {a : α} [b : DecidablePred.{succ u1} α p], Iff (Eq.{succ u1} (Option.{u1} α) (Option.guard.{u1} α p (fun (a : α) => b a) _inst_1) (Option.some.{u1} α a)) (And (Eq.{succ u1} α _inst_1 a) (p _inst_1))
Case conversion may be inaccurate. Consider using '#align option.guard_eq_some Option.guard_eq_someₓ'. -/
@[simp]
theorem guard_eq_some {p : α → Prop} [DecidablePred p] {a b : α} :
    guard p a = some b ↔ a = b ∧ p a := by
  by_cases p a <;> simp [Option.guard, h] <;> intro <;> contradiction
#align option.guard_eq_some Option.guard_eq_some

/- warning: option.guard_eq_some' -> Option.guard_eq_some' is a dubious translation:
lean 3 declaration is
  forall {p : Prop} [_inst_1 : Decidable p] (u : Unit), Iff (Eq.{1} (Option.{0} Unit) (guard.{0} Option.{0} Option.alternative.{0} p _inst_1) (Option.some.{0} Unit u)) p
but is expected to have type
  forall {p : Prop} [_inst_1 : Decidable p] (u : Unit), Iff (Eq.{1} (Option.{0} Unit) (guard.{0} Option.{0} instAlternativeOption.{0} p _inst_1) (Option.some.{0} Unit u)) p
Case conversion may be inaccurate. Consider using '#align option.guard_eq_some' Option.guard_eq_some'ₓ'. -/
@[simp]
theorem guard_eq_some' {p : Prop} [Decidable p] (u) : guard p = some u ↔ p :=
  by
  cases u
  by_cases p <;> simp [_root_.guard, h] <;> first |rfl|contradiction
#align option.guard_eq_some' Option.guard_eq_some'

#print Option.liftOrGet_choice /-
theorem liftOrGet_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, liftOrGet f o₁ o₂ = o₁ ∨ liftOrGet f o₁ o₂ = o₂
  | none, none => Or.inl rfl
  | some a, none => Or.inl rfl
  | none, some b => Or.inr rfl
  | some a, some b => by simpa [lift_or_get] using h a b
#align option.lift_or_get_choice Option.liftOrGet_choice
-/

#print Option.liftOrGet_none_left /-
@[simp]
theorem liftOrGet_none_left {f} {b : Option α} : liftOrGet f none b = b := by cases b <;> rfl
#align option.lift_or_get_none_left Option.liftOrGet_none_left
-/

#print Option.liftOrGet_none_right /-
@[simp]
theorem liftOrGet_none_right {f} {a : Option α} : liftOrGet f a none = a := by cases a <;> rfl
#align option.lift_or_get_none_right Option.liftOrGet_none_right
-/

#print Option.liftOrGet_some_some /-
@[simp]
theorem liftOrGet_some_some {f} {a b : α} : liftOrGet f (some a) (some b) = f a b :=
  rfl
#align option.lift_or_get_some_some Option.liftOrGet_some_some
-/

#print Option.casesOn' /-
/-- Given an element of `a : option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
def casesOn' : Option α → β → (α → β) → β
  | none, n, s => n
  | some a, n, s => s a
#align option.cases_on' Option.casesOn'
-/

@[simp]
theorem cases_on'_none (x : β) (f : α → β) : casesOn' none x f = x :=
  rfl
#align option.cases_on'_none Option.cases_on'_none

@[simp]
theorem cases_on'_some (x : β) (f : α → β) (a : α) : casesOn' (some a) x f = f a :=
  rfl
#align option.cases_on'_some Option.cases_on'_some

@[simp]
theorem cases_on'_coe (x : β) (f : α → β) (a : α) : casesOn' (a : Option α) x f = f a :=
  rfl
#align option.cases_on'_coe Option.cases_on'_coe

@[simp]
theorem cases_on'_none_coe (f : Option α → β) (o : Option α) :
    casesOn' o (f none) (f ∘ coe) = f o := by cases o <;> rfl
#align option.cases_on'_none_coe Option.cases_on'_none_coe

@[simp]
theorem get_or_else_map (f : α → β) (x : α) (o : Option α) : getD (o.map f) (f x) = f (getD o x) :=
  by cases o <;> rfl
#align option.get_or_else_map Option.get_or_else_map

theorem orelse_eq_some (o o' : Option α) (x : α) :
    (o <|> o') = some x ↔ o = some x ∨ o = none ∧ o' = some x :=
  by
  cases o
  · simp only [true_and_iff, false_or_iff, eq_self_iff_true, none_orelse]
  · simp only [some_orelse, or_false_iff, false_and_iff]
#align option.orelse_eq_some Option.orelse_eq_some

theorem orelse_eq_some' (o o' : Option α) (x : α) :
    o.orelse o' = some x ↔ o = some x ∨ o = none ∧ o' = some x :=
  Option.orelse_eq_some o o' x
#align option.orelse_eq_some' Option.orelse_eq_some'

@[simp]
theorem orelse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = none :=
  by
  cases o
  · simp only [true_and_iff, none_orelse, eq_self_iff_true]
  · simp only [some_orelse, false_and_iff]
#align option.orelse_eq_none Option.orelse_eq_none

@[simp]
theorem orelse_eq_none' (o o' : Option α) : o.orelse o' = none ↔ o = none ∧ o' = none :=
  Option.orelse_eq_none o o'
#align option.orelse_eq_none' Option.orelse_eq_none'

section

open Classical

#print Option.choice /-
/-- An arbitrary `some a` with `a : α` if `α` is nonempty, and otherwise `none`. -/
noncomputable def choice (α : Type _) : Option α :=
  if h : Nonempty α then some h.some else none
#align option.choice Option.choice
-/

#print Option.choice_eq /-
theorem choice_eq {α : Type _} [Subsingleton α] (a : α) : choice α = some a :=
  by
  dsimp [choice]
  rw [dif_pos (⟨a⟩ : Nonempty α)]
  congr
#align option.choice_eq Option.choice_eq
-/

#print Option.choice_eq_none /-
theorem choice_eq_none (α : Type _) [IsEmpty α] : choice α = none :=
  dif_neg (not_nonempty_iff_imp_false.mpr isEmptyElim)
#align option.choice_eq_none Option.choice_eq_none
-/

#print Option.choice_isSome_iff_nonempty /-
theorem choice_isSome_iff_nonempty {α : Type _} : (choice α).isSome ↔ Nonempty α :=
  by
  fconstructor
  · intro h
    exact ⟨Option.get h⟩
  · intro h
    dsimp only [choice]
    rw [dif_pos h]
    exact is_some_some
#align option.choice_is_some_iff_nonempty Option.choice_isSome_iff_nonempty
-/

end

#print Option.to_list_some /-
@[simp]
theorem to_list_some (a : α) : (a : Option α).toList = [a] :=
  rfl
#align option.to_list_some Option.to_list_some
-/

#print Option.to_list_none /-
@[simp]
theorem to_list_none (α : Type _) : (none : Option α).toList = [] :=
  rfl
#align option.to_list_none Option.to_list_none
-/

/- warning: option.elim_none_some -> Option.elim_none_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : (Option.{u1} α) -> β), Eq.{max (succ u1) (succ u2)} ((Option.{u1} α) -> β) (Option.elim'.{u1, u2} α β (f (Option.none.{u1} α)) (Function.comp.{succ u1, succ u1, succ u2} α (Option.{u1} α) β f (Option.some.{u1} α))) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : (Option.{u2} α) -> β), Eq.{max (succ u2) (succ u1)} ((Option.{u2} α) -> β) (fun (x : Option.{u2} α) => Option.elim.{u2, succ u1} α β x (f (Option.none.{u2} α)) (Function.comp.{succ u2, succ u2, succ u1} α (Option.{u2} α) β f (Option.some.{u2} α))) f
Case conversion may be inaccurate. Consider using '#align option.elim_none_some Option.elim_none_someₓ'. -/
@[simp]
theorem elim_none_some (f : Option α → β) : Option.elim' (f none) (f ∘ some) = f :=
  funext fun o => by cases o <;> rfl
#align option.elim_none_some Option.elim_none_some

end Option

