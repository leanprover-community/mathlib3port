/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.option.n_ary
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Option.Basic

/-!
# Binary map of options

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the binary map of `option`. This is mostly useful to define pointwise operations
on intervals.

## Main declarations

* `option.map₂`: Binary map of options.

## Notes

This file is very similar to `data.set.n_ary`, `data.finset.n_ary` and `order.filter.n_ary`. Please
keep them in sync.

We do not define `option.map₃` as its only purpose so far would be to prove properties of
`option.map₂` and casing already fulfills this task.
-/


open Function

namespace Option

variable {α α' β β' γ γ' δ δ' ε ε' : Type _} {f : α → β → γ} {a : Option α} {b : Option β}
  {c : Option γ}

#print Option.map₂ /-
/-- The image of a binary function `f : α → β → γ` as a function `option α → option β → option γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ (f : α → β → γ) (a : Option α) (b : Option β) : Option γ :=
  a.bind fun a => b.map <| f a
#align option.map₂ Option.map₂
-/

/- warning: option.map₂_def -> Option.map₂_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (f : α -> β -> γ) (a : Option.{u1} α) (b : Option.{u1} β), Eq.{succ u1} (Option.{u1} γ) (Option.map₂.{u1, u1, u1} α β γ f a b) (Seq.seq.{u1, u1} Option.{u1} (Applicative.toHasSeq.{u1, u1} Option.{u1} (Monad.toApplicative.{u1, u1} Option.{u1} Option.monad.{u1})) β γ (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α (β -> γ) f a) b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (f : α -> β -> γ) (a : Option.{u1} α) (b : Option.{u1} β), Eq.{succ u1} (Option.{u1} γ) (Option.map₂.{u1, u1, u1} α β γ f a b) (Seq.seq.{u1, u1} Option.{u1} (Applicative.toSeq.{u1, u1} Option.{u1} (Alternative.toApplicative.{u1, u1} Option.{u1} instAlternativeOption.{u1})) β γ (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α (β -> γ) f a) (fun (x._@.Mathlib.Data.Option.NAry._hyg.142 : Unit) => b))
Case conversion may be inaccurate. Consider using '#align option.map₂_def Option.map₂_defₓ'. -/
/-- `option.map₂` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem map₂_def {α β γ : Type _} (f : α → β → γ) (a : Option α) (b : Option β) :
    map₂ f a b = f <$> a <*> b := by cases a <;> rfl
#align option.map₂_def Option.map₂_def

/- warning: option.map₂_some_some -> Option.map₂_some_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (a : α) (b : β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f (Option.some.{u1} α a) (Option.some.{u2} β b)) (Option.some.{u3} γ (f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (f : α -> β -> γ) (a : α) (b : β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u2, u1, u3} α β γ f (Option.some.{u2} α a) (Option.some.{u1} β b)) (Option.some.{u3} γ (f a b))
Case conversion may be inaccurate. Consider using '#align option.map₂_some_some Option.map₂_some_someₓ'. -/
@[simp]
theorem map₂_some_some (f : α → β → γ) (a : α) (b : β) : map₂ f (some a) (some b) = some (f a b) :=
  rfl
#align option.map₂_some_some Option.map₂_some_some

/- warning: option.map₂_coe_coe -> Option.map₂_coe_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (a : α) (b : β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) β (Option.{u2} β) (HasLiftT.mk.{succ u2, succ u2} β (Option.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} β (Option.{u2} β) (coeOption.{u2} β))) b)) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) γ (Option.{u3} γ) (HasLiftT.mk.{succ u3, succ u3} γ (Option.{u3} γ) (CoeTCₓ.coe.{succ u3, succ u3} γ (Option.{u3} γ) (coeOption.{u3} γ))) (f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (f : α -> β -> γ) (a : α) (b : β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u2, u1, u3} α β γ f (Option.some.{u2} α a) (Option.some.{u1} β b)) (Option.some.{u3} γ (f a b))
Case conversion may be inaccurate. Consider using '#align option.map₂_coe_coe Option.map₂_coe_coeₓ'. -/
theorem map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b :=
  rfl
#align option.map₂_coe_coe Option.map₂_coe_coe

/- warning: option.map₂_none_left -> Option.map₂_none_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (b : Option.{u2} β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f (Option.none.{u1} α) b) (Option.none.{u3} γ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : α -> β -> γ) (b : Option.{u3} β), Eq.{succ u2} (Option.{u2} γ) (Option.map₂.{u1, u3, u2} α β γ f (Option.none.{u1} α) b) (Option.none.{u2} γ)
Case conversion may be inaccurate. Consider using '#align option.map₂_none_left Option.map₂_none_leftₓ'. -/
@[simp]
theorem map₂_none_left (f : α → β → γ) (b : Option β) : map₂ f none b = none :=
  rfl
#align option.map₂_none_left Option.map₂_none_left

/- warning: option.map₂_none_right -> Option.map₂_none_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (a : Option.{u1} α), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f a (Option.none.{u2} β)) (Option.none.{u3} γ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (f : α -> β -> γ) (a : Option.{u3} α), Eq.{succ u2} (Option.{u2} γ) (Option.map₂.{u3, u1, u2} α β γ f a (Option.none.{u1} β)) (Option.none.{u2} γ)
Case conversion may be inaccurate. Consider using '#align option.map₂_none_right Option.map₂_none_rightₓ'. -/
@[simp]
theorem map₂_none_right (f : α → β → γ) (a : Option α) : map₂ f a none = none := by cases a <;> rfl
#align option.map₂_none_right Option.map₂_none_right

/- warning: option.map₂_coe_left -> Option.map₂_coe_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (a : α) (b : Option.{u2} β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a) b) (Option.map.{u2, u3} β γ (fun (b : β) => f a b) b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : α -> β -> γ) (a : α) (b : Option.{u3} β), Eq.{succ u2} (Option.{u2} γ) (Option.map₂.{u1, u3, u2} α β γ f (Option.some.{u1} α a) b) (Option.map.{u3, u2} β γ (fun (b : β) => f a b) b)
Case conversion may be inaccurate. Consider using '#align option.map₂_coe_left Option.map₂_coe_leftₓ'. -/
@[simp]
theorem map₂_coe_left (f : α → β → γ) (a : α) (b : Option β) : map₂ f a b = b.map fun b => f a b :=
  rfl
#align option.map₂_coe_left Option.map₂_coe_left

/- warning: option.map₂_coe_right -> Option.map₂_coe_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (a : Option.{u1} α) (b : β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f a ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) β (Option.{u2} β) (HasLiftT.mk.{succ u2, succ u2} β (Option.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} β (Option.{u2} β) (coeOption.{u2} β))) b)) (Option.map.{u1, u3} α γ (fun (a : α) => f a b) a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (f : α -> β -> γ) (a : Option.{u3} α) (b : β), Eq.{succ u2} (Option.{u2} γ) (Option.map₂.{u3, u1, u2} α β γ f a (Option.some.{u1} β b)) (Option.map.{u3, u2} α γ (fun (a : α) => f a b) a)
Case conversion may be inaccurate. Consider using '#align option.map₂_coe_right Option.map₂_coe_rightₓ'. -/
@[simp]
theorem map₂_coe_right (f : α → β → γ) (a : Option α) (b : β) : map₂ f a b = a.map fun a => f a b :=
  rfl
#align option.map₂_coe_right Option.map₂_coe_right

/- warning: option.mem_map₂_iff -> Option.mem_map₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u2} β} {c : γ}, Iff (Membership.Mem.{u3, u3} γ (Option.{u3} γ) (Option.hasMem.{u3} γ) c (Option.map₂.{u1, u2, u3} α β γ f a b)) (Exists.{succ u1} α (fun (a' : α) => Exists.{succ u2} β (fun (b' : β) => And (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a' a) (And (Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b' b) (Eq.{succ u3} γ (f a' b') c)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {a : Option.{u2} α} {b : Option.{u1} β} {c : γ}, Iff (Membership.mem.{u3, u3} γ (Option.{u3} γ) (Option.instMembershipOption.{u3} γ) c (Option.map₂.{u2, u1, u3} α β γ f a b)) (Exists.{succ u2} α (fun (a' : α) => Exists.{succ u1} β (fun (b' : β) => And (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) a' a) (And (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b' b) (Eq.{succ u3} γ (f a' b') c)))))
Case conversion may be inaccurate. Consider using '#align option.mem_map₂_iff Option.mem_map₂_iffₓ'. -/
@[simp]
theorem mem_map₂_iff {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  simp [map₂]
#align option.mem_map₂_iff Option.mem_map₂_iff

/- warning: option.map₂_eq_none_iff -> Option.map₂_eq_none_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u2} β}, Iff (Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f a b) (Option.none.{u3} γ)) (Or (Eq.{succ u1} (Option.{u1} α) a (Option.none.{u1} α)) (Eq.{succ u2} (Option.{u2} β) b (Option.none.{u2} β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {a : Option.{u2} α} {b : Option.{u1} β}, Iff (Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u2, u1, u3} α β γ f a b) (Option.none.{u3} γ)) (Or (Eq.{succ u2} (Option.{u2} α) a (Option.none.{u2} α)) (Eq.{succ u1} (Option.{u1} β) b (Option.none.{u1} β)))
Case conversion may be inaccurate. Consider using '#align option.map₂_eq_none_iff Option.map₂_eq_none_iffₓ'. -/
@[simp]
theorem map₂_eq_none_iff : map₂ f a b = none ↔ a = none ∨ b = none := by
  cases a <;> cases b <;> simp
#align option.map₂_eq_none_iff Option.map₂_eq_none_iff

/- warning: option.map₂_swap -> Option.map₂_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (a : Option.{u1} α) (b : Option.{u2} β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f a b) (Option.map₂.{u2, u1, u3} β α γ (fun (a : β) (b : α) => f b a) b a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (a : Option.{u3} α) (b : Option.{u2} β), Eq.{succ u1} (Option.{u1} γ) (Option.map₂.{u3, u2, u1} α β γ f a b) (Option.map₂.{u2, u3, u1} β α γ (fun (a : β) (b : α) => f b a) b a)
Case conversion may be inaccurate. Consider using '#align option.map₂_swap Option.map₂_swapₓ'. -/
theorem map₂_swap (f : α → β → γ) (a : Option α) (b : Option β) :
    map₂ f a b = map₂ (fun a b => f b a) b a := by cases a <;> cases b <;> rfl
#align option.map₂_swap Option.map₂_swap

/- warning: option.map_map₂ -> Option.map_map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {a : Option.{u1} α} {b : Option.{u2} β} (f : α -> β -> γ) (g : γ -> δ), Eq.{succ u4} (Option.{u4} δ) (Option.map.{u3, u4} γ δ g (Option.map₂.{u1, u2, u3} α β γ f a b)) (Option.map₂.{u1, u2, u4} α β δ (fun (a : α) (b : β) => g (f a b)) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Option.{u2} α} {a : Option.{u1} β} {b : Type.{u4}} (f : α -> β -> γ) (g : γ -> b), Eq.{succ u4} (Option.{u4} b) (Option.map.{u3, u4} γ b g (Option.map₂.{u2, u1, u3} α β γ f δ a)) (Option.map₂.{u2, u1, u4} α β b (fun (a : α) (b : β) => g (f a b)) δ a)
Case conversion may be inaccurate. Consider using '#align option.map_map₂ Option.map_map₂ₓ'. -/
theorem map_map₂ (f : α → β → γ) (g : γ → δ) :
    (map₂ f a b).map g = map₂ (fun a b => g (f a b)) a b := by cases a <;> cases b <;> rfl
#align option.map_map₂ Option.map_map₂

/- warning: option.map₂_map_left -> Option.map₂_map_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {a : Option.{u1} α} {b : Option.{u2} β} (f : γ -> β -> δ) (g : α -> γ), Eq.{succ u4} (Option.{u4} δ) (Option.map₂.{u3, u2, u4} γ β δ f (Option.map.{u1, u3} α γ g a) b) (Option.map₂.{u1, u2, u4} α β δ (fun (a : α) (b : β) => f (g a) b) a b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Option.{u1} α} {a : Option.{u2} β} {b : Type.{u4}} (f : γ -> β -> b) (g : α -> γ), Eq.{succ u4} (Option.{u4} b) (Option.map₂.{u3, u2, u4} γ β b f (Option.map.{u1, u3} α γ g δ) a) (Option.map₂.{u1, u2, u4} α β b (fun (a : α) (b : β) => f (g a) b) δ a)
Case conversion may be inaccurate. Consider using '#align option.map₂_map_left Option.map₂_map_leftₓ'. -/
theorem map₂_map_left (f : γ → β → δ) (g : α → γ) :
    map₂ f (a.map g) b = map₂ (fun a b => f (g a) b) a b := by cases a <;> rfl
#align option.map₂_map_left Option.map₂_map_left

/- warning: option.map₂_map_right -> Option.map₂_map_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {a : Option.{u1} α} {b : Option.{u2} β} (f : α -> γ -> δ) (g : β -> γ), Eq.{succ u4} (Option.{u4} δ) (Option.map₂.{u1, u3, u4} α γ δ f a (Option.map.{u2, u3} β γ g b)) (Option.map₂.{u1, u2, u4} α β δ (fun (a : α) (b : β) => f a (g b)) a b)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {δ : Option.{u3} α} {a : Option.{u1} β} {b : Type.{u4}} (f : α -> γ -> b) (g : β -> γ), Eq.{succ u4} (Option.{u4} b) (Option.map₂.{u3, u2, u4} α γ b f δ (Option.map.{u1, u2} β γ g a)) (Option.map₂.{u3, u1, u4} α β b (fun (a : α) (b : β) => f a (g b)) δ a)
Case conversion may be inaccurate. Consider using '#align option.map₂_map_right Option.map₂_map_rightₓ'. -/
theorem map₂_map_right (f : α → γ → δ) (g : β → γ) :
    map₂ f a (b.map g) = map₂ (fun a b => f a (g b)) a b := by cases b <;> rfl
#align option.map₂_map_right Option.map₂_map_right

/- warning: option.map₂_curry -> Option.map₂_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : (Prod.{u1, u2} α β) -> γ) (a : Option.{u1} α) (b : Option.{u2} β), Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ (Function.curry.{u1, u2, u3} α β γ f) a b) (Option.map.{max u1 u2, u3} (Prod.{u1, u2} α β) γ f (Option.map₂.{u1, u2, max u1 u2} α β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β) a b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : (Prod.{u3, u2} α β) -> γ) (a : Option.{u3} α) (b : Option.{u2} β), Eq.{succ u1} (Option.{u1} γ) (Option.map₂.{u3, u2, u1} α β γ (Function.curry.{u3, u2, u1} α β γ f) a b) (Option.map.{max u3 u2, u1} (Prod.{u3, u2} α β) γ f (Option.map₂.{u3, u2, max u3 u2} α β (Prod.{u3, u2} α β) (Prod.mk.{u3, u2} α β) a b))
Case conversion may be inaccurate. Consider using '#align option.map₂_curry Option.map₂_curryₓ'. -/
@[simp]
theorem map₂_curry (f : α × β → γ) (a : Option α) (b : Option β) :
    map₂ (curry f) a b = Option.map f (map₂ Prod.mk a b) :=
  (map_map₂ _ _).symm
#align option.map₂_curry Option.map₂_curry

/- warning: option.map_uncurry -> Option.map_uncurry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (x : Option.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u3} (Option.{u3} γ) (Option.map.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Function.uncurry.{u1, u2, u3} α β γ f) x) (Option.map₂.{u1, u2, u3} α β γ f (Option.map.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) x) (Option.map.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} (f : α -> β -> γ) (x : Option.{max u3 u2} (Prod.{u2, u3} α β)), Eq.{succ u1} (Option.{u1} γ) (Option.map.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (Function.uncurry.{u2, u3, u1} α β γ f) x) (Option.map₂.{u2, u3, u1} α β γ f (Option.map.{max u3 u2, u2} (Prod.{u2, u3} α β) α (Prod.fst.{u2, u3} α β) x) (Option.map.{max u3 u2, u3} (Prod.{u2, u3} α β) β (Prod.snd.{u2, u3} α β) x))
Case conversion may be inaccurate. Consider using '#align option.map_uncurry Option.map_uncurryₓ'. -/
@[simp]
theorem map_uncurry (f : α → β → γ) (x : Option (α × β)) :
    x.map (uncurry f) = map₂ f (x.map Prod.fst) (x.map Prod.snd) := by cases x <;> rfl
#align option.map_uncurry Option.map_uncurry

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `option.map₂` of those operations.
The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) a b = map₂ (*) g f` in a `comm_semigroup`.
-/


/- warning: option.map₂_assoc -> Option.map₂_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {ε' : Type.{u6}} {a : Option.{u1} α} {b : Option.{u2} β} {c : Option.{u3} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (f (g a b) c) (f' a (g' b c))) -> (Eq.{succ u5} (Option.{u5} ε) (Option.map₂.{u4, u3, u5} δ γ ε f (Option.map₂.{u1, u2, u4} α β δ g a b) c) (Option.map₂.{u1, u6, u5} α ε' ε f' a (Option.map₂.{u2, u3, u6} β γ ε' g' b c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Option.{u2} α} {ε : Option.{u1} β} {ε' : Option.{u3} γ} {a : Type.{u6}} {b : Type.{u5}} {c : Type.{u4}} {f : a -> γ -> b} {g : α -> β -> a} {f' : α -> c -> b} {g' : β -> γ -> c}, (forall (a : α) (b_1 : β) (c : γ), Eq.{succ u5} b (f (g a b_1) c) (f' a (g' b_1 c))) -> (Eq.{succ u5} (Option.{u5} b) (Option.map₂.{u6, u3, u5} a γ b f (Option.map₂.{u2, u1, u6} α β a g δ ε) ε') (Option.map₂.{u2, u4, u5} α c b f' δ (Option.map₂.{u1, u3, u4} β γ c g' ε ε')))
Case conversion may be inaccurate. Consider using '#align option.map₂_assoc Option.map₂_assocₓ'. -/
theorem map₂_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    map₂ f (map₂ g a b) c = map₂ f' a (map₂ g' b c) := by
  cases a <;> cases b <;> cases c <;> simp [h_assoc]
#align option.map₂_assoc Option.map₂_assoc

/- warning: option.map₂_comm -> Option.map₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u2} β} {g : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (g b a)) -> (Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u1, u2, u3} α β γ f a b) (Option.map₂.{u2, u1, u3} β α γ g b a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {a : Option.{u2} α} {b : Option.{u1} β} {g : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (g b a)) -> (Eq.{succ u3} (Option.{u3} γ) (Option.map₂.{u2, u1, u3} α β γ f a b) (Option.map₂.{u1, u2, u3} β α γ g b a))
Case conversion may be inaccurate. Consider using '#align option.map₂_comm Option.map₂_commₓ'. -/
theorem map₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : map₂ f a b = map₂ g b a := by
  cases a <;> cases b <;> simp [h_comm]
#align option.map₂_comm Option.map₂_comm

/- warning: option.map₂_left_comm -> Option.map₂_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {δ' : Type.{u5}} {ε : Type.{u6}} {a : Option.{u1} α} {b : Option.{u2} β} {c : Option.{u3} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f a (g b c)) (g' b (f' a c))) -> (Eq.{succ u6} (Option.{u6} ε) (Option.map₂.{u1, u4, u6} α δ ε f a (Option.map₂.{u2, u3, u4} β γ δ g b c)) (Option.map₂.{u2, u5, u6} β δ' ε g' b (Option.map₂.{u1, u3, u5} α γ δ' f' a c)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Option.{u3} α} {δ' : Option.{u2} β} {ε : Option.{u1} γ} {a : Type.{u6}} {b : Type.{u5}} {c : Type.{u4}} {f : α -> a -> b} {g : β -> γ -> a} {f' : α -> γ -> c} {g' : β -> c -> b}, (forall (a : α) (b_1 : β) (c : γ), Eq.{succ u5} b (f a (g b_1 c)) (g' b_1 (f' a c))) -> (Eq.{succ u5} (Option.{u5} b) (Option.map₂.{u3, u6, u5} α a b f δ (Option.map₂.{u2, u1, u6} β γ a g δ' ε)) (Option.map₂.{u2, u4, u5} β c b g' δ' (Option.map₂.{u3, u1, u4} α γ c f' δ ε)))
Case conversion may be inaccurate. Consider using '#align option.map₂_left_comm Option.map₂_left_commₓ'. -/
theorem map₂_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    map₂ f a (map₂ g b c) = map₂ g' b (map₂ f' a c) := by
  cases a <;> cases b <;> cases c <;> simp [h_left_comm]
#align option.map₂_left_comm Option.map₂_left_comm

/- warning: option.map₂_right_comm -> Option.map₂_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {δ' : Type.{u5}} {ε : Type.{u6}} {a : Option.{u1} α} {b : Option.{u2} β} {c : Option.{u3} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f (g a b) c) (g' (f' a c) b)) -> (Eq.{succ u6} (Option.{u6} ε) (Option.map₂.{u4, u3, u6} δ γ ε f (Option.map₂.{u1, u2, u4} α β δ g a b) c) (Option.map₂.{u5, u2, u6} δ' β ε g' (Option.map₂.{u1, u3, u5} α γ δ' f' a c) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Option.{u2} α} {δ' : Option.{u1} β} {ε : Option.{u3} γ} {a : Type.{u6}} {b : Type.{u5}} {c : Type.{u4}} {f : a -> γ -> b} {g : α -> β -> a} {f' : α -> γ -> c} {g' : c -> β -> b}, (forall (a : α) (b_1 : β) (c : γ), Eq.{succ u5} b (f (g a b_1) c) (g' (f' a c) b_1)) -> (Eq.{succ u5} (Option.{u5} b) (Option.map₂.{u6, u3, u5} a γ b f (Option.map₂.{u2, u1, u6} α β a g δ δ') ε) (Option.map₂.{u4, u1, u5} c β b g' (Option.map₂.{u2, u3, u4} α γ c f' δ ε) δ'))
Case conversion may be inaccurate. Consider using '#align option.map₂_right_comm Option.map₂_right_commₓ'. -/
theorem map₂_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    map₂ f (map₂ g a b) c = map₂ g' (map₂ f' a c) b := by
  cases a <;> cases b <;> cases c <;> simp [h_right_comm]
#align option.map₂_right_comm Option.map₂_right_comm

/- warning: option.map_map₂_distrib -> Option.map_map₂_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u3} β} {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ a) (g₂ b))) -> (Eq.{succ u6} (Option.{u6} δ) (Option.map.{u5, u6} γ δ g (Option.map₂.{u1, u3, u5} α β γ f a b)) (Option.map₂.{u2, u4, u6} α' β' δ f' (Option.map.{u1, u2} α α' g₁ a) (Option.map.{u3, u4} β β' g₂ b)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u1}} {β : Type.{u3}} {β' : α -> α' -> β} {γ : Option.{u2} α} {δ : Option.{u1} α'} {f : Type.{u6}} {a : Type.{u5}} {b : Type.{u4}} {g : β -> f} {f' : a -> b -> f} {g₁ : α -> a} {g₂ : α' -> b}, (forall (a : α) (b : α'), Eq.{succ u6} f (g (β' a b)) (f' (g₁ a) (g₂ b))) -> (Eq.{succ u6} (Option.{u6} f) (Option.map.{u3, u6} β f g (Option.map₂.{u2, u1, u3} α α' β β' γ δ)) (Option.map₂.{u5, u4, u6} a b f f' (Option.map.{u2, u5} α a g₁ γ) (Option.map.{u1, u4} α' b g₂ δ)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_distrib Option.map_map₂_distribₓ'. -/
theorem map_map₂_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (map₂ f a b).map g = map₂ f' (a.map g₁) (b.map g₂) := by
  cases a <;> cases b <;> simp [h_distrib]
#align option.map_map₂_distrib Option.map_map₂_distrib

/-!
The following symmetric restatement are needed because unification has a hard time figuring all the
functions if you symmetrize on the spot. This is also how the other n-ary APIs do it.
-/


/- warning: option.map_map₂_distrib_left -> Option.map_map₂_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u3} β} {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' a) b)) -> (Eq.{succ u5} (Option.{u5} δ) (Option.map.{u4, u5} γ δ g (Option.map₂.{u1, u3, u4} α β γ f a b)) (Option.map₂.{u2, u3, u5} α' β δ f' (Option.map.{u1, u2} α α' g' a) b))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u1}} {β : Type.{u3}} {γ : α -> α' -> β} {δ : Option.{u2} α} {f : Option.{u1} α'} {a : Type.{u5}} {b : Type.{u4}} {g : β -> a} {f' : b -> α' -> a} {g' : α -> b}, (forall (a_1 : α) (b : α'), Eq.{succ u5} a (g (γ a_1 b)) (f' (g' a_1) b)) -> (Eq.{succ u5} (Option.{u5} a) (Option.map.{u3, u5} β a g (Option.map₂.{u2, u1, u3} α α' β γ δ f)) (Option.map₂.{u4, u1, u5} b α' a f' (Option.map.{u2, u4} α b g' δ) f))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_distrib_left Option.map_map₂_distrib_leftₓ'. -/
/-- Symmetric statement to `option.map₂_map_left_comm`. -/
theorem map_map₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) : (map₂ f a b).map g = map₂ f' (a.map g') b := by
  cases a <;> cases b <;> simp [h_distrib]
#align option.map_map₂_distrib_left Option.map_map₂_distrib_left

/- warning: option.map_map₂_distrib_right -> Option.map_map₂_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u2} β} {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' a (g' b))) -> (Eq.{succ u5} (Option.{u5} δ) (Option.map.{u4, u5} γ δ g (Option.map₂.{u1, u2, u4} α β γ f a b)) (Option.map₂.{u1, u3, u5} α β' δ f' a (Option.map.{u2, u3} β β' g' b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {β' : Type.{u3}} {γ : α -> β -> β'} {δ : Option.{u2} α} {f : Option.{u1} β} {a : Type.{u5}} {b : Type.{u4}} {g : β' -> a} {f' : α -> b -> a} {g' : β -> b}, (forall (a_1 : α) (b : β), Eq.{succ u5} a (g (γ a_1 b)) (f' a_1 (g' b))) -> (Eq.{succ u5} (Option.{u5} a) (Option.map.{u3, u5} β' a g (Option.map₂.{u2, u1, u3} α β β' γ δ f)) (Option.map₂.{u2, u4, u5} α b a f' δ (Option.map.{u1, u4} β b g' f)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_distrib_right Option.map_map₂_distrib_rightₓ'. -/
/-- Symmetric statement to `option.map_map₂_right_comm`. -/
theorem map_map₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) : (map₂ f a b).map g = map₂ f' a (b.map g') := by
  cases a <;> cases b <;> simp [h_distrib]
#align option.map_map₂_distrib_right Option.map_map₂_distrib_right

/- warning: option.map₂_map_left_comm -> Option.map₂_map_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {a : Option.{u1} α} {b : Option.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f (g a) b) (g' (f' a b))) -> (Eq.{succ u4} (Option.{u4} γ) (Option.map₂.{u2, u3, u4} α' β γ f (Option.map.{u1, u2} α α' g a) b) (Option.map.{u5, u4} δ γ g' (Option.map₂.{u1, u3, u5} α β δ f' a b)))
but is expected to have type
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Option.{u1} α} {δ : Option.{u2} α'} {a : Type.{u5}} {b : Type.{u4}} {f : a -> α' -> β} {g : α -> a} {f' : α -> α' -> b} {g' : b -> β}, (forall (a : α) (b : α'), Eq.{succ u3} β (f (g a) b) (g' (f' a b))) -> (Eq.{succ u3} (Option.{u3} β) (Option.map₂.{u5, u2, u3} a α' β f (Option.map.{u1, u5} α a g γ) δ) (Option.map.{u4, u3} b β g' (Option.map₂.{u1, u2, u4} α α' b f' γ δ)))
Case conversion may be inaccurate. Consider using '#align option.map₂_map_left_comm Option.map₂_map_left_commₓ'. -/
/-- Symmetric statement to `option.map_map₂_distrib_left`. -/
theorem map₂_map_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) : map₂ f (a.map g) b = (map₂ f' a b).map g' := by
  cases a <;> cases b <;> simp [h_left_comm]
#align option.map₂_map_left_comm Option.map₂_map_left_comm

/- warning: option.map_map₂_right_comm -> Option.map_map₂_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {a : Option.{u1} α} {b : Option.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f a (g b)) (g' (f' a b))) -> (Eq.{succ u4} (Option.{u4} γ) (Option.map₂.{u1, u3, u4} α β' γ f a (Option.map.{u2, u3} β β' g b)) (Option.map.{u5, u4} δ γ g' (Option.map₂.{u1, u2, u5} α β δ f' a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {β' : Type.{u3}} {γ : Option.{u2} α} {δ : Option.{u1} β} {a : Type.{u5}} {b : Type.{u4}} {f : α -> a -> β'} {g : β -> a} {f' : α -> β -> b} {g' : b -> β'}, (forall (a : α) (b : β), Eq.{succ u3} β' (f a (g b)) (g' (f' a b))) -> (Eq.{succ u3} (Option.{u3} β') (Option.map₂.{u2, u5, u3} α a β' f γ (Option.map.{u1, u5} β a g δ)) (Option.map.{u4, u3} b β' g' (Option.map₂.{u2, u1, u4} α β b f' γ δ)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_right_comm Option.map_map₂_right_commₓ'. -/
/-- Symmetric statement to `option.map_map₂_distrib_right`. -/
theorem map_map₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) : map₂ f a (b.map g) = (map₂ f' a b).map g' :=
  by cases a <;> cases b <;> simp [h_right_comm]
#align option.map_map₂_right_comm Option.map_map₂_right_comm

/- warning: option.map_map₂_antidistrib -> Option.map_map₂_antidistrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u3} β} {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ b) (g₂ a))) -> (Eq.{succ u6} (Option.{u6} δ) (Option.map.{u5, u6} γ δ g (Option.map₂.{u1, u3, u5} α β γ f a b)) (Option.map₂.{u4, u2, u6} β' α' δ f' (Option.map.{u3, u4} β β' g₁ b) (Option.map.{u1, u2} α α' g₂ a)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u1}} {β : Type.{u3}} {β' : α -> α' -> β} {γ : Option.{u2} α} {δ : Option.{u1} α'} {f : Type.{u6}} {a : Type.{u5}} {b : Type.{u4}} {g : β -> f} {f' : a -> b -> f} {g₁ : α' -> a} {g₂ : α -> b}, (forall (a : α) (b : α'), Eq.{succ u6} f (g (β' a b)) (f' (g₁ b) (g₂ a))) -> (Eq.{succ u6} (Option.{u6} f) (Option.map.{u3, u6} β f g (Option.map₂.{u2, u1, u3} α α' β β' γ δ)) (Option.map₂.{u5, u4, u6} a b f f' (Option.map.{u1, u5} α' a g₁ δ) (Option.map.{u2, u4} α b g₂ γ)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_antidistrib Option.map_map₂_antidistribₓ'. -/
theorem map_map₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (map₂ f a b).map g = map₂ f' (b.map g₁) (a.map g₂) := by
  cases a <;> cases b <;> simp [h_antidistrib]
#align option.map_map₂_antidistrib Option.map_map₂_antidistrib

/- warning: option.map_map₂_antidistrib_left -> Option.map_map₂_antidistrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u2} β} {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' b) a)) -> (Eq.{succ u5} (Option.{u5} δ) (Option.map.{u4, u5} γ δ g (Option.map₂.{u1, u2, u4} α β γ f a b)) (Option.map₂.{u3, u1, u5} β' α δ f' (Option.map.{u2, u3} β β' g' b) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {β' : Type.{u3}} {γ : α -> β -> β'} {δ : Option.{u2} α} {f : Option.{u1} β} {a : Type.{u5}} {b : Type.{u4}} {g : β' -> a} {f' : b -> α -> a} {g' : β -> b}, (forall (a_1 : α) (b : β), Eq.{succ u5} a (g (γ a_1 b)) (f' (g' b) a_1)) -> (Eq.{succ u5} (Option.{u5} a) (Option.map.{u3, u5} β' a g (Option.map₂.{u2, u1, u3} α β β' γ δ f)) (Option.map₂.{u4, u2, u5} b α a f' (Option.map.{u1, u4} β b g' f) δ))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_antidistrib_left Option.map_map₂_antidistrib_leftₓ'. -/
/-- Symmetric statement to `option.map₂_map_left_anticomm`. -/
theorem map_map₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) : (map₂ f a b).map g = map₂ f' (b.map g') a :=
  by cases a <;> cases b <;> simp [h_antidistrib]
#align option.map_map₂_antidistrib_left Option.map_map₂_antidistrib_left

/- warning: option.map_map₂_antidistrib_right -> Option.map_map₂_antidistrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {a : Option.{u1} α} {b : Option.{u3} β} {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' b (g' a))) -> (Eq.{succ u5} (Option.{u5} δ) (Option.map.{u4, u5} γ δ g (Option.map₂.{u1, u3, u4} α β γ f a b)) (Option.map₂.{u3, u2, u5} β α' δ f' b (Option.map.{u1, u2} α α' g' a)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u1}} {β : Type.{u3}} {γ : α -> α' -> β} {δ : Option.{u2} α} {f : Option.{u1} α'} {a : Type.{u5}} {b : Type.{u4}} {g : β -> a} {f' : α' -> b -> a} {g' : α -> b}, (forall (a_1 : α) (b : α'), Eq.{succ u5} a (g (γ a_1 b)) (f' b (g' a_1))) -> (Eq.{succ u5} (Option.{u5} a) (Option.map.{u3, u5} β a g (Option.map₂.{u2, u1, u3} α α' β γ δ f)) (Option.map₂.{u1, u4, u5} α' b a f' f (Option.map.{u2, u4} α b g' δ)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_antidistrib_right Option.map_map₂_antidistrib_rightₓ'. -/
/-- Symmetric statement to `option.map_map₂_right_anticomm`. -/
theorem map_map₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) : (map₂ f a b).map g = map₂ f' b (a.map g') :=
  by cases a <;> cases b <;> simp [h_antidistrib]
#align option.map_map₂_antidistrib_right Option.map_map₂_antidistrib_right

/- warning: option.map₂_map_left_anticomm -> Option.map₂_map_left_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {a : Option.{u1} α} {b : Option.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f (g a) b) (g' (f' b a))) -> (Eq.{succ u4} (Option.{u4} γ) (Option.map₂.{u2, u3, u4} α' β γ f (Option.map.{u1, u2} α α' g a) b) (Option.map.{u5, u4} δ γ g' (Option.map₂.{u3, u1, u5} β α δ f' b a)))
but is expected to have type
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Option.{u1} α} {δ : Option.{u2} α'} {a : Type.{u5}} {b : Type.{u4}} {f : a -> α' -> β} {g : α -> a} {f' : α' -> α -> b} {g' : b -> β}, (forall (a : α) (b : α'), Eq.{succ u3} β (f (g a) b) (g' (f' b a))) -> (Eq.{succ u3} (Option.{u3} β) (Option.map₂.{u5, u2, u3} a α' β f (Option.map.{u1, u5} α a g γ) δ) (Option.map.{u4, u3} b β g' (Option.map₂.{u2, u1, u4} α' α b f' δ γ)))
Case conversion may be inaccurate. Consider using '#align option.map₂_map_left_anticomm Option.map₂_map_left_anticommₓ'. -/
/-- Symmetric statement to `option.map_map₂_antidistrib_left`. -/
theorem map₂_map_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    map₂ f (a.map g) b = (map₂ f' b a).map g' := by cases a <;> cases b <;> simp [h_left_anticomm]
#align option.map₂_map_left_anticomm Option.map₂_map_left_anticomm

/- warning: option.map_map₂_right_anticomm -> Option.map_map₂_right_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {a : Option.{u1} α} {b : Option.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f a (g b)) (g' (f' b a))) -> (Eq.{succ u4} (Option.{u4} γ) (Option.map₂.{u1, u3, u4} α β' γ f a (Option.map.{u2, u3} β β' g b)) (Option.map.{u5, u4} δ γ g' (Option.map₂.{u2, u1, u5} β α δ f' b a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {β' : Type.{u3}} {γ : Option.{u2} α} {δ : Option.{u1} β} {a : Type.{u5}} {b : Type.{u4}} {f : α -> a -> β'} {g : β -> a} {f' : β -> α -> b} {g' : b -> β'}, (forall (a : α) (b : β), Eq.{succ u3} β' (f a (g b)) (g' (f' b a))) -> (Eq.{succ u3} (Option.{u3} β') (Option.map₂.{u2, u5, u3} α a β' f γ (Option.map.{u1, u5} β a g δ)) (Option.map.{u4, u3} b β' g' (Option.map₂.{u1, u2, u4} β α b f' δ γ)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_right_anticomm Option.map_map₂_right_anticommₓ'. -/
/-- Symmetric statement to `option.map_map₂_antidistrib_right`. -/
theorem map_map₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    map₂ f a (b.map g) = (map₂ f' b a).map g' := by cases a <;> cases b <;> simp [h_right_anticomm]
#align option.map_map₂_right_anticomm Option.map_map₂_right_anticomm

#print Option.map₂_left_identity /-
/-- If `a` is a left identity for a binary operation `f`, then `some a` is a left identity for
`option.map₂ f`. -/
theorem map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (o : Option β) :
    map₂ f (some a) o = o := by
  cases o
  exacts[rfl, congr_arg some (h _)]
#align option.map₂_left_identity Option.map₂_left_identity
-/

/- warning: option.map₂_right_identity -> Option.map₂_right_identity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β -> α} {b : β}, (forall (a : α), Eq.{succ u1} α (f a b) a) -> (forall (o : Option.{u1} α), Eq.{succ u1} (Option.{u1} α) (Option.map₂.{u1, u2, u1} α β α f o (Option.some.{u2} β b)) o)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β -> α} {b : β}, (forall (a : α), Eq.{succ u2} α (f a b) a) -> (forall (o : Option.{u2} α), Eq.{succ u2} (Option.{u2} α) (Option.map₂.{u2, u1, u2} α β α f o (Option.some.{u1} β b)) o)
Case conversion may be inaccurate. Consider using '#align option.map₂_right_identity Option.map₂_right_identityₓ'. -/
/-- If `b` is a right identity for a binary operation `f`, then `some b` is a right identity for
`option.map₂ f`. -/
theorem map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (o : Option α) :
    map₂ f o (some b) = o := by simp [h, map₂]
#align option.map₂_right_identity Option.map₂_right_identity

end Option

