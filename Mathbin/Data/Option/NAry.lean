/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Option.Basic

/-!
# Binary map of options

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/656
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the binary map of `option`. This is mostly useful to define pointwise operations
on intervals.

## Main declarations

* `option.map₂`: Binary map of options.

## Notes

This file is very similar to the n-ary section of `data.set.basic`, to `data.finset.n_ary` and to
`order.filter.n_ary`. Please keep them in sync.

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
  forall {α : Type.{u_1}} {β : Type.{u_1}} {γ : Type.{u_1}} (f : α -> β -> γ) (a : Option.{u_1} α) (b : Option.{u_1} β), Eq.{succ u_1} (Option.{u_1} γ) (Option.map₂.{u_1, u_1, u_1} α β γ f a b) (Seq.seq.{u_1, u_1} Option.{u_1} (Applicative.toHasSeq.{u_1, u_1} Option.{u_1} (Monad.toApplicative.{u_1, u_1} Option.{u_1} Option.monad.{u_1})) β γ (Functor.map.{u_1, u_1} Option.{u_1} (Traversable.toFunctor.{u_1} Option.{u_1} Option.traversable.{u_1}) α (β -> γ) f a) b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_1}} {γ : Type.{u_1}} (f : α -> β -> γ) (a : Option.{u_1} α) (b : Option.{u_1} β), Eq.{succ u_1} (Option.{u_1} γ) (Option.map₂.{u_1, u_1, u_1} α β γ f a b) (Seq.seq.{u_1, u_1} Option.{u_1} (Applicative.toSeq.{u_1, u_1} Option.{u_1} (Alternative.toApplicative.{u_1, u_1} Option.{u_1} instAlternativeOption.{u_1})) β γ (Functor.map.{u_1, u_1} Option.{u_1} instFunctorOption.{u_1} α (β -> γ) f a) (fun (x._@.Mathlib.Data.Option.NAry._hyg.144 : Unit) => b))
Case conversion may be inaccurate. Consider using '#align option.map₂_def Option.map₂_defₓ'. -/
/-- `option.map₂` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem map₂_def {α β γ : Type _} (f : α → β → γ) (a : Option α) (b : Option β) :
    map₂ f a b = f <$> a <*> b := by cases a <;> rfl
#align option.map₂_def Option.map₂_def

/- warning: option.map₂_some_some -> Option.map₂_some_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : α -> β -> γ) (a : α) (b : β), Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f (Option.some.{u_1} α a) (Option.some.{u_3} β b)) ((fun (a : Type.{u_5}) (b : Type.{u_5}) [self : HasLiftT.{succ u_5, succ u_5} a b] => self.0) γ (Option.{u_5} γ) (HasLiftT.mk.{succ u_5, succ u_5} γ (Option.{u_5} γ) (CoeTCₓ.coe.{succ u_5, succ u_5} γ (Option.{u_5} γ) (coeOption.{u_5} γ))) (f a b))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_1}} (f : α -> β -> γ) (a : α) (b : β), Eq.{succ u_1} (Option.{u_1} γ) (Option.map₂.{u_2, u_3, u_1} α β γ f (Option.some.{u_2} α a) (Option.some.{u_3} β b)) (Option.some.{u_1} γ (f a b))
Case conversion may be inaccurate. Consider using '#align option.map₂_some_some Option.map₂_some_someₓ'. -/
@[simp]
theorem map₂_some_some (f : α → β → γ) (a : α) (b : β) : map₂ f (some a) (some b) = f a b :=
  rfl
#align option.map₂_some_some Option.map₂_some_some

/- warning: option.map₂_coe_coe -> Option.map₂_coe_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : α -> β -> γ) (a : α) (b : β), Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (Option.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (Option.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (Option.{u_1} α) (coeOption.{u_1} α))) a) ((fun (a : Type.{u_3}) (b : Type.{u_3}) [self : HasLiftT.{succ u_3, succ u_3} a b] => self.0) β (Option.{u_3} β) (HasLiftT.mk.{succ u_3, succ u_3} β (Option.{u_3} β) (CoeTCₓ.coe.{succ u_3, succ u_3} β (Option.{u_3} β) (coeOption.{u_3} β))) b)) ((fun (a : Type.{u_5}) (b : Type.{u_5}) [self : HasLiftT.{succ u_5, succ u_5} a b] => self.0) γ (Option.{u_5} γ) (HasLiftT.mk.{succ u_5, succ u_5} γ (Option.{u_5} γ) (CoeTCₓ.coe.{succ u_5, succ u_5} γ (Option.{u_5} γ) (coeOption.{u_5} γ))) (f a b))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_1}} (f : α -> β -> γ) (a : α) (b : β), Eq.{succ u_1} (Option.{u_1} γ) (Option.map₂.{u_2, u_3, u_1} α β γ f (Option.some.{u_2} α a) (Option.some.{u_3} β b)) (Option.some.{u_1} γ (f a b))
Case conversion may be inaccurate. Consider using '#align option.map₂_coe_coe Option.map₂_coe_coeₓ'. -/
theorem map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b :=
  rfl
#align option.map₂_coe_coe Option.map₂_coe_coe

/- warning: option.map₂_none_left -> Option.map₂_none_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : α -> β -> γ) (b : Option.{u_3} β), Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f (Option.none.{u_1} α) b) (Option.none.{u_5} γ)
but is expected to have type
  forall {α : Type.{u_3}} {β : Type.{u_1}} {γ : Type.{u_2}} (f : α -> β -> γ) (b : Option.{u_1} β), Eq.{succ u_2} (Option.{u_2} γ) (Option.map₂.{u_3, u_1, u_2} α β γ f (Option.none.{u_3} α) b) (Option.none.{u_2} γ)
Case conversion may be inaccurate. Consider using '#align option.map₂_none_left Option.map₂_none_leftₓ'. -/
@[simp]
theorem map₂_none_left (f : α → β → γ) (b : Option β) : map₂ f none b = none :=
  rfl
#align option.map₂_none_left Option.map₂_none_left

/- warning: option.map₂_none_right -> Option.map₂_none_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : α -> β -> γ) (a : Option.{u_1} α), Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f a (Option.none.{u_3} β)) (Option.none.{u_5} γ)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_2}} (f : α -> β -> γ) (a : Option.{u_1} α), Eq.{succ u_2} (Option.{u_2} γ) (Option.map₂.{u_1, u_3, u_2} α β γ f a (Option.none.{u_3} β)) (Option.none.{u_2} γ)
Case conversion may be inaccurate. Consider using '#align option.map₂_none_right Option.map₂_none_rightₓ'. -/
@[simp]
theorem map₂_none_right (f : α → β → γ) (a : Option α) : map₂ f a none = none := by cases a <;> rfl
#align option.map₂_none_right Option.map₂_none_right

/- warning: option.map₂_coe_left -> Option.map₂_coe_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : α -> β -> γ) (a : α) (b : Option.{u_3} β), Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (Option.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (Option.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (Option.{u_1} α) (coeOption.{u_1} α))) a) b) (Option.map.{u_3, u_5} β γ (fun (b : β) => f a b) b)
but is expected to have type
  forall {α : Type.{u_3}} {β : Type.{u_1}} {γ : Type.{u_2}} (f : α -> β -> γ) (a : α) (b : Option.{u_1} β), Eq.{succ u_2} (Option.{u_2} γ) (Option.map₂.{u_3, u_1, u_2} α β γ f (Option.some.{u_3} α a) b) (Option.map.{u_1, u_2} β γ (fun (b : β) => f a b) b)
Case conversion may be inaccurate. Consider using '#align option.map₂_coe_left Option.map₂_coe_leftₓ'. -/
@[simp]
theorem map₂_coe_left (f : α → β → γ) (a : α) (b : Option β) : map₂ f a b = b.map fun b => f a b :=
  rfl
#align option.map₂_coe_left Option.map₂_coe_left

/- warning: option.map₂_coe_right -> Option.map₂_coe_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : α -> β -> γ) (a : Option.{u_1} α) (b : β), Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f a ((fun (a : Type.{u_3}) (b : Type.{u_3}) [self : HasLiftT.{succ u_3, succ u_3} a b] => self.0) β (Option.{u_3} β) (HasLiftT.mk.{succ u_3, succ u_3} β (Option.{u_3} β) (CoeTCₓ.coe.{succ u_3, succ u_3} β (Option.{u_3} β) (coeOption.{u_3} β))) b)) (Option.map.{u_1, u_5} α γ (fun (a : α) => f a b) a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_2}} (f : α -> β -> γ) (a : Option.{u_1} α) (b : β), Eq.{succ u_2} (Option.{u_2} γ) (Option.map₂.{u_1, u_3, u_2} α β γ f a (Option.some.{u_3} β b)) (Option.map.{u_1, u_2} α γ (fun (a : α) => f a b) a)
Case conversion may be inaccurate. Consider using '#align option.map₂_coe_right Option.map₂_coe_rightₓ'. -/
@[simp]
theorem map₂_coe_right (f : α → β → γ) (a : Option α) (b : β) : map₂ f a b = a.map fun a => f a b :=
  rfl
#align option.map₂_coe_right Option.map₂_coe_right

/- warning: option.mem_map₂_iff -> Option.mem_map₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β} {c : γ}, Iff (Membership.Mem.{u_5, u_5} γ (Option.{u_5} γ) (Option.hasMem.{u_5} γ) c (Option.map₂.{u_1, u_3, u_5} α β γ f a b)) (Exists.{succ u_1} α (fun (a' : α) => Exists.{succ u_3} β (fun (b' : β) => And (Membership.Mem.{u_1, u_1} α (Option.{u_1} α) (Option.hasMem.{u_1} α) a' a) (And (Membership.Mem.{u_3, u_3} β (Option.{u_3} β) (Option.hasMem.{u_3} β) b' b) (Eq.{succ u_5} γ (f a' b') c)))))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_1}} {f : α -> β -> γ} {a : Option.{u_2} α} {b : Option.{u_3} β} {c : γ}, Iff (Membership.mem.{u_1, u_1} γ (Option.{u_1} γ) (Option.instMembershipOption.{u_1} γ) c (Option.map₂.{u_2, u_3, u_1} α β γ f a b)) (Exists.{succ u_2} α (fun (a' : α) => Exists.{succ u_3} β (fun (b' : β) => And (Membership.mem.{u_2, u_2} α (Option.{u_2} α) (Option.instMembershipOption.{u_2} α) a' a) (And (Membership.mem.{u_3, u_3} β (Option.{u_3} β) (Option.instMembershipOption.{u_3} β) b' b) (Eq.{succ u_1} γ (f a' b') c)))))
Case conversion may be inaccurate. Consider using '#align option.mem_map₂_iff Option.mem_map₂_iffₓ'. -/
@[simp]
theorem mem_map₂_iff {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  simp [map₂]
#align option.mem_map₂_iff Option.mem_map₂_iff

/- warning: option.map₂_eq_none_iff -> Option.map₂_eq_none_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β}, Iff (Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f a b) (Option.none.{u_5} γ)) (Or (Eq.{succ u_1} (Option.{u_1} α) a (Option.none.{u_1} α)) (Eq.{succ u_3} (Option.{u_3} β) b (Option.none.{u_3} β)))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_1}} {f : α -> β -> γ} {a : Option.{u_2} α} {b : Option.{u_3} β}, Iff (Eq.{succ u_1} (Option.{u_1} γ) (Option.map₂.{u_2, u_3, u_1} α β γ f a b) (Option.none.{u_1} γ)) (Or (Eq.{succ u_2} (Option.{u_2} α) a (Option.none.{u_2} α)) (Eq.{succ u_3} (Option.{u_3} β) b (Option.none.{u_3} β)))
Case conversion may be inaccurate. Consider using '#align option.map₂_eq_none_iff Option.map₂_eq_none_iffₓ'. -/
@[simp]
theorem map₂_eq_none_iff : map₂ f a b = none ↔ a = none ∨ b = none := by
  cases a <;> cases b <;> simp
#align option.map₂_eq_none_iff Option.map₂_eq_none_iff

/- warning: option.map₂_swap -> Option.map₂_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : α -> β -> γ) (a : Option.{u_1} α) (b : Option.{u_3} β), Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f a b) (Option.map₂.{u_3, u_1, u_5} β α γ (fun (a : β) (b : α) => f b a) b a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (f : α -> β -> γ) (a : Option.{u_1} α) (b : Option.{u_2} β), Eq.{succ u_3} (Option.{u_3} γ) (Option.map₂.{u_1, u_2, u_3} α β γ f a b) (Option.map₂.{u_2, u_1, u_3} β α γ (fun (a : β) (b : α) => f b a) b a)
Case conversion may be inaccurate. Consider using '#align option.map₂_swap Option.map₂_swapₓ'. -/
theorem map₂_swap (f : α → β → γ) (a : Option α) (b : Option β) :
    map₂ f a b = map₂ (fun a b => f b a) b a := by cases a <;> cases b <;> rfl
#align option.map₂_swap Option.map₂_swap

/- warning: option.map_map₂ -> Option.map_map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {a : Option.{u_1} α} {b : Option.{u_3} β} (f : α -> β -> γ) (g : γ -> δ), Eq.{succ u_7} (Option.{u_7} δ) (Option.map.{u_5, u_7} γ δ g (Option.map₂.{u_1, u_3, u_5} α β γ f a b)) (Option.map₂.{u_1, u_3, u_7} α β δ (fun (a : α) (b : β) => g (f a b)) a b)
but is expected to have type
  forall {α : Type.{u_3}} {β : Type.{u_4}} {γ : Type.{u_2}} {a : Option.{u_3} α} {b : Option.{u_4} β} {δ : Type.{u_1}} (f : α -> β -> γ) (g : γ -> δ), Eq.{succ u_1} (Option.{u_1} δ) (Option.map.{u_2, u_1} γ δ g (Option.map₂.{u_3, u_4, u_2} α β γ f a b)) (Option.map₂.{u_3, u_4, u_1} α β δ (fun (a : α) (b : β) => g (f a b)) a b)
Case conversion may be inaccurate. Consider using '#align option.map_map₂ Option.map_map₂ₓ'. -/
theorem map_map₂ (f : α → β → γ) (g : γ → δ) :
    (map₂ f a b).map g = map₂ (fun a b => g (f a b)) a b := by cases a <;> cases b <;> rfl
#align option.map_map₂ Option.map_map₂

/- warning: option.map₂_map_left -> Option.map₂_map_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {a : Option.{u_1} α} {b : Option.{u_3} β} (f : γ -> β -> δ) (g : α -> γ), Eq.{succ u_7} (Option.{u_7} δ) (Option.map₂.{u_5, u_3, u_7} γ β δ f (Option.map.{u_1, u_5} α γ g a) b) (Option.map₂.{u_1, u_3, u_7} α β δ (fun (a : α) (b : β) => f (g a) b) a b)
but is expected to have type
  forall {α : Type.{u_4}} {β : Type.{u_3}} {γ : Type.{u_2}} {a : Option.{u_4} α} {b : Option.{u_3} β} {δ : Type.{u_1}} (f : γ -> β -> δ) (g : α -> γ), Eq.{succ u_1} (Option.{u_1} δ) (Option.map₂.{u_2, u_3, u_1} γ β δ f (Option.map.{u_4, u_2} α γ g a) b) (Option.map₂.{u_4, u_3, u_1} α β δ (fun (a : α) (b : β) => f (g a) b) a b)
Case conversion may be inaccurate. Consider using '#align option.map₂_map_left Option.map₂_map_leftₓ'. -/
theorem map₂_map_left (f : γ → β → δ) (g : α → γ) :
    map₂ f (a.map g) b = map₂ (fun a b => f (g a) b) a b := by cases a <;> rfl
#align option.map₂_map_left Option.map₂_map_left

/- warning: option.map₂_map_right -> Option.map₂_map_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {a : Option.{u_1} α} {b : Option.{u_3} β} (f : α -> γ -> δ) (g : β -> γ), Eq.{succ u_7} (Option.{u_7} δ) (Option.map₂.{u_1, u_5, u_7} α γ δ f a (Option.map.{u_3, u_5} β γ g b)) (Option.map₂.{u_1, u_3, u_7} α β δ (fun (a : α) (b : β) => f a (g b)) a b)
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_4}} {γ : Type.{u_3}} {a : Option.{u_2} α} {b : Option.{u_4} β} {δ : Type.{u_1}} (f : α -> γ -> δ) (g : β -> γ), Eq.{succ u_1} (Option.{u_1} δ) (Option.map₂.{u_2, u_3, u_1} α γ δ f a (Option.map.{u_4, u_3} β γ g b)) (Option.map₂.{u_2, u_4, u_1} α β δ (fun (a : α) (b : β) => f a (g b)) a b)
Case conversion may be inaccurate. Consider using '#align option.map₂_map_right Option.map₂_map_rightₓ'. -/
theorem map₂_map_right (f : α → γ → δ) (g : β → γ) :
    map₂ f a (b.map g) = map₂ (fun a b => f a (g b)) a b := by cases b <;> rfl
#align option.map₂_map_right Option.map₂_map_right

/- warning: option.map₂_curry -> Option.map₂_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : (Prod.{u_1, u_3} α β) -> γ) (a : Option.{u_1} α) (b : Option.{u_3} β), Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ (Function.curry.{u_1, u_3, u_5} α β γ f) a b) (Option.map.{max u_1 u_3, u_5} (Prod.{u_1, u_3} α β) γ f (Option.map₂.{u_1, u_3, max u_1 u_3} α β (Prod.{u_1, u_3} α β) (Prod.mk.{u_1, u_3} α β) a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (f : (Prod.{u_1, u_2} α β) -> γ) (a : Option.{u_1} α) (b : Option.{u_2} β), Eq.{succ u_3} (Option.{u_3} γ) (Option.map₂.{u_1, u_2, u_3} α β γ (Function.curry.{u_1, u_2, u_3} α β γ f) a b) (Option.map.{max u_1 u_2, u_3} (Prod.{u_1, u_2} α β) γ f (Option.map₂.{u_1, u_2, max u_1 u_2} α β (Prod.{u_1, u_2} α β) (Prod.mk.{u_1, u_2} α β) a b))
Case conversion may be inaccurate. Consider using '#align option.map₂_curry Option.map₂_curryₓ'. -/
@[simp]
theorem map₂_curry (f : α × β → γ) (a : Option α) (b : Option β) :
    map₂ (curry f) a b = Option.map f (map₂ Prod.mk a b) :=
  (map_map₂ _ _).symm
#align option.map₂_curry Option.map₂_curry

/- warning: option.map_uncurry -> Option.map_uncurry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} (f : α -> β -> γ) (x : Option.{max u_1 u_3} (Prod.{u_1, u_3} α β)), Eq.{succ u_5} (Option.{u_5} γ) (Option.map.{max u_1 u_3, u_5} (Prod.{u_1, u_3} α β) γ (Function.uncurry.{u_1, u_3, u_5} α β γ f) x) (Option.map₂.{u_1, u_3, u_5} α β γ f (Option.map.{max u_1 u_3, u_1} (Prod.{u_1, u_3} α β) α (Prod.fst.{u_1, u_3} α β) x) (Option.map.{max u_1 u_3, u_3} (Prod.{u_1, u_3} α β) β (Prod.snd.{u_1, u_3} α β) x))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_1}} {γ : Type.{u_3}} (f : α -> β -> γ) (x : Option.{max u_1 u_2} (Prod.{u_2, u_1} α β)), Eq.{succ u_3} (Option.{u_3} γ) (Option.map.{max u_1 u_2, u_3} (Prod.{u_2, u_1} α β) γ (Function.uncurry.{u_2, u_1, u_3} α β γ f) x) (Option.map₂.{u_2, u_1, u_3} α β γ f (Option.map.{max u_1 u_2, u_2} (Prod.{u_2, u_1} α β) α (Prod.fst.{u_2, u_1} α β) x) (Option.map.{max u_1 u_2, u_1} (Prod.{u_2, u_1} α β) β (Prod.snd.{u_2, u_1} α β) x))
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
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {ε : Type.{u_9}} {ε' : Type.{u_10}} {a : Option.{u_1} α} {b : Option.{u_3} β} {c : Option.{u_5} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}, (forall (a : α) (b : β) (c : γ), Eq.{succ u_9} ε (f (g a b) c) (f' a (g' b c))) -> (Eq.{succ u_9} (Option.{u_9} ε) (Option.map₂.{u_7, u_5, u_9} δ γ ε f (Option.map₂.{u_1, u_3, u_7} α β δ g a b) c) (Option.map₂.{u_1, u_10, u_9} α ε' ε f' a (Option.map₂.{u_3, u_5, u_10} β γ ε' g' b c)))
but is expected to have type
  forall {α : Type.{u_5}} {β : Type.{u_6}} {γ : Type.{u_4}} {a : Option.{u_5} α} {b : Option.{u_6} β} {c : Option.{u_4} γ} {δ : Type.{u_1}} {ε : Type.{u_2}} {ε' : Type.{u_3}} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}, (forall (a : α) (b : β) (c : γ), Eq.{succ u_2} ε (f (g a b) c) (f' a (g' b c))) -> (Eq.{succ u_2} (Option.{u_2} ε) (Option.map₂.{u_1, u_4, u_2} δ γ ε f (Option.map₂.{u_5, u_6, u_1} α β δ g a b) c) (Option.map₂.{u_5, u_3, u_2} α ε' ε f' a (Option.map₂.{u_6, u_4, u_3} β γ ε' g' b c)))
Case conversion may be inaccurate. Consider using '#align option.map₂_assoc Option.map₂_assocₓ'. -/
theorem map₂_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    map₂ f (map₂ g a b) c = map₂ f' a (map₂ g' b c) := by
  cases a <;> cases b <;> cases c <;> simp [h_assoc]
#align option.map₂_assoc Option.map₂_assoc

/- warning: option.map₂_comm -> Option.map₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β} {g : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u_5} γ (f a b) (g b a)) -> (Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_3, u_5} α β γ f a b) (Option.map₂.{u_3, u_1, u_5} β α γ g b a))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_1}} {f : α -> β -> γ} {a : Option.{u_2} α} {b : Option.{u_3} β} {g : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u_1} γ (f a b) (g b a)) -> (Eq.{succ u_1} (Option.{u_1} γ) (Option.map₂.{u_2, u_3, u_1} α β γ f a b) (Option.map₂.{u_3, u_2, u_1} β α γ g b a))
Case conversion may be inaccurate. Consider using '#align option.map₂_comm Option.map₂_commₓ'. -/
theorem map₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : map₂ f a b = map₂ g b a := by
  cases a <;> cases b <;> simp [h_comm]
#align option.map₂_comm Option.map₂_comm

/- warning: option.map₂_left_comm -> Option.map₂_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {δ' : Type.{u_8}} {ε : Type.{u_9}} {a : Option.{u_1} α} {b : Option.{u_3} β} {c : Option.{u_5} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u_9} ε (f a (g b c)) (g' b (f' a c))) -> (Eq.{succ u_9} (Option.{u_9} ε) (Option.map₂.{u_1, u_7, u_9} α δ ε f a (Option.map₂.{u_3, u_5, u_7} β γ δ g b c)) (Option.map₂.{u_3, u_8, u_9} β δ' ε g' b (Option.map₂.{u_1, u_5, u_8} α γ δ' f' a c)))
but is expected to have type
  forall {α : Type.{u_4}} {β : Type.{u_5}} {γ : Type.{u_6}} {a : Option.{u_4} α} {b : Option.{u_5} β} {c : Option.{u_6} γ} {δ : Type.{u_1}} {ε : Type.{u_2}} {δ' : Type.{u_3}} {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u_2} ε (f a (g b c)) (g' b (f' a c))) -> (Eq.{succ u_2} (Option.{u_2} ε) (Option.map₂.{u_4, u_1, u_2} α δ ε f a (Option.map₂.{u_5, u_6, u_1} β γ δ g b c)) (Option.map₂.{u_5, u_3, u_2} β δ' ε g' b (Option.map₂.{u_4, u_6, u_3} α γ δ' f' a c)))
Case conversion may be inaccurate. Consider using '#align option.map₂_left_comm Option.map₂_left_commₓ'. -/
theorem map₂_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    map₂ f a (map₂ g b c) = map₂ g' b (map₂ f' a c) := by
  cases a <;> cases b <;> cases c <;> simp [h_left_comm]
#align option.map₂_left_comm Option.map₂_left_comm

/- warning: option.map₂_right_comm -> Option.map₂_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {δ' : Type.{u_8}} {ε : Type.{u_9}} {a : Option.{u_1} α} {b : Option.{u_3} β} {c : Option.{u_5} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u_9} ε (f (g a b) c) (g' (f' a c) b)) -> (Eq.{succ u_9} (Option.{u_9} ε) (Option.map₂.{u_7, u_5, u_9} δ γ ε f (Option.map₂.{u_1, u_3, u_7} α β δ g a b) c) (Option.map₂.{u_8, u_3, u_9} δ' β ε g' (Option.map₂.{u_1, u_5, u_8} α γ δ' f' a c) b))
but is expected to have type
  forall {α : Type.{u_5}} {β : Type.{u_6}} {γ : Type.{u_4}} {a : Option.{u_5} α} {b : Option.{u_6} β} {c : Option.{u_4} γ} {δ : Type.{u_1}} {ε : Type.{u_2}} {δ' : Type.{u_3}} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u_2} ε (f (g a b) c) (g' (f' a c) b)) -> (Eq.{succ u_2} (Option.{u_2} ε) (Option.map₂.{u_1, u_4, u_2} δ γ ε f (Option.map₂.{u_5, u_6, u_1} α β δ g a b) c) (Option.map₂.{u_3, u_6, u_2} δ' β ε g' (Option.map₂.{u_5, u_4, u_3} α γ δ' f' a c) b))
Case conversion may be inaccurate. Consider using '#align option.map₂_right_comm Option.map₂_right_commₓ'. -/
theorem map₂_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    map₂ f (map₂ g a b) c = map₂ g' (map₂ f' a c) b := by
  cases a <;> cases b <;> cases c <;> simp [h_right_comm]
#align option.map₂_right_comm Option.map₂_right_comm

/- warning: option.map_map₂_distrib -> Option.map_map₂_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {α' : Type.{u_2}} {β : Type.{u_3}} {β' : Type.{u_4}} {γ : Type.{u_5}} {δ : Type.{u_7}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β} {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u_7} δ (g (f a b)) (f' (g₁ a) (g₂ b))) -> (Eq.{succ u_7} (Option.{u_7} δ) (Option.map.{u_5, u_7} γ δ g (Option.map₂.{u_1, u_3, u_5} α β γ f a b)) (Option.map₂.{u_2, u_4, u_7} α' β' δ f' (Option.map.{u_1, u_2} α α' g₁ a) (Option.map.{u_3, u_4} β β' g₂ b)))
but is expected to have type
  forall {α : Type.{u_5}} {β : Type.{u_6}} {γ : Type.{u_4}} {f : α -> β -> γ} {a : Option.{u_5} α} {b : Option.{u_6} β} {δ : Type.{u_1}} {α' : Type.{u_2}} {β' : Type.{u_3}} {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u_1} δ (g (f a b)) (f' (g₁ a) (g₂ b))) -> (Eq.{succ u_1} (Option.{u_1} δ) (Option.map.{u_4, u_1} γ δ g (Option.map₂.{u_5, u_6, u_4} α β γ f a b)) (Option.map₂.{u_2, u_3, u_1} α' β' δ f' (Option.map.{u_5, u_2} α α' g₁ a) (Option.map.{u_6, u_3} β β' g₂ b)))
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
  forall {α : Type.{u_1}} {α' : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β} {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u_7} δ (g (f a b)) (f' (g' a) b)) -> (Eq.{succ u_7} (Option.{u_7} δ) (Option.map.{u_5, u_7} γ δ g (Option.map₂.{u_1, u_3, u_5} α β γ f a b)) (Option.map₂.{u_2, u_3, u_7} α' β δ f' (Option.map.{u_1, u_2} α α' g' a) b))
but is expected to have type
  forall {α : Type.{u_4}} {β : Type.{u_5}} {γ : Type.{u_3}} {f : α -> β -> γ} {a : Option.{u_4} α} {b : Option.{u_5} β} {δ : Type.{u_1}} {α' : Type.{u_2}} {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u_1} δ (g (f a b)) (f' (g' a) b)) -> (Eq.{succ u_1} (Option.{u_1} δ) (Option.map.{u_3, u_1} γ δ g (Option.map₂.{u_4, u_5, u_3} α β γ f a b)) (Option.map₂.{u_2, u_5, u_1} α' β δ f' (Option.map.{u_4, u_2} α α' g' a) b))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_distrib_left Option.map_map₂_distrib_leftₓ'. -/
/-- Symmetric statement to `option.map₂_map_left_comm`. -/
theorem map_map₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) : (map₂ f a b).map g = map₂ f' (a.map g') b := by
  cases a <;> cases b <;> simp [h_distrib]
#align option.map_map₂_distrib_left Option.map_map₂_distrib_left

/- warning: option.map_map₂_distrib_right -> Option.map_map₂_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {β' : Type.{u_4}} {γ : Type.{u_5}} {δ : Type.{u_7}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β} {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u_7} δ (g (f a b)) (f' a (g' b))) -> (Eq.{succ u_7} (Option.{u_7} δ) (Option.map.{u_5, u_7} γ δ g (Option.map₂.{u_1, u_3, u_5} α β γ f a b)) (Option.map₂.{u_1, u_4, u_7} α β' δ f' a (Option.map.{u_3, u_4} β β' g' b)))
but is expected to have type
  forall {α : Type.{u_4}} {β : Type.{u_5}} {γ : Type.{u_3}} {f : α -> β -> γ} {a : Option.{u_4} α} {b : Option.{u_5} β} {δ : Type.{u_1}} {β' : Type.{u_2}} {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u_1} δ (g (f a b)) (f' a (g' b))) -> (Eq.{succ u_1} (Option.{u_1} δ) (Option.map.{u_3, u_1} γ δ g (Option.map₂.{u_4, u_5, u_3} α β γ f a b)) (Option.map₂.{u_4, u_2, u_1} α β' δ f' a (Option.map.{u_5, u_2} β β' g' b)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_distrib_right Option.map_map₂_distrib_rightₓ'. -/
/-- Symmetric statement to `option.map_map₂_right_comm`. -/
theorem map_map₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) : (map₂ f a b).map g = map₂ f' a (b.map g') := by
  cases a <;> cases b <;> simp [h_distrib]
#align option.map_map₂_distrib_right Option.map_map₂_distrib_right

/- warning: option.map₂_map_left_comm -> Option.map₂_map_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {α' : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {a : Option.{u_1} α} {b : Option.{u_3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u_5} γ (f (g a) b) (g' (f' a b))) -> (Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_2, u_3, u_5} α' β γ f (Option.map.{u_1, u_2} α α' g a) b) (Option.map.{u_7, u_5} δ γ g' (Option.map₂.{u_1, u_3, u_7} α β δ f' a b)))
but is expected to have type
  forall {α : Type.{u_5}} {β : Type.{u_4}} {γ : Type.{u_3}} {a : Option.{u_5} α} {b : Option.{u_4} β} {α' : Type.{u_1}} {δ : Type.{u_2}} {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u_3} γ (f (g a) b) (g' (f' a b))) -> (Eq.{succ u_3} (Option.{u_3} γ) (Option.map₂.{u_1, u_4, u_3} α' β γ f (Option.map.{u_5, u_1} α α' g a) b) (Option.map.{u_2, u_3} δ γ g' (Option.map₂.{u_5, u_4, u_2} α β δ f' a b)))
Case conversion may be inaccurate. Consider using '#align option.map₂_map_left_comm Option.map₂_map_left_commₓ'. -/
/-- Symmetric statement to `option.map_map₂_distrib_left`. -/
theorem map₂_map_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) : map₂ f (a.map g) b = (map₂ f' a b).map g' := by
  cases a <;> cases b <;> simp [h_left_comm]
#align option.map₂_map_left_comm Option.map₂_map_left_comm

/- warning: option.map_map₂_right_comm -> Option.map_map₂_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {β' : Type.{u_4}} {γ : Type.{u_5}} {δ : Type.{u_7}} {a : Option.{u_1} α} {b : Option.{u_3} β} {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u_5} γ (f a (g b)) (g' (f' a b))) -> (Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_4, u_5} α β' γ f a (Option.map.{u_3, u_4} β β' g b)) (Option.map.{u_7, u_5} δ γ g' (Option.map₂.{u_1, u_3, u_7} α β δ f' a b)))
but is expected to have type
  forall {α : Type.{u_4}} {β : Type.{u_5}} {γ : Type.{u_3}} {a : Option.{u_4} α} {b : Option.{u_5} β} {β' : Type.{u_1}} {δ : Type.{u_2}} {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u_3} γ (f a (g b)) (g' (f' a b))) -> (Eq.{succ u_3} (Option.{u_3} γ) (Option.map₂.{u_4, u_1, u_3} α β' γ f a (Option.map.{u_5, u_1} β β' g b)) (Option.map.{u_2, u_3} δ γ g' (Option.map₂.{u_4, u_5, u_2} α β δ f' a b)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_right_comm Option.map_map₂_right_commₓ'. -/
/-- Symmetric statement to `option.map_map₂_distrib_right`. -/
theorem map_map₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) : map₂ f a (b.map g) = (map₂ f' a b).map g' :=
  by cases a <;> cases b <;> simp [h_right_comm]
#align option.map_map₂_right_comm Option.map_map₂_right_comm

/- warning: option.map_map₂_antidistrib -> Option.map_map₂_antidistrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {α' : Type.{u_2}} {β : Type.{u_3}} {β' : Type.{u_4}} {γ : Type.{u_5}} {δ : Type.{u_7}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β} {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u_7} δ (g (f a b)) (f' (g₁ b) (g₂ a))) -> (Eq.{succ u_7} (Option.{u_7} δ) (Option.map.{u_5, u_7} γ δ g (Option.map₂.{u_1, u_3, u_5} α β γ f a b)) (Option.map₂.{u_4, u_2, u_7} β' α' δ f' (Option.map.{u_3, u_4} β β' g₁ b) (Option.map.{u_1, u_2} α α' g₂ a)))
but is expected to have type
  forall {α : Type.{u_5}} {β : Type.{u_6}} {γ : Type.{u_4}} {f : α -> β -> γ} {a : Option.{u_5} α} {b : Option.{u_6} β} {δ : Type.{u_1}} {β' : Type.{u_2}} {α' : Type.{u_3}} {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u_1} δ (g (f a b)) (f' (g₁ b) (g₂ a))) -> (Eq.{succ u_1} (Option.{u_1} δ) (Option.map.{u_4, u_1} γ δ g (Option.map₂.{u_5, u_6, u_4} α β γ f a b)) (Option.map₂.{u_2, u_3, u_1} β' α' δ f' (Option.map.{u_6, u_2} β β' g₁ b) (Option.map.{u_5, u_3} α α' g₂ a)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_antidistrib Option.map_map₂_antidistribₓ'. -/
theorem map_map₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (map₂ f a b).map g = map₂ f' (b.map g₁) (a.map g₂) := by
  cases a <;> cases b <;> simp [h_antidistrib]
#align option.map_map₂_antidistrib Option.map_map₂_antidistrib

/- warning: option.map_map₂_antidistrib_left -> Option.map_map₂_antidistrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {β' : Type.{u_4}} {γ : Type.{u_5}} {δ : Type.{u_7}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β} {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u_7} δ (g (f a b)) (f' (g' b) a)) -> (Eq.{succ u_7} (Option.{u_7} δ) (Option.map.{u_5, u_7} γ δ g (Option.map₂.{u_1, u_3, u_5} α β γ f a b)) (Option.map₂.{u_4, u_1, u_7} β' α δ f' (Option.map.{u_3, u_4} β β' g' b) a))
but is expected to have type
  forall {α : Type.{u_4}} {β : Type.{u_5}} {γ : Type.{u_3}} {f : α -> β -> γ} {a : Option.{u_4} α} {b : Option.{u_5} β} {δ : Type.{u_1}} {β' : Type.{u_2}} {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u_1} δ (g (f a b)) (f' (g' b) a)) -> (Eq.{succ u_1} (Option.{u_1} δ) (Option.map.{u_3, u_1} γ δ g (Option.map₂.{u_4, u_5, u_3} α β γ f a b)) (Option.map₂.{u_2, u_4, u_1} β' α δ f' (Option.map.{u_5, u_2} β β' g' b) a))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_antidistrib_left Option.map_map₂_antidistrib_leftₓ'. -/
/-- Symmetric statement to `option.map₂_map_left_anticomm`. -/
theorem map_map₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) : (map₂ f a b).map g = map₂ f' (b.map g') a :=
  by cases a <;> cases b <;> simp [h_antidistrib]
#align option.map_map₂_antidistrib_left Option.map_map₂_antidistrib_left

/- warning: option.map_map₂_antidistrib_right -> Option.map_map₂_antidistrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {α' : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {f : α -> β -> γ} {a : Option.{u_1} α} {b : Option.{u_3} β} {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u_7} δ (g (f a b)) (f' b (g' a))) -> (Eq.{succ u_7} (Option.{u_7} δ) (Option.map.{u_5, u_7} γ δ g (Option.map₂.{u_1, u_3, u_5} α β γ f a b)) (Option.map₂.{u_3, u_2, u_7} β α' δ f' b (Option.map.{u_1, u_2} α α' g' a)))
but is expected to have type
  forall {α : Type.{u_4}} {β : Type.{u_5}} {γ : Type.{u_3}} {f : α -> β -> γ} {a : Option.{u_4} α} {b : Option.{u_5} β} {δ : Type.{u_1}} {α' : Type.{u_2}} {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u_1} δ (g (f a b)) (f' b (g' a))) -> (Eq.{succ u_1} (Option.{u_1} δ) (Option.map.{u_3, u_1} γ δ g (Option.map₂.{u_4, u_5, u_3} α β γ f a b)) (Option.map₂.{u_5, u_2, u_1} β α' δ f' b (Option.map.{u_4, u_2} α α' g' a)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_antidistrib_right Option.map_map₂_antidistrib_rightₓ'. -/
/-- Symmetric statement to `option.map_map₂_right_anticomm`. -/
theorem map_map₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) : (map₂ f a b).map g = map₂ f' b (a.map g') :=
  by cases a <;> cases b <;> simp [h_antidistrib]
#align option.map_map₂_antidistrib_right Option.map_map₂_antidistrib_right

/- warning: option.map₂_map_left_anticomm -> Option.map₂_map_left_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {α' : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_5}} {δ : Type.{u_7}} {a : Option.{u_1} α} {b : Option.{u_3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u_5} γ (f (g a) b) (g' (f' b a))) -> (Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_2, u_3, u_5} α' β γ f (Option.map.{u_1, u_2} α α' g a) b) (Option.map.{u_7, u_5} δ γ g' (Option.map₂.{u_3, u_1, u_7} β α δ f' b a)))
but is expected to have type
  forall {α : Type.{u_5}} {β : Type.{u_4}} {γ : Type.{u_3}} {a : Option.{u_5} α} {b : Option.{u_4} β} {α' : Type.{u_1}} {δ : Type.{u_2}} {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u_3} γ (f (g a) b) (g' (f' b a))) -> (Eq.{succ u_3} (Option.{u_3} γ) (Option.map₂.{u_1, u_4, u_3} α' β γ f (Option.map.{u_5, u_1} α α' g a) b) (Option.map.{u_2, u_3} δ γ g' (Option.map₂.{u_4, u_5, u_2} β α δ f' b a)))
Case conversion may be inaccurate. Consider using '#align option.map₂_map_left_anticomm Option.map₂_map_left_anticommₓ'. -/
/-- Symmetric statement to `option.map_map₂_antidistrib_left`. -/
theorem map₂_map_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    map₂ f (a.map g) b = (map₂ f' b a).map g' := by cases a <;> cases b <;> simp [h_left_anticomm]
#align option.map₂_map_left_anticomm Option.map₂_map_left_anticomm

/- warning: option.map_map₂_right_anticomm -> Option.map_map₂_right_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_3}} {β' : Type.{u_4}} {γ : Type.{u_5}} {δ : Type.{u_7}} {a : Option.{u_1} α} {b : Option.{u_3} β} {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u_5} γ (f a (g b)) (g' (f' b a))) -> (Eq.{succ u_5} (Option.{u_5} γ) (Option.map₂.{u_1, u_4, u_5} α β' γ f a (Option.map.{u_3, u_4} β β' g b)) (Option.map.{u_7, u_5} δ γ g' (Option.map₂.{u_3, u_1, u_7} β α δ f' b a)))
but is expected to have type
  forall {α : Type.{u_4}} {β : Type.{u_5}} {γ : Type.{u_3}} {a : Option.{u_4} α} {b : Option.{u_5} β} {β' : Type.{u_1}} {δ : Type.{u_2}} {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u_3} γ (f a (g b)) (g' (f' b a))) -> (Eq.{succ u_3} (Option.{u_3} γ) (Option.map₂.{u_4, u_1, u_3} α β' γ f a (Option.map.{u_5, u_1} β β' g b)) (Option.map.{u_2, u_3} δ γ g' (Option.map₂.{u_5, u_4, u_2} β α δ f' b a)))
Case conversion may be inaccurate. Consider using '#align option.map_map₂_right_anticomm Option.map_map₂_right_anticommₓ'. -/
/-- Symmetric statement to `option.map_map₂_antidistrib_right`. -/
theorem map_map₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    map₂ f a (b.map g) = (map₂ f' b a).map g' := by cases a <;> cases b <;> simp [h_right_anticomm]
#align option.map_map₂_right_anticomm Option.map_map₂_right_anticomm

end Option

