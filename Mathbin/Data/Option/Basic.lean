/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Logic.IsEmpty
import Mathbin.Tactic.Basic
import Mathbin.Logic.Relator

/-!
# Option of a type

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

theorem coe_def : (coe : α → Option α) = some :=
  rfl

theorem some_ne_none (x : α) : some x ≠ none := fun h => Option.noConfusion h

protected theorem forall {p : Option α → Prop} : (∀ x, p x) ↔ p none ∧ ∀ x, p (some x) :=
  ⟨fun h => ⟨h _, fun x => h _⟩, fun h x => Option.casesOn x h.1 h.2⟩

protected theorem exists {p : Option α → Prop} : (∃ x, p x) ↔ p none ∨ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx⟩ => ((Option.casesOn x Or.inl) fun x hx => Or.inr ⟨x, hx⟩) hx, fun h =>
    h.elim (fun h => ⟨_, h⟩) fun ⟨x, hx⟩ => ⟨_, hx⟩⟩

@[simp]
theorem get_mem : ∀ {o : Option α} (h : isSome o), Option.get h ∈ o
  | some a, _ => rfl

theorem get_of_mem {a : α} : ∀ {o : Option α} (h : isSome o), a ∈ o → Option.get h = a
  | _, _, rfl => rfl

@[simp]
theorem not_mem_none (a : α) : a ∉ (none : Option α) := fun h => Option.noConfusion h

@[simp]
theorem some_get : ∀ {x : Option α} (h : isSome x), some (Option.get h) = x
  | some x, hx => rfl

@[simp]
theorem get_some (x : α) (h : isSome (some x)) : Option.get h = x :=
  rfl

@[simp]
theorem get_or_else_some (x y : α) : Option.getOrElse (some x) y = x :=
  rfl

@[simp]
theorem get_or_else_none (x : α) : Option.getOrElse none x = x :=
  rfl

@[simp]
theorem get_or_else_coe (x y : α) : Option.getOrElse (↑x) y = x :=
  rfl

theorem get_or_else_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) : some (x.getOrElse y) = x := by
  cases x <;> [contradiction, rw [get_or_else_some]]

@[simp]
theorem coe_get {o : Option α} (h : o.isSome) : ((Option.get h : α) : Option α) = o :=
  Option.some_get h

theorem mem_unique {o : Option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
  Option.some.inj <| ha.symm.trans hb

theorem eq_of_mem_of_mem {a : α} {o1 o2 : Option α} (h1 : a ∈ o1) (h2 : a ∈ o2) : o1 = o2 :=
  h1.trans h2.symm

theorem Mem.left_unique : Relator.LeftUnique ((· ∈ ·) : α → Option α → Prop) := fun a o b => mem_unique

theorem some_injective (α : Type _) : Function.Injective (@some α) := fun _ _ => some_inj.mp

/- warning: option.map_injective -> Option.map_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {f : α -> β}, (Function.Injective.{succ u_1 succ u_2} α β f) -> (Function.Injective.{succ u_1 succ u_2} (Option.{u_1} α) (Option.{u_2} β) (Option.map.{u_1 u_2} α β f))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {f : α -> β}, (Function.injective.{succ u_1 succ u_2} α β f) -> (Function.injective.{succ u_1 succ u_2} (Option.{u_1} α) (Option.{u_2} β) (Option.map.{u_1 u_2} α β f))
Case conversion may be inaccurate. Consider using '#align option.map_injective Option.map_injectiveₓ'. -/
/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.Injective f) : Function.Injective (Option.map f)
  | none, none, H => rfl
  | some a₁, some a₂, H => by rw [Hf (Option.some.inj H)]

@[simp]
theorem map_comp_some (f : α → β) : Option.map f ∘ some = some ∘ f :=
  rfl

@[ext]
theorem ext : ∀ {o₁ o₂ : Option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
  | none, none, H => rfl
  | some a, o, H => ((H _).1 rfl).symm
  | o, some b, H => (H _).2 rfl

theorem eq_none_iff_forall_not_mem {o : Option α} : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e a h => by rw [e] at h <;> cases h, fun h => ext <| by simpa⟩

/- warning: option.none_bind -> Option.none_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} (f : α -> (Option.{u_1} β)), Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1 u_1} Option.{u_1} (Monad.toHasBind.{u_1 u_1} Option.{u_1} Option.monad.{u_1}) α β (Option.none.{u_1} α) f) (Option.none.{u_1} β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> (Option.{u_2} β)), Eq.{succ u_2} (Option.{u_2} β) (Option.bind.{u_1 u_2} α β (Option.none.{u_1} α) f) (Option.none.{u_2} β)
Case conversion may be inaccurate. Consider using '#align option.none_bind Option.none_bindₓ'. -/
@[simp]
theorem none_bind {α β} (f : α → Option β) : none >>= f = none :=
  rfl

/- warning: option.some_bind -> Option.some_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} (a : α) (f : α -> (Option.{u_1} β)), Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1 u_1} Option.{u_1} (Monad.toHasBind.{u_1 u_1} Option.{u_1} Option.monad.{u_1}) α β (Option.some.{u_1} α a) f) (f a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (a : α) (f : α -> (Option.{u_2} β)), Eq.{succ u_2} (Option.{u_2} β) (Option.bind.{u_1 u_2} α β (Option.some.{u_1} α a) f) (f a)
Case conversion may be inaccurate. Consider using '#align option.some_bind Option.some_bindₓ'. -/
@[simp]
theorem some_bind {α β} (a : α) (f : α → Option β) : some a >>= f = f a :=
  rfl

@[simp]
theorem none_bind' (f : α → Option β) : none.bind f = none :=
  rfl

@[simp]
theorem some_bind' (a : α) (f : α → Option β) : (some a).bind f = f a :=
  rfl

/- warning: option.bind_some -> Option.bind_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (x : Option.{u_1} α), Eq.{succ u_1} (Option.{u_1} α) (Bind.bind.{u_1 u_1} Option.{u_1} (Monad.toHasBind.{u_1 u_1} Option.{u_1} Option.monad.{u_1}) α α x (Option.some.{u_1} α)) x
but is expected to have type
  forall {α : Type.{u_1}} (x : Option.{u_1} α), Eq.{succ u_1} (Option.{u_1} α) (Option.bind.{u_1 u_1} α α x (Option.some.{u_1} α)) x
Case conversion may be inaccurate. Consider using '#align option.bind_some Option.bind_someₓ'. -/
@[simp]
theorem bind_some : ∀ x : Option α, x >>= some = x :=
  @bind_pure α Option _ _

@[simp]
theorem bind_some' : ∀ x : Option α, x.bind some = x :=
  bind_some

/- warning: option.bind_eq_some -> Option.bind_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {x : Option.{u_1} α} {f : α -> (Option.{u_1} β)} {b : β}, Iff (Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1 u_1} Option.{u_1} (Monad.toHasBind.{u_1 u_1} Option.{u_1} Option.monad.{u_1}) α β x f) (Option.some.{u_1} β b)) (Exists.{succ u_1} α (fun (a : α) => And (Eq.{succ u_1} (Option.{u_1} α) x (Option.some.{u_1} α a)) (Eq.{succ u_1} (Option.{u_1} β) (f a) (Option.some.{u_1} β b))))
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.1657 : Type.{u_1}} {b : α._@.Std.Data.Option.Lemmas._hyg.1657} {α._@.Std.Data.Option.Lemmas._hyg.1656 : Type.{u_2}} {x : Option.{u_2} α._@.Std.Data.Option.Lemmas._hyg.1656} {f : α._@.Std.Data.Option.Lemmas._hyg.1656 -> (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1657)}, Iff (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1657) (Option.bind.{u_2 u_1} α._@.Std.Data.Option.Lemmas._hyg.1656 α._@.Std.Data.Option.Lemmas._hyg.1657 x f) (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1657 b)) (Exists.{succ u_2} α._@.Std.Data.Option.Lemmas._hyg.1656 (fun (a : α._@.Std.Data.Option.Lemmas._hyg.1656) => And (Eq.{succ u_2} (Option.{u_2} α._@.Std.Data.Option.Lemmas._hyg.1656) x (Option.some.{u_2} α._@.Std.Data.Option.Lemmas._hyg.1656 a)) (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1657) (f a) (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1657 b))))
Case conversion may be inaccurate. Consider using '#align option.bind_eq_some Option.bind_eq_someₓ'. -/
@[simp]
theorem bind_eq_some {α β} {x : Option α} {f : α → Option β} {b : β} :
    x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b := by cases x <;> simp

@[simp]
theorem bind_eq_some' {x : Option α} {f : α → Option β} {b : β} : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
  by cases x <;> simp

@[simp]
theorem bind_eq_none' {o : Option α} {f : α → Option β} : o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some']

/- warning: option.bind_eq_none -> Option.bind_eq_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {o : Option.{u_1} α} {f : α -> (Option.{u_1} β)}, Iff (Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1 u_1} Option.{u_1} (Monad.toHasBind.{u_1 u_1} Option.{u_1} Option.monad.{u_1}) α β o f) (Option.none.{u_1} β)) (forall (b : β) (a : α), (Membership.Mem.{u_1 u_1} α (Option.{u_1} α) (Option.hasMem.{u_1} α) a o) -> (Not (Membership.Mem.{u_1 u_1} β (Option.{u_1} β) (Option.hasMem.{u_1} β) b (f a))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {o : Option.{u_1} α} {f : α -> (Option.{u_2} β)}, Iff (Eq.{succ u_2} (Option.{u_2} β) (Option.bind.{u_1 u_2} α β o f) (Option.none.{u_2} β)) (forall (b : β) (a : α), (Membership.mem.{u_1 u_1} α (Option.{u_1} α) (Option.instMembershipOption.{u_1} α) a o) -> (Not (Membership.mem.{u_2 u_2} β (Option.{u_2} β) (Option.instMembershipOption.{u_2} β) b (f a))))
Case conversion may be inaccurate. Consider using '#align option.bind_eq_none Option.bind_eq_noneₓ'. -/
@[simp]
theorem bind_eq_none {α β} {o : Option α} {f : α → Option β} : o >>= f = none ↔ ∀ b a, a ∈ o → b ∉ f a :=
  bind_eq_none'

/- warning: option.bind_comm -> Option.bind_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {f : α -> β -> (Option.{u_3} γ)} (a : Option.{u_1} α) (b : Option.{u_2} β), Eq.{succ u_3} (Option.{u_3} γ) (Option.bind.{u_1 u_3} α γ a (fun (x : α) => Option.bind.{u_2 u_3} β γ b (f x))) (Option.bind.{u_2 u_3} β γ b (fun (y : β) => Option.bind.{u_1 u_3} α γ a (fun (x : α) => f x y)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {f : α -> β -> (Option.{u_3} γ)} (a : Option.{u_1} α) (b : Option.{u_2} β), Eq.{succ u_3} (Option.{u_3} γ) (Option.bind.{u_1 u_3} α γ a (fun (x : α) => Option.bind.{u_2 u_3} β γ b (f x))) (Option.bind.{u_2 u_3} β γ b (fun (y : β) => Option.bind.{u_1 u_3} α γ a (fun (x : α) => f x y)))
Case conversion may be inaccurate. Consider using '#align option.bind_comm Option.bind_commₓ'. -/
theorem bind_comm {α β γ} {f : α → β → Option γ} (a : Option α) (b : Option β) :
    (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by cases a <;> cases b <;> rfl

/- warning: option.bind_assoc -> Option.bind_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (x : Option.{u_1} α) (f : α -> (Option.{u_2} β)) (g : β -> (Option.{u_3} γ)), Eq.{succ u_3} (Option.{u_3} γ) (Option.bind.{u_2 u_3} β γ (Option.bind.{u_1 u_2} α β x f) g) (Option.bind.{u_1 u_3} α γ x (fun (y : α) => Option.bind.{u_2 u_3} β γ (f y) g))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (x : Option.{u_1} α) (f : α -> (Option.{u_2} β)) (g : β -> (Option.{u_3} γ)), Eq.{succ u_3} (Option.{u_3} γ) (Option.bind.{u_2 u_3} β γ (Option.bind.{u_1 u_2} α β x f) g) (Option.bind.{u_1 u_3} α γ x (fun (y : α) => Option.bind.{u_2 u_3} β γ (f y) g))
Case conversion may be inaccurate. Consider using '#align option.bind_assoc Option.bind_assocₓ'. -/
theorem bind_assoc (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun y => (f y).bind g := by cases x <;> rfl

/- warning: option.join_eq_some -> Option.join_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {x : Option.{u_1} (Option.{u_1} α)} {a : α}, Iff (Eq.{succ u_1} (Option.{u_1} α) (Option.join.{u_1} α x) (Option.some.{u_1} α a)) (Eq.{succ u_1} (Option.{u_1} (Option.{u_1} α)) x (Option.some.{u_1} (Option.{u_1} α) (Option.some.{u_1} α a)))
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.1985 : Type.{u_1}} {a : α._@.Std.Data.Option.Lemmas._hyg.1985} {x : Option.{u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1985)}, Iff (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1985) (Option.join.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1985 x) (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1985 a)) (Eq.{succ u_1} (Option.{u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1985)) x (Option.some.{u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1985) (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.1985 a)))
Case conversion may be inaccurate. Consider using '#align option.join_eq_some Option.join_eq_someₓ'. -/
theorem join_eq_some {x : Option (Option α)} {a : α} : x.join = some a ↔ x = some (some a) := by simp

theorem join_ne_none {x : Option (Option α)} : x.join ≠ none ↔ ∃ z, x = some (some z) := by simp

theorem join_ne_none' {x : Option (Option α)} : ¬x.join = none ↔ ∃ z, x = some (some z) := by simp

theorem join_eq_none {o : Option (Option α)} : o.join = none ↔ o = none ∨ o = some none := by
  rcases o with (_ | _ | _) <;> simp

/- warning: option.bind_id_eq_join -> Option.bind_id_eq_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {x : Option.{u_1} (Option.{u_1} α)}, Eq.{succ u_1} (Option.{u_1} α) (Bind.bind.{u_1 u_1} Option.{u_1} (Monad.toHasBind.{u_1 u_1} Option.{u_1} Option.monad.{u_1}) (Option.{u_1} α) α x (id.{succ u_1} (Option.{u_1} α))) (Option.join.{u_1} α x)
but is expected to have type
  forall {α : Type.{u_1}} {x : Option.{u_1} (Option.{u_1} α)}, Eq.{succ u_1} (Option.{u_1} α) (Option.bind.{u_1 u_1} (Option.{u_1} α) α x (id.{succ u_1} (Option.{u_1} α))) (Option.join.{u_1} α x)
Case conversion may be inaccurate. Consider using '#align option.bind_id_eq_join Option.bind_id_eq_joinₓ'. -/
theorem bind_id_eq_join {x : Option (Option α)} : x >>= id = x.join := by simp

theorem join_eq_join : mjoin = @join α :=
  funext fun x => by rw [mjoin, bind_id_eq_join]

theorem bind_eq_bind {α β : Type _} {f : α → Option β} {x : Option α} : x >>= f = x.bind f :=
  rfl

/- warning: option.map_eq_map -> Option.map_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {f : α -> β}, Eq.{succ u_1} ((Option.{u_1} α) -> (Option.{u_1} β)) (Functor.map.{u_1 u_1} Option.{u_1} (Traversable.toFunctor.{u_1} Option.{u_1} Option.traversable.{u_1}) α β f) (Option.map.{u_1 u_1} α β f)
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.2205 : Type.{u_1}} {α._@.Std.Data.Option.Lemmas._hyg.2206 : Type.{u_1}} {f : α._@.Std.Data.Option.Lemmas._hyg.2205 -> α._@.Std.Data.Option.Lemmas._hyg.2206}, Eq.{succ u_1} ((Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2205) -> (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2206)) (Functor.map.{u_1 u_1} Option.{u_1} instFunctorOption.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2205 α._@.Std.Data.Option.Lemmas._hyg.2206 f) (Option.map.{u_1 u_1} α._@.Std.Data.Option.Lemmas._hyg.2205 α._@.Std.Data.Option.Lemmas._hyg.2206 f)
Case conversion may be inaccurate. Consider using '#align option.map_eq_map Option.map_eq_mapₓ'. -/
@[simp]
theorem map_eq_map {α β} {f : α → β} : (· <$> ·) f = Option.map f :=
  rfl

/- warning: option.map_none -> Option.map_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {f : α -> β}, Eq.{succ u_1} (Option.{u_1} β) (Functor.map.{u_1 u_1} Option.{u_1} (Traversable.toFunctor.{u_1} Option.{u_1} Option.traversable.{u_1}) α β f (Option.none.{u_1} α)) (Option.none.{u_1} β)
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.2228 : Type.{u_1}} {α._@.Std.Data.Option.Lemmas._hyg.2227 : Type.{u_1}} {f : α._@.Std.Data.Option.Lemmas._hyg.2228 -> α._@.Std.Data.Option.Lemmas._hyg.2227}, Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2227) (Functor.map.{u_1 u_1} Option.{u_1} instFunctorOption.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2228 α._@.Std.Data.Option.Lemmas._hyg.2227 f (Option.none.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2228)) (Option.none.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2227)
Case conversion may be inaccurate. Consider using '#align option.map_none Option.map_noneₓ'. -/
theorem map_none {α β} {f : α → β} : f <$> none = none :=
  rfl

/- warning: option.map_some -> Option.map_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {a : α} {f : α -> β}, Eq.{succ u_1} (Option.{u_1} β) (Functor.map.{u_1 u_1} Option.{u_1} (Traversable.toFunctor.{u_1} Option.{u_1} Option.traversable.{u_1}) α β f (Option.some.{u_1} α a)) (Option.some.{u_1} β (f a))
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.2265 : Type.{u_1}} {α._@.Std.Data.Option.Lemmas._hyg.2264 : Type.{u_1}} {f : α._@.Std.Data.Option.Lemmas._hyg.2265 -> α._@.Std.Data.Option.Lemmas._hyg.2264} {a : α._@.Std.Data.Option.Lemmas._hyg.2265}, Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2264) (Functor.map.{u_1 u_1} Option.{u_1} instFunctorOption.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2265 α._@.Std.Data.Option.Lemmas._hyg.2264 f (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2265 a)) (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2264 (f a))
Case conversion may be inaccurate. Consider using '#align option.map_some Option.map_someₓ'. -/
theorem map_some {α β} {a : α} {f : α → β} : f <$> some a = some (f a) :=
  rfl

theorem map_coe {α β} {a : α} {f : α → β} : f <$> (a : Option α) = ↑(f a) :=
  rfl

/- warning: option.map_none' -> Option.map_none' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {f : α -> β}, Eq.{succ u_2} (Option.{u_2} β) (Option.map.{u_1 u_2} α β f (Option.none.{u_1} α)) (Option.none.{u_2} β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β), Eq.{succ u_2} (Option.{u_2} β) (Option.map.{u_1 u_2} α β f (Option.none.{u_1} α)) (Option.none.{u_2} β)
Case conversion may be inaccurate. Consider using '#align option.map_none' Option.map_none'ₓ'. -/
@[simp]
theorem map_none' {f : α → β} : Option.map f none = none :=
  rfl

/- warning: option.map_some' -> Option.map_some' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {a : α} {f : α -> β}, Eq.{succ u_2} (Option.{u_2} β) (Option.map.{u_1 u_2} α β f (Option.some.{u_1} α a)) (Option.some.{u_2} β (f a))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (a : α) (f : α -> β), Eq.{succ u_2} (Option.{u_2} β) (Option.map.{u_1 u_2} α β f (Option.some.{u_1} α a)) (Option.some.{u_2} β (f a))
Case conversion may be inaccurate. Consider using '#align option.map_some' Option.map_some'ₓ'. -/
@[simp]
theorem map_some' {a : α} {f : α → β} : Option.map f (some a) = some (f a) :=
  rfl

@[simp]
theorem map_coe' {a : α} {f : α → β} : Option.map f (a : Option α) = ↑(f a) :=
  rfl

/- warning: option.map_eq_some -> Option.map_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {x : Option.{u_1} α} {f : α -> β} {b : β}, Iff (Eq.{succ u_1} (Option.{u_1} β) (Functor.map.{u_1 u_1} (fun {α : Type.{u_1}} => Option.{u_1} α) (Traversable.toFunctor.{u_1} (fun {α : Type.{u_1}} => Option.{u_1} α) Option.traversable.{u_1}) α β f x) (Option.some.{u_1} β b)) (Exists.{succ u_1} α (fun (a : α) => And (Eq.{succ u_1} (Option.{u_1} α) x (Option.some.{u_1} α a)) (Eq.{succ u_1} β (f a) b)))
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.2466 : Type.{u_1}} {α._@.Std.Data.Option.Lemmas._hyg.2467 : Type.{u_1}} {f : α._@.Std.Data.Option.Lemmas._hyg.2466 -> α._@.Std.Data.Option.Lemmas._hyg.2467} {x : Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2466} {b : α._@.Std.Data.Option.Lemmas._hyg.2467}, Iff (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2467) (Functor.map.{u_1 u_1} Option.{u_1} instFunctorOption.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2466 α._@.Std.Data.Option.Lemmas._hyg.2467 f x) (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2467 b)) (Exists.{succ u_1} α._@.Std.Data.Option.Lemmas._hyg.2466 (fun (a : α._@.Std.Data.Option.Lemmas._hyg.2466) => And (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2466) x (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2466 a)) (Eq.{succ u_1} α._@.Std.Data.Option.Lemmas._hyg.2467 (f a) b)))
Case conversion may be inaccurate. Consider using '#align option.map_eq_some Option.map_eq_someₓ'. -/
theorem map_eq_some {α β} {x : Option α} {f : α → β} {b : β} : f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b := by
  cases x <;> simp

/- warning: option.map_eq_some' -> Option.map_eq_some' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {x : Option.{u_1} α} {f : α -> β} {b : β}, Iff (Eq.{succ u_2} (Option.{u_2} β) (Option.map.{u_1 u_2} α β f x) (Option.some.{u_2} β b)) (Exists.{succ u_1} α (fun (a : α) => And (Eq.{succ u_1} (Option.{u_1} α) x (Option.some.{u_1} α a)) (Eq.{succ u_2} β (f a) b)))
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.2370 : Type.{u_1}} {b : α._@.Std.Data.Option.Lemmas._hyg.2370} {α._@.Std.Data.Option.Lemmas._hyg.2369 : Type.{u_2}} {x : Option.{u_2} α._@.Std.Data.Option.Lemmas._hyg.2369} {f : α._@.Std.Data.Option.Lemmas._hyg.2369 -> α._@.Std.Data.Option.Lemmas._hyg.2370}, Iff (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2370) (Option.map.{u_2 u_1} α._@.Std.Data.Option.Lemmas._hyg.2369 α._@.Std.Data.Option.Lemmas._hyg.2370 f x) (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2370 b)) (Exists.{succ u_2} α._@.Std.Data.Option.Lemmas._hyg.2369 (fun (a : α._@.Std.Data.Option.Lemmas._hyg.2369) => And (Eq.{succ u_2} (Option.{u_2} α._@.Std.Data.Option.Lemmas._hyg.2369) x (Option.some.{u_2} α._@.Std.Data.Option.Lemmas._hyg.2369 a)) (Eq.{succ u_1} α._@.Std.Data.Option.Lemmas._hyg.2370 (f a) b)))
Case conversion may be inaccurate. Consider using '#align option.map_eq_some' Option.map_eq_some'ₓ'. -/
@[simp]
theorem map_eq_some' {x : Option α} {f : α → β} {b : β} : x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by
  cases x <;> simp

/- warning: option.map_eq_none -> Option.map_eq_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {x : Option.{u_1} α} {f : α -> β}, Iff (Eq.{succ u_1} (Option.{u_1} β) (Functor.map.{u_1 u_1} (fun {α : Type.{u_1}} => Option.{u_1} α) (Traversable.toFunctor.{u_1} (fun {α : Type.{u_1}} => Option.{u_1} α) Option.traversable.{u_1}) α β f x) (Option.none.{u_1} β)) (Eq.{succ u_1} (Option.{u_1} α) x (Option.none.{u_1} α))
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.2584 : Type.{u_1}} {α._@.Std.Data.Option.Lemmas._hyg.2585 : Type.{u_1}} {f : α._@.Std.Data.Option.Lemmas._hyg.2584 -> α._@.Std.Data.Option.Lemmas._hyg.2585} {x : Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2584}, Iff (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2585) (Functor.map.{u_1 u_1} Option.{u_1} instFunctorOption.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2584 α._@.Std.Data.Option.Lemmas._hyg.2585 f x) (Option.none.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2585)) (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2584) x (Option.none.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2584))
Case conversion may be inaccurate. Consider using '#align option.map_eq_none Option.map_eq_noneₓ'. -/
theorem map_eq_none {α β} {x : Option α} {f : α → β} : f <$> x = none ↔ x = none := by
  cases x <;> simp only [map_none, map_some, eq_self_iff_true]

/- warning: option.map_eq_none' -> Option.map_eq_none' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {x : Option.{u_1} α} {f : α -> β}, Iff (Eq.{succ u_2} (Option.{u_2} β) (Option.map.{u_1 u_2} α β f x) (Option.none.{u_2} β)) (Eq.{succ u_1} (Option.{u_1} α) x (Option.none.{u_1} α))
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.2518 : Type.{u_1}} {x : Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2518} {α._@.Std.Data.Option.Lemmas._hyg.2519 : Type.{u_2}} {f : α._@.Std.Data.Option.Lemmas._hyg.2518 -> α._@.Std.Data.Option.Lemmas._hyg.2519}, Iff (Eq.{succ u_2} (Option.{u_2} α._@.Std.Data.Option.Lemmas._hyg.2519) (Option.map.{u_1 u_2} α._@.Std.Data.Option.Lemmas._hyg.2518 α._@.Std.Data.Option.Lemmas._hyg.2519 f x) (Option.none.{u_2} α._@.Std.Data.Option.Lemmas._hyg.2519)) (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2518) x (Option.none.{u_1} α._@.Std.Data.Option.Lemmas._hyg.2518))
Case conversion may be inaccurate. Consider using '#align option.map_eq_none' Option.map_eq_none'ₓ'. -/
@[simp]
theorem map_eq_none' {x : Option α} {f : α → β} : x.map f = none ↔ x = none := by
  cases x <;> simp only [map_none', map_some', eq_self_iff_true]

/-- `option.map` as a function between functions is injective. -/
theorem map_injective' : Function.Injective (@Option.map α β) := fun f g h =>
  funext fun x => some_injective _ <| by simp only [← map_some', h]

@[simp]
theorem map_inj {f g : α → β} : Option.map f = Option.map g ↔ f = g :=
  map_injective'.eq_iff

/- warning: option.map_congr -> Option.map_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {f : α -> β} {g : α -> β} {x : Option.{u_1} α}, (forall (a : α), (Membership.Mem.{u_1 u_1} α (Option.{u_1} α) (Option.hasMem.{u_1} α) a x) -> (Eq.{succ u_2} β (f a) (g a))) -> (Eq.{succ u_2} (Option.{u_2} β) (Option.map.{u_1 u_2} α β f x) (Option.map.{u_1 u_2} α β g x))
but is expected to have type
  forall {α : Type.{u_1}} {α._@.Std.Data.Option.Lemmas._hyg.2666 : Type.{u_2}} {f : α -> α._@.Std.Data.Option.Lemmas._hyg.2666} {g : α -> α._@.Std.Data.Option.Lemmas._hyg.2666} {x : Option.{u_1} α}, (forall (a : α), (Membership.mem.{u_1 u_1} α (Option.{u_1} α) (Option.instMembershipOption.{u_1} α) a x) -> (Eq.{succ u_2} α._@.Std.Data.Option.Lemmas._hyg.2666 (f a) (g a))) -> (Eq.{succ u_2} (Option.{u_2} α._@.Std.Data.Option.Lemmas._hyg.2666) (Option.map.{u_1 u_2} α α._@.Std.Data.Option.Lemmas._hyg.2666 f x) (Option.map.{u_1 u_2} α α._@.Std.Data.Option.Lemmas._hyg.2666 g x))
Case conversion may be inaccurate. Consider using '#align option.map_congr Option.map_congrₓ'. -/
theorem map_congr {f g : α → β} {x : Option α} (h : ∀ a ∈ x, f a = g a) : Option.map f x = Option.map g x := by
  cases x <;> simp only [map_none', map_some', h, mem_def]

attribute [simp] map_id

@[simp]
theorem map_eq_id {f : α → α} : Option.map f = id ↔ f = id :=
  map_injective'.eq_iff' map_id

/- warning: option.map_map -> Option.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (h : β -> γ) (g : α -> β) (x : Option.{u_1} α), Eq.{succ u_3} (Option.{u_3} γ) (Option.map.{u_2 u_3} β γ h (Option.map.{u_1 u_2} α β g x)) (Option.map.{u_1 u_3} α γ (Function.comp.{succ u_1 succ u_2 succ u_3} α β γ h g) x)
but is expected to have type
  forall {β : Type.{u_1}} {γ : Type.{u_2}} {α : Type.{u_3}} (h : β -> γ) (g : α -> β) (x : Option.{u_3} α), Eq.{succ u_2} (Option.{u_2} γ) (Option.map.{u_1 u_2} β γ h (Option.map.{u_3 u_1} α β g x)) (Option.map.{u_3 u_2} α γ (Function.comp.{succ u_3 succ u_1 succ u_2} α β γ h g) x)
Case conversion may be inaccurate. Consider using '#align option.map_map Option.map_mapₓ'. -/
@[simp]
theorem map_map (h : β → γ) (g : α → β) (x : Option α) : Option.map h (Option.map g x) = Option.map (h ∘ g) x := by
  cases x <;> simp only [map_none', map_some']

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂ := by rw [map_map, h, ← map_map]

/- warning: option.comp_map -> Option.comp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (h : β -> γ) (g : α -> β) (x : Option.{u_1} α), Eq.{succ u_3} (Option.{u_3} γ) (Option.map.{u_1 u_3} α γ (Function.comp.{succ u_1 succ u_2 succ u_3} α β γ h g) x) (Option.map.{u_2 u_3} β γ h (Option.map.{u_1 u_2} α β g x))
but is expected to have type
  forall {β : Type.{u_1}} {γ : Type.{u_2}} {α : Type.{u_3}} (h : β -> γ) (g : α -> β) (x : Option.{u_3} α), Eq.{succ u_2} (Option.{u_2} γ) (Option.map.{u_3 u_2} α γ (Function.comp.{succ u_3 succ u_1 succ u_2} α β γ h g) x) (Option.map.{u_1 u_2} β γ h (Option.map.{u_3 u_1} α β g x))
Case conversion may be inaccurate. Consider using '#align option.comp_map Option.comp_mapₓ'. -/
theorem comp_map (h : β → γ) (g : α → β) (x : Option α) : Option.map (h ∘ g) x = Option.map h (Option.map g x) :=
  (map_map _ _ _).symm

/- warning: option.map_comp_map -> Option.map_comp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (f : α -> β) (g : β -> γ), Eq.{(max (succ u_1) (succ u_3))} ((Option.{u_1} α) -> (Option.{u_3} γ)) (Function.comp.{succ u_1 succ u_2 succ u_3} (Option.{u_1} α) (Option.{u_2} β) (Option.{u_3} γ) (Option.map.{u_2 u_3} β γ g) (Option.map.{u_1 u_2} α β f)) (Option.map.{u_1 u_3} α γ (Function.comp.{succ u_1 succ u_2 succ u_3} α β γ g f))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} (f : α -> β) (g : β -> γ), Eq.{(max (succ u_3) (succ u_1))} ((Option.{u_1} α) -> (Option.{u_3} γ)) (Function.comp.{succ u_1 succ u_2 succ u_3} (Option.{u_1} α) (Option.{u_2} β) (Option.{u_3} γ) (Option.map.{u_2 u_3} β γ g) (Option.map.{u_1 u_2} α β f)) (Option.map.{u_1 u_3} α γ (Function.comp.{succ u_1 succ u_2 succ u_3} α β γ g f))
Case conversion may be inaccurate. Consider using '#align option.map_comp_map Option.map_comp_mapₓ'. -/
@[simp]
theorem map_comp_map (f : α → β) (g : β → γ) : Option.map g ∘ Option.map f = Option.map (g ∘ f) := by
  ext x
  rw [comp_map]

/- warning: option.mem_map_of_mem -> Option.mem_map_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {a : α} {x : Option.{u_1} α} (g : α -> β), (Membership.Mem.{u_1 u_1} α (Option.{u_1} α) (Option.hasMem.{u_1} α) a x) -> (Membership.Mem.{u_2 u_2} β (Option.{u_2} β) (Option.hasMem.{u_2} β) (g a) (Option.map.{u_1 u_2} α β g x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {a : α} {x : Option.{u_1} α} (g : α -> β), (Membership.mem.{u_1 u_1} α (Option.{u_1} α) (Option.instMembershipOption.{u_1} α) a x) -> (Membership.mem.{u_2 u_2} β (Option.{u_2} β) (Option.instMembershipOption.{u_2} β) (g a) (Option.map.{u_1 u_2} α β g x))
Case conversion may be inaccurate. Consider using '#align option.mem_map_of_mem Option.mem_map_of_memₓ'. -/
theorem mem_map_of_mem {a : α} {x : Option α} (g : α → β) (h : a ∈ x) : g a ∈ x.map g :=
  mem_def.mpr ((mem_def.mp h).symm ▸ map_some')

theorem mem_map {f : α → β} {y : β} {o : Option α} : y ∈ o.map f ↔ ∃ x ∈ o, f x = y := by simp

theorem forall_mem_map {f : α → β} {o : Option α} {p : β → Prop} : (∀ y ∈ o.map f, p y) ↔ ∀ x ∈ o, p (f x) := by simp

theorem exists_mem_map {f : α → β} {o : Option α} {p : β → Prop} : (∃ y ∈ o.map f, p y) ↔ ∃ x ∈ o, p (f x) := by simp

/- warning: option.bind_map_comm -> Option.bind_map_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_1}} {x : Option.{u_1} (Option.{u_1} α)} {f : α -> β}, Eq.{succ u_1} (Option.{u_1} β) (Bind.bind.{u_1 u_1} Option.{u_1} (Monad.toHasBind.{u_1 u_1} Option.{u_1} Option.monad.{u_1}) (Option.{u_1} α) β x (Option.map.{u_1 u_1} α β f)) (Bind.bind.{u_1 u_1} Option.{u_1} (Monad.toHasBind.{u_1 u_1} Option.{u_1} Option.monad.{u_1}) (Option.{u_1} β) β (Option.map.{u_1 u_1} (Option.{u_1} α) (Option.{u_1} β) (Option.map.{u_1 u_1} α β f) x) (id.{succ u_1} (Option.{u_1} β)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {x : Option.{u_1} (Option.{u_1} α)} {f : α -> β}, Eq.{succ u_2} (Option.{u_2} β) (Option.bind.{u_1 u_2} (Option.{u_1} α) β x (Option.map.{u_1 u_2} α β f)) (Option.bind.{u_2 u_2} (Option.{u_2} β) β (Option.map.{u_1 u_2} (Option.{u_1} α) (Option.{u_2} β) (Option.map.{u_1 u_2} α β f) x) (id.{succ u_2} (Option.{u_2} β)))
Case conversion may be inaccurate. Consider using '#align option.bind_map_comm Option.bind_map_commₓ'. -/
theorem bind_map_comm {α β} {x : Option (Option α)} {f : α → β} : x >>= Option.map f = x.map (Option.map f) >>= id := by
  cases x <;> simp

/- warning: option.join_map_eq_map_join -> Option.join_map_eq_map_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {f : α -> β} {x : Option.{u_1} (Option.{u_1} α)}, Eq.{succ u_2} (Option.{u_2} β) (Option.join.{u_2} β (Option.map.{u_1 u_2} (Option.{u_1} α) (Option.{u_2} β) (Option.map.{u_1 u_2} α β f) x)) (Option.map.{u_1 u_2} α β f (Option.join.{u_1} α x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {f : α -> β} {x : Option.{u_1} (Option.{u_1} α)}, Eq.{succ u_2} (Option.{u_2} β) (Option.join.{u_2} β (Option.map.{u_1 u_2} (Option.{u_1} α) (Option.{u_2} β) (Option.map.{u_1 u_2} α β f) x)) (Option.map.{u_1 u_2} α β f (Option.join.{u_1} α x))
Case conversion may be inaccurate. Consider using '#align option.join_map_eq_map_join Option.join_map_eq_map_joinₓ'. -/
theorem join_map_eq_map_join {f : α → β} {x : Option (Option α)} : (x.map (Option.map f)).join = x.join.map f := by
  rcases x with (_ | _ | x) <;> simp

theorem join_join {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  rcases x with (_ | _ | _ | x) <;> simp

theorem mem_of_mem_join {a : α} {x : Option (Option α)} (h : a ∈ x.join) : some a ∈ x :=
  mem_def.mpr ((mem_def.mp h).symm ▸ join_eq_some.mp h)

section Pmap

variable {p : α → Prop} (f : ∀ a : α, p a → β) (x : Option α)

@[simp]
theorem pbind_eq_bind (f : α → Option β) (x : Option α) : (x.pbind fun a _ => f a) = x.bind f := by
  cases x <;> simp only [pbind, none_bind', some_bind']

theorem map_bind {α β γ} (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x >>= g) = x >>= fun a => Option.map f (g a) := by
  simp_rw [← map_eq_map, ← bind_pure_comp_eq_map, LawfulMonad.bind_assoc]

theorem map_bind' (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x.bind g) = x.bind fun a => Option.map f (g a) := by cases x <;> simp

theorem map_pbind (f : β → γ) (x : Option α) (g : ∀ a, a ∈ x → Option β) :
    Option.map f (x.pbind g) = x.pbind fun a H => Option.map f (g a H) := by cases x <;> simp only [pbind, map_none']

theorem pbind_map (f : α → β) (x : Option α) (g : ∀ b : β, b ∈ x.map f → Option γ) :
    pbind (Option.map f x) g = x.pbind fun a h => g (f a) (mem_map_of_mem _ h) := by cases x <;> rfl

@[simp]
theorem pmap_none (f : ∀ a : α, p a → β) {H} : pmap f (@none α) H = none :=
  rfl

@[simp]
theorem pmap_some (f : ∀ a : α, p a → β) {x : α} (h : p x) : pmap f (some x) = fun _ => some (f x h) :=
  rfl

theorem mem_pmem {a : α} (h : ∀ a ∈ x, p a) (ha : a ∈ x) : f a (h a ha) ∈ pmap f x h := by
  rw [mem_def] at ha⊢
  subst ha
  rfl

theorem pmap_map (g : γ → α) (x : Option γ) (H) :
    pmap f (x.map g) H = pmap (fun a h => f (g a) h) x fun a h => H _ (mem_map_of_mem _ h) := by
  cases x <;> simp only [map_none', map_some', pmap]

theorem map_pmap (g : β → γ) (f : ∀ a, p a → β) (x H) : Option.map g (pmap f x H) = pmap (fun a h => g (f a h)) x H :=
  by cases x <;> simp only [map_none', map_some', pmap]

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (x H) : @pmap _ _ p (fun a _ => f a) x H = Option.map f x := by
  cases x <;> simp only [map_none', map_some', pmap]

theorem pmap_bind {α β γ} {x : Option α} {g : α → Option β} {p : β → Prop} {f : ∀ b, p b → γ} (H)
    (H' : ∀ (a : α), ∀ b ∈ g a, b ∈ x >>= g) :
    pmap f (x >>= g) H = x >>= fun a => pmap f (g a) fun b h => H _ (H' a _ h) := by
  cases x <;> simp only [pmap, none_bind, some_bind]

theorem bind_pmap {α β γ} {p : α → Prop} (f : ∀ a, p a → β) (x : Option α) (g : β → Option γ) (H) :
    pmap f x H >>= g = x.pbind fun a h => g (f a (H _ h)) := by
  cases x <;> simp only [pmap, none_bind, some_bind, pbind]

variable {f x}

theorem pbind_eq_none {f : ∀ a : α, a ∈ x → Option β} (h' : ∀ a ∈ x, f a H = none → x = none) :
    x.pbind f = none ↔ x = none := by
  cases x
  · simp
    
  · simp only [pbind, iff_false_iff]
    intro h
    cases h' x rfl h
    

theorem pbind_eq_some {f : ∀ a : α, a ∈ x → Option β} {y : β} : x.pbind f = some y ↔ ∃ z ∈ x, f z H = some y := by
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
      
    

@[simp]
theorem pmap_eq_none_iff {h} : pmap f x h = none ↔ x = none := by cases x <;> simp

@[simp]
theorem pmap_eq_some_iff {hf} {y : β} : pmap f x hf = some y ↔ ∃ (a : α)(H : x = some a), f a (hf a H) = y := by
  cases x
  · simp only [not_mem_none, exists_false, pmap, not_false_iff, exists_prop_of_false]
    
  · constructor
    · intro h
      simp only [pmap] at h
      exact ⟨x, rfl, h⟩
      
    · rintro ⟨a, H, rfl⟩
      simp only [mem_def] at H
      simp only [H, pmap]
      
    

@[simp]
theorem join_pmap_eq_pmap_join {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h => H (some a) (mem_of_mem_join h) _ rfl := by
  rcases x with (_ | _ | x) <;> simp

end Pmap

@[simp]
theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) :=
  rfl

@[simp]
theorem some_orelse' (a : α) (x : Option α) : (some a).orelse x = some a :=
  rfl

@[simp]
theorem some_orelse (a : α) (x : Option α) : (some a <|> x) = some a :=
  rfl

@[simp]
theorem none_orelse' (x : Option α) : none.orelse x = x := by cases x <;> rfl

@[simp]
theorem none_orelse (x : Option α) : (none <|> x) = x :=
  none_orelse' x

@[simp]
theorem orelse_none' (x : Option α) : x.orelse none = x := by cases x <;> rfl

@[simp]
theorem orelse_none (x : Option α) : (x <|> none) = x :=
  orelse_none' x

@[simp]
theorem is_some_none : @isSome α none = ff :=
  rfl

@[simp]
theorem is_some_some {a : α} : isSome (some a) = tt :=
  rfl

theorem is_some_iff_exists {x : Option α} : isSome x ↔ ∃ a, x = some a := by
  cases x <;> simp [is_some] <;> exact ⟨_, rfl⟩

@[simp]
theorem is_none_none : @isNone α none = tt :=
  rfl

@[simp]
theorem is_none_some {a : α} : isNone (some a) = ff :=
  rfl

@[simp]
theorem not_is_some {a : Option α} : isSome a = ff ↔ a.isNone = tt := by cases a <;> simp

theorem eq_some_iff_get_eq {o : Option α} {a : α} : o = some a ↔ ∃ h : o.isSome, Option.get h = a := by cases o <;> simp

theorem not_is_some_iff_eq_none {o : Option α} : ¬o.isSome ↔ o = none := by cases o <;> simp

theorem ne_none_iff_is_some {o : Option α} : o ≠ none ↔ o.isSome := by cases o <;> simp

theorem ne_none_iff_exists {o : Option α} : o ≠ none ↔ ∃ x : α, some x = o := by cases o <;> simp

theorem ne_none_iff_exists' {o : Option α} : o ≠ none ↔ ∃ x : α, o = some x :=
  ne_none_iff_exists.trans <| exists_congr fun _ => eq_comm

/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x «expr ≠ » none[option.none]) -/
theorem bex_ne_none {p : Option α → Prop} : (∃ (x : _)(_ : x ≠ none), p x) ↔ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx, hp⟩ => ⟨get <| ne_none_iff_is_some.1 hx, by rwa [some_get]⟩, fun ⟨x, hx⟩ => ⟨some x, some_ne_none x, hx⟩⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x «expr ≠ » none[option.none]) -/
theorem ball_ne_none {p : Option α → Prop} : (∀ (x) (_ : x ≠ none), p x) ↔ ∀ x, p (some x) :=
  ⟨fun h x => h (some x) (some_ne_none x), fun h x hx => by
    simpa only [some_get] using h (get <| ne_none_iff_is_some.1 hx)⟩

theorem iget_mem [Inhabited α] : ∀ {o : Option α}, isSome o → o.iget ∈ o
  | some a, _ => rfl

theorem iget_of_mem [Inhabited α] {a : α} : ∀ {o : Option α}, a ∈ o → o.iget = a
  | _, rfl => rfl

theorem get_or_else_default_eq_iget [Inhabited α] (o : Option α) : o.getOrElse default = o.iget := by cases o <;> rfl

/- warning: option.guard_eq_some -> Option.guard_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u_1} α p] {a : α} {b : α}, Iff (Eq.{succ u_1} (Option.{u_1} α) (Option.guard.{u_1} α p (fun (a : α) => _inst_1 a) a) (Option.some.{u_1} α b)) (And (Eq.{succ u_1} α a b) (p a))
but is expected to have type
  forall {α._@.Std.Data.Option.Lemmas._hyg.3204 : Type.{u_1}} {p : α._@.Std.Data.Option.Lemmas._hyg.3204 -> Prop} {a : α._@.Std.Data.Option.Lemmas._hyg.3204} {b : α._@.Std.Data.Option.Lemmas._hyg.3204} [inst._@.Std.Data.Option.Lemmas._hyg.3180 : DecidablePred.{succ u_1} α._@.Std.Data.Option.Lemmas._hyg.3204 p], Iff (Eq.{succ u_1} (Option.{u_1} α._@.Std.Data.Option.Lemmas._hyg.3204) (Option.guard.{u_1} α._@.Std.Data.Option.Lemmas._hyg.3204 p (fun (a : α._@.Std.Data.Option.Lemmas._hyg.3204) => inst._@.Std.Data.Option.Lemmas._hyg.3180 a) a) (Option.some.{u_1} α._@.Std.Data.Option.Lemmas._hyg.3204 b)) (And (Eq.{succ u_1} α._@.Std.Data.Option.Lemmas._hyg.3204 a b) (p a))
Case conversion may be inaccurate. Consider using '#align option.guard_eq_some Option.guard_eq_someₓ'. -/
@[simp]
theorem guard_eq_some {p : α → Prop} [DecidablePred p] {a b : α} : guard p a = some b ↔ a = b ∧ p a := by
  by_cases p a <;> simp [Option.guard, h] <;> intro <;> contradiction

@[simp]
theorem guard_eq_some' {p : Prop} [Decidable p] (u) : guard p = some u ↔ p := by
  cases u
  by_cases p <;> simp [_root_.guard, h] <;> first |rfl|contradiction

theorem lift_or_get_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, liftOrGet f o₁ o₂ = o₁ ∨ liftOrGet f o₁ o₂ = o₂
  | none, none => Or.inl rfl
  | some a, none => Or.inl rfl
  | none, some b => Or.inr rfl
  | some a, some b => by simpa [lift_or_get] using h a b

/- warning: option.lift_or_get_none_left -> Option.lift_or_get_none_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {f : α -> α -> α} {b : Option.{u_1} α}, Eq.{succ u_1} (Option.{u_1} α) (Option.liftOrGet.{u_1} α f (Option.none.{u_1} α) b) b
but is expected to have type
  forall {α : Type.{u_1}} {f : α -> α -> α} {b : Option.{u_1} α}, Eq.{succ u_1} (Option.{u_1} α) (Option.lift_or_get.{u_1} α f (Option.none.{u_1} α) b) b
Case conversion may be inaccurate. Consider using '#align option.lift_or_get_none_left Option.lift_or_get_none_leftₓ'. -/
@[simp]
theorem lift_or_get_none_left {f} {b : Option α} : liftOrGet f none b = b := by cases b <;> rfl

/- warning: option.lift_or_get_none_right -> Option.lift_or_get_none_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {f : α -> α -> α} {a : Option.{u_1} α}, Eq.{succ u_1} (Option.{u_1} α) (Option.liftOrGet.{u_1} α f a (Option.none.{u_1} α)) a
but is expected to have type
  forall {α : Type.{u_1}} {f : α -> α -> α} {a : Option.{u_1} α}, Eq.{succ u_1} (Option.{u_1} α) (Option.lift_or_get.{u_1} α f a (Option.none.{u_1} α)) a
Case conversion may be inaccurate. Consider using '#align option.lift_or_get_none_right Option.lift_or_get_none_rightₓ'. -/
@[simp]
theorem lift_or_get_none_right {f} {a : Option α} : liftOrGet f a none = a := by cases a <;> rfl

@[simp]
theorem lift_or_get_some_some {f} {a b : α} : liftOrGet f (some a) (some b) = f a b :=
  rfl

/-- Given an element of `a : option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
def casesOn' : Option α → β → (α → β) → β
  | none, n, s => n
  | some a, n, s => s a

@[simp]
theorem cases_on'_none (x : β) (f : α → β) : casesOn' none x f = x :=
  rfl

@[simp]
theorem cases_on'_some (x : β) (f : α → β) (a : α) : casesOn' (some a) x f = f a :=
  rfl

@[simp]
theorem cases_on'_coe (x : β) (f : α → β) (a : α) : casesOn' (a : Option α) x f = f a :=
  rfl

@[simp]
theorem cases_on'_none_coe (f : Option α → β) (o : Option α) : casesOn' o (f none) (f ∘ coe) = f o := by cases o <;> rfl

@[simp]
theorem get_or_else_map (f : α → β) (x : α) (o : Option α) : getOrElse (o.map f) (f x) = f (getOrElse o x) := by
  cases o <;> rfl

theorem orelse_eq_some (o o' : Option α) (x : α) : (o <|> o') = some x ↔ o = some x ∨ o = none ∧ o' = some x := by
  cases o
  · simp only [true_and_iff, false_or_iff, eq_self_iff_true, none_orelse]
    
  · simp only [some_orelse, or_false_iff, false_and_iff]
    

theorem orelse_eq_some' (o o' : Option α) (x : α) : o.orelse o' = some x ↔ o = some x ∨ o = none ∧ o' = some x :=
  Option.orelse_eq_some o o' x

@[simp]
theorem orelse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = none := by
  cases o
  · simp only [true_and_iff, none_orelse, eq_self_iff_true]
    
  · simp only [some_orelse, false_and_iff]
    

@[simp]
theorem orelse_eq_none' (o o' : Option α) : o.orelse o' = none ↔ o = none ∧ o' = none :=
  Option.orelse_eq_none o o'

section

open Classical

/-- An arbitrary `some a` with `a : α` if `α` is nonempty, and otherwise `none`. -/
noncomputable def choice (α : Type _) : Option α :=
  if h : Nonempty α then some h.some else none

theorem choice_eq {α : Type _} [Subsingleton α] (a : α) : choice α = some a := by
  dsimp [choice]
  rw [dif_pos (⟨a⟩ : Nonempty α)]
  congr

theorem choice_eq_none (α : Type _) [IsEmpty α] : choice α = none :=
  dif_neg (not_nonempty_iff_imp_false.mpr isEmptyElim)

theorem choice_is_some_iff_nonempty {α : Type _} : (choice α).isSome ↔ Nonempty α := by
  fconstructor
  · intro h
    exact ⟨Option.get h⟩
    
  · intro h
    dsimp only [choice]
    rw [dif_pos h]
    exact is_some_some
    

end

@[simp]
theorem to_list_some (a : α) : (a : Option α).toList = [a] :=
  rfl

@[simp]
theorem to_list_none (α : Type _) : (none : Option α).toList = [] :=
  rfl

@[simp]
theorem elim_none_some (f : Option α → β) : Option.elim (f none) (f ∘ some) = f :=
  funext fun o => by cases o <;> rfl

end Option

