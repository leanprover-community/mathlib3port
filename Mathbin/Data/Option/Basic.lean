/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Logic.IsEmpty
import Control.Traversable.Basic
import Tactic.Basic

#align_import data.option.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Option of a type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
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
  nofun
#align option.coe_ne_none Option.coe_ne_none

#print Option.forall /-
protected theorem forall {p : Option α → Prop} : (∀ x, p x) ↔ p none ∧ ∀ x, p (some x) :=
  ⟨fun h => ⟨h _, fun x => h _⟩, fun h x => Option.casesOn x h.1 h.2⟩
#align option.forall Option.forall
-/

#print Option.exists /-
protected theorem exists {p : Option α → Prop} : (∃ x, p x) ↔ p none ∨ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx⟩ => (Option.casesOn x Or.inl fun x hx => Or.inr ⟨x, hx⟩) hx, fun h =>
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

/- warning: option.get_or_else_some clashes with option.get_or_else_coe -> Option.getD_some
Case conversion may be inaccurate. Consider using '#align option.get_or_else_some Option.getD_someₓ'. -/
#print Option.getD_some /-
@[simp]
theorem getD_some (x y : α) : Option.getD (some x) y = x :=
  rfl
#align option.get_or_else_some Option.getD_some
-/

#print Option.getD_none /-
@[simp]
theorem getD_none (x : α) : Option.getD none x = x :=
  rfl
#align option.get_or_else_none Option.getD_none
-/

#print Option.getD_some /-
@[simp]
theorem getD_some (x y : α) : Option.getD (↑x) y = x :=
  rfl
#align option.get_or_else_coe Option.getD_some
-/

#print Option.getD_of_ne_none /-
theorem getD_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) : some (x.getD y) = x := by
  cases x <;> [contradiction; rw [get_or_else_some]]
#align option.get_or_else_of_ne_none Option.getD_of_ne_none
-/

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

#print Option.map_injective /-
/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.Injective f) : Function.Injective (Option.map f)
  | none, none, H => rfl
  | some a₁, some a₂, H => by rw [Hf (Option.some.inj H)]
#align option.map_injective Option.map_injective
-/

#print Option.map_comp_some /-
@[simp]
theorem map_comp_some (f : α → β) : Option.map f ∘ some = some ∘ f :=
  rfl
#align option.map_comp_some Option.map_comp_some
-/

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

#print Option.none_bind /-
@[simp]
theorem none_bind {α β} (f : α → Option β) : none >>= f = none :=
  rfl
#align option.none_bind Option.none_bind
-/

#print Option.some_bind /-
@[simp]
theorem some_bind {α β} (a : α) (f : α → Option β) : some a >>= f = f a :=
  rfl
#align option.some_bind Option.some_bind
-/

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

#print Option.bind_some /-
@[simp]
theorem bind_some : ∀ x : Option α, x >>= some = x :=
  @bind_pure α Option _ _
#align option.bind_some Option.bind_some
-/

@[simp]
theorem bind_some' : ∀ x : Option α, x.bind some = x :=
  bind_some
#align option.bind_some' Option.bind_some'

#print Option.bind_eq_some /-
@[simp]
theorem bind_eq_some {α β} {x : Option α} {f : α → Option β} {b : β} :
    x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b := by cases x <;> simp
#align option.bind_eq_some Option.bind_eq_some
-/

#print Option.bind_eq_some' /-
@[simp]
theorem bind_eq_some' {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by cases x <;> simp
#align option.bind_eq_some' Option.bind_eq_some'
-/

#print Option.bind_eq_none' /-
@[simp]
theorem bind_eq_none' {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some']
#align option.bind_eq_none' Option.bind_eq_none'
-/

#print Option.bind_eq_none /-
@[simp]
theorem bind_eq_none {α β} {o : Option α} {f : α → Option β} :
    o >>= f = none ↔ ∀ b a, a ∈ o → b ∉ f a :=
  bind_eq_none'
#align option.bind_eq_none Option.bind_eq_none
-/

#print Option.bind_comm /-
theorem bind_comm {α β γ} {f : α → β → Option γ} (a : Option α) (b : Option β) :
    (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by
  cases a <;> cases b <;> rfl
#align option.bind_comm Option.bind_comm
-/

#print Option.bind_assoc /-
theorem bind_assoc (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun y => (f y).bind g := by cases x <;> rfl
#align option.bind_assoc Option.bind_assoc
-/

#print Option.join_eq_some /-
theorem join_eq_some {x : Option (Option α)} {a : α} : x.join = some a ↔ x = some (some a) := by
  simp
#align option.join_eq_some Option.join_eq_some
-/

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

#print Option.bind_id_eq_join /-
theorem bind_id_eq_join {x : Option (Option α)} : x >>= id = x.join := by simp
#align option.bind_id_eq_join Option.bind_id_eq_join
-/

#print Option.joinM_eq_join /-
theorem joinM_eq_join : joinM = @join α :=
  funext fun x => by rw [joinM, bind_id_eq_join]
#align option.join_eq_join Option.joinM_eq_join
-/

#print Option.bind_eq_bind' /-
theorem bind_eq_bind' {α β : Type _} {f : α → Option β} {x : Option α} : x >>= f = x.bind f :=
  rfl
#align option.bind_eq_bind Option.bind_eq_bind'
-/

#print Option.map_eq_map /-
@[simp]
theorem map_eq_map {α β} {f : α → β} : (· <$> ·) f = Option.map f :=
  rfl
#align option.map_eq_map Option.map_eq_map
-/

#print Option.map_none /-
theorem map_none {α β} {f : α → β} : f <$> none = none :=
  rfl
#align option.map_none Option.map_none
-/

#print Option.map_some /-
theorem map_some {α β} {a : α} {f : α → β} : f <$> some a = some (f a) :=
  rfl
#align option.map_some Option.map_some
-/

#print Option.map_coe /-
theorem map_coe {α β} {a : α} {f : α → β} : f <$> (a : Option α) = ↑(f a) :=
  rfl
#align option.map_coe Option.map_coe
-/

#print Option.map_none' /-
@[simp]
theorem map_none' {f : α → β} : Option.map f none = none :=
  rfl
#align option.map_none' Option.map_none'
-/

#print Option.map_some' /-
@[simp]
theorem map_some' {a : α} {f : α → β} : Option.map f (some a) = some (f a) :=
  rfl
#align option.map_some' Option.map_some'
-/

#print Option.map_coe' /-
@[simp]
theorem map_coe' {a : α} {f : α → β} : Option.map f (a : Option α) = ↑(f a) :=
  rfl
#align option.map_coe' Option.map_coe'
-/

#print Option.map_eq_some /-
theorem map_eq_some {α β} {x : Option α} {f : α → β} {b : β} :
    f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b := by cases x <;> simp
#align option.map_eq_some Option.map_eq_some
-/

#print Option.map_eq_some' /-
@[simp]
theorem map_eq_some' {x : Option α} {f : α → β} {b : β} :
    x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by cases x <;> simp
#align option.map_eq_some' Option.map_eq_some'
-/

#print Option.map_eq_none /-
theorem map_eq_none {α β} {x : Option α} {f : α → β} : f <$> x = none ↔ x = none := by
  cases x <;> simp only [map_none, map_some, eq_self_iff_true]
#align option.map_eq_none Option.map_eq_none
-/

#print Option.map_eq_none' /-
@[simp]
theorem map_eq_none' {x : Option α} {f : α → β} : x.map f = none ↔ x = none := by
  cases x <;> simp only [map_none', map_some', eq_self_iff_true]
#align option.map_eq_none' Option.map_eq_none'
-/

#print Option.map_injective' /-
/-- `option.map` as a function between functions is injective. -/
theorem map_injective' : Function.Injective (@Option.map α β) := fun f g h =>
  funext fun x => some_injective _ <| by simp only [← map_some', h]
#align option.map_injective' Option.map_injective'
-/

#print Option.map_inj /-
@[simp]
theorem map_inj {f g : α → β} : Option.map f = Option.map g ↔ f = g :=
  map_injective'.eq_iff
#align option.map_inj Option.map_inj
-/

#print Option.map_congr /-
theorem map_congr {f g : α → β} {x : Option α} (h : ∀ a ∈ x, f a = g a) :
    Option.map f x = Option.map g x := by cases x <;> simp only [map_none', map_some', h, mem_def]
#align option.map_congr Option.map_congr
-/

attribute [simp] map_id

#print Option.map_eq_id /-
@[simp]
theorem map_eq_id {f : α → α} : Option.map f = id ↔ f = id :=
  map_injective'.eq_iff' map_id
#align option.map_eq_id Option.map_eq_id
-/

#print Option.map_map /-
@[simp]
theorem map_map (h : β → γ) (g : α → β) (x : Option α) :
    Option.map h (Option.map g x) = Option.map (h ∘ g) x := by
  cases x <;> simp only [map_none', map_some']
#align option.map_map Option.map_map
-/

#print Option.map_comm /-
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) : (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂ := by rw [map_map, h, ← map_map]
#align option.map_comm Option.map_comm
-/

#print Option.comp_map /-
theorem comp_map (h : β → γ) (g : α → β) (x : Option α) :
    Option.map (h ∘ g) x = Option.map h (Option.map g x) :=
  (map_map _ _ _).symm
#align option.comp_map Option.comp_map
-/

#print Option.map_comp_map /-
@[simp]
theorem map_comp_map (f : α → β) (g : β → γ) : Option.map g ∘ Option.map f = Option.map (g ∘ f) :=
  by ext x; rw [comp_map]
#align option.map_comp_map Option.map_comp_map
-/

#print Option.mem_map_of_mem /-
theorem mem_map_of_mem {a : α} {x : Option α} (g : α → β) (h : a ∈ x) : g a ∈ x.map g :=
  mem_def.mpr ((mem_def.mp h).symm ▸ map_some')
#align option.mem_map_of_mem Option.mem_map_of_mem
-/

#print Option.mem_map /-
theorem mem_map {f : α → β} {y : β} {o : Option α} : y ∈ o.map f ↔ ∃ x ∈ o, f x = y := by simp
#align option.mem_map Option.mem_map
-/

#print Option.forall_mem_map /-
theorem forall_mem_map {f : α → β} {o : Option α} {p : β → Prop} :
    (∀ y ∈ o.map f, p y) ↔ ∀ x ∈ o, p (f x) := by simp
#align option.forall_mem_map Option.forall_mem_map
-/

#print Option.exists_mem_map /-
theorem exists_mem_map {f : α → β} {o : Option α} {p : β → Prop} :
    (∃ y ∈ o.map f, p y) ↔ ∃ x ∈ o, p (f x) := by simp
#align option.exists_mem_map Option.exists_mem_map
-/

#print Option.bind_map_comm /-
theorem bind_map_comm {α β} {x : Option (Option α)} {f : α → β} :
    x >>= Option.map f = x.map (Option.map f) >>= id := by cases x <;> simp
#align option.bind_map_comm Option.bind_map_comm
-/

#print Option.join_map_eq_map_join /-
theorem join_map_eq_map_join {f : α → β} {x : Option (Option α)} :
    (x.map (Option.map f)).join = x.join.map f := by rcases x with (_ | _ | x) <;> simp
#align option.join_map_eq_map_join Option.join_map_eq_map_join
-/

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

#print Option.map_bind /-
theorem map_bind {α β γ} (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x >>= g) = x >>= fun a => Option.map f (g a) := by
  simp_rw [← map_eq_map, ← bind_pure_comp_eq_map, LawfulMonad.bind_assoc]
#align option.map_bind Option.map_bind
-/

#print Option.map_bind' /-
theorem map_bind' (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x.bind g) = x.bind fun a => Option.map f (g a) := by cases x <;> simp
#align option.map_bind' Option.map_bind'
-/

#print Option.map_pbind /-
theorem map_pbind (f : β → γ) (x : Option α) (g : ∀ a, a ∈ x → Option β) :
    Option.map f (x.pbind g) = x.pbind fun a H => Option.map f (g a H) := by
  cases x <;> simp only [pbind, map_none']
#align option.map_pbind Option.map_pbind
-/

#print Option.pbind_map /-
theorem pbind_map (f : α → β) (x : Option α) (g : ∀ b : β, b ∈ x.map f → Option γ) :
    pbind (Option.map f x) g = x.pbind fun a h => g (f a) (mem_map_of_mem _ h) := by cases x <;> rfl
#align option.pbind_map Option.pbind_map
-/

#print Option.pmap_none /-
@[simp]
theorem pmap_none (f : ∀ a : α, p a → β) {H} : pmap f (@none α) H = none :=
  rfl
#align option.pmap_none Option.pmap_none
-/

#print Option.pmap_some /-
@[simp]
theorem pmap_some (f : ∀ a : α, p a → β) {x : α} (h : p x) :
    pmap f (some x) = fun _ => some (f x h) :=
  rfl
#align option.pmap_some Option.pmap_some
-/

#print Option.mem_pmem /-
theorem mem_pmem {a : α} (h : ∀ a ∈ x, p a) (ha : a ∈ x) : f a (h a ha) ∈ pmap f x h := by
  rw [mem_def] at ha ⊢; subst ha; rfl
#align option.mem_pmem Option.mem_pmem
-/

#print Option.pmap_map /-
theorem pmap_map (g : γ → α) (x : Option γ) (H) :
    pmap f (x.map g) H = pmap (fun a h => f (g a) h) x fun a h => H _ (mem_map_of_mem _ h) := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.pmap_map Option.pmap_map
-/

#print Option.map_pmap /-
theorem map_pmap (g : β → γ) (f : ∀ a, p a → β) (x H) :
    Option.map g (pmap f x H) = pmap (fun a h => g (f a h)) x H := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.map_pmap Option.map_pmap
-/

#print Option.pmap_eq_map /-
@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (x H) :
    @pmap _ _ p (fun a _ => f a) x H = Option.map f x := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.pmap_eq_map Option.pmap_eq_map
-/

#print Option.pmap_bind /-
theorem pmap_bind {α β γ} {x : Option α} {g : α → Option β} {p : β → Prop} {f : ∀ b, p b → γ} (H)
    (H' : ∀ (a : α), ∀ b ∈ g a, b ∈ x >>= g) :
    pmap f (x >>= g) H = x >>= fun a => pmap f (g a) fun b h => H _ (H' a _ h) := by
  cases x <;> simp only [pmap, none_bind, some_bind]
#align option.pmap_bind Option.pmap_bind
-/

#print Option.bind_pmap /-
theorem bind_pmap {α β γ} {p : α → Prop} (f : ∀ a, p a → β) (x : Option α) (g : β → Option γ) (H) :
    pmap f x H >>= g = x.pbind fun a h => g (f a (H _ h)) := by
  cases x <;> simp only [pmap, none_bind, some_bind, pbind]
#align option.bind_pmap Option.bind_pmap
-/

variable {f x}

#print Option.pbind_eq_none /-
theorem pbind_eq_none {f : ∀ a : α, a ∈ x → Option β} (h' : ∀ a ∈ x, f a H = none → x = none) :
    x.pbind f = none ↔ x = none := by
  cases x
  · simp
  · simp only [pbind, iff_false_iff]
    intro h
    cases h' x rfl h
#align option.pbind_eq_none Option.pbind_eq_none
-/

#print Option.pbind_eq_some /-
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
-/

#print Option.pmap_eq_none_iff /-
@[simp]
theorem pmap_eq_none_iff {h} : pmap f x h = none ↔ x = none := by cases x <;> simp
#align option.pmap_eq_none_iff Option.pmap_eq_none_iff
-/

#print Option.pmap_eq_some_iff /-
@[simp]
theorem pmap_eq_some_iff {hf} {y : β} :
    pmap f x hf = some y ↔ ∃ (a : α) (H : x = some a), f a (hf a H) = y :=
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
-/

#print Option.join_pmap_eq_pmap_join /-
@[simp]
theorem join_pmap_eq_pmap_join {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h => H (some a) (mem_of_mem_join h) _ rfl := by
  rcases x with (_ | _ | x) <;> simp
#align option.join_pmap_eq_pmap_join Option.join_pmap_eq_pmap_join
-/

end Pmap

#print Option.seq_some /-
@[simp]
theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) :=
  rfl
#align option.seq_some Option.seq_some
-/

#print Option.some_orElse' /-
@[simp]
theorem some_orElse' (a : α) (x : Option α) : (some a).orelse x = some a :=
  rfl
#align option.some_orelse' Option.some_orElse'
-/

#print Option.some_orElse /-
@[simp]
theorem some_orElse (a : α) (x : Option α) : (some a <|> x) = some a :=
  rfl
#align option.some_orelse Option.some_orElse
-/

#print Option.none_orElse' /-
@[simp]
theorem none_orElse' (x : Option α) : none.orelse x = x := by cases x <;> rfl
#align option.none_orelse' Option.none_orElse'
-/

#print Option.none_orElse /-
@[simp]
theorem none_orElse (x : Option α) : (none <|> x) = x :=
  none_orElse' x
#align option.none_orelse Option.none_orElse
-/

#print Option.orElse_none' /-
@[simp]
theorem orElse_none' (x : Option α) : x.orelse none = x := by cases x <;> rfl
#align option.orelse_none' Option.orElse_none'
-/

#print Option.orElse_none /-
@[simp]
theorem orElse_none (x : Option α) : (x <|> none) = x :=
  orElse_none' x
#align option.orelse_none Option.orElse_none
-/

#print Option.isSome_none /-
@[simp]
theorem isSome_none : @isSome α none = false :=
  rfl
#align option.is_some_none Option.isSome_none
-/

#print Option.isSome_some /-
@[simp]
theorem isSome_some {a : α} : isSome (some a) = true :=
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
theorem isNone_none : @isNone α none = true :=
  rfl
#align option.is_none_none Option.isNone_none
-/

#print Option.isNone_some /-
@[simp]
theorem isNone_some {a : α} : isNone (some a) = false :=
  rfl
#align option.is_none_some Option.isNone_some
-/

#print Option.not_isSome /-
@[simp]
theorem not_isSome {a : Option α} : isSome a = false ↔ a.isNone = true := by cases a <;> simp
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

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (x «expr ≠ » none[option.none]) -/
#print Option.bex_ne_none /-
theorem bex_ne_none {p : Option α → Prop} : (∃ (x : _) (_ : x ≠ none), p x) ↔ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx, hp⟩ => ⟨get <| ne_none_iff_isSome.1 hx, by rwa [some_get]⟩, fun ⟨x, hx⟩ =>
    ⟨some x, some_ne_none x, hx⟩⟩
#align option.bex_ne_none Option.bex_ne_none
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (x «expr ≠ » none[option.none]) -/
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
theorem getD_default_eq_iget [Inhabited α] (o : Option α) : o.getD default = o.iget := by
  cases o <;> rfl
#align option.get_or_else_default_eq_iget Option.getD_default_eq_iget
-/

#print Option.guard_eq_some /-
@[simp]
theorem guard_eq_some {p : α → Prop} [DecidablePred p] {a b : α} :
    guard p a = some b ↔ a = b ∧ p a := by
  by_cases p a <;> simp [Option.guard, h] <;> intro <;> contradiction
#align option.guard_eq_some Option.guard_eq_some
-/

#print Option.guard_eq_some' /-
@[simp]
theorem guard_eq_some' {p : Prop} [Decidable p] (u) : guard p = some u ↔ p :=
  by
  cases u
  by_cases p <;> simp [_root_.guard, h] <;>
    first
    | rfl
    | contradiction
#align option.guard_eq_some' Option.guard_eq_some'
-/

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

#print Option.casesOn'_none /-
@[simp]
theorem casesOn'_none (x : β) (f : α → β) : casesOn' none x f = x :=
  rfl
#align option.cases_on'_none Option.casesOn'_none
-/

#print Option.casesOn'_some /-
@[simp]
theorem casesOn'_some (x : β) (f : α → β) (a : α) : casesOn' (some a) x f = f a :=
  rfl
#align option.cases_on'_some Option.casesOn'_some
-/

#print Option.casesOn'_coe /-
@[simp]
theorem casesOn'_coe (x : β) (f : α → β) (a : α) : casesOn' (a : Option α) x f = f a :=
  rfl
#align option.cases_on'_coe Option.casesOn'_coe
-/

#print Option.casesOn'_none_coe /-
@[simp]
theorem casesOn'_none_coe (f : Option α → β) (o : Option α) : casesOn' o (f none) (f ∘ coe) = f o :=
  by cases o <;> rfl
#align option.cases_on'_none_coe Option.casesOn'_none_coe
-/

#print Option.getD_map /-
@[simp]
theorem getD_map (f : α → β) (x : α) (o : Option α) : getD (o.map f) (f x) = f (getD o x) := by
  cases o <;> rfl
#align option.get_or_else_map Option.getD_map
-/

#print Option.orElse_eq_some /-
theorem orElse_eq_some (o o' : Option α) (x : α) :
    (o <|> o') = some x ↔ o = some x ∨ o = none ∧ o' = some x :=
  by
  cases o
  · simp only [true_and_iff, false_or_iff, eq_self_iff_true, none_orelse]
  · simp only [some_orelse, or_false_iff, false_and_iff]
#align option.orelse_eq_some Option.orElse_eq_some
-/

#print Option.orElse_eq_some' /-
theorem orElse_eq_some' (o o' : Option α) (x : α) :
    o.orelse o' = some x ↔ o = some x ∨ o = none ∧ o' = some x :=
  Option.orElse_eq_some o o' x
#align option.orelse_eq_some' Option.orElse_eq_some'
-/

#print Option.orElse_eq_none /-
@[simp]
theorem orElse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = none :=
  by
  cases o
  · simp only [true_and_iff, none_orelse, eq_self_iff_true]
  · simp only [some_orelse, false_and_iff]
#align option.orelse_eq_none Option.orElse_eq_none
-/

#print Option.orElse_eq_none' /-
@[simp]
theorem orElse_eq_none' (o o' : Option α) : o.orelse o' = none ↔ o = none ∧ o' = none :=
  Option.orElse_eq_none o o'
#align option.orelse_eq_none' Option.orElse_eq_none'
-/

section

open scoped Classical

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
  · intro h; exact ⟨Option.get h⟩
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

#print Option.elim_none_some /-
@[simp]
theorem elim_none_some (f : Option α → β) : Option.elim' (f none) (f ∘ some) = f :=
  funext fun o => by cases o <;> rfl
#align option.elim_none_some Option.elim_none_some
-/

end Option

