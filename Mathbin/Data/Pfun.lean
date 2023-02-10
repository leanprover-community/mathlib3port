/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.pfun
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Part
import Mathbin.Data.Rel

/-!
# Partial functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → part β`.

## Definitions

* `pfun α β`: Type of partial functions from `α` to `β`. Defined as `α → part β` and denoted
  `α →. β`.
* `pfun.dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `pfun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `dom`.
* `pfun.as_subtype`: Returns a partial function as a function from its `dom`.
* `pfun.to_subtype`: Restricts the codomain of a function to a subtype.
* `pfun.eval_opt`: Returns a partial function with a decidable `dom` as a function `a → option β`.
* `pfun.lift`: Turns a function into a partial function.
* `pfun.id`: The identity as a partial function.
* `pfun.comp`: Composition of partial functions.
* `pfun.restrict`: Restriction of a partial function to a smaller `dom`.
* `pfun.res`: Turns a function into a partial function with a prescribed domain.
* `pfun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `pfun.fix_induction`: A recursion principle for `pfun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `rel` definitions to `pfun`:
* `pfun.image`: Image of a set under a partial function.
* `pfun.ran`: Range of a partial function.
* `pfun.preimage`: Preimage of a set under a partial function.
* `pfun.core`: Core of a set under a partial function.
* `pfun.graph`: Graph of a partial function `a →. β`as a `set (α × β)`.
* `pfun.graph'`: Graph of a partial function `a →. β`as a `rel α β`.

### `pfun α` as a monad

Monad operations:
* `pfun.pure`: The monad `pure` function, the constant `x` function.
* `pfun.bind`: The monad `bind` function, pointwise `part.bind`
* `pfun.map`: The monad `map` function, pointwise `part.map`.
-/


open Function

#print PFun /-
/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → part β`. -/
def PFun (α β : Type _) :=
  α → Part β
#align pfun PFun
-/

-- mathport name: «expr →. »
infixr:25 " →. " => PFun

namespace PFun

variable {α β γ δ ε ι : Type _}

instance : Inhabited (α →. β) :=
  ⟨fun a => Part.none⟩

#print PFun.Dom /-
/-- The domain of a partial function -/
def Dom (f : α →. β) : Set α :=
  { a | (f a).Dom }
#align pfun.dom PFun.Dom
-/

/- warning: pfun.mem_dom -> PFun.mem_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (x : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (PFun.Dom.{u1, u2} α β f)) (Exists.{succ u2} β (fun (y : β) => Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) y (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (x : α), Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (PFun.Dom.{u2, u1} α β f)) (Exists.{succ u1} β (fun (y : β) => Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) y (f x)))
Case conversion may be inaccurate. Consider using '#align pfun.mem_dom PFun.mem_domₓ'. -/
@[simp]
theorem mem_dom (f : α →. β) (x : α) : x ∈ Dom f ↔ ∃ y, y ∈ f x := by simp [dom, Part.dom_iff_mem]
#align pfun.mem_dom PFun.mem_dom

/- warning: pfun.dom_mk -> PFun.dom_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Prop) (f : forall (a : α), (p a) -> β), Eq.{succ u1} (Set.{u1} α) (PFun.Dom.{u1, u2} α β (fun (x : α) => Part.mk.{u2} β (p x) (f x))) (setOf.{u1} α (fun (x : α) => p x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : α -> Prop) (f : forall (a : α), (p a) -> β), Eq.{succ u2} (Set.{u2} α) (PFun.Dom.{u2, u1} α β (fun (x : α) => Part.mk.{u1} β (p x) (f x))) (setOf.{u2} α (fun (x : α) => p x))
Case conversion may be inaccurate. Consider using '#align pfun.dom_mk PFun.dom_mkₓ'. -/
@[simp]
theorem dom_mk (p : α → Prop) (f : ∀ a, p a → β) : (PFun.Dom fun x => ⟨p x, f x⟩) = { x | p x } :=
  rfl
#align pfun.dom_mk PFun.dom_mk

/- warning: pfun.dom_eq -> PFun.dom_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β), Eq.{succ u1} (Set.{u1} α) (PFun.Dom.{u1, u2} α β f) (setOf.{u1} α (fun (x : α) => Exists.{succ u2} β (fun (y : β) => Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) y (f x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β), Eq.{succ u2} (Set.{u2} α) (PFun.Dom.{u2, u1} α β f) (setOf.{u2} α (fun (x : α) => Exists.{succ u1} β (fun (y : β) => Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) y (f x))))
Case conversion may be inaccurate. Consider using '#align pfun.dom_eq PFun.dom_eqₓ'. -/
theorem dom_eq (f : α →. β) : Dom f = { x | ∃ y, y ∈ f x } :=
  Set.ext (mem_dom f)
#align pfun.dom_eq PFun.dom_eq

#print PFun.fn /-
/-- Evaluate a partial function -/
def fn (f : α →. β) (a : α) : Dom f a → β :=
  (f a).get
#align pfun.fn PFun.fn
-/

/- warning: pfun.fn_apply -> PFun.fn_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (a : α), Eq.{succ u2} ((PFun.Dom.{u1, u2} α β f a) -> β) (PFun.fn.{u1, u2} α β f a) (Part.get.{u2} β (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (a : α), Eq.{succ u1} ((PFun.Dom.{u2, u1} α β f a) -> β) (PFun.fn.{u2, u1} α β f a) (Part.get.{u1} β (f a))
Case conversion may be inaccurate. Consider using '#align pfun.fn_apply PFun.fn_applyₓ'. -/
@[simp]
theorem fn_apply (f : α →. β) (a : α) : f.fn a = (f a).get :=
  rfl
#align pfun.fn_apply PFun.fn_apply

#print PFun.evalOpt /-
/-- Evaluate a partial function to return an `option` -/
def evalOpt (f : α →. β) [D : DecidablePred (· ∈ Dom f)] (x : α) : Option β :=
  @Part.toOption _ _ (D x)
#align pfun.eval_opt PFun.evalOpt
-/

/- warning: pfun.ext' -> PFun.ext' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, u2} α β} {g : PFun.{u1, u2} α β}, (forall (a : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (PFun.Dom.{u1, u2} α β f)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (PFun.Dom.{u1, u2} α β g))) -> (forall (a : α) (p : PFun.Dom.{u1, u2} α β f a) (q : PFun.Dom.{u1, u2} α β g a), Eq.{succ u2} β (PFun.fn.{u1, u2} α β f a p) (PFun.fn.{u1, u2} α β g a q)) -> (Eq.{max (succ u1) (succ u2)} (PFun.{u1, u2} α β) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, u1} α β} {g : PFun.{u2, u1} α β}, (forall (a : α), Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (PFun.Dom.{u2, u1} α β f)) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (PFun.Dom.{u2, u1} α β g))) -> (forall (a : α) (p : PFun.Dom.{u2, u1} α β f a) (q : PFun.Dom.{u2, u1} α β g a), Eq.{succ u1} β (PFun.fn.{u2, u1} α β f a p) (PFun.fn.{u2, u1} α β g a q)) -> (Eq.{max (succ u2) (succ u1)} (PFun.{u2, u1} α β) f g)
Case conversion may be inaccurate. Consider using '#align pfun.ext' PFun.ext'ₓ'. -/
/-- Partial function extensionality -/
theorem ext' {f g : α →. β} (H1 : ∀ a, a ∈ Dom f ↔ a ∈ Dom g) (H2 : ∀ a p q, f.fn a p = g.fn a q) :
    f = g :=
  funext fun a => Part.ext' (H1 a) (H2 a)
#align pfun.ext' PFun.ext'

/- warning: pfun.ext -> PFun.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, u2} α β} {g : PFun.{u1, u2} α β}, (forall (a : α) (b : β), Iff (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (f a)) (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (g a))) -> (Eq.{max (succ u1) (succ u2)} (PFun.{u1, u2} α β) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, u1} α β} {g : PFun.{u2, u1} α β}, (forall (a : α) (b : β), Iff (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (f a)) (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (g a))) -> (Eq.{max (succ u2) (succ u1)} (PFun.{u2, u1} α β) f g)
Case conversion may be inaccurate. Consider using '#align pfun.ext PFun.extₓ'. -/
theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
  funext fun a => Part.ext (H a)
#align pfun.ext PFun.ext

#print PFun.asSubtype /-
/-- Turns a partial function into a function out of its domain. -/
def asSubtype (f : α →. β) (s : f.Dom) : β :=
  f.fn s s.2
#align pfun.as_subtype PFun.asSubtype
-/

#print PFun.equivSubtype /-
/-- The type of partial functions `α →. β` is equivalent to
the type of pairs `(p : α → Prop, f : subtype p → β)`. -/
def equivSubtype : (α →. β) ≃ Σp : α → Prop, Subtype p → β :=
  ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun f =>
    funext fun a => Part.eta _, fun ⟨p, f⟩ => by dsimp <;> congr <;> funext a <;> cases a <;> rfl⟩
#align pfun.equiv_subtype PFun.equivSubtype
-/

/- warning: pfun.as_subtype_eq_of_mem -> PFun.asSubtype_eq_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, u2} α β} {x : α} {y : β}, (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) y (f x)) -> (forall (domx : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (PFun.Dom.{u1, u2} α β f)), Eq.{succ u2} β (PFun.asSubtype.{u1, u2} α β f (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (PFun.Dom.{u1, u2} α β f)) x domx)) y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, u1} α β} {x : α} {y : β}, (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) y (f x)) -> (forall (domx : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (PFun.Dom.{u2, u1} α β f)), Eq.{succ u1} β (PFun.asSubtype.{u2, u1} α β f (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (PFun.Dom.{u2, u1} α β f)) x domx)) y)
Case conversion may be inaccurate. Consider using '#align pfun.as_subtype_eq_of_mem PFun.asSubtype_eq_of_memₓ'. -/
theorem asSubtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.Dom) :
    f.asSubtype ⟨x, domx⟩ = y :=
  Part.mem_unique (Part.get_mem _) fxy
#align pfun.as_subtype_eq_of_mem PFun.asSubtype_eq_of_mem

#print PFun.lift /-
/-- Turn a total function into a partial function. -/
protected def lift (f : α → β) : α →. β := fun a => Part.some (f a)
#align pfun.lift PFun.lift
-/

instance : Coe (α → β) (α →. β) :=
  ⟨PFun.lift⟩

@[simp]
theorem lift_eq_coe (f : α → β) : PFun.lift f = f :=
  rfl
#align pfun.lift_eq_coe PFun.lift_eq_coe

#print PFun.coe_val /-
@[simp]
theorem coe_val (f : α → β) (a : α) : (f : α →. β) a = Part.some (f a) :=
  rfl
#align pfun.coe_val PFun.coe_val
-/

/- warning: pfun.dom_coe -> PFun.dom_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{succ u1} (Set.{u1} α) (PFun.Dom.{u1, u2} α β ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (α -> β) (PFun.{u1, u2} α β) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (PFun.hasCoe.{u1, u2} α β)))) f)) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{succ u2} (Set.{u2} α) (PFun.Dom.{u2, u1} α β (PFun.lift.{u2, u1} α β f)) (Set.univ.{u2} α)
Case conversion may be inaccurate. Consider using '#align pfun.dom_coe PFun.dom_coeₓ'. -/
@[simp]
theorem dom_coe (f : α → β) : (f : α →. β).Dom = Set.univ :=
  rfl
#align pfun.dom_coe PFun.dom_coe

/- warning: pfun.coe_injective -> PFun.lift_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (α -> β) (PFun.{u1, u2} α β) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (PFun.hasCoe.{u1, u2} α β)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> β) (PFun.{u2, u1} α β) (PFun.lift.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align pfun.coe_injective PFun.lift_injectiveₓ'. -/
theorem lift_injective : Injective (coe : (α → β) → α →. β) := fun f g h =>
  funext fun a => Part.some_injective <| congr_fun h a
#align pfun.coe_injective PFun.lift_injective

#print PFun.graph /-
/-- Graph of a partial function `f` as the set of pairs `(x, f x)` where `x` is in the domain of
`f`. -/
def graph (f : α →. β) : Set (α × β) :=
  { p | p.2 ∈ f p.1 }
#align pfun.graph PFun.graph
-/

#print PFun.graph' /-
/-- Graph of a partial function as a relation. `x` and `y` are related iff `f x` is defined and
"equals" `y`. -/
def graph' (f : α →. β) : Rel α β := fun x y => y ∈ f x
#align pfun.graph' PFun.graph'
-/

#print PFun.ran /-
/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
def ran (f : α →. β) : Set β :=
  { b | ∃ a, b ∈ f a }
#align pfun.ran PFun.ran
-/

#print PFun.restrict /-
/-- Restrict a partial function to a smaller domain. -/
def restrict (f : α →. β) {p : Set α} (H : p ⊆ f.Dom) : α →. β := fun x =>
  (f x).restrict (x ∈ p) (@H x)
#align pfun.restrict PFun.restrict
-/

/- warning: pfun.mem_restrict -> PFun.mem_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, u2} α β} {s : Set.{u1} α} (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (PFun.Dom.{u1, u2} α β f)) (a : α) (b : β), Iff (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.restrict.{u1, u2} α β f s h a)) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, u1} α β} {s : Set.{u2} α} (h : HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (PFun.Dom.{u2, u1} α β f)) (a : α) (b : β), Iff (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.restrict.{u2, u1} α β f s h a)) (And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (f a)))
Case conversion may be inaccurate. Consider using '#align pfun.mem_restrict PFun.mem_restrictₓ'. -/
@[simp]
theorem mem_restrict {f : α →. β} {s : Set α} (h : s ⊆ f.Dom) (a : α) (b : β) :
    b ∈ f.restrict h a ↔ a ∈ s ∧ b ∈ f a := by simp [restrict]
#align pfun.mem_restrict PFun.mem_restrict

#print PFun.res /-
/-- Turns a function into a partial function with a prescribed domain. -/
def res (f : α → β) (s : Set α) : α →. β :=
  (PFun.lift f).restrict s.subset_univ
#align pfun.res PFun.res
-/

/- warning: pfun.mem_res -> PFun.mem_res is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (a : α) (b : β), Iff (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.res.{u1, u2} α β f s a)) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Eq.{succ u2} β (f a) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (a : α) (b : β), Iff (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.res.{u2, u1} α β f s a)) (And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (Eq.{succ u1} β (f a) b))
Case conversion may be inaccurate. Consider using '#align pfun.mem_res PFun.mem_resₓ'. -/
theorem mem_res (f : α → β) (s : Set α) (a : α) (b : β) : b ∈ res f s a ↔ a ∈ s ∧ f a = b := by
  simp [res, @eq_comm _ b]
#align pfun.mem_res PFun.mem_res

/- warning: pfun.res_univ -> PFun.res_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{max (succ u1) (succ u2)} (PFun.{u1, u2} α β) (PFun.res.{u1, u2} α β f (Set.univ.{u1} α)) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (α -> β) (PFun.{u1, u2} α β) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (PFun.hasCoe.{u1, u2} α β)))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{max (succ u2) (succ u1)} (PFun.{u2, u1} α β) (PFun.res.{u2, u1} α β f (Set.univ.{u2} α)) (PFun.lift.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align pfun.res_univ PFun.res_univₓ'. -/
theorem res_univ (f : α → β) : PFun.res f Set.univ = f :=
  rfl
#align pfun.res_univ PFun.res_univ

/- warning: pfun.dom_iff_graph -> PFun.dom_iff_graph is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (x : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (PFun.Dom.{u1, u2} α β f)) (Exists.{succ u2} β (fun (y : β) => Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β x y) (PFun.graph.{u1, u2} α β f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (x : α), Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (PFun.Dom.{u2, u1} α β f)) (Exists.{succ u1} β (fun (y : β) => Membership.mem.{max u1 u2, max u2 u1} (Prod.{u2, u1} α β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β x y) (PFun.graph.{u2, u1} α β f)))
Case conversion may be inaccurate. Consider using '#align pfun.dom_iff_graph PFun.dom_iff_graphₓ'. -/
theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.Dom ↔ ∃ y, (x, y) ∈ f.graph :=
  Part.dom_iff_mem
#align pfun.dom_iff_graph PFun.dom_iff_graph

#print PFun.lift_graph /-
theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
  show (∃ h : True, f a = b) ↔ f a = b by simp
#align pfun.lift_graph PFun.lift_graph
-/

#print PFun.pure /-
/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β := fun _ => Part.some x
#align pfun.pure PFun.pure
-/

#print PFun.bind /-
/-- The monad `bind` function, pointwise `part.bind` -/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ := fun a => (f a).bind fun b => g b a
#align pfun.bind PFun.bind
-/

/- warning: pfun.bind_apply -> PFun.bind_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : PFun.{u1, u2} α β) (g : β -> (PFun.{u1, u3} α γ)) (a : α), Eq.{succ u3} (Part.{u3} γ) (PFun.bind.{u1, u2, u3} α β γ f g a) (Part.bind.{u2, u3} β γ (f a) (fun (b : β) => g b a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : PFun.{u3, u2} α β) (g : β -> (PFun.{u3, u1} α γ)) (a : α), Eq.{succ u1} (Part.{u1} γ) (PFun.bind.{u3, u2, u1} α β γ f g a) (Part.bind.{u2, u1} β γ (f a) (fun (b : β) => g b a))
Case conversion may be inaccurate. Consider using '#align pfun.bind_apply PFun.bind_applyₓ'. -/
@[simp]
theorem bind_apply (f : α →. β) (g : β → α →. γ) (a : α) : f.bind g a = (f a).bind fun b => g b a :=
  rfl
#align pfun.bind_apply PFun.bind_apply

#print PFun.map /-
/-- The monad `map` function, pointwise `part.map` -/
def map (f : β → γ) (g : α →. β) : α →. γ := fun a => (g a).map f
#align pfun.map PFun.map
-/

instance : Monad (PFun α) where
  pure := @PFun.pure _
  bind := @PFun.bind _
  map := @PFun.map _

instance : LawfulMonad (PFun α)
    where
  bind_pure_comp_eq_map β γ f x := funext fun a => Part.bind_some_eq_map _ _
  id_map β f := by funext a <;> dsimp [Functor.map, PFun.map] <;> cases f a <;> rfl
  pure_bind β γ x f := funext fun a => Part.bind_some.{u_1, u_2} _ (f x)
  bind_assoc β γ δ f g k := funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a

/- warning: pfun.pure_defined -> PFun.pure_defined is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Set.{u1} α) (x : β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) p (PFun.Dom.{u1, u2} α β (PFun.pure.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : Set.{u2} α) (x : β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) p (PFun.Dom.{u2, u1} α β (PFun.pure.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align pfun.pure_defined PFun.pure_definedₓ'. -/
theorem pure_defined (p : Set α) (x : β) : p ⊆ (@PFun.pure α _ x).Dom :=
  p.subset_univ
#align pfun.pure_defined PFun.pure_defined

/- warning: pfun.bind_defined -> PFun.bind_defined is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u2}} (p : Set.{u1} α) {f : PFun.{u1, u2} α β} {g : β -> (PFun.{u1, u2} α γ)}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) p (PFun.Dom.{u1, u2} α β f)) -> (forall (x : β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) p (PFun.Dom.{u1, u2} α γ (g x))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) p (PFun.Dom.{u1, u2} α γ (Bind.bind.{u2, max u1 u2} (PFun.{u1, u2} α) (Monad.toHasBind.{u2, max u1 u2} (PFun.{u1, u2} α) (PFun.monad.{u1, u2} α)) β γ f g)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u1}} (p : Set.{u2} α) {f : PFun.{u2, u1} α β} {g : β -> (PFun.{u2, u1} α γ)}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) p (PFun.Dom.{u2, u1} α β f)) -> (forall (x : β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) p (PFun.Dom.{u2, u1} α γ (g x))) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) p (PFun.Dom.{u2, u1} α γ (Bind.bind.{u1, max u2 u1} (PFun.{u2, u1} α) (Monad.toBind.{u1, max u2 u1} (PFun.{u2, u1} α) (PFun.instMonadPFun.{u2, u1} α)) β γ f g)))
Case conversion may be inaccurate. Consider using '#align pfun.bind_defined PFun.bind_definedₓ'. -/
theorem bind_defined {α β γ} (p : Set α) {f : α →. β} {g : β → α →. γ} (H1 : p ⊆ f.Dom)
    (H2 : ∀ x, p ⊆ (g x).Dom) : p ⊆ (f >>= g).Dom := fun a ha =>
  (⟨H1 ha, H2 _ ha⟩ : (f >>= g).Dom a)
#align pfun.bind_defined PFun.bind_defined

#print PFun.fix /-
/-- First return map. Transforms a partial function `f : α →. β ⊕ α` into the partial function
`α →. β` which sends `a : α` to the first value in `β` it hits by iterating `f`, if such a value
exists. By abusing notation to illustrate, either `f a` is in the `β` part of `β ⊕ α` (in which
case `f.fix a` returns `f a`), or it is undefined (in which case `f.fix a` is undefined as well), or
it is in the `α` part of `β ⊕ α` (in which case we repeat the procedure, so `f.fix a` will return
`f.fix (f a)`). -/
def fix (f : α →. Sum β α) : α →. β := fun a =>
  Part.assert (Acc (fun x y => Sum.inr x ∈ f y) a) fun h =>
    @WellFounded.fixF _ (fun x y => Sum.inr x ∈ f y) _
      (fun a IH =>
        Part.assert (f a).Dom fun hf => by
          cases' e : (f a).get hf with b a' <;> [exact Part.some b, exact IH _ ⟨hf, e⟩])
      a h
#align pfun.fix PFun.fix
-/

/- warning: pfun.dom_of_mem_fix -> PFun.dom_of_mem_fix is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} β α)} {a : α} {b : β}, (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a)) -> (Part.Dom.{max u2 u1} (Sum.{u2, u1} β α) (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} β α)} {a : α} {b : β}, (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a)) -> (Part.Dom.{max u2 u1} (Sum.{u1, u2} β α) (f a))
Case conversion may be inaccurate. Consider using '#align pfun.dom_of_mem_fix PFun.dom_of_mem_fixₓ'. -/
theorem dom_of_mem_fix {f : α →. Sum β α} {a : α} {b : β} (h : b ∈ f.fix a) : (f a).Dom :=
  by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  rw [WellFounded.fixF_eq] at h₂ <;> exact h₂.fst.fst
#align pfun.dom_of_mem_fix PFun.dom_of_mem_fix

/- warning: pfun.mem_fix_iff -> PFun.mem_fix_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} β α)} {a : α} {b : β}, Iff (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a)) (Or (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inl.{u2, u1} β α b) (f a)) (Exists.{succ u1} α (fun (a' : α) => And (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inr.{u2, u1} β α a') (f a)) (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a')))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} β α)} {a : α} {b : β}, Iff (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a)) (Or (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u1 u2} (Sum.{u1, u2} β α)) (Sum.inl.{u1, u2} β α b) (f a)) (Exists.{succ u2} α (fun (a' : α) => And (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} β α)) (Sum.inr.{u1, u2} β α a') (f a)) (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a')))))
Case conversion may be inaccurate. Consider using '#align pfun.mem_fix_iff PFun.mem_fix_iffₓ'. -/
theorem mem_fix_iff {f : α →. Sum β α} {a : α} {b : β} :
    b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
  ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fixF_eq] at h₂
    simp at h₂
    cases' h₂ with h₂ h₃
    cases' e : (f a).get h₂ with b' a' <;> simp [e] at h₃
    · subst b'
      refine' Or.inl ⟨h₂, e⟩
    · exact Or.inr ⟨a', ⟨_, e⟩, Part.mem_assert _ h₃⟩, fun h =>
    by
    simp [fix]
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine' ⟨⟨_, fun y h' => _⟩, _⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
      · rw [WellFounded.fixF_eq]
        simp [h₁, h₂]
    · simp [fix] at h₃
      cases' h₃ with h₃ h₄
      refine' ⟨⟨_, fun y h' => _⟩, _⟩
      · injection Part.mem_unique h h' with e
        exact e ▸ h₃
      · cases' h with h₁ h₂
        rw [WellFounded.fixF_eq]
        simp [h₁, h₂, h₄]⟩
#align pfun.mem_fix_iff PFun.mem_fix_iff

/- warning: pfun.fix_stop -> PFun.fix_stop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} β α)} {b : β} {a : α}, (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inl.{u2, u1} β α b) (f a)) -> (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} β α)} {b : β} {a : α}, (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u1 u2} (Sum.{u1, u2} β α)) (Sum.inl.{u1, u2} β α b) (f a)) -> (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a))
Case conversion may be inaccurate. Consider using '#align pfun.fix_stop PFun.fix_stopₓ'. -/
/-- If advancing one step from `a` leads to `b : β`, then `f.fix a = b` -/
theorem fix_stop {f : α →. Sum β α} {b : β} {a : α} (hb : Sum.inl b ∈ f a) : b ∈ f.fix a :=
  by
  rw [PFun.mem_fix_iff]
  exact Or.inl hb
#align pfun.fix_stop PFun.fix_stop

/- warning: pfun.fix_fwd_eq -> PFun.fix_fwd_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} β α)} {a : α} {a' : α}, (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inr.{u2, u1} β α a') (f a)) -> (Eq.{succ u2} (Part.{u2} β) (PFun.fix.{u1, u2} α β f a) (PFun.fix.{u1, u2} α β f a'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} β α)} {a : α} {a' : α}, (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} β α)) (Sum.inr.{u1, u2} β α a') (f a)) -> (Eq.{succ u1} (Part.{u1} β) (PFun.fix.{u2, u1} α β f a) (PFun.fix.{u2, u1} α β f a'))
Case conversion may be inaccurate. Consider using '#align pfun.fix_fwd_eq PFun.fix_fwd_eqₓ'. -/
/-- If advancing one step from `a` on `f` leads to `a' : α`, then `f.fix a = f.fix a'` -/
theorem fix_fwd_eq {f : α →. Sum β α} {a a' : α} (ha' : Sum.inr a' ∈ f a) : f.fix a = f.fix a' :=
  by
  ext b; constructor
  · intro h
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    exact e'
  · intro h
    rw [PFun.mem_fix_iff]
    right
    use a'
    exact ⟨ha', h⟩
#align pfun.fix_fwd_eq PFun.fix_fwd_eq

/- warning: pfun.fix_fwd -> PFun.fix_fwd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} β α)} {b : β} {a : α} {a' : α}, (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a)) -> (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inr.{u2, u1} β α a') (f a)) -> (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} β α)} {b : β} {a : α} {a' : α}, (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a)) -> (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} β α)) (Sum.inr.{u1, u2} β α a') (f a)) -> (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a'))
Case conversion may be inaccurate. Consider using '#align pfun.fix_fwd PFun.fix_fwdₓ'. -/
theorem fix_fwd {f : α →. Sum β α} {b : β} {a a' : α} (hb : b ∈ f.fix a) (ha' : Sum.inr a' ∈ f a) :
    b ∈ f.fix a' := by rwa [← fix_fwd_eq ha']
#align pfun.fix_fwd PFun.fix_fwd

#print PFun.fixInduction /-
/-- A recursion principle for `pfun.fix`. -/
@[elab_as_elim]
def fixInduction {C : α → Sort _} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') : C a :=
  by
  have h₂ := (Part.mem_assert_iff.1 h).snd; generalize_proofs h₁  at h₂; clear h
  induction' h₁ with a ha IH
  have h : b ∈ f.fix a := Part.mem_assert_iff.2 ⟨⟨a, ha⟩, h₂⟩
  exact H a h fun a' fa' => IH a' fa' (Part.mem_assert_iff.1 (fix_fwd h fa')).snd
#align pfun.fix_induction PFun.fixInduction
-/

/- warning: pfun.fix_induction_spec -> PFun.fixInduction_spec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : α -> Sort.{u3}} {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} β α)} {b : β} {a : α} (h : Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a)) (H : forall (a' : α), (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a')) -> (forall (a'' : α), (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inr.{u2, u1} β α a'') (f a')) -> (C a'')) -> (C a')), Eq.{u3} (C a) (PFun.fixInduction.{u1, u2, u3} α β C f b a h H) (H a h (fun (a' : α) (h' : Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inr.{u2, u1} β α a') (f a)) => PFun.fixInduction.{u1, u2, u3} α β (fun (_x : α) => C _x) f b a' (PFun.fix_fwd.{u1, u2} α β f b a a' h h') H))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {C : α -> Sort.{u3}} {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} β α)} {b : β} {a : α} (h : Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a)) (H : forall (a' : α), (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a')) -> (forall (a'' : α), (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} β α)) (Sum.inr.{u1, u2} β α a'') (f a')) -> (C a'')) -> (C a')), Eq.{u3} (C a) (PFun.fixInduction.{u2, u1, u3} α β C f b a h H) (H a h (fun (a' : α) (h' : Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} β α)) (Sum.inr.{u1, u2} β α a') (f a)) => PFun.fixInduction.{u2, u1, u3} α β (fun (_x : α) => C _x) f b a' (PFun.fix_fwd.{u1, u2} α β f b a a' h h') H))
Case conversion may be inaccurate. Consider using '#align pfun.fix_induction_spec PFun.fixInduction_specₓ'. -/
theorem fixInduction_spec {C : α → Sort _} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') :
    @fixInduction _ _ C _ _ _ h H = H a h fun a' h' => fixInduction (fix_fwd h h') H :=
  by
  unfold fix_induction
  generalize_proofs ha
  induction ha
  rfl
#align pfun.fix_induction_spec PFun.fixInduction_spec

#print PFun.fixInduction' /-
/-- Another induction lemma for `b ∈ f.fix a` which allows one to prove a predicate `P` holds for
`a` given that `f a` inherits `P` from `a` and `P` holds for preimages of `b`.
-/
@[elab_as_elim]
def fixInduction' {C : α → Sort _} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) : C a :=
  by
  refine' fix_induction h fun a' h ih => _
  cases' e : (f a').get (dom_of_mem_fix h) with b' a'' <;> replace e : _ ∈ f a' := ⟨_, e⟩
  · apply hbase
    convert e
    exact Part.mem_unique h (fix_stop e)
  · exact hind _ _ (fix_fwd h e) e (ih _ e)
#align pfun.fix_induction' PFun.fixInduction'
-/

/- warning: pfun.fix_induction'_stop -> PFun.fixInduction'_stop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : α -> Sort.{u3}} {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} β α)} {b : β} {a : α} (h : Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a)) (fa : Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inl.{u2, u1} β α b) (f a)) (hbase : forall (a_final : α), (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inl.{u2, u1} β α b) (f a_final)) -> (C a_final)) (hind : forall (a₀ : α) (a₁ : α), (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a₁)) -> (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inr.{u2, u1} β α a₁) (f a₀)) -> (C a₁) -> (C a₀)), Eq.{u3} (C a) (PFun.fixInduction'.{u1, u2, u3} α β C f b a h hbase hind) (hbase a fa)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {C : α -> Sort.{u3}} {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} β α)} {b : β} {a : α} (h : Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a)) (fa : Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u1 u2} (Sum.{u1, u2} β α)) (Sum.inl.{u1, u2} β α b) (f a)) (hbase : forall (a_final : α), (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u1 u2} (Sum.{u1, u2} β α)) (Sum.inl.{u1, u2} β α b) (f a_final)) -> (C a_final)) (hind : forall (a₀ : α) (a₁ : α), (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a₁)) -> (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} β α)) (Sum.inr.{u1, u2} β α a₁) (f a₀)) -> (C a₁) -> (C a₀)), Eq.{u3} (C a) (PFun.fixInduction'.{u2, u1, u3} α β C f b a h hbase hind) (hbase a fa)
Case conversion may be inaccurate. Consider using '#align pfun.fix_induction'_stop PFun.fixInduction'_stopₓ'. -/
theorem fixInduction'_stop {C : α → Sort _} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (fa : Sum.inl b ∈ f a) (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hbase a fa :=
  by
  unfold fix_induction'
  rw [fix_induction_spec]
  simp [Part.get_eq_of_mem fa]
#align pfun.fix_induction'_stop PFun.fixInduction'_stop

/- warning: pfun.fix_induction'_fwd -> PFun.fixInduction'_fwd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : α -> Sort.{u3}} {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} β α)} {b : β} {a : α} {a' : α} (h : Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a)) (h' : Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a')) (fa : Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inr.{u2, u1} β α a') (f a)) (hbase : forall (a_final : α), (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inl.{u2, u1} β α b) (f a_final)) -> (C a_final)) (hind : forall (a₀ : α) (a₁ : α), (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (PFun.fix.{u1, u2} α β f a₁)) -> (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} β α) (Part.{max u2 u1} (Sum.{u2, u1} β α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} β α)) (Sum.inr.{u2, u1} β α a₁) (f a₀)) -> (C a₁) -> (C a₀)), Eq.{u3} (C a) (PFun.fixInduction'.{u1, u2, u3} α β C f b a h hbase hind) (hind a a' h' fa (PFun.fixInduction'.{u1, u2, u3} α β (fun (_x : α) => C _x) f b a' h' hbase hind))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {C : α -> Sort.{u3}} {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} β α)} {b : β} {a : α} {a' : α} (h : Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a)) (h' : Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a')) (fa : Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} β α)) (Sum.inr.{u1, u2} β α a') (f a)) (hbase : forall (a_final : α), (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u1 u2} (Sum.{u1, u2} β α)) (Sum.inl.{u1, u2} β α b) (f a_final)) -> (C a_final)) (hind : forall (a₀ : α) (a₁ : α), (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) b (PFun.fix.{u2, u1} α β f a₁)) -> (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} β α) (Part.{max u2 u1} (Sum.{u1, u2} β α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} β α)) (Sum.inr.{u1, u2} β α a₁) (f a₀)) -> (C a₁) -> (C a₀)), Eq.{u3} (C a) (PFun.fixInduction'.{u2, u1, u3} α β C f b a h hbase hind) (hind a a' h' fa (PFun.fixInduction'.{u2, u1, u3} α β (fun (_x : α) => C _x) f b a' h' hbase hind))
Case conversion may be inaccurate. Consider using '#align pfun.fix_induction'_fwd PFun.fixInduction'_fwdₓ'. -/
theorem fixInduction'_fwd {C : α → Sort _} {f : α →. Sum β α} {b : β} {a a' : α} (h : b ∈ f.fix a)
    (h' : b ∈ f.fix a') (fa : Sum.inr a' ∈ f a)
    (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hind a a' h' fa (fixInduction' h' hbase hind) :=
  by
  unfold fix_induction'
  rw [fix_induction_spec]
  simpa [Part.get_eq_of_mem fa]
#align pfun.fix_induction'_fwd PFun.fixInduction'_fwd

variable (f : α →. β)

#print PFun.image /-
/-- Image of a set under a partial function. -/
def image (s : Set α) : Set β :=
  f.graph'.image s
#align pfun.image PFun.image
-/

/- warning: pfun.image_def -> PFun.image_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (PFun.image.{u1, u2} α β f s) (setOf.{u2} β (fun (y : β) => Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) y (f x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (PFun.image.{u2, u1} α β f s) (setOf.{u1} β (fun (y : β) => Exists.{succ u2} α (fun (x : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) y (f x)))))
Case conversion may be inaccurate. Consider using '#align pfun.image_def PFun.image_defₓ'. -/
theorem image_def (s : Set α) : f.image s = { y | ∃ x ∈ s, y ∈ f x } :=
  rfl
#align pfun.image_def PFun.image_def

/- warning: pfun.mem_image -> PFun.mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (y : β) (s : Set.{u1} α), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (PFun.image.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) y (f x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (y : β) (s : Set.{u2} α), Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (PFun.image.{u2, u1} α β f s)) (Exists.{succ u2} α (fun (x : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (Membership.mem.{u1, u1} β (Part.{u1} β) (Part.instMembershipPart.{u1} β) y (f x))))
Case conversion may be inaccurate. Consider using '#align pfun.mem_image PFun.mem_imageₓ'. -/
theorem mem_image (y : β) (s : Set α) : y ∈ f.image s ↔ ∃ x ∈ s, y ∈ f x :=
  Iff.rfl
#align pfun.mem_image PFun.mem_image

/- warning: pfun.image_mono -> PFun.image_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (PFun.image.{u1, u2} α β f s) (PFun.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) {s : Set.{u2} α} {t : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (PFun.image.{u2, u1} α β f s) (PFun.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align pfun.image_mono PFun.image_monoₓ'. -/
theorem image_mono {s t : Set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
  Rel.image_mono _ h
#align pfun.image_mono PFun.image_mono

/- warning: pfun.image_inter -> PFun.image_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (PFun.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (PFun.image.{u1, u2} α β f s) (PFun.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (s : Set.{u2} α) (t : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (PFun.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (PFun.image.{u2, u1} α β f s) (PFun.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align pfun.image_inter PFun.image_interₓ'. -/
theorem image_inter (s t : Set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
  Rel.image_inter _ s t
#align pfun.image_inter PFun.image_inter

/- warning: pfun.image_union -> PFun.image_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (PFun.image.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (PFun.image.{u1, u2} α β f s) (PFun.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (s : Set.{u2} α) (t : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (PFun.image.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (PFun.image.{u2, u1} α β f s) (PFun.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align pfun.image_union PFun.image_unionₓ'. -/
theorem image_union (s t : Set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
  Rel.image_union _ s t
#align pfun.image_union PFun.image_union

#print PFun.preimage /-
/-- Preimage of a set under a partial function. -/
def preimage (s : Set β) : Set α :=
  Rel.image (fun x y => x ∈ f y) s
#align pfun.preimage PFun.preimage
-/

/- warning: pfun.preimage_def -> PFun.Preimage_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.preimage.{u1, u2} α β f s) (setOf.{u1} α (fun (x : α) => Exists.{succ u2} β (fun (y : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) => Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) y (f x)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.preimage.{u1, u2} α β f s) (setOf.{u1} α (fun (x : α) => Exists.{succ u2} β (fun (y : β) => And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y s) (Membership.mem.{u2, u2} β (Part.{u2} β) (Part.instMembershipPart.{u2} β) y (f x)))))
Case conversion may be inaccurate. Consider using '#align pfun.preimage_def PFun.Preimage_defₓ'. -/
theorem Preimage_def (s : Set β) : f.Preimage s = { x | ∃ y ∈ s, y ∈ f x } :=
  rfl
#align pfun.preimage_def PFun.Preimage_def

/- warning: pfun.mem_preimage -> PFun.mem_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β) (x : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (PFun.preimage.{u1, u2} α β f s)) (Exists.{succ u2} β (fun (y : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) => Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) y (f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β) (x : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (PFun.preimage.{u1, u2} α β f s)) (Exists.{succ u2} β (fun (y : β) => And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y s) (Membership.mem.{u2, u2} β (Part.{u2} β) (Part.instMembershipPart.{u2} β) y (f x))))
Case conversion may be inaccurate. Consider using '#align pfun.mem_preimage PFun.mem_preimageₓ'. -/
@[simp]
theorem mem_preimage (s : Set β) (x : α) : x ∈ f.Preimage s ↔ ∃ y ∈ s, y ∈ f x :=
  Iff.rfl
#align pfun.mem_preimage PFun.mem_preimage

#print PFun.preimage_subset_dom /-
theorem preimage_subset_dom (s : Set β) : f.Preimage s ⊆ f.Dom := fun x ⟨y, ys, fxy⟩ =>
  Part.dom_iff_mem.mpr ⟨y, fxy⟩
#align pfun.preimage_subset_dom PFun.preimage_subset_dom
-/

#print PFun.preimage_mono /-
theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f.Preimage s ⊆ f.Preimage t :=
  Rel.preimage_mono _ h
#align pfun.preimage_mono PFun.preimage_mono
-/

/- warning: pfun.preimage_inter -> PFun.preimage_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (PFun.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (PFun.preimage.{u1, u2} α β f s) (PFun.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (PFun.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (PFun.preimage.{u1, u2} α β f s) (PFun.preimage.{u1, u2} α β f t))
Case conversion may be inaccurate. Consider using '#align pfun.preimage_inter PFun.preimage_interₓ'. -/
theorem preimage_inter (s t : Set β) : f.Preimage (s ∩ t) ⊆ f.Preimage s ∩ f.Preimage t :=
  Rel.preimage_inter _ s t
#align pfun.preimage_inter PFun.preimage_inter

/- warning: pfun.preimage_union -> PFun.preimage_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.preimage.{u1, u2} α β f (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (PFun.preimage.{u1, u2} α β f s) (PFun.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.preimage.{u1, u2} α β f (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (PFun.preimage.{u1, u2} α β f s) (PFun.preimage.{u1, u2} α β f t))
Case conversion may be inaccurate. Consider using '#align pfun.preimage_union PFun.preimage_unionₓ'. -/
theorem preimage_union (s t : Set β) : f.Preimage (s ∪ t) = f.Preimage s ∪ f.Preimage t :=
  Rel.preimage_union _ s t
#align pfun.preimage_union PFun.preimage_union

/- warning: pfun.preimage_univ -> PFun.preimage_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β), Eq.{succ u1} (Set.{u1} α) (PFun.preimage.{u1, u2} α β f (Set.univ.{u2} β)) (PFun.Dom.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β), Eq.{succ u2} (Set.{u2} α) (PFun.preimage.{u2, u1} α β f (Set.univ.{u1} β)) (PFun.Dom.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align pfun.preimage_univ PFun.preimage_univₓ'. -/
theorem preimage_univ : f.Preimage Set.univ = f.Dom := by ext <;> simp [mem_preimage, mem_dom]
#align pfun.preimage_univ PFun.preimage_univ

#print PFun.coe_preimage /-
theorem coe_preimage (f : α → β) (s : Set β) : (f : α →. β).Preimage s = f ⁻¹' s := by ext <;> simp
#align pfun.coe_preimage PFun.coe_preimage
-/

#print PFun.core /-
/-- Core of a set `s : set β` with respect to a partial function `f : α →. β`. Set of all `a : α`
such that `f a ∈ s`, if `f a` is defined. -/
def core (s : Set β) : Set α :=
  f.graph'.core s
#align pfun.core PFun.core
-/

#print PFun.core_def /-
theorem core_def (s : Set β) : f.core s = { x | ∀ y, y ∈ f x → y ∈ s } :=
  rfl
#align pfun.core_def PFun.core_def
-/

#print PFun.mem_core /-
@[simp]
theorem mem_core (x : α) (s : Set β) : x ∈ f.core s ↔ ∀ y, y ∈ f x → y ∈ s :=
  Iff.rfl
#align pfun.mem_core PFun.mem_core
-/

/- warning: pfun.compl_dom_subset_core -> PFun.compl_dom_subset_core is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (PFun.Dom.{u1, u2} α β f)) (PFun.core.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (PFun.Dom.{u1, u2} α β f)) (PFun.core.{u1, u2} α β f s)
Case conversion may be inaccurate. Consider using '#align pfun.compl_dom_subset_core PFun.compl_dom_subset_coreₓ'. -/
theorem compl_dom_subset_core (s : Set β) : f.Domᶜ ⊆ f.core s := fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx
#align pfun.compl_dom_subset_core PFun.compl_dom_subset_core

#print PFun.core_mono /-
theorem core_mono {s t : Set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
  Rel.core_mono _ h
#align pfun.core_mono PFun.core_mono
-/

/- warning: pfun.core_inter -> PFun.core_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.core.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (PFun.core.{u1, u2} α β f s) (PFun.core.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.core.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (PFun.core.{u1, u2} α β f s) (PFun.core.{u1, u2} α β f t))
Case conversion may be inaccurate. Consider using '#align pfun.core_inter PFun.core_interₓ'. -/
theorem core_inter (s t : Set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
  Rel.core_inter _ s t
#align pfun.core_inter PFun.core_inter

/- warning: pfun.mem_core_res -> PFun.mem_core_res is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u2} β) (x : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (PFun.core.{u1, u2} α β (PFun.res.{u1, u2} α β f s) t)) ((Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u1} β) (x : α), Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (PFun.core.{u2, u1} α β (PFun.res.{u2, u1} α β f s) t)) ((Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) t))
Case conversion may be inaccurate. Consider using '#align pfun.mem_core_res PFun.mem_core_resₓ'. -/
theorem mem_core_res (f : α → β) (s : Set α) (t : Set β) (x : α) :
    x ∈ (res f s).core t ↔ x ∈ s → f x ∈ t := by simp [mem_core, mem_res]
#align pfun.mem_core_res PFun.mem_core_res

section

open Classical

/- warning: pfun.core_res -> PFun.core_res is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.core.{u1, u2} α β (PFun.res.{u1, u2} α β f s) t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (Set.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u1} β), Eq.{succ u2} (Set.{u2} α) (PFun.core.{u2, u1} α β (PFun.res.{u2, u1} α β f s) t) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (Set.preimage.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align pfun.core_res PFun.core_resₓ'. -/
theorem core_res (f : α → β) (s : Set α) (t : Set β) : (res f s).core t = sᶜ ∪ f ⁻¹' t :=
  by
  ext
  rw [mem_core_res]
  by_cases h : x ∈ s <;> simp [h]
#align pfun.core_res PFun.core_res

end

#print PFun.core_restrict /-
theorem core_restrict (f : α → β) (s : Set β) : (f : α →. β).core s = s.Preimage f := by
  ext x <;> simp [core_def]
#align pfun.core_restrict PFun.core_restrict
-/

/- warning: pfun.preimage_subset_core -> PFun.preimage_subset_core is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (PFun.preimage.{u1, u2} α β f s) (PFun.core.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (s : Set.{u1} β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (PFun.preimage.{u2, u1} α β f s) (PFun.core.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align pfun.preimage_subset_core PFun.preimage_subset_coreₓ'. -/
theorem preimage_subset_core (f : α →. β) (s : Set β) : f.Preimage s ⊆ f.core s :=
  fun x ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys
#align pfun.preimage_subset_core PFun.preimage_subset_core

/- warning: pfun.preimage_eq -> PFun.preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.preimage.{u1, u2} α β f s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (PFun.core.{u1, u2} α β f s) (PFun.Dom.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (s : Set.{u1} β), Eq.{succ u2} (Set.{u2} α) (PFun.preimage.{u2, u1} α β f s) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (PFun.core.{u2, u1} α β f s) (PFun.Dom.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align pfun.preimage_eq PFun.preimage_eqₓ'. -/
theorem preimage_eq (f : α →. β) (s : Set β) : f.Preimage s = f.core s ∩ f.Dom :=
  Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y ∈ s := xcore _ (Part.get_mem _)
    show x ∈ f.Preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩
#align pfun.preimage_eq PFun.preimage_eq

/- warning: pfun.core_eq -> PFun.core_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (PFun.core.{u1, u2} α β f s) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (PFun.preimage.{u1, u2} α β f s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (PFun.Dom.{u1, u2} α β f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (s : Set.{u1} β), Eq.{succ u2} (Set.{u2} α) (PFun.core.{u2, u1} α β f s) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (PFun.preimage.{u2, u1} α β f s) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) (PFun.Dom.{u2, u1} α β f)))
Case conversion may be inaccurate. Consider using '#align pfun.core_eq PFun.core_eqₓ'. -/
theorem core_eq (f : α →. β) (s : Set β) : f.core s = f.Preimage s ∪ f.Domᶜ := by
  rw [preimage_eq, Set.union_distrib_right, Set.union_comm (dom f), Set.compl_union_self,
    Set.inter_univ, Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]
#align pfun.core_eq PFun.core_eq

/- warning: pfun.preimage_as_subtype -> PFun.preimage_as_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (PFun.Dom.{u1, u2} α β f))) (Set.preimage.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (PFun.Dom.{u1, u2} α β f)) β (PFun.asSubtype.{u1, u2} α β f) s) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (PFun.Dom.{u1, u2} α β f)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (PFun.Dom.{u1, u2} α β f))) (PFun.preimage.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β) (s : Set.{u1} β), Eq.{succ u2} (Set.{u2} (Set.Elem.{u2} α (PFun.Dom.{u2, u1} α β f))) (Set.preimage.{u2, u1} (Set.Elem.{u2} α (PFun.Dom.{u2, u1} α β f)) β (PFun.asSubtype.{u2, u1} α β f) s) (Set.preimage.{u2, u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (PFun.Dom.{u2, u1} α β f))) α (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (PFun.Dom.{u2, u1} α β f))) (PFun.preimage.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align pfun.preimage_as_subtype PFun.preimage_as_subtypeₓ'. -/
theorem preimage_as_subtype (f : α →. β) (s : Set β) :
    f.asSubtype ⁻¹' s = Subtype.val ⁻¹' f.Preimage s :=
  by
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, PFun.asSubtype, PFun.mem_preimage]
  show f.fn x.val _ ∈ s ↔ ∃ y ∈ s, y ∈ f x.val
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property ∈ f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys
#align pfun.preimage_as_subtype PFun.preimage_as_subtype

#print PFun.toSubtype /-
/-- Turns a function into a partial function to a subtype. -/
def toSubtype (p : β → Prop) (f : α → β) : α →. Subtype p := fun a => ⟨p (f a), Subtype.mk _⟩
#align pfun.to_subtype PFun.toSubtype
-/

/- warning: pfun.dom_to_subtype -> PFun.dom_to_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : β -> Prop) (f : α -> β), Eq.{succ u1} (Set.{u1} α) (PFun.Dom.{u1, u2} α (Subtype.{succ u2} β p) (PFun.toSubtype.{u1, u2} α β p f)) (setOf.{u1} α (fun (a : α) => p (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : β -> Prop) (f : α -> β), Eq.{succ u2} (Set.{u2} α) (PFun.Dom.{u2, u1} α (Subtype.{succ u1} β p) (PFun.toSubtype.{u2, u1} α β p f)) (setOf.{u2} α (fun (a : α) => p (f a)))
Case conversion may be inaccurate. Consider using '#align pfun.dom_to_subtype PFun.dom_to_subtypeₓ'. -/
@[simp]
theorem dom_to_subtype (p : β → Prop) (f : α → β) : (toSubtype p f).Dom = { a | p (f a) } :=
  rfl
#align pfun.dom_to_subtype PFun.dom_to_subtype

#print PFun.to_subtype_apply /-
@[simp]
theorem to_subtype_apply (p : β → Prop) (f : α → β) (a : α) :
    toSubtype p f a = ⟨p (f a), Subtype.mk _⟩ :=
  rfl
#align pfun.to_subtype_apply PFun.to_subtype_apply
-/

#print PFun.dom_to_subtype_apply_iff /-
theorem dom_to_subtype_apply_iff {p : β → Prop} {f : α → β} {a : α} :
    (toSubtype p f a).Dom ↔ p (f a) :=
  Iff.rfl
#align pfun.dom_to_subtype_apply_iff PFun.dom_to_subtype_apply_iff
-/

#print PFun.mem_to_subtype_iff /-
theorem mem_to_subtype_iff {p : β → Prop} {f : α → β} {a : α} {b : Subtype p} :
    b ∈ toSubtype p f a ↔ ↑b = f a := by
  rw [to_subtype_apply, Part.mem_mk_iff, exists_subtype_mk_eq_iff, eq_comm]
#align pfun.mem_to_subtype_iff PFun.mem_to_subtype_iff
-/

#print PFun.id /-
/-- The identity as a partial function -/
protected def id (α : Type _) : α →. α :=
  Part.some
#align pfun.id PFun.id
-/

#print PFun.coe_id /-
@[simp]
theorem coe_id (α : Type _) : ((id : α → α) : α →. α) = PFun.id α :=
  rfl
#align pfun.coe_id PFun.coe_id
-/

#print PFun.id_apply /-
@[simp]
theorem id_apply (a : α) : PFun.id α a = Part.some a :=
  rfl
#align pfun.id_apply PFun.id_apply
-/

#print PFun.comp /-
/-- Composition of partial functions as a partial function. -/
def comp (f : β →. γ) (g : α →. β) : α →. γ := fun a => (g a).bind f
#align pfun.comp PFun.comp
-/

/- warning: pfun.comp_apply -> PFun.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : PFun.{u2, u3} β γ) (g : PFun.{u1, u2} α β) (a : α), Eq.{succ u3} (Part.{u3} γ) (PFun.comp.{u1, u2, u3} α β γ f g a) (Part.bind.{u2, u3} β γ (g a) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : PFun.{u3, u2} β γ) (g : PFun.{u1, u3} α β) (a : α), Eq.{succ u2} (Part.{u2} γ) (PFun.comp.{u1, u3, u2} α β γ f g a) (Part.bind.{u3, u2} β γ (g a) f)
Case conversion may be inaccurate. Consider using '#align pfun.comp_apply PFun.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : β →. γ) (g : α →. β) (a : α) : f.comp g a = (g a).bind f :=
  rfl
#align pfun.comp_apply PFun.comp_apply

/- warning: pfun.id_comp -> PFun.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (PFun.{u1, u2} α β) (PFun.comp.{u1, u2, u2} α β β (PFun.id.{u2} β) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (PFun.{u2, u1} α β) (PFun.comp.{u2, u1, u1} α β β (PFun.id.{u1} β) f) f
Case conversion may be inaccurate. Consider using '#align pfun.id_comp PFun.id_compₓ'. -/
@[simp]
theorem id_comp (f : α →. β) : (PFun.id β).comp f = f :=
  ext fun _ _ => by simp
#align pfun.id_comp PFun.id_comp

/- warning: pfun.comp_id -> PFun.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : PFun.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (PFun.{u1, u2} α β) (PFun.comp.{u1, u1, u2} α α β f (PFun.id.{u1} α)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : PFun.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (PFun.{u2, u1} α β) (PFun.comp.{u2, u2, u1} α α β f (PFun.id.{u2} α)) f
Case conversion may be inaccurate. Consider using '#align pfun.comp_id PFun.comp_idₓ'. -/
@[simp]
theorem comp_id (f : α →. β) : f.comp (PFun.id α) = f :=
  ext fun _ _ => by simp
#align pfun.comp_id PFun.comp_id

/- warning: pfun.dom_comp -> PFun.dom_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : PFun.{u2, u3} β γ) (g : PFun.{u1, u2} α β), Eq.{succ u1} (Set.{u1} α) (PFun.Dom.{u1, u3} α γ (PFun.comp.{u1, u2, u3} α β γ f g)) (PFun.preimage.{u1, u2} α β g (PFun.Dom.{u2, u3} β γ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : PFun.{u3, u2} β γ) (g : PFun.{u1, u3} α β), Eq.{succ u1} (Set.{u1} α) (PFun.Dom.{u1, u2} α γ (PFun.comp.{u1, u3, u2} α β γ f g)) (PFun.preimage.{u1, u3} α β g (PFun.Dom.{u3, u2} β γ f))
Case conversion may be inaccurate. Consider using '#align pfun.dom_comp PFun.dom_compₓ'. -/
@[simp]
theorem dom_comp (f : β →. γ) (g : α →. β) : (f.comp g).Dom = g.Preimage f.Dom :=
  by
  ext
  simp_rw [mem_preimage, mem_dom, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_right]
  rw [exists_comm]
  simp_rw [and_comm]
#align pfun.dom_comp PFun.dom_comp

/- warning: pfun.preimage_comp -> PFun.preimage_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : PFun.{u2, u3} β γ) (g : PFun.{u1, u2} α β) (s : Set.{u3} γ), Eq.{succ u1} (Set.{u1} α) (PFun.preimage.{u1, u3} α γ (PFun.comp.{u1, u2, u3} α β γ f g) s) (PFun.preimage.{u1, u2} α β g (PFun.preimage.{u2, u3} β γ f s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : PFun.{u3, u2} β γ) (g : PFun.{u1, u3} α β) (s : Set.{u2} γ), Eq.{succ u1} (Set.{u1} α) (PFun.preimage.{u1, u2} α γ (PFun.comp.{u1, u3, u2} α β γ f g) s) (PFun.preimage.{u1, u3} α β g (PFun.preimage.{u3, u2} β γ f s))
Case conversion may be inaccurate. Consider using '#align pfun.preimage_comp PFun.preimage_compₓ'. -/
@[simp]
theorem preimage_comp (f : β →. γ) (g : α →. β) (s : Set γ) :
    (f.comp g).Preimage s = g.Preimage (f.Preimage s) :=
  by
  ext
  simp_rw [mem_preimage, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_right, ←
    exists_and_left]
  rw [exists_comm]
  simp_rw [and_assoc', and_comm]
#align pfun.preimage_comp PFun.preimage_comp

/- warning: part.bind_comp -> PFun.Part.bind_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : PFun.{u2, u3} β γ) (g : PFun.{u1, u2} α β) (a : Part.{u1} α), Eq.{succ u3} (Part.{u3} γ) (Part.bind.{u1, u3} α γ a (PFun.comp.{u1, u2, u3} α β γ f g)) (Part.bind.{u2, u3} β γ (Part.bind.{u1, u2} α β a g) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (f : PFun.{u3, u2} β γ) (g : PFun.{u1, u3} α β) (a : Part.{u1} α), Eq.{succ u2} (Part.{u2} γ) (Part.bind.{u1, u2} α γ a (PFun.comp.{u1, u3, u2} α β γ f g)) (Part.bind.{u3, u2} β γ (Part.bind.{u1, u3} α β a g) f)
Case conversion may be inaccurate. Consider using '#align part.bind_comp PFun.Part.bind_compₓ'. -/
@[simp]
theorem PFun.Part.bind_comp (f : β →. γ) (g : α →. β) (a : Part α) :
    a.bind (f.comp g) = (a.bind g).bind f := by
  ext c
  simp_rw [Part.mem_bind_iff, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_right, ←
    exists_and_left]
  rw [exists_comm]
  simp_rw [and_assoc']
#align part.bind_comp PFun.Part.bind_comp

/- warning: pfun.comp_assoc -> PFun.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : PFun.{u3, u4} γ δ) (g : PFun.{u2, u3} β γ) (h : PFun.{u1, u2} α β), Eq.{max (succ u1) (succ u4)} (PFun.{u1, u4} α δ) (PFun.comp.{u1, u2, u4} α β δ (PFun.comp.{u2, u3, u4} β γ δ f g) h) (PFun.comp.{u1, u3, u4} α γ δ f (PFun.comp.{u1, u2, u3} α β γ g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} (f : PFun.{u4, u3} γ δ) (g : PFun.{u2, u4} β γ) (h : PFun.{u1, u2} α β), Eq.{max (succ u1) (succ u3)} (PFun.{u1, u3} α δ) (PFun.comp.{u1, u2, u3} α β δ (PFun.comp.{u2, u4, u3} β γ δ f g) h) (PFun.comp.{u1, u4, u3} α γ δ f (PFun.comp.{u1, u2, u4} α β γ g h))
Case conversion may be inaccurate. Consider using '#align pfun.comp_assoc PFun.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : γ →. δ) (g : β →. γ) (h : α →. β) : (f.comp g).comp h = f.comp (g.comp h) :=
  ext fun _ _ => by simp only [comp_apply, PFun.Part.bind_comp]
#align pfun.comp_assoc PFun.comp_assoc

/- warning: pfun.coe_comp -> PFun.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (g : β -> γ) (f : α -> β), Eq.{max (succ u1) (succ u3)} (PFun.{u1, u3} α γ) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Sort.{max (succ u1) (succ u3)}) [self : HasLiftT.{max (succ u1) (succ u3), max (succ u1) (succ u3)} a b] => self.0) (α -> γ) (PFun.{u1, u3} α γ) (HasLiftT.mk.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (α -> γ) (PFun.{u1, u3} α γ) (CoeTCₓ.coe.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (α -> γ) (PFun.{u1, u3} α γ) (coeBase.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (α -> γ) (PFun.{u1, u3} α γ) (PFun.hasCoe.{u1, u3} α γ)))) (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (PFun.comp.{u1, u2, u3} α β γ ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (β -> γ) (PFun.{u2, u3} β γ) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (β -> γ) (PFun.{u2, u3} β γ) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (β -> γ) (PFun.{u2, u3} β γ) (coeBase.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (β -> γ) (PFun.{u2, u3} β γ) (PFun.hasCoe.{u2, u3} β γ)))) g) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (α -> β) (PFun.{u1, u2} α β) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (PFun.{u1, u2} α β) (PFun.hasCoe.{u1, u2} α β)))) f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (g : β -> γ) (f : α -> β), Eq.{max (succ u3) (succ u2)} (PFun.{u3, u2} α γ) (PFun.lift.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f)) (PFun.comp.{u3, u1, u2} α β γ (PFun.lift.{u1, u2} β γ g) (PFun.lift.{u3, u1} α β f))
Case conversion may be inaccurate. Consider using '#align pfun.coe_comp PFun.coe_compₓ'. -/
-- This can't be `simp`
theorem coe_comp (g : β → γ) (f : α → β) : ((g ∘ f : α → γ) : α →. γ) = (g : β →. γ).comp f :=
  ext fun _ _ => by simp only [coe_val, comp_apply, Part.bind_some]
#align pfun.coe_comp PFun.coe_comp

#print PFun.prodLift /-
/-- Product of partial functions. -/
def prodLift (f : α →. β) (g : α →. γ) : α →. β × γ := fun x =>
  ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩
#align pfun.prod_lift PFun.prodLift
-/

/- warning: pfun.dom_prod_lift -> PFun.dom_prodLift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : PFun.{u1, u2} α β) (g : PFun.{u1, u3} α γ), Eq.{succ u1} (Set.{u1} α) (PFun.Dom.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (PFun.prodLift.{u1, u2, u3} α β γ f g)) (setOf.{u1} α (fun (x : α) => And (Part.Dom.{u2} β (f x)) (Part.Dom.{u3} γ (g x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : PFun.{u3, u2} α β) (g : PFun.{u3, u1} α γ), Eq.{succ u3} (Set.{u3} α) (PFun.Dom.{u3, max u2 u1} α (Prod.{u2, u1} β γ) (PFun.prodLift.{u3, u2, u1} α β γ f g)) (setOf.{u3} α (fun (x : α) => And (Part.Dom.{u2} β (f x)) (Part.Dom.{u1} γ (g x))))
Case conversion may be inaccurate. Consider using '#align pfun.dom_prod_lift PFun.dom_prodLiftₓ'. -/
@[simp]
theorem dom_prodLift (f : α →. β) (g : α →. γ) :
    (f.prodLift g).Dom = { x | (f x).Dom ∧ (g x).Dom } :=
  rfl
#align pfun.dom_prod_lift PFun.dom_prodLift

/- warning: pfun.get_prod_lift -> PFun.get_prodLift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : PFun.{u1, u2} α β) (g : PFun.{u1, u3} α γ) (x : α) (h : Part.Dom.{max u2 u3} (Prod.{u2, u3} β γ) (PFun.prodLift.{u1, u2, u3} α β γ f g x)), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} β γ) (Part.get.{max u2 u3} (Prod.{u2, u3} β γ) (PFun.prodLift.{u1, u2, u3} α β γ f g x) h) (Prod.mk.{u2, u3} β γ (Part.get.{u2} β (f x) (And.left (Part.Dom.{u2} β (f x)) (Part.Dom.{u3} γ (g x)) h)) (Part.get.{u3} γ (g x) (And.right (Part.Dom.{u2} β (f x)) (Part.Dom.{u3} γ (g x)) h)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : PFun.{u3, u2} α β) (g : PFun.{u3, u1} α γ) (x : α) (h : Part.Dom.{max u2 u1} (Prod.{u2, u1} β γ) (PFun.prodLift.{u3, u2, u1} α β γ f g x)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β γ) (Part.get.{max u2 u1} (Prod.{u2, u1} β γ) (PFun.prodLift.{u3, u2, u1} α β γ f g x) h) (Prod.mk.{u2, u1} β γ (Part.get.{u2} β (f x) (And.left (Part.Dom.{u2} β (f x)) (Part.Dom.{u1} γ (g x)) h)) (Part.get.{u1} γ (g x) (And.right (Part.Dom.{u2} β (f x)) (Part.Dom.{u1} γ (g x)) h)))
Case conversion may be inaccurate. Consider using '#align pfun.get_prod_lift PFun.get_prodLiftₓ'. -/
theorem get_prodLift (f : α →. β) (g : α →. γ) (x : α) (h) :
    (f.prodLift g x).get h = ((f x).get h.1, (g x).get h.2) :=
  rfl
#align pfun.get_prod_lift PFun.get_prodLift

/- warning: pfun.prod_lift_apply -> PFun.prodLift_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : PFun.{u1, u2} α β) (g : PFun.{u1, u3} α γ) (x : α), Eq.{succ (max u2 u3)} (Part.{max u2 u3} (Prod.{u2, u3} β γ)) (PFun.prodLift.{u1, u2, u3} α β γ f g x) (Part.mk.{max u2 u3} (Prod.{u2, u3} β γ) (And (Part.Dom.{u2} β (f x)) (Part.Dom.{u3} γ (g x))) (fun (h : And (Part.Dom.{u2} β (f x)) (Part.Dom.{u3} γ (g x))) => Prod.mk.{u2, u3} β γ (Part.get.{u2} β (f x) (And.left (Part.Dom.{u2} β (f x)) (Part.Dom.{u3} γ (g x)) h)) (Part.get.{u3} γ (g x) (And.right (Part.Dom.{u2} β (f x)) (Part.Dom.{u3} γ (g x)) h))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : PFun.{u3, u2} α β) (g : PFun.{u3, u1} α γ) (x : α), Eq.{max (succ u2) (succ u1)} (Part.{max u1 u2} (Prod.{u2, u1} β γ)) (PFun.prodLift.{u3, u2, u1} α β γ f g x) (Part.mk.{max u2 u1} (Prod.{u2, u1} β γ) (And (Part.Dom.{u2} β (f x)) (Part.Dom.{u1} γ (g x))) (fun (h : And (Part.Dom.{u2} β (f x)) (Part.Dom.{u1} γ (g x))) => Prod.mk.{u2, u1} β γ (Part.get.{u2} β (f x) (And.left (Part.Dom.{u2} β (f x)) (Part.Dom.{u1} γ (g x)) h)) (Part.get.{u1} γ (g x) (And.right (Part.Dom.{u2} β (f x)) (Part.Dom.{u1} γ (g x)) h))))
Case conversion may be inaccurate. Consider using '#align pfun.prod_lift_apply PFun.prodLift_applyₓ'. -/
@[simp]
theorem prodLift_apply (f : α →. β) (g : α →. γ) (x : α) :
    f.prodLift g x = ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩ :=
  rfl
#align pfun.prod_lift_apply PFun.prodLift_apply

/- warning: pfun.mem_prod_lift -> PFun.mem_prodLift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : PFun.{u1, u2} α β} {g : PFun.{u1, u3} α γ} {x : α} {y : Prod.{u2, u3} β γ}, Iff (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Part.{max u2 u3} (Prod.{u2, u3} β γ)) (Part.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) y (PFun.prodLift.{u1, u2, u3} α β γ f g x)) (And (Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) (Prod.fst.{u2, u3} β γ y) (f x)) (Membership.Mem.{u3, u3} γ (Part.{u3} γ) (Part.hasMem.{u3} γ) (Prod.snd.{u2, u3} β γ y) (g x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : PFun.{u3, u2} α β} {g : PFun.{u3, u1} α γ} {x : α} {y : Prod.{u2, u1} β γ}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Prod.{u2, u1} β γ) (Part.{max u1 u2} (Prod.{u2, u1} β γ)) (Part.instMembershipPart.{max u2 u1} (Prod.{u2, u1} β γ)) y (PFun.prodLift.{u3, u2, u1} α β γ f g x)) (And (Membership.mem.{u2, u2} β (Part.{u2} β) (Part.instMembershipPart.{u2} β) (Prod.fst.{u2, u1} β γ y) (f x)) (Membership.mem.{u1, u1} γ (Part.{u1} γ) (Part.instMembershipPart.{u1} γ) (Prod.snd.{u2, u1} β γ y) (g x)))
Case conversion may be inaccurate. Consider using '#align pfun.mem_prod_lift PFun.mem_prodLiftₓ'. -/
theorem mem_prodLift {f : α →. β} {g : α →. γ} {x : α} {y : β × γ} :
    y ∈ f.prodLift g x ↔ y.1 ∈ f x ∧ y.2 ∈ g x :=
  by
  trans ∃ hp hq, (f x).get hp = y.1 ∧ (g x).get hq = y.2
  · simp only [prod_lift, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simpa only [exists_and_left, exists_and_right]
#align pfun.mem_prod_lift PFun.mem_prodLift

#print PFun.prodMap /-
/-- Product of partial functions. -/
def prodMap (f : α →. γ) (g : β →. δ) : α × β →. γ × δ := fun x =>
  ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩
#align pfun.prod_map PFun.prodMap
-/

/- warning: pfun.dom_prod_map -> PFun.dom_prodMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : PFun.{u1, u3} α γ) (g : PFun.{u2, u4} β δ), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (PFun.Dom.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (PFun.prodMap.{u1, u2, u3, u4} α β γ δ f g)) (setOf.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => And (Part.Dom.{u3} γ (f (Prod.fst.{u1, u2} α β x))) (Part.Dom.{u4} δ (g (Prod.snd.{u1, u2} α β x)))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} (f : PFun.{u4, u3} α γ) (g : PFun.{u2, u1} β δ), Eq.{max (succ u4) (succ u2)} (Set.{max u4 u2} (Prod.{u4, u2} α β)) (PFun.Dom.{max u4 u2, max u3 u1} (Prod.{u4, u2} α β) (Prod.{u3, u1} γ δ) (PFun.prodMap.{u4, u2, u3, u1} α β γ δ f g)) (setOf.{max u4 u2} (Prod.{u4, u2} α β) (fun (x : Prod.{u4, u2} α β) => And (Part.Dom.{u3} γ (f (Prod.fst.{u4, u2} α β x))) (Part.Dom.{u1} δ (g (Prod.snd.{u4, u2} α β x)))))
Case conversion may be inaccurate. Consider using '#align pfun.dom_prod_map PFun.dom_prodMapₓ'. -/
@[simp]
theorem dom_prodMap (f : α →. γ) (g : β →. δ) :
    (f.Prod_map g).Dom = { x | (f x.1).Dom ∧ (g x.2).Dom } :=
  rfl
#align pfun.dom_prod_map PFun.dom_prodMap

/- warning: pfun.get_prod_map -> PFun.get_prodMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : PFun.{u1, u3} α γ) (g : PFun.{u2, u4} β δ) (x : Prod.{u1, u2} α β) (h : Part.Dom.{max u3 u4} (Prod.{u3, u4} γ δ) (PFun.prodMap.{u1, u2, u3, u4} α β γ δ f g x)), Eq.{max (succ u3) (succ u4)} (Prod.{u3, u4} γ δ) (Part.get.{max u3 u4} (Prod.{u3, u4} γ δ) (PFun.prodMap.{u1, u2, u3, u4} α β γ δ f g x) h) (Prod.mk.{u3, u4} γ δ (Part.get.{u3} γ (f (Prod.fst.{u1, u2} α β x)) (And.left (Part.Dom.{u3} γ (f (Prod.fst.{u1, u2} α β x))) (Part.Dom.{u4} δ (g (Prod.snd.{u1, u2} α β x))) h)) (Part.get.{u4} δ (g (Prod.snd.{u1, u2} α β x)) (And.right (Part.Dom.{u3} γ (f (Prod.fst.{u1, u2} α β x))) (Part.Dom.{u4} δ (g (Prod.snd.{u1, u2} α β x))) h)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} (f : PFun.{u4, u3} α γ) (g : PFun.{u2, u1} β δ) (x : Prod.{u4, u2} α β) (h : Part.Dom.{max u3 u1} (Prod.{u3, u1} γ δ) (PFun.prodMap.{u4, u2, u3, u1} α β γ δ f g x)), Eq.{max (succ u3) (succ u1)} (Prod.{u3, u1} γ δ) (Part.get.{max u3 u1} (Prod.{u3, u1} γ δ) (PFun.prodMap.{u4, u2, u3, u1} α β γ δ f g x) h) (Prod.mk.{u3, u1} γ δ (Part.get.{u3} γ (f (Prod.fst.{u4, u2} α β x)) (And.left (Part.Dom.{u3} γ (f (Prod.fst.{u4, u2} α β x))) (Part.Dom.{u1} δ (g (Prod.snd.{u4, u2} α β x))) h)) (Part.get.{u1} δ (g (Prod.snd.{u4, u2} α β x)) (And.right (Part.Dom.{u3} γ (f (Prod.fst.{u4, u2} α β x))) (Part.Dom.{u1} δ (g (Prod.snd.{u4, u2} α β x))) h)))
Case conversion may be inaccurate. Consider using '#align pfun.get_prod_map PFun.get_prodMapₓ'. -/
theorem get_prodMap (f : α →. γ) (g : β →. δ) (x : α × β) (h) :
    (f.Prod_map g x).get h = ((f x.1).get h.1, (g x.2).get h.2) :=
  rfl
#align pfun.get_prod_map PFun.get_prodMap

/- warning: pfun.prod_map_apply -> PFun.prodMap_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : PFun.{u1, u3} α γ) (g : PFun.{u2, u4} β δ) (x : Prod.{u1, u2} α β), Eq.{succ (max u3 u4)} (Part.{max u3 u4} (Prod.{u3, u4} γ δ)) (PFun.prodMap.{u1, u2, u3, u4} α β γ δ f g x) (Part.mk.{max u3 u4} (Prod.{u3, u4} γ δ) (And (Part.Dom.{u3} γ (f (Prod.fst.{u1, u2} α β x))) (Part.Dom.{u4} δ (g (Prod.snd.{u1, u2} α β x)))) (fun (h : And (Part.Dom.{u3} γ (f (Prod.fst.{u1, u2} α β x))) (Part.Dom.{u4} δ (g (Prod.snd.{u1, u2} α β x)))) => Prod.mk.{u3, u4} γ δ (Part.get.{u3} γ (f (Prod.fst.{u1, u2} α β x)) (And.left (Part.Dom.{u3} γ (f (Prod.fst.{u1, u2} α β x))) (Part.Dom.{u4} δ (g (Prod.snd.{u1, u2} α β x))) h)) (Part.get.{u4} δ (g (Prod.snd.{u1, u2} α β x)) (And.right (Part.Dom.{u3} γ (f (Prod.fst.{u1, u2} α β x))) (Part.Dom.{u4} δ (g (Prod.snd.{u1, u2} α β x))) h))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} (f : PFun.{u4, u3} α γ) (g : PFun.{u2, u1} β δ) (x : Prod.{u4, u2} α β), Eq.{max (succ u3) (succ u1)} (Part.{max u1 u3} (Prod.{u3, u1} γ δ)) (PFun.prodMap.{u4, u2, u3, u1} α β γ δ f g x) (Part.mk.{max u3 u1} (Prod.{u3, u1} γ δ) (And (Part.Dom.{u3} γ (f (Prod.fst.{u4, u2} α β x))) (Part.Dom.{u1} δ (g (Prod.snd.{u4, u2} α β x)))) (fun (h : And (Part.Dom.{u3} γ (f (Prod.fst.{u4, u2} α β x))) (Part.Dom.{u1} δ (g (Prod.snd.{u4, u2} α β x)))) => Prod.mk.{u3, u1} γ δ (Part.get.{u3} γ (f (Prod.fst.{u4, u2} α β x)) (And.left (Part.Dom.{u3} γ (f (Prod.fst.{u4, u2} α β x))) (Part.Dom.{u1} δ (g (Prod.snd.{u4, u2} α β x))) h)) (Part.get.{u1} δ (g (Prod.snd.{u4, u2} α β x)) (And.right (Part.Dom.{u3} γ (f (Prod.fst.{u4, u2} α β x))) (Part.Dom.{u1} δ (g (Prod.snd.{u4, u2} α β x))) h))))
Case conversion may be inaccurate. Consider using '#align pfun.prod_map_apply PFun.prodMap_applyₓ'. -/
@[simp]
theorem prodMap_apply (f : α →. γ) (g : β →. δ) (x : α × β) :
    f.Prod_map g x = ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩ :=
  rfl
#align pfun.prod_map_apply PFun.prodMap_apply

/- warning: pfun.mem_prod_map -> PFun.mem_prodMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {f : PFun.{u1, u3} α γ} {g : PFun.{u2, u4} β δ} {x : Prod.{u1, u2} α β} {y : Prod.{u3, u4} γ δ}, Iff (Membership.Mem.{max u3 u4, max u3 u4} (Prod.{u3, u4} γ δ) (Part.{max u3 u4} (Prod.{u3, u4} γ δ)) (Part.hasMem.{max u3 u4} (Prod.{u3, u4} γ δ)) y (PFun.prodMap.{u1, u2, u3, u4} α β γ δ f g x)) (And (Membership.Mem.{u3, u3} γ (Part.{u3} γ) (Part.hasMem.{u3} γ) (Prod.fst.{u3, u4} γ δ y) (f (Prod.fst.{u1, u2} α β x))) (Membership.Mem.{u4, u4} δ (Part.{u4} δ) (Part.hasMem.{u4} δ) (Prod.snd.{u3, u4} γ δ y) (g (Prod.snd.{u1, u2} α β x))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} {f : PFun.{u4, u3} α γ} {g : PFun.{u2, u1} β δ} {x : Prod.{u4, u2} α β} {y : Prod.{u3, u1} γ δ}, Iff (Membership.mem.{max u3 u1, max u3 u1} (Prod.{u3, u1} γ δ) (Part.{max u1 u3} (Prod.{u3, u1} γ δ)) (Part.instMembershipPart.{max u3 u1} (Prod.{u3, u1} γ δ)) y (PFun.prodMap.{u4, u2, u3, u1} α β γ δ f g x)) (And (Membership.mem.{u3, u3} γ (Part.{u3} γ) (Part.instMembershipPart.{u3} γ) (Prod.fst.{u3, u1} γ δ y) (f (Prod.fst.{u4, u2} α β x))) (Membership.mem.{u1, u1} δ (Part.{u1} δ) (Part.instMembershipPart.{u1} δ) (Prod.snd.{u3, u1} γ δ y) (g (Prod.snd.{u4, u2} α β x))))
Case conversion may be inaccurate. Consider using '#align pfun.mem_prod_map PFun.mem_prodMapₓ'. -/
theorem mem_prodMap {f : α →. γ} {g : β →. δ} {x : α × β} {y : γ × δ} :
    y ∈ f.Prod_map g x ↔ y.1 ∈ f x.1 ∧ y.2 ∈ g x.2 :=
  by
  trans ∃ hp hq, (f x.1).get hp = y.1 ∧ (g x.2).get hq = y.2
  · simp only [Prod_map, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simpa only [exists_and_left, exists_and_right]
#align pfun.mem_prod_map PFun.mem_prodMap

/- warning: pfun.prod_lift_fst_comp_snd_comp -> PFun.prodLift_fst_comp_snd_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : PFun.{u1, u3} α γ) (g : PFun.{u2, u4} β δ), Eq.{max (succ (max u1 u2)) (succ (max u3 u4))} (PFun.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ)) (PFun.prodLift.{max u1 u2, u3, u4} (Prod.{u1, u2} α β) γ δ (PFun.comp.{max u1 u2, u1, u3} (Prod.{u1, u2} α β) α γ f ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ (max u1 u2)) (succ u1)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ (max u1 u2)) (succ u1)} a b] => self.0) ((Prod.{u1, u2} α β) -> α) (PFun.{max u1 u2, u1} (Prod.{u1, u2} α β) α) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ (max u1 u2)) (succ u1)} ((Prod.{u1, u2} α β) -> α) (PFun.{max u1 u2, u1} (Prod.{u1, u2} α β) α) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ (max u1 u2)) (succ u1)} ((Prod.{u1, u2} α β) -> α) (PFun.{max u1 u2, u1} (Prod.{u1, u2} α β) α) (coeBase.{max (succ u1) (succ u2), max (succ (max u1 u2)) (succ u1)} ((Prod.{u1, u2} α β) -> α) (PFun.{max u1 u2, u1} (Prod.{u1, u2} α β) α) (PFun.hasCoe.{max u1 u2, u1} (Prod.{u1, u2} α β) α)))) (Prod.fst.{u1, u2} α β))) (PFun.comp.{max u1 u2, u2, u4} (Prod.{u1, u2} α β) β δ g ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ (max u1 u2)) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ (max u1 u2)) (succ u2)} a b] => self.0) ((Prod.{u1, u2} α β) -> β) (PFun.{max u1 u2, u2} (Prod.{u1, u2} α β) β) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ (max u1 u2)) (succ u2)} ((Prod.{u1, u2} α β) -> β) (PFun.{max u1 u2, u2} (Prod.{u1, u2} α β) β) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ (max u1 u2)) (succ u2)} ((Prod.{u1, u2} α β) -> β) (PFun.{max u1 u2, u2} (Prod.{u1, u2} α β) β) (coeBase.{max (succ u1) (succ u2), max (succ (max u1 u2)) (succ u2)} ((Prod.{u1, u2} α β) -> β) (PFun.{max u1 u2, u2} (Prod.{u1, u2} α β) β) (PFun.hasCoe.{max u1 u2, u2} (Prod.{u1, u2} α β) β)))) (Prod.snd.{u1, u2} α β)))) (PFun.prodMap.{u1, u2, u3, u4} α β γ δ f g)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} (f : PFun.{u4, u3} α γ) (g : PFun.{u2, u1} β δ), Eq.{max (max (max (succ u4) (succ u2)) (succ u3)) (succ u1)} (PFun.{max u4 u2, max u1 u3} (Prod.{u4, u2} α β) (Prod.{u3, u1} γ δ)) (PFun.prodLift.{max u4 u2, u3, u1} (Prod.{u4, u2} α β) γ δ (PFun.comp.{max u4 u2, u4, u3} (Prod.{u4, u2} α β) α γ f (PFun.lift.{max u4 u2, u4} (Prod.{u4, u2} α β) α (Prod.fst.{u4, u2} α β))) (PFun.comp.{max u4 u2, u2, u1} (Prod.{u4, u2} α β) β δ g (PFun.lift.{max u4 u2, u2} (Prod.{u4, u2} α β) β (Prod.snd.{u4, u2} α β)))) (PFun.prodMap.{u4, u2, u3, u1} α β γ δ f g)
Case conversion may be inaccurate. Consider using '#align pfun.prod_lift_fst_comp_snd_comp PFun.prodLift_fst_comp_snd_compₓ'. -/
@[simp]
theorem prodLift_fst_comp_snd_comp (f : α →. γ) (g : β →. δ) :
    prodLift (f.comp ((Prod.fst : α × β → α) : α × β →. α))
        (g.comp ((Prod.snd : α × β → β) : α × β →. β)) =
      prodMap f g :=
  ext fun a => by simp
#align pfun.prod_lift_fst_comp_snd_comp PFun.prodLift_fst_comp_snd_comp

/- warning: pfun.prod_map_id_id -> PFun.prodMap_id_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (PFun.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (PFun.prodMap.{u1, u2, u1, u2} α β α β (PFun.id.{u1} α) (PFun.id.{u2} β)) (PFun.id.{max u1 u2} (Prod.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (PFun.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u2, u1} α β)) (PFun.prodMap.{u2, u1, u2, u1} α β α β (PFun.id.{u2} α) (PFun.id.{u1} β)) (PFun.id.{max u2 u1} (Prod.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align pfun.prod_map_id_id PFun.prodMap_id_idₓ'. -/
@[simp]
theorem prodMap_id_id : (PFun.id α).Prod_map (PFun.id β) = PFun.id _ :=
  ext fun _ _ => by simp [eq_comm]
#align pfun.prod_map_id_id PFun.prodMap_id_id

/- warning: pfun.prod_map_comp_comp -> PFun.prodMap_comp_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {ι : Type.{u6}} (f₁ : PFun.{u1, u2} α β) (f₂ : PFun.{u2, u3} β γ) (g₁ : PFun.{u4, u5} δ ε) (g₂ : PFun.{u5, u6} ε ι), Eq.{max (succ (max u1 u4)) (succ (max u3 u6))} (PFun.{max u1 u4, max u3 u6} (Prod.{u1, u4} α δ) (Prod.{u3, u6} γ ι)) (PFun.prodMap.{u1, u4, u3, u6} α δ γ ι (PFun.comp.{u1, u2, u3} α β γ f₂ f₁) (PFun.comp.{u4, u5, u6} δ ε ι g₂ g₁)) (PFun.comp.{max u1 u4, max u2 u5, max u3 u6} (Prod.{u1, u4} α δ) (Prod.{u2, u5} β ε) (Prod.{u3, u6} γ ι) (PFun.prodMap.{u2, u5, u3, u6} β ε γ ι f₂ g₂) (PFun.prodMap.{u1, u4, u2, u5} α δ β ε f₁ g₁))
but is expected to have type
  forall {α : Type.{u6}} {β : Type.{u5}} {γ : Type.{u4}} {δ : Type.{u3}} {ε : Type.{u2}} {ι : Type.{u1}} (f₁ : PFun.{u6, u5} α β) (f₂ : PFun.{u5, u4} β γ) (g₁ : PFun.{u3, u2} δ ε) (g₂ : PFun.{u2, u1} ε ι), Eq.{max (max (max (succ u6) (succ u4)) (succ u3)) (succ u1)} (PFun.{max u3 u6, max u1 u4} (Prod.{u6, u3} α δ) (Prod.{u4, u1} γ ι)) (PFun.prodMap.{u6, u3, u4, u1} α δ γ ι (PFun.comp.{u6, u5, u4} α β γ f₂ f₁) (PFun.comp.{u3, u2, u1} δ ε ι g₂ g₁)) (PFun.comp.{max u6 u3, max u5 u2, max u4 u1} (Prod.{u6, u3} α δ) (Prod.{u5, u2} β ε) (Prod.{u4, u1} γ ι) (PFun.prodMap.{u5, u2, u4, u1} β ε γ ι f₂ g₂) (PFun.prodMap.{u6, u3, u5, u2} α δ β ε f₁ g₁))
Case conversion may be inaccurate. Consider using '#align pfun.prod_map_comp_comp PFun.prodMap_comp_compₓ'. -/
@[simp]
theorem prodMap_comp_comp (f₁ : α →. β) (f₂ : β →. γ) (g₁ : δ →. ε) (g₂ : ε →. ι) :
    (f₂.comp f₁).Prod_map (g₂.comp g₁) = (f₂.Prod_map g₂).comp (f₁.Prod_map g₁) :=
  ext fun _ _ => by tidy
#align pfun.prod_map_comp_comp PFun.prodMap_comp_comp

end PFun

