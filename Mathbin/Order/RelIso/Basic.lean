/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module order.rel_iso.basic
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.FunLike.Basic
import Mathbin.Logic.Embedding.Basic
import Mathbin.Order.RelClasses

/-!
# Relation homomorphisms, embeddings, isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines relation homomorphisms, embeddings, isomorphisms and order embeddings and
isomorphisms.

## Main declarations

* `rel_hom`: Relation homomorphism. A `rel_hom r s` is a function `f : α → β` such that
  `r a b → s (f a) (f b)`.
* `rel_embedding`: Relation embedding. A `rel_embedding r s` is an embedding `f : α ↪ β` such that
  `r a b ↔ s (f a) (f b)`.
* `rel_iso`: Relation isomorphism. A `rel_iso r s` is an equivalence `f : α ≃ β` such that
  `r a b ↔ s (f a) (f b)`.
* `sum_lex_congr`, `prod_lex_congr`: Creates a relation homomorphism between two `sum_lex` or two
  `prod_lex` from relation homomorphisms between their arguments.

## Notation

* `→r`: `rel_hom`
* `↪r`: `rel_embedding`
* `≃r`: `rel_iso`
-/


open Function

universe u v w

variable {α β γ δ : Type _} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  {u : δ → δ → Prop}

#print RelHom /-
/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
@[nolint has_nonempty_instance]
structure RelHom {α β : Type _} (r : α → α → Prop) (s : β → β → Prop) where
  toFun : α → β
  map_rel' : ∀ {a b}, r a b → s (to_fun a) (to_fun b)
#align rel_hom RelHom
-/

-- mathport name: «expr →r »
infixl:25 " →r " => RelHom

section

#print RelHomClass /-
/-- `rel_hom_class F r s` asserts that `F` is a type of functions such that all `f : F`
satisfy `r a b → s (f a) (f b)`.

The relations `r` and `s` are `out_param`s since figuring them out from a goal is a higher-order
matching problem that Lean usually can't do unaided.
-/
class RelHomClass (F : Type _) {α β : outParam <| Type _} (r : outParam <| α → α → Prop)
  (s : outParam <| β → β → Prop) extends FunLike F α fun _ => β where
  map_rel : ∀ (f : F) {a b}, r a b → s (f a) (f b)
#align rel_hom_class RelHomClass
-/

export RelHomClass (map_rel)

-- The free parameters `r` and `s` are `out_param`s so this is not dangerous.
attribute [nolint dangerous_instance] RelHomClass.toFunLike

end

namespace RelHomClass

variable {F : Type _}

/- warning: rel_hom_class.is_irrefl -> RelHomClass.isIrrefl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {F : Type.{u3}} [_inst_1 : RelHomClass.{u3, u1, u2} F α β r s], F -> (forall [_inst_2 : IsIrrefl.{u2} β s], IsIrrefl.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {F : Type.{u3}} [_inst_1 : RelHomClass.{u3, u2, u1} F α β r s], F -> (forall [_inst_2 : IsIrrefl.{u1} β s], IsIrrefl.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_hom_class.is_irrefl RelHomClass.isIrreflₓ'. -/
protected theorem isIrrefl [RelHomClass F r s] (f : F) : ∀ [IsIrrefl β s], IsIrrefl α r
  | ⟨H⟩ => ⟨fun a h => H _ (map_rel f h)⟩
#align rel_hom_class.is_irrefl RelHomClass.isIrrefl

/- warning: rel_hom_class.is_asymm -> RelHomClass.isAsymm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {F : Type.{u3}} [_inst_1 : RelHomClass.{u3, u1, u2} F α β r s], F -> (forall [_inst_2 : IsAsymm.{u2} β s], IsAsymm.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {F : Type.{u3}} [_inst_1 : RelHomClass.{u3, u2, u1} F α β r s], F -> (forall [_inst_2 : IsAsymm.{u1} β s], IsAsymm.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_hom_class.is_asymm RelHomClass.isAsymmₓ'. -/
protected theorem isAsymm [RelHomClass F r s] (f : F) : ∀ [IsAsymm β s], IsAsymm α r
  | ⟨H⟩ => ⟨fun a b h₁ h₂ => H _ _ (map_rel f h₁) (map_rel f h₂)⟩
#align rel_hom_class.is_asymm RelHomClass.isAsymm

/- warning: rel_hom_class.acc -> RelHomClass.acc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {F : Type.{u3}} [_inst_1 : RelHomClass.{u3, u1, u2} F α β r s] (f : F) (a : α), (Acc.{succ u2} β s (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (RelHomClass.toFunLike.{u3, u1, u2} F α β r s _inst_1)) f a)) -> (Acc.{succ u1} α r a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {F : Type.{u3}} [_inst_1 : RelHomClass.{u3, u2, u1} F α β r s] (f : F) (a : α), (Acc.{succ u1} β s (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{u3, u2, u1} F α β r s _inst_1) f a)) -> (Acc.{succ u2} α r a)
Case conversion may be inaccurate. Consider using '#align rel_hom_class.acc RelHomClass.accₓ'. -/
protected theorem acc [RelHomClass F r s] (f : F) (a : α) : Acc s (f a) → Acc r a :=
  by
  generalize h : f a = b; intro ac
  induction' ac with _ H IH generalizing a; subst h
  exact ⟨_, fun a' h => IH (f a') (map_rel f h) _ rfl⟩
#align rel_hom_class.acc RelHomClass.acc

/- warning: rel_hom_class.well_founded -> RelHomClass.wellFounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {F : Type.{u3}} [_inst_1 : RelHomClass.{u3, u1, u2} F α β r s], F -> (WellFounded.{succ u2} β s) -> (WellFounded.{succ u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {F : Type.{u3}} [_inst_1 : RelHomClass.{u3, u2, u1} F α β r s], F -> (WellFounded.{succ u1} β s) -> (WellFounded.{succ u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_hom_class.well_founded RelHomClass.wellFoundedₓ'. -/
protected theorem wellFounded [RelHomClass F r s] (f : F) : ∀ h : WellFounded s, WellFounded r
  | ⟨H⟩ => ⟨fun a => RelHomClass.acc f _ (H _)⟩
#align rel_hom_class.well_founded RelHomClass.wellFounded

end RelHomClass

namespace RelHom

instance : RelHomClass (r →r s) r s where
  coe o := o.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
  map_rel := map_rel'

/-- Auxiliary instance if `rel_hom_class.to_fun_like.to_has_coe_to_fun` isn't found -/
instance : CoeFun (r →r s) fun _ => α → β :=
  ⟨fun o => o.toFun⟩

initialize_simps_projections RelHom (toFun → apply)

/- warning: rel_hom.map_rel -> RelHom.map_rel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelHom.{u1, u2} α β r s) {a : α} {b : α}, (r a b) -> (s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (_x : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (_x : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s) f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelHom.{u2, u1} α β r s) {a : α} {b : α}, (r a b) -> (s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) f b))
Case conversion may be inaccurate. Consider using '#align rel_hom.map_rel RelHom.map_relₓ'. -/
protected theorem map_rel (f : r →r s) {a b} : r a b → s (f a) (f b) :=
  f.map_rel'
#align rel_hom.map_rel RelHom.map_rel

@[simp]
theorem coe_fn_mk (f : α → β) (o) : (@RelHom.mk _ _ r s f o : α → β) = f :=
  rfl
#align rel_hom.coe_fn_mk RelHom.coe_fn_mk

/- warning: rel_hom.coe_fn_to_fun -> RelHom.coe_fn_toFun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelHom.{u1, u2} α β r s), Eq.{max (succ u1) (succ u2)} (α -> β) (RelHom.toFun.{u1, u2} α β r s f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (_x : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelHom.{u2, u1} α β r s), Eq.{max (succ u2) (succ u1)} (α -> β) (RelHom.toFun.{u2, u1} α β r s f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) f)
Case conversion may be inaccurate. Consider using '#align rel_hom.coe_fn_to_fun RelHom.coe_fn_toFunₓ'. -/
@[simp]
theorem coe_fn_toFun (f : r →r s) : (f.toFun : α → β) = f :=
  rfl
#align rel_hom.coe_fn_to_fun RelHom.coe_fn_toFun

/- warning: rel_hom.coe_fn_injective -> RelHom.coe_fn_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (ᾰ : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelHom.{u2, u1} α β r s) (forall (ᾰ : α), (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) ᾰ) (fun (f : RelHom.{u2, u1} α β r s) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (a : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) a) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) f)
Case conversion may be inaccurate. Consider using '#align rel_hom.coe_fn_injective RelHom.coe_fn_injectiveₓ'. -/
/-- The map `coe_fn : (r →r s) → (α → β)` is injective. -/
theorem coe_fn_injective : @Function.Injective (r →r s) (α → β) coeFn :=
  FunLike.coe_injective
#align rel_hom.coe_fn_injective RelHom.coe_fn_injective

/- warning: rel_hom.ext -> RelHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {{f : RelHom.{u1, u2} α β r s}} {{g : RelHom.{u1, u2} α β r s}}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (_x : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (_x : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s) g x)) -> (Eq.{max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {{f : RelHom.{u2, u1} α β r s}} {{g : RelHom.{u2, u1} α β r s}}, (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) g x)) -> (Eq.{max (succ u2) (succ u1)} (RelHom.{u2, u1} α β r s) f g)
Case conversion may be inaccurate. Consider using '#align rel_hom.ext RelHom.extₓ'. -/
@[ext]
theorem ext ⦃f g : r →r s⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align rel_hom.ext RelHom.ext

/- warning: rel_hom.ext_iff -> RelHom.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : RelHom.{u1, u2} α β r s} {g : RelHom.{u1, u2} α β r s}, Iff (Eq.{max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) f g) (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (_x : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (_x : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s) g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : RelHom.{u2, u1} α β r s} {g : RelHom.{u2, u1} α β r s}, Iff (Eq.{max (succ u2) (succ u1)} (RelHom.{u2, u1} α β r s) f g) (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) g x))
Case conversion may be inaccurate. Consider using '#align rel_hom.ext_iff RelHom.ext_iffₓ'. -/
theorem ext_iff {f g : r →r s} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align rel_hom.ext_iff RelHom.ext_iff

#print RelHom.id /-
/-- Identity map is a relation homomorphism. -/
@[refl, simps]
protected def id (r : α → α → Prop) : r →r r :=
  ⟨fun x => x, fun a b x => x⟩
#align rel_hom.id RelHom.id
-/

#print RelHom.comp /-
/-- Composition of two relation homomorphisms is a relation homomorphism. -/
@[trans, simps]
protected def comp (g : s →r t) (f : r →r s) : r →r t :=
  ⟨fun x => g (f x), fun a b h => g.2 (f.2 h)⟩
#align rel_hom.comp RelHom.comp
-/

#print RelHom.swap /-
/-- A relation homomorphism is also a relation homomorphism between dual relations. -/
protected def swap (f : r →r s) : swap r →r swap s :=
  ⟨f, fun a b => f.map_rel⟩
#align rel_hom.swap RelHom.swap
-/

#print RelHom.preimage /-
/-- A function is a relation homomorphism from the preimage relation of `s` to `s`. -/
def preimage (f : α → β) (s : β → β → Prop) : f ⁻¹'o s →r s :=
  ⟨f, fun a b => id⟩
#align rel_hom.preimage RelHom.preimage
-/

end RelHom

/- warning: injective_of_increasing -> injective_of_increasing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> α -> Prop) (s : β -> β -> Prop) [_inst_1 : IsTrichotomous.{u1} α r] [_inst_2 : IsIrrefl.{u2} β s] (f : α -> β), (forall {x : α} {y : α}, (r x y) -> (s (f x) (f y))) -> (Function.Injective.{succ u1, succ u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> α -> Prop) (s : β -> β -> Prop) [_inst_1 : IsTrichotomous.{u2} α r] [_inst_2 : IsIrrefl.{u1} β s] (f : α -> β), (forall {x : α} {y : α}, (r x y) -> (s (f x) (f y))) -> (Function.Injective.{succ u2, succ u1} α β f)
Case conversion may be inaccurate. Consider using '#align injective_of_increasing injective_of_increasingₓ'. -/
/-- An increasing function is injective -/
theorem injective_of_increasing (r : α → α → Prop) (s : β → β → Prop) [IsTrichotomous α r]
    [IsIrrefl β s] (f : α → β) (hf : ∀ {x y}, r x y → s (f x) (f y)) : Injective f :=
  by
  intro x y hxy
  rcases trichotomous_of r x y with (h | h | h)
  have := hf h; rw [hxy] at this; exfalso; exact irrefl_of s (f y) this
  exact h
  have := hf h; rw [hxy] at this; exfalso; exact irrefl_of s (f y) this
#align injective_of_increasing injective_of_increasing

/- warning: rel_hom.injective_of_increasing -> RelHom.injective_of_increasing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrichotomous.{u1} α r] [_inst_2 : IsIrrefl.{u2} β s] (f : RelHom.{u1, u2} α β r s), Function.Injective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelHom.{u1, u2} α β r s) (fun (_x : RelHom.{u1, u2} α β r s) => α -> β) (RelHom.hasCoeToFun.{u1, u2} α β r s) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrichotomous.{u2} α r] [_inst_2 : IsIrrefl.{u1} β s] (f : RelHom.{u2, u1} α β r s), Function.Injective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelHom.{u2, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelHom.{u2, u1} α β r s) α β r s (RelHom.instRelHomClassRelHom.{u2, u1} α β r s)) f)
Case conversion may be inaccurate. Consider using '#align rel_hom.injective_of_increasing RelHom.injective_of_increasingₓ'. -/
/-- An increasing function is injective -/
theorem RelHom.injective_of_increasing [IsTrichotomous α r] [IsIrrefl β s] (f : r →r s) :
    Injective f :=
  injective_of_increasing r s f fun x y => f.map_rel
#align rel_hom.injective_of_increasing RelHom.injective_of_increasing

/- warning: surjective.well_founded_iff -> Surjective.wellFounded_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (forall {a : α} {b : α}, Iff (r a b) (s (f a) (f b))) -> (Iff (WellFounded.{succ u1} α r) (WellFounded.{succ u2} β s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (forall {a : α} {b : α}, Iff (r a b) (s (f a) (f b))) -> (Iff (WellFounded.{succ u2} α r) (WellFounded.{succ u1} β s))
Case conversion may be inaccurate. Consider using '#align surjective.well_founded_iff Surjective.wellFounded_iffₓ'. -/
-- TODO: define a `rel_iff_class` so we don't have to do all the `convert` trickery?
theorem Surjective.wellFounded_iff {f : α → β} (hf : Surjective f)
    (o : ∀ {a b}, r a b ↔ s (f a) (f b)) : WellFounded r ↔ WellFounded s :=
  Iff.intro
    (by
      refine' RelHomClass.wellFounded (RelHom.mk _ _ : s →r r)
      · exact Classical.choose hf.has_right_inverse
      intro a b h; apply o.2; convert h
      iterate 2 apply Classical.choose_spec hf.has_right_inverse)
    (RelHomClass.wellFounded (⟨f, fun _ _ => o.1⟩ : r →r s))
#align surjective.well_founded_iff Surjective.wellFounded_iff

#print RelEmbedding /-
/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
structure RelEmbedding {α β : Type _} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β where
  map_rel_iff' : ∀ {a b}, s (to_embedding a) (to_embedding b) ↔ r a b
#align rel_embedding RelEmbedding
-/

-- mathport name: «expr ↪r »
infixl:25 " ↪r " => RelEmbedding

#print Subtype.relEmbedding /-
/-- The induced relation on a subtype is an embedding under the natural inclusion. -/
def Subtype.relEmbedding {X : Type _} (r : X → X → Prop) (p : X → Prop) :
    (Subtype.val : Subtype p → X) ⁻¹'o r ↪r r :=
  ⟨Embedding.subtype p, fun x y => Iff.rfl⟩
#align subtype.rel_embedding Subtype.relEmbedding
-/

/- warning: preimage_equivalence -> preimage_equivalence is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (f : α -> β) {s : β -> β -> Prop}, (Equivalence.{u2} β s) -> (Equivalence.{u1} α (Order.Preimage.{u1, u2} α β f s))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (f : α -> β) {s : β -> β -> Prop}, (Equivalence.{u1} β s) -> (Equivalence.{u2} α (Order.Preimage.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align preimage_equivalence preimage_equivalenceₓ'. -/
theorem preimage_equivalence {α β} (f : α → β) {s : β → β → Prop} (hs : Equivalence s) :
    Equivalence (f ⁻¹'o s) :=
  ⟨fun a => hs.1 _, fun a b h => hs.2.1 h, fun a b c h₁ h₂ => hs.2.2 h₁ h₂⟩
#align preimage_equivalence preimage_equivalence

namespace RelEmbedding

#print RelEmbedding.toRelHom /-
/-- A relation embedding is also a relation homomorphism -/
def toRelHom (f : r ↪r s) : r →r s
    where
  toFun := f.toEmbedding.toFun
  map_rel' x y := (map_rel_iff' f).mpr
#align rel_embedding.to_rel_hom RelEmbedding.toRelHom
-/

instance : Coe (r ↪r s) (r →r s) :=
  ⟨toRelHom⟩

-- see Note [function coercion]
instance : CoeFun (r ↪r s) fun _ => α → β :=
  ⟨fun o => o.toEmbedding⟩

-- TODO: define and instantiate a `rel_embedding_class` when `embedding_like` is defined
instance : RelHomClass (r ↪r s) r s where
  coe := coeFn
  coe_injective' f g h := by
    rcases f with ⟨⟨⟩⟩
    rcases g with ⟨⟨⟩⟩
    congr
  map_rel f a b := Iff.mpr (map_rel_iff' f)

#print RelEmbedding.Simps.apply /-
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (h : r ↪r s) : α → β :=
  h
#align rel_embedding.simps.apply RelEmbedding.Simps.apply
-/

initialize_simps_projections RelEmbedding (to_embedding_to_fun → apply, -toEmbedding)

@[simp]
theorem to_rel_hom_eq_coe (f : r ↪r s) : f.toRelHom = f :=
  rfl
#align rel_embedding.to_rel_hom_eq_coe RelEmbedding.to_rel_hom_eq_coe

@[simp]
theorem coe_coe_fn (f : r ↪r s) : ((f : r →r s) : α → β) = f :=
  rfl
#align rel_embedding.coe_coe_fn RelEmbedding.coe_coe_fn

/- warning: rel_embedding.injective -> RelEmbedding.injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u1, u2} α β r s), Function.Injective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u2, u1} α β r s), Function.Injective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f))
Case conversion may be inaccurate. Consider using '#align rel_embedding.injective RelEmbedding.injectiveₓ'. -/
theorem injective (f : r ↪r s) : Injective f :=
  f.inj'
#align rel_embedding.injective RelEmbedding.injective

/- warning: rel_embedding.inj -> RelEmbedding.inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u1, u2} α β r s) {a : α} {b : α}, Iff (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f b)) (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u2, u1} α β r s) {a : α} {b : α}, Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f) b)) (Eq.{succ u2} α a b)
Case conversion may be inaccurate. Consider using '#align rel_embedding.inj RelEmbedding.injₓ'. -/
@[simp]
theorem inj (f : r ↪r s) {a b} : f a = f b ↔ a = b :=
  f.Injective.eq_iff
#align rel_embedding.inj RelEmbedding.inj

/- warning: rel_embedding.map_rel_iff -> RelEmbedding.map_rel_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u1, u2} α β r s) {a : α} {b : α}, Iff (s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f b)) (r a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u2, u1} α β r s) {a : α} {b : α}, Iff (s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f) b)) (r a b)
Case conversion may be inaccurate. Consider using '#align rel_embedding.map_rel_iff RelEmbedding.map_rel_iffₓ'. -/
theorem map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'
#align rel_embedding.map_rel_iff RelEmbedding.map_rel_iff

@[simp]
theorem coe_fn_mk (f : α ↪ β) (o) : (@RelEmbedding.mk _ _ r s f o : α → β) = f :=
  rfl
#align rel_embedding.coe_fn_mk RelEmbedding.coe_fn_mk

@[simp]
theorem coe_fn_to_embedding (f : r ↪r s) : (f.toEmbedding : α → β) = f :=
  rfl
#align rel_embedding.coe_fn_to_embedding RelEmbedding.coe_fn_to_embedding

/- warning: rel_embedding.coe_fn_injective -> RelEmbedding.coe_fn_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (ᾰ : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelEmbedding.{u2, u1} α β r s) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) ᾰ) (fun (f : RelEmbedding.{u2, u1} α β r s) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f))
Case conversion may be inaccurate. Consider using '#align rel_embedding.coe_fn_injective RelEmbedding.coe_fn_injectiveₓ'. -/
/-- The map `coe_fn : (r ↪r s) → (α → β)` is injective. -/
theorem coe_fn_injective : @Function.Injective (r ↪r s) (α → β) coeFn :=
  FunLike.coe_injective
#align rel_embedding.coe_fn_injective RelEmbedding.coe_fn_injective

/- warning: rel_embedding.ext -> RelEmbedding.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {{f : RelEmbedding.{u1, u2} α β r s}} {{g : RelEmbedding.{u1, u2} α β r s}}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) g x)) -> (Eq.{max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {{f : RelEmbedding.{u2, u1} α β r s}} {{g : RelEmbedding.{u2, u1} α β r s}}, (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s g) x)) -> (Eq.{max (succ u2) (succ u1)} (RelEmbedding.{u2, u1} α β r s) f g)
Case conversion may be inaccurate. Consider using '#align rel_embedding.ext RelEmbedding.extₓ'. -/
@[ext]
theorem ext ⦃f g : r ↪r s⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align rel_embedding.ext RelEmbedding.ext

/- warning: rel_embedding.ext_iff -> RelEmbedding.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : RelEmbedding.{u1, u2} α β r s} {g : RelEmbedding.{u1, u2} α β r s}, Iff (Eq.{max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) f g) (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : RelEmbedding.{u2, u1} α β r s} {g : RelEmbedding.{u2, u1} α β r s}, Iff (Eq.{max (succ u2) (succ u1)} (RelEmbedding.{u2, u1} α β r s) f g) (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s g) x))
Case conversion may be inaccurate. Consider using '#align rel_embedding.ext_iff RelEmbedding.ext_iffₓ'. -/
theorem ext_iff {f g : r ↪r s} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align rel_embedding.ext_iff RelEmbedding.ext_iff

#print RelEmbedding.refl /-
/-- Identity map is a relation embedding. -/
@[refl, simps]
protected def refl (r : α → α → Prop) : r ↪r r :=
  ⟨Embedding.refl _, fun a b => Iff.rfl⟩
#align rel_embedding.refl RelEmbedding.refl
-/

#print RelEmbedding.trans /-
/-- Composition of two relation embeddings is a relation embedding. -/
@[trans]
protected def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
  ⟨f.1.trans g.1, fun a b => by simp [f.map_rel_iff, g.map_rel_iff]⟩
#align rel_embedding.trans RelEmbedding.trans
-/

instance (r : α → α → Prop) : Inhabited (r ↪r r) :=
  ⟨RelEmbedding.refl _⟩

/- warning: rel_embedding.trans_apply -> RelEmbedding.trans_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : RelEmbedding.{u1, u2} α β r s) (g : RelEmbedding.{u2, u3} β γ s t) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (RelEmbedding.{u1, u3} α γ r t) (fun (_x : RelEmbedding.{u1, u3} α γ r t) => α -> γ) (RelEmbedding.hasCoeToFun.{u1, u3} α γ r t) (RelEmbedding.trans.{u1, u2, u3} α β γ r s t f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RelEmbedding.{u2, u3} β γ s t) (fun (_x : RelEmbedding.{u2, u3} β γ s t) => β -> γ) (RelEmbedding.hasCoeToFun.{u2, u3} β γ s t) g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : RelEmbedding.{u3, u2} α β r s) (g : RelEmbedding.{u2, u1} β γ s t) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => γ) a) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α γ) α γ (Function.instEmbeddingLikeEmbedding.{succ u3, succ u1} α γ)) (RelEmbedding.toEmbedding.{u3, u1} α γ r t (RelEmbedding.trans.{u3, u2, u1} α β γ r s t f g)) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) (RelEmbedding.toEmbedding.{u2, u1} β γ s t g) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β r s f) a))
Case conversion may be inaccurate. Consider using '#align rel_embedding.trans_apply RelEmbedding.trans_applyₓ'. -/
theorem trans_apply (f : r ↪r s) (g : s ↪r t) (a : α) : (f.trans g) a = g (f a) :=
  rfl
#align rel_embedding.trans_apply RelEmbedding.trans_apply

/- warning: rel_embedding.coe_trans -> RelEmbedding.coe_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : RelEmbedding.{u1, u2} α β r s) (g : RelEmbedding.{u2, u3} β γ s t), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (RelEmbedding.{u1, u3} α γ r t) (fun (_x : RelEmbedding.{u1, u3} α γ r t) => α -> γ) (RelEmbedding.hasCoeToFun.{u1, u3} α γ r t) (RelEmbedding.trans.{u1, u2, u3} α β γ r s t f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RelEmbedding.{u2, u3} β γ s t) (fun (_x : RelEmbedding.{u2, u3} β γ s t) => β -> γ) (RelEmbedding.hasCoeToFun.{u2, u3} β γ s t) g) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} (f : RelEmbedding.{u3, u2} α β r s) (g : RelEmbedding.{u2, u1} β γ s t), Eq.{max (succ u3) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => γ) ᾰ) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α γ) α γ (Function.instEmbeddingLikeEmbedding.{succ u3, succ u1} α γ)) (RelEmbedding.toEmbedding.{u3, u1} α γ r t (RelEmbedding.trans.{u3, u2, u1} α β γ r s t f g))) (Function.comp.{succ u3, succ u2, succ u1} α β γ (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) (RelEmbedding.toEmbedding.{u2, u1} β γ s t g)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β r s f)))
Case conversion may be inaccurate. Consider using '#align rel_embedding.coe_trans RelEmbedding.coe_transₓ'. -/
@[simp]
theorem coe_trans (f : r ↪r s) (g : s ↪r t) : ⇑(f.trans g) = g ∘ f :=
  rfl
#align rel_embedding.coe_trans RelEmbedding.coe_trans

#print RelEmbedding.swap /-
/-- A relation embedding is also a relation embedding between dual relations. -/
protected def swap (f : r ↪r s) : swap r ↪r swap s :=
  ⟨f.toEmbedding, fun a b => f.map_rel_iff⟩
#align rel_embedding.swap RelEmbedding.swap
-/

#print RelEmbedding.preimage /-
/-- If `f` is injective, then it is a relation embedding from the
  preimage relation of `s` to `s`. -/
def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ↪r s :=
  ⟨f, fun a b => Iff.rfl⟩
#align rel_embedding.preimage RelEmbedding.preimage
-/

/- warning: rel_embedding.eq_preimage -> RelEmbedding.eq_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u1, u2} α β r s), Eq.{succ u1} (α -> α -> Prop) r (Order.Preimage.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u2, u1} α β r s), Eq.{succ u2} (α -> α -> Prop) r (Order.Preimage.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f)) s)
Case conversion may be inaccurate. Consider using '#align rel_embedding.eq_preimage RelEmbedding.eq_preimageₓ'. -/
theorem eq_preimage (f : r ↪r s) : r = f ⁻¹'o s :=
  by
  ext (a b)
  exact f.map_rel_iff.symm
#align rel_embedding.eq_preimage RelEmbedding.eq_preimage

/- warning: rel_embedding.is_irrefl -> RelEmbedding.isIrrefl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsIrrefl.{u2} β s], IsIrrefl.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsIrrefl.{u1} β s], IsIrrefl.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_irrefl RelEmbedding.isIrreflₓ'. -/
protected theorem isIrrefl (f : r ↪r s) [IsIrrefl β s] : IsIrrefl α r :=
  ⟨fun a => mt f.map_rel_iff.2 (irrefl (f a))⟩
#align rel_embedding.is_irrefl RelEmbedding.isIrrefl

/- warning: rel_embedding.is_refl -> RelEmbedding.isRefl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsRefl.{u2} β s], IsRefl.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsRefl.{u1} β s], IsRefl.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_refl RelEmbedding.isReflₓ'. -/
protected theorem isRefl (f : r ↪r s) [IsRefl β s] : IsRefl α r :=
  ⟨fun a => f.map_rel_iff.1 <| refl _⟩
#align rel_embedding.is_refl RelEmbedding.isRefl

/- warning: rel_embedding.is_symm -> RelEmbedding.isSymm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsSymm.{u2} β s], IsSymm.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsSymm.{u1} β s], IsSymm.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_symm RelEmbedding.isSymmₓ'. -/
protected theorem isSymm (f : r ↪r s) [IsSymm β s] : IsSymm α r :=
  ⟨fun a b => imp_imp_imp f.map_rel_iff.2 f.map_rel_iff.1 symm⟩
#align rel_embedding.is_symm RelEmbedding.isSymm

/- warning: rel_embedding.is_asymm -> RelEmbedding.isAsymm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsAsymm.{u2} β s], IsAsymm.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsAsymm.{u1} β s], IsAsymm.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_asymm RelEmbedding.isAsymmₓ'. -/
protected theorem isAsymm (f : r ↪r s) [IsAsymm β s] : IsAsymm α r :=
  ⟨fun a b h₁ h₂ => asymm (f.map_rel_iff.2 h₁) (f.map_rel_iff.2 h₂)⟩
#align rel_embedding.is_asymm RelEmbedding.isAsymm

/- warning: rel_embedding.is_antisymm -> RelEmbedding.isAntisymm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsAntisymm.{u2} β s], IsAntisymm.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsAntisymm.{u1} β s], IsAntisymm.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_antisymm RelEmbedding.isAntisymmₓ'. -/
protected theorem isAntisymm : ∀ (f : r ↪r s) [IsAntisymm β s], IsAntisymm α r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun a b h₁ h₂ => f.inj' (H _ _ (o.2 h₁) (o.2 h₂))⟩
#align rel_embedding.is_antisymm RelEmbedding.isAntisymm

/- warning: rel_embedding.is_trans -> RelEmbedding.isTrans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsTrans.{u2} β s], IsTrans.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsTrans.{u1} β s], IsTrans.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_trans RelEmbedding.isTransₓ'. -/
protected theorem isTrans : ∀ (f : r ↪r s) [IsTrans β s], IsTrans α r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun a b c h₁ h₂ => o.1 (H _ _ _ (o.2 h₁) (o.2 h₂))⟩
#align rel_embedding.is_trans RelEmbedding.isTrans

/- warning: rel_embedding.is_total -> RelEmbedding.isTotal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsTotal.{u2} β s], IsTotal.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsTotal.{u1} β s], IsTotal.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_total RelEmbedding.isTotalₓ'. -/
protected theorem isTotal : ∀ (f : r ↪r s) [IsTotal β s], IsTotal α r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun a b => (or_congr o o).1 (H _ _)⟩
#align rel_embedding.is_total RelEmbedding.isTotal

/- warning: rel_embedding.is_preorder -> RelEmbedding.isPreorder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsPreorder.{u2} β s], IsPreorder.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsPreorder.{u1} β s], IsPreorder.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_preorder RelEmbedding.isPreorderₓ'. -/
protected theorem isPreorder : ∀ (f : r ↪r s) [IsPreorder β s], IsPreorder α r
  | f, H => { f.is_refl, f.is_trans with }
#align rel_embedding.is_preorder RelEmbedding.isPreorder

/- warning: rel_embedding.is_partial_order -> RelEmbedding.isPartialOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsPartialOrder.{u2} β s], IsPartialOrder.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsPartialOrder.{u1} β s], IsPartialOrder.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_partial_order RelEmbedding.isPartialOrderₓ'. -/
protected theorem isPartialOrder : ∀ (f : r ↪r s) [IsPartialOrder β s], IsPartialOrder α r
  | f, H => { f.is_preorder, f.is_antisymm with }
#align rel_embedding.is_partial_order RelEmbedding.isPartialOrder

/- warning: rel_embedding.is_linear_order -> RelEmbedding.isLinearOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsLinearOrder.{u2} β s], IsLinearOrder.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsLinearOrder.{u1} β s], IsLinearOrder.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_linear_order RelEmbedding.isLinearOrderₓ'. -/
protected theorem isLinearOrder : ∀ (f : r ↪r s) [IsLinearOrder β s], IsLinearOrder α r
  | f, H => { f.is_partial_order, f.is_total with }
#align rel_embedding.is_linear_order RelEmbedding.isLinearOrder

/- warning: rel_embedding.is_strict_order -> RelEmbedding.isStrictOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsStrictOrder.{u2} β s], IsStrictOrder.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsStrictOrder.{u1} β s], IsStrictOrder.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_strict_order RelEmbedding.isStrictOrderₓ'. -/
protected theorem isStrictOrder : ∀ (f : r ↪r s) [IsStrictOrder β s], IsStrictOrder α r
  | f, H => { f.is_irrefl, f.is_trans with }
#align rel_embedding.is_strict_order RelEmbedding.isStrictOrder

/- warning: rel_embedding.is_trichotomous -> RelEmbedding.isTrichotomous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsTrichotomous.{u2} β s], IsTrichotomous.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsTrichotomous.{u1} β s], IsTrichotomous.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_trichotomous RelEmbedding.isTrichotomousₓ'. -/
protected theorem isTrichotomous : ∀ (f : r ↪r s) [IsTrichotomous β s], IsTrichotomous α r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun a b => (or_congr o (or_congr f.inj'.eq_iff o)).1 (H _ _)⟩
#align rel_embedding.is_trichotomous RelEmbedding.isTrichotomous

/- warning: rel_embedding.is_strict_total_order -> RelEmbedding.isStrictTotalOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsStrictTotalOrder.{u2} β s], IsStrictTotalOrder.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsStrictTotalOrder.{u1} β s], IsStrictTotalOrder.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_strict_total_order RelEmbedding.isStrictTotalOrderₓ'. -/
protected theorem isStrictTotalOrder :
    ∀ (f : r ↪r s) [IsStrictTotalOrder β s], IsStrictTotalOrder α r
  | f, H => { f.is_trichotomous, f.is_strict_order with }
#align rel_embedding.is_strict_total_order RelEmbedding.isStrictTotalOrder

/- warning: rel_embedding.acc -> RelEmbedding.acc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u1, u2} α β r s) (a : α), (Acc.{succ u2} β s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a)) -> (Acc.{succ u1} α r a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u2, u1} α β r s) (a : α), (Acc.{succ u1} β s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s f) a)) -> (Acc.{succ u2} α r a)
Case conversion may be inaccurate. Consider using '#align rel_embedding.acc RelEmbedding.accₓ'. -/
protected theorem acc (f : r ↪r s) (a : α) : Acc s (f a) → Acc r a :=
  by
  generalize h : f a = b; intro ac
  induction' ac with _ H IH generalizing a; subst h
  exact ⟨_, fun a' h => IH (f a') (f.map_rel_iff.2 h) _ rfl⟩
#align rel_embedding.acc RelEmbedding.acc

/- warning: rel_embedding.well_founded -> RelEmbedding.wellFounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (WellFounded.{succ u2} β s) -> (WellFounded.{succ u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (WellFounded.{succ u1} β s) -> (WellFounded.{succ u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.well_founded RelEmbedding.wellFoundedₓ'. -/
protected theorem wellFounded : ∀ (f : r ↪r s) (h : WellFounded s), WellFounded r
  | f, ⟨H⟩ => ⟨fun a => f.Acc _ (H _)⟩
#align rel_embedding.well_founded RelEmbedding.wellFounded

/- warning: rel_embedding.is_well_order -> RelEmbedding.isWellOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u1, u2} α β r s) -> (forall [_inst_1 : IsWellOrder.{u2} β s], IsWellOrder.{u1} α r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, (RelEmbedding.{u2, u1} α β r s) -> (forall [_inst_1 : IsWellOrder.{u1} β s], IsWellOrder.{u2} α r)
Case conversion may be inaccurate. Consider using '#align rel_embedding.is_well_order RelEmbedding.isWellOrderₓ'. -/
protected theorem isWellOrder : ∀ (f : r ↪r s) [IsWellOrder β s], IsWellOrder α r
  | f, H => { f.is_strict_total_order with wf := f.well_founded H.wf }
#align rel_embedding.is_well_order RelEmbedding.isWellOrder

#print Quotient.outRelEmbedding /-
/-- `quotient.out` as a relation embedding between the lift of a relation and the relation. -/
@[simps]
noncomputable def Quotient.outRelEmbedding [s : Setoid α] {r : α → α → Prop} (H) :
    Quotient.lift₂ r H ↪r r :=
  ⟨Embedding.quotientOut α,
    by
    refine' fun x y => Quotient.induction_on₂ x y fun a b => _
    apply iff_iff_eq.2 (H _ _ _ _ _ _) <;> apply Quotient.mk_out⟩
#align quotient.out_rel_embedding Quotient.outRelEmbedding
-/

#print wellFounded_lift₂_iff /-
/-- A relation is well founded iff its lift to a quotient is. -/
@[simp]
theorem wellFounded_lift₂_iff [s : Setoid α] {r : α → α → Prop} {H} :
    WellFounded (Quotient.lift₂ r H) ↔ WellFounded r :=
  ⟨fun hr =>
    by
    suffices ∀ {x : Quotient s} {a : α}, ⟦a⟧ = x → Acc r a by exact ⟨fun a => this rfl⟩
    · refine' fun x => hr.induction x _
      rintro x IH a rfl
      exact ⟨_, fun b hb => IH ⟦b⟧ hb rfl⟩, (Quotient.outRelEmbedding H).WellFounded⟩
#align well_founded_lift₂_iff wellFounded_lift₂_iff
-/

alias _root_.well_founded_lift₂_iff ↔
  _root_.well_founded.of_quotient_lift₂ _root_.well_founded.quotient_lift₂

#print RelEmbedding.ofMapRelIff /-
/--
To define an relation embedding from an antisymmetric relation `r` to a reflexive relation `s` it
suffices to give a function together with a proof that it satisfies `s (f a) (f b) ↔ r a b`.
-/
def ofMapRelIff (f : α → β) [IsAntisymm α r] [IsRefl β s] (hf : ∀ a b, s (f a) (f b) ↔ r a b) :
    r ↪r s where
  toFun := f
  inj' x y h := antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _))
  map_rel_iff' := hf
#align rel_embedding.of_map_rel_iff RelEmbedding.ofMapRelIff
-/

/- warning: rel_embedding.of_map_rel_iff_coe -> RelEmbedding.ofMapRelIff_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : α -> β) [_inst_1 : IsAntisymm.{u1} α r] [_inst_2 : IsRefl.{u2} β s] (hf : forall (a : α) (b : α), Iff (s (f a) (f b)) (r a b)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) (RelEmbedding.ofMapRelIff.{u1, u2} α β r s f _inst_1 _inst_2 hf)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : α -> β) [_inst_1 : IsAntisymm.{u2} α r] [_inst_2 : IsRefl.{u1} β s] (hf : forall (a : α) (b : α), Iff (s (f a) (f b)) (r a b)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelEmbedding.ofMapRelIff.{u2, u1} α β r s f _inst_1 _inst_2 hf))) f
Case conversion may be inaccurate. Consider using '#align rel_embedding.of_map_rel_iff_coe RelEmbedding.ofMapRelIff_coeₓ'. -/
@[simp]
theorem ofMapRelIff_coe (f : α → β) [IsAntisymm α r] [IsRefl β s]
    (hf : ∀ a b, s (f a) (f b) ↔ r a b) : ⇑(ofMapRelIff f hf : r ↪r s) = f :=
  rfl
#align rel_embedding.of_map_rel_iff_coe RelEmbedding.ofMapRelIff_coe

#print RelEmbedding.ofMonotone /-
/-- It suffices to prove `f` is monotone between strict relations
  to show it is a relation embedding. -/
def ofMonotone [IsTrichotomous α r] [IsAsymm β s] (f : α → β) (H : ∀ a b, r a b → s (f a) (f b)) :
    r ↪r s := by
  haveI := @IsAsymm.is_irrefl β s _
  refine' ⟨⟨f, fun a b e => _⟩, fun a b => ⟨fun h => _, H _ _⟩⟩
  ·
    refine' ((@trichotomous _ r _ a b).resolve_left _).resolve_right _ <;>
      exact fun h => @irrefl _ s _ _ (by simpa [e] using H _ _ h)
  · refine' (@trichotomous _ r _ a b).resolve_right (Or.ndrec (fun e => _) fun h' => _)
    · subst e
      exact irrefl _ h
    · exact asymm (H _ _ h') h
#align rel_embedding.of_monotone RelEmbedding.ofMonotone
-/

/- warning: rel_embedding.of_monotone_coe -> RelEmbedding.ofMonotone_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrichotomous.{u1} α r] [_inst_2 : IsAsymm.{u2} β s] (f : α -> β) (H : forall (a : α) (b : α), (r a b) -> (s (f a) (f b))), Eq.{max (succ u1) (succ u2)} ((fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.ofMonotone.{u1, u2} α β r s _inst_1 _inst_2 f H)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) (RelEmbedding.ofMonotone.{u1, u2} α β r s _inst_1 _inst_2 f H)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrichotomous.{u2} α r] [_inst_2 : IsAsymm.{u1} β s] (f : α -> β) (H : forall (a : α) (b : α), (r a b) -> (s (f a) (f b))), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelEmbedding.ofMonotone.{u2, u1} α β r s _inst_1 _inst_2 f H))) f
Case conversion may be inaccurate. Consider using '#align rel_embedding.of_monotone_coe RelEmbedding.ofMonotone_coeₓ'. -/
@[simp]
theorem ofMonotone_coe [IsTrichotomous α r] [IsAsymm β s] (f : α → β) (H) :
    (@ofMonotone _ _ r s _ _ f H : α → β) = f :=
  rfl
#align rel_embedding.of_monotone_coe RelEmbedding.ofMonotone_coe

#print RelEmbedding.ofIsEmpty /-
/-- A relation embedding from an empty type. -/
def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ↪r s :=
  ⟨Embedding.ofIsEmpty, isEmptyElim⟩
#align rel_embedding.of_is_empty RelEmbedding.ofIsEmpty
-/

#print RelEmbedding.sumLiftRelInl /-
/-- `sum.inl` as a relation embedding into `sum.lift_rel r s`. -/
@[simps]
def sumLiftRelInl (r : α → α → Prop) (s : β → β → Prop) : r ↪r Sum.LiftRel r s
    where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' a b := Sum.liftRel_inl_inl
#align rel_embedding.sum_lift_rel_inl RelEmbedding.sumLiftRelInl
-/

#print RelEmbedding.sumLiftRelInr /-
/-- `sum.inr` as a relation embedding into `sum.lift_rel r s`. -/
@[simps]
def sumLiftRelInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.LiftRel r s
    where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' a b := Sum.liftRel_inr_inr
#align rel_embedding.sum_lift_rel_inr RelEmbedding.sumLiftRelInr
-/

#print RelEmbedding.sumLiftRelMap /-
/-- `sum.map` as a relation embedding between `sum.lift_rel` relations. -/
@[simps]
def sumLiftRelMap (f : r ↪r s) (g : t ↪r u) : Sum.LiftRel r t ↪r Sum.LiftRel s u
    where
  toFun := Sum.map f g
  inj' := f.Injective.sum_map g.Injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]
#align rel_embedding.sum_lift_rel_map RelEmbedding.sumLiftRelMap
-/

#print RelEmbedding.sumLexInl /-
/-- `sum.inl` as a relation embedding into `sum.lex r s`. -/
@[simps]
def sumLexInl (r : α → α → Prop) (s : β → β → Prop) : r ↪r Sum.Lex r s
    where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' a b := Sum.lex_inl_inl
#align rel_embedding.sum_lex_inl RelEmbedding.sumLexInl
-/

#print RelEmbedding.sumLexInr /-
/-- `sum.inr` as a relation embedding into `sum.lex r s`. -/
@[simps]
def sumLexInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.Lex r s
    where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' a b := Sum.lex_inr_inr
#align rel_embedding.sum_lex_inr RelEmbedding.sumLexInr
-/

#print RelEmbedding.sumLexMap /-
/-- `sum.map` as a relation embedding between `sum.lex` relations. -/
@[simps]
def sumLexMap (f : r ↪r s) (g : t ↪r u) : Sum.Lex r t ↪r Sum.Lex s u
    where
  toFun := Sum.map f g
  inj' := f.Injective.sum_map g.Injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]
#align rel_embedding.sum_lex_map RelEmbedding.sumLexMap
-/

#print RelEmbedding.prodLexMkLeft /-
/-- `λ b, prod.mk a b` as a relation embedding. -/
@[simps]
def prodLexMkLeft (s : β → β → Prop) {a : α} (h : ¬r a a) : s ↪r Prod.Lex r s
    where
  toFun := Prod.mk a
  inj' := Prod.mk.inj_left a
  map_rel_iff' b₁ b₂ := by simp [Prod.lex_def, h]
#align rel_embedding.prod_lex_mk_left RelEmbedding.prodLexMkLeft
-/

#print RelEmbedding.prodLexMkRight /-
/-- `λ a, prod.mk a b` as a relation embedding. -/
@[simps]
def prodLexMkRight (r : α → α → Prop) {b : β} (h : ¬s b b) : r ↪r Prod.Lex r s
    where
  toFun a := (a, b)
  inj' := Prod.mk.inj_right b
  map_rel_iff' a₁ a₂ := by simp [Prod.lex_def, h]
#align rel_embedding.prod_lex_mk_right RelEmbedding.prodLexMkRight
-/

#print RelEmbedding.prodLexMap /-
/-- `prod.map` as a relation embedding. -/
@[simps]
def prodLexMap (f : r ↪r s) (g : t ↪r u) : Prod.Lex r t ↪r Prod.Lex s u
    where
  toFun := Prod.map f g
  inj' := f.Injective.prod_map g.Injective
  map_rel_iff' a b := by simp [Prod.lex_def, f.map_rel_iff, g.map_rel_iff]
#align rel_embedding.prod_lex_map RelEmbedding.prodLexMap
-/

end RelEmbedding

#print RelIso /-
/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
structure RelIso {α β : Type _} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β where
  map_rel_iff' : ∀ {a b}, s (to_equiv a) (to_equiv b) ↔ r a b
#align rel_iso RelIso
-/

-- mathport name: «expr ≃r »
infixl:25 " ≃r " => RelIso

namespace RelIso

#print RelIso.toRelEmbedding /-
/-- Convert an `rel_iso` to an `rel_embedding`. This function is also available as a coercion
but often it is easier to write `f.to_rel_embedding` than to write explicitly `r` and `s`
in the target type. -/
def toRelEmbedding (f : r ≃r s) : r ↪r s :=
  ⟨f.toEquiv.toEmbedding, fun _ _ => f.map_rel_iff'⟩
#align rel_iso.to_rel_embedding RelIso.toRelEmbedding
-/

/- warning: rel_iso.to_equiv_injective -> RelIso.toEquiv_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, Function.Injective.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (RelIso.{u1, u2} α β r s) (Equiv.{succ u1, succ u2} α β) (RelIso.toEquiv.{u1, u2} α β r s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelIso.{u2, u1} α β r s) (Equiv.{succ u2, succ u1} α β) (RelIso.toEquiv.{u2, u1} α β r s)
Case conversion may be inaccurate. Consider using '#align rel_iso.to_equiv_injective RelIso.toEquiv_injectiveₓ'. -/
theorem toEquiv_injective : Injective (toEquiv : r ≃r s → α ≃ β)
  | ⟨e₁, o₁⟩, ⟨e₂, o₂⟩, h => by
    congr
    exact h
#align rel_iso.to_equiv_injective RelIso.toEquiv_injective

instance : Coe (r ≃r s) (r ↪r s) :=
  ⟨toRelEmbedding⟩

-- see Note [function coercion]
instance : CoeFun (r ≃r s) fun _ => α → β :=
  ⟨fun f => f⟩

-- TODO: define and instantiate a `rel_iso_class` when `equiv_like` is defined
instance : RelHomClass (r ≃r s) r s where
  coe := coeFn
  coe_injective' := Equiv.coe_fn_injective.comp toEquiv_injective
  map_rel f a b := Iff.mpr (map_rel_iff' f)

@[simp]
theorem to_rel_embedding_eq_coe (f : r ≃r s) : f.toRelEmbedding = f :=
  rfl
#align rel_iso.to_rel_embedding_eq_coe RelIso.to_rel_embedding_eq_coe

@[simp]
theorem coe_coe_fn (f : r ≃r s) : ((f : r ↪r s) : α → β) = f :=
  rfl
#align rel_iso.coe_coe_fn RelIso.coe_coe_fn

/- warning: rel_iso.map_rel_iff -> RelIso.map_rel_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelIso.{u1, u2} α β r s) {a : α} {b : α}, Iff (s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) f b)) (r a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelIso.{u2, u1} α β r s) {a : α} {b : α}, Iff (s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s f)) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s f)) b)) (r a b)
Case conversion may be inaccurate. Consider using '#align rel_iso.map_rel_iff RelIso.map_rel_iffₓ'. -/
theorem map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'
#align rel_iso.map_rel_iff RelIso.map_rel_iff

/- warning: rel_iso.coe_fn_mk -> RelIso.coe_fn_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : Equiv.{succ u1, succ u2} α β) (o : forall {{a : α}} {{b : α}}, Iff (s (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f a) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f b)) (r a b)), Eq.{max (succ u1) (succ u2)} ((fun (_x : RelIso.{u1, u2} α β (fun (a : α) (b : α) => r a b) s) => α -> β) (RelIso.mk.{u1, u2} α β (fun (a : α) (b : α) => r a b) s f o)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β (fun (a : α) (b : α) => r a b) s) (fun (_x : RelIso.{u1, u2} α β (fun (a : α) (b : α) => r a b) s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (fun (a : α) (b : α) => r a b) s) (RelIso.mk.{u1, u2} α β (fun (a : α) (b : α) => r a b) s f o)) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : Equiv.{succ u2, succ u1} α β) (o : forall {{a : α}} {{b : α}}, Iff (s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α β))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α β))) f b)) (r a b)), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (a : α) (b : α) => r a b) s (RelIso.toRelEmbedding.{u2, u1} α β (fun (a : α) (b : α) => r a b) s (RelIso.mk.{u2, u1} α β (fun (a : α) (b : α) => r a b) s f o)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α β))) f)
Case conversion may be inaccurate. Consider using '#align rel_iso.coe_fn_mk RelIso.coe_fn_mkₓ'. -/
@[simp]
theorem coe_fn_mk (f : α ≃ β) (o : ∀ ⦃a b⦄, s (f a) (f b) ↔ r a b) : (RelIso.mk f o : α → β) = f :=
  rfl
#align rel_iso.coe_fn_mk RelIso.coe_fn_mk

/- warning: rel_iso.coe_fn_to_equiv -> RelIso.coe_fn_toEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelIso.{u1, u2} α β r s), Eq.{max (succ u1) (succ u2)} ((fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (RelIso.toEquiv.{u1, u2} α β r s f)) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) (RelIso.toEquiv.{u1, u2} α β r s f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelIso.{u2, u1} α β r s), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α β))) (RelIso.toEquiv.{u2, u1} α β r s f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s f)))
Case conversion may be inaccurate. Consider using '#align rel_iso.coe_fn_to_equiv RelIso.coe_fn_toEquivₓ'. -/
@[simp]
theorem coe_fn_toEquiv (f : r ≃r s) : (f.toEquiv : α → β) = f :=
  rfl
#align rel_iso.coe_fn_to_equiv RelIso.coe_fn_toEquiv

/- warning: rel_iso.coe_fn_injective -> RelIso.coe_fn_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop}, Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (ᾰ : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelIso.{u2, u1} α β r s) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) ᾰ) (fun (f : RelIso.{u2, u1} α β r s) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s f)))
Case conversion may be inaccurate. Consider using '#align rel_iso.coe_fn_injective RelIso.coe_fn_injectiveₓ'. -/
/-- The map `coe_fn : (r ≃r s) → (α → β)` is injective. Lean fails to parse
`function.injective (λ e : r ≃r s, (e : α → β))`, so we use a trick to say the same. -/
theorem coe_fn_injective : @Function.Injective (r ≃r s) (α → β) coeFn :=
  FunLike.coe_injective
#align rel_iso.coe_fn_injective RelIso.coe_fn_injective

/- warning: rel_iso.ext -> RelIso.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {{f : RelIso.{u1, u2} α β r s}} {{g : RelIso.{u1, u2} α β r s}}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) g x)) -> (Eq.{max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {{f : RelIso.{u2, u1} α β r s}} {{g : RelIso.{u2, u1} α β r s}}, (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s f)) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s g)) x)) -> (Eq.{max (succ u2) (succ u1)} (RelIso.{u2, u1} α β r s) f g)
Case conversion may be inaccurate. Consider using '#align rel_iso.ext RelIso.extₓ'. -/
@[ext]
theorem ext ⦃f g : r ≃r s⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align rel_iso.ext RelIso.ext

/- warning: rel_iso.ext_iff -> RelIso.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : RelIso.{u1, u2} α β r s} {g : RelIso.{u1, u2} α β r s}, Iff (Eq.{max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) f g) (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} {f : RelIso.{u2, u1} α β r s} {g : RelIso.{u2, u1} α β r s}, Iff (Eq.{max (succ u2) (succ u1)} (RelIso.{u2, u1} α β r s) f g) (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s f)) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s g)) x))
Case conversion may be inaccurate. Consider using '#align rel_iso.ext_iff RelIso.ext_iffₓ'. -/
theorem ext_iff {f g : r ≃r s} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align rel_iso.ext_iff RelIso.ext_iff

#print RelIso.symm /-
/-- Inverse map of a relation isomorphism is a relation isomorphism. -/
@[symm]
protected def symm (f : r ≃r s) : s ≃r r :=
  ⟨f.toEquiv.symm, fun a b => by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩
#align rel_iso.symm RelIso.symm
-/

#print RelIso.Simps.apply /-
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : r ≃r s) : α → β :=
  h
#align rel_iso.simps.apply RelIso.Simps.apply
-/

#print RelIso.Simps.symmApply /-
/-- See Note [custom simps projection]. -/
def Simps.symmApply (h : r ≃r s) : β → α :=
  h.symm
#align rel_iso.simps.symm_apply RelIso.Simps.symmApply
-/

initialize_simps_projections RelIso (to_equiv_to_fun → apply, to_equiv_inv_fun → symmApply,
  -toEquiv)

#print RelIso.refl /-
/-- Identity map is a relation isomorphism. -/
@[refl, simps apply]
protected def refl (r : α → α → Prop) : r ≃r r :=
  ⟨Equiv.refl _, fun a b => Iff.rfl⟩
#align rel_iso.refl RelIso.refl
-/

#print RelIso.trans /-
/-- Composition of two relation isomorphisms is a relation isomorphism. -/
@[trans, simps apply]
protected def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
  ⟨f₁.toEquiv.trans f₂.toEquiv, fun a b => f₂.map_rel_iff.trans f₁.map_rel_iff⟩
#align rel_iso.trans RelIso.trans
-/

instance (r : α → α → Prop) : Inhabited (r ≃r r) :=
  ⟨RelIso.refl _⟩

#print RelIso.default_def /-
@[simp]
theorem default_def (r : α → α → Prop) : default = RelIso.refl r :=
  rfl
#align rel_iso.default_def RelIso.default_def
-/

#print RelIso.cast /-
/-- A relation isomorphism between equal relations on equal types. -/
@[simps toEquiv apply]
protected def cast {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β)
    (h₂ : HEq r s) : r ≃r s :=
  ⟨Equiv.cast h₁, fun a b => by
    subst h₁
    rw [eq_of_heq h₂]
    rfl⟩
#align rel_iso.cast RelIso.cast
-/

#print RelIso.cast_symm /-
@[simp]
protected theorem cast_symm {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β)
    (h₂ : HEq r s) : (RelIso.cast h₁ h₂).symm = RelIso.cast h₁.symm h₂.symm :=
  rfl
#align rel_iso.cast_symm RelIso.cast_symm
-/

#print RelIso.cast_refl /-
@[simp]
protected theorem cast_refl {α : Type u} {r : α → α → Prop} (h₁ : α = α := rfl)
    (h₂ : HEq r r := HEq.rfl) : RelIso.cast h₁ h₂ = RelIso.refl r :=
  rfl
#align rel_iso.cast_refl RelIso.cast_refl
-/

#print RelIso.cast_trans /-
@[simp]
protected theorem cast_trans {α β γ : Type u} {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} (h₁ : α = β) (h₁' : β = γ) (h₂ : HEq r s) (h₂' : HEq s t) :
    (RelIso.cast h₁ h₂).trans (RelIso.cast h₁' h₂') = RelIso.cast (h₁.trans h₁') (h₂.trans h₂') :=
  ext fun x => by
    subst h₁
    rfl
#align rel_iso.cast_trans RelIso.cast_trans
-/

#print RelIso.swap /-
/-- a relation isomorphism is also a relation isomorphism between dual relations. -/
protected def swap (f : r ≃r s) : swap r ≃r swap s :=
  ⟨f.toEquiv, fun _ _ => f.map_rel_iff⟩
#align rel_iso.swap RelIso.swap
-/

/- warning: rel_iso.coe_fn_symm_mk -> RelIso.coe_fn_symm_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : Equiv.{succ u1, succ u2} α β) (o : forall {a : α} {b : α}, Iff (s (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f a) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f b)) (r a b)), Eq.{max (succ u2) (succ u1)} ((fun (_x : RelIso.{u2, u1} β α s r) => β -> α) (RelIso.symm.{u1, u2} α β r s (RelIso.mk.{u1, u2} α β r s f o))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelIso.{u2, u1} β α s r) (fun (_x : RelIso.{u2, u1} β α s r) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α s r) (RelIso.symm.{u1, u2} α β r s (RelIso.mk.{u1, u2} α β r s f o))) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : Equiv.{succ u2, succ u1} α β) (o : forall {a : α} {b : α}, Iff (s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α β))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α β (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α β))) f b)) (r a b)), Eq.{max (succ u2) (succ u1)} (forall (a : β), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α s r (RelIso.toRelEmbedding.{u1, u2} β α s r (RelIso.symm.{u2, u1} α β r s (RelIso.mk.{u2, u1} α β r s f o))))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β α (Equiv.instEquivLikeEquiv.{succ u1, succ u2} β α))) (Equiv.symm.{succ u2, succ u1} α β f))
Case conversion may be inaccurate. Consider using '#align rel_iso.coe_fn_symm_mk RelIso.coe_fn_symm_mkₓ'. -/
@[simp]
theorem coe_fn_symm_mk (f o) : ((@RelIso.mk _ _ r s f o).symm : β → α) = f.symm :=
  rfl
#align rel_iso.coe_fn_symm_mk RelIso.coe_fn_symm_mk

/- warning: rel_iso.apply_symm_apply -> RelIso.apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u1, u2} α β r s) (x : β), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) e (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelIso.{u2, u1} β α s r) (fun (_x : RelIso.{u2, u1} β α s r) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α s r) (RelIso.symm.{u1, u2} α β r s e) x)) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u2, u1} α β r s) (x : β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) a) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α s r (RelIso.toRelEmbedding.{u1, u2} β α s r (RelIso.symm.{u2, u1} α β r s e))) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α s r (RelIso.toRelEmbedding.{u1, u2} β α s r (RelIso.symm.{u2, u1} α β r s e))) x)) x
Case conversion may be inaccurate. Consider using '#align rel_iso.apply_symm_apply RelIso.apply_symm_applyₓ'. -/
@[simp]
theorem apply_symm_apply (e : r ≃r s) (x : β) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x
#align rel_iso.apply_symm_apply RelIso.apply_symm_apply

/- warning: rel_iso.symm_apply_apply -> RelIso.symm_apply_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u1, u2} α β r s) (x : α), Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelIso.{u2, u1} β α s r) (fun (_x : RelIso.{u2, u1} β α s r) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α s r) (RelIso.symm.{u1, u2} α β r s e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) e x)) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u2, u1} α β r s) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)) x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α s r (RelIso.toRelEmbedding.{u1, u2} β α s r (RelIso.symm.{u2, u1} α β r s e))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)) x)) x
Case conversion may be inaccurate. Consider using '#align rel_iso.symm_apply_apply RelIso.symm_apply_applyₓ'. -/
@[simp]
theorem symm_apply_apply (e : r ≃r s) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
#align rel_iso.symm_apply_apply RelIso.symm_apply_apply

/- warning: rel_iso.rel_symm_apply -> RelIso.rel_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u1, u2} α β r s) {x : α} {y : β}, Iff (r x (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelIso.{u2, u1} β α s r) (fun (_x : RelIso.{u2, u1} β α s r) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α s r) (RelIso.symm.{u1, u2} α β r s e) y)) (s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) e x) y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u2, u1} α β r s) {x : α} {y : β}, Iff (r x (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α s r (RelIso.toRelEmbedding.{u1, u2} β α s r (RelIso.symm.{u2, u1} α β r s e))) y)) (s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)) x) y)
Case conversion may be inaccurate. Consider using '#align rel_iso.rel_symm_apply RelIso.rel_symm_applyₓ'. -/
theorem rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y) ↔ s (e x) y := by
  rw [← e.map_rel_iff, e.apply_symm_apply]
#align rel_iso.rel_symm_apply RelIso.rel_symm_apply

/- warning: rel_iso.symm_apply_rel -> RelIso.symm_apply_rel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u1, u2} α β r s) {x : β} {y : α}, Iff (r (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RelIso.{u2, u1} β α s r) (fun (_x : RelIso.{u2, u1} β α s r) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α s r) (RelIso.symm.{u1, u2} α β r s e) x) y) (s x (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) e y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u2, u1} α β r s) {x : β} {y : α}, Iff (r (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α s r (RelIso.toRelEmbedding.{u1, u2} β α s r (RelIso.symm.{u2, u1} α β r s e))) x) y) (s x (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)) y))
Case conversion may be inaccurate. Consider using '#align rel_iso.symm_apply_rel RelIso.symm_apply_relₓ'. -/
theorem symm_apply_rel (e : r ≃r s) {x y} : r (e.symm x) y ↔ s x (e y) := by
  rw [← e.map_rel_iff, e.apply_symm_apply]
#align rel_iso.symm_apply_rel RelIso.symm_apply_rel

/- warning: rel_iso.bijective -> RelIso.bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u1, u2} α β r s), Function.Bijective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u2, u1} α β r s), Function.Bijective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)))
Case conversion may be inaccurate. Consider using '#align rel_iso.bijective RelIso.bijectiveₓ'. -/
protected theorem bijective (e : r ≃r s) : Bijective e :=
  e.toEquiv.Bijective
#align rel_iso.bijective RelIso.bijective

/- warning: rel_iso.injective -> RelIso.injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u1, u2} α β r s), Function.Injective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u2, u1} α β r s), Function.Injective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)))
Case conversion may be inaccurate. Consider using '#align rel_iso.injective RelIso.injectiveₓ'. -/
protected theorem injective (e : r ≃r s) : Injective e :=
  e.toEquiv.Injective
#align rel_iso.injective RelIso.injective

/- warning: rel_iso.surjective -> RelIso.surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u1, u2} α β r s), Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u2, u1} α β r s), Function.Surjective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)))
Case conversion may be inaccurate. Consider using '#align rel_iso.surjective RelIso.surjectiveₓ'. -/
protected theorem surjective (e : r ≃r s) : Surjective e :=
  e.toEquiv.Surjective
#align rel_iso.surjective RelIso.surjective

/- warning: rel_iso.eq_iff_eq -> RelIso.eq_iff_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelIso.{u1, u2} α β r s) {a : α} {b : α}, Iff (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) f b)) (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelIso.{u2, u1} α β r s) {a : α} {b : α}, Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s f)) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s f)) b)) (Eq.{succ u2} α a b)
Case conversion may be inaccurate. Consider using '#align rel_iso.eq_iff_eq RelIso.eq_iff_eqₓ'. -/
@[simp]
theorem eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b :=
  f.Injective.eq_iff
#align rel_iso.eq_iff_eq RelIso.eq_iff_eq

#print RelIso.preimage /-
/-- Any equivalence lifts to a relation isomorphism between `s` and its preimage. -/
protected def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃r s :=
  ⟨f, fun a b => Iff.rfl⟩
#align rel_iso.preimage RelIso.preimage
-/

#print RelIso.IsWellOrder.preimage /-
instance IsWellOrder.preimage {α : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    IsWellOrder β (f ⁻¹'o r) :=
  @RelEmbedding.isWellOrder _ _ (f ⁻¹'o r) r (RelIso.preimage f r) _
#align rel_iso.is_well_order.preimage RelIso.IsWellOrder.preimage
-/

#print RelIso.IsWellOrder.ulift /-
instance IsWellOrder.ulift {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    IsWellOrder (ULift α) (ULift.down ⁻¹'o r) :=
  IsWellOrder.preimage r Equiv.ulift
#align rel_iso.is_well_order.ulift RelIso.IsWellOrder.ulift
-/

/- warning: rel_iso.of_surjective -> RelIso.ofSurjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u1, u2} α β r s), (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f)) -> (RelIso.{u1, u2} α β r s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (f : RelEmbedding.{u1, u2} α β r s), (Function.Surjective.{succ u1, succ u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s f))) -> (RelIso.{u1, u2} α β r s)
Case conversion may be inaccurate. Consider using '#align rel_iso.of_surjective RelIso.ofSurjectiveₓ'. -/
/-- A surjective relation embedding is a relation isomorphism. -/
@[simps apply]
noncomputable def ofSurjective (f : r ↪r s) (H : Surjective f) : r ≃r s :=
  ⟨Equiv.ofBijective f ⟨f.Injective, H⟩, fun a b => f.map_rel_iff⟩
#align rel_iso.of_surjective RelIso.ofSurjective

#print RelIso.sumLexCongr /-
/-- Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the sum.
-/
def sumLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Sum.Lex r₁ r₂ ≃r Sum.Lex s₁ s₂ :=
  ⟨Equiv.sumCongr e₁.toEquiv e₂.toEquiv, fun a b => by
    cases' e₁ with f hf <;> cases' e₂ with g hg <;> cases a <;> cases b <;> simp [hf, hg]⟩
#align rel_iso.sum_lex_congr RelIso.sumLexCongr
-/

#print RelIso.prodLexCongr /-
/-- Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the product.
-/
def prodLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Prod.Lex r₁ r₂ ≃r Prod.Lex s₁ s₂ :=
  ⟨Equiv.prodCongr e₁.toEquiv e₂.toEquiv, fun a b => by
    simp [Prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff]⟩
#align rel_iso.prod_lex_congr RelIso.prodLexCongr
-/

#print RelIso.relIsoOfIsEmpty /-
/-- Two relations on empty types are isomorphic. -/
def relIsoOfIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] [IsEmpty β] : r ≃r s :=
  ⟨Equiv.equivOfIsEmpty α β, isEmptyElim⟩
#align rel_iso.rel_iso_of_is_empty RelIso.relIsoOfIsEmpty
-/

#print RelIso.relIsoOfUniqueOfIrrefl /-
/-- Two irreflexive relations on a unique type are isomorphic. -/
def relIsoOfUniqueOfIrrefl (r : α → α → Prop) (s : β → β → Prop) [IsIrrefl α r] [IsIrrefl β s]
    [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.equivOfUnique α β, fun x y => by
    simp [not_rel_of_subsingleton r, not_rel_of_subsingleton s]⟩
#align rel_iso.rel_iso_of_unique_of_irrefl RelIso.relIsoOfUniqueOfIrrefl
-/

#print RelIso.relIsoOfUniqueOfRefl /-
/-- Two reflexive relations on a unique type are isomorphic. -/
def relIsoOfUniqueOfRefl (r : α → α → Prop) (s : β → β → Prop) [IsRefl α r] [IsRefl β s] [Unique α]
    [Unique β] : r ≃r s :=
  ⟨Equiv.equivOfUnique α β, fun x y => by simp [rel_of_subsingleton r, rel_of_subsingleton s]⟩
#align rel_iso.rel_iso_of_unique_of_refl RelIso.relIsoOfUniqueOfRefl
-/

end RelIso

