/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Data.FunLike.Embedding

/-!
# Typeclass for a type `F` with an injective map to `A ≃ B`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/541
> Any changes to this file require a corresponding PR to mathlib4.

This typeclass is primarily for use by isomorphisms like `monoid_equiv` and `linear_equiv`.

## Basic usage of `equiv_like`

A typical type of morphisms should be declared as:
```
structure my_iso (A B : Type*) [my_class A] [my_class B]
  extends equiv A B :=
(map_op' : ∀ {x y : A}, to_fun (my_class.op x y) = my_class.op (to_fun x) (to_fun y))

namespace my_iso

variables (A B : Type*) [my_class A] [my_class B]

-- This instance is optional if you follow the "Isomorphism class" design below:
instance : equiv_like (my_iso A B) A (λ _, B) :=
{ coe := my_iso.to_equiv.to_fun,
  inv := my_iso.to_equiv.inv_fun,
  left_inv := my_iso.to_equiv.left_inv,
  right_inv := my_iso.to_equiv.right_inv,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `equiv_like.coe` directly. -/
instance : has_coe_to_fun (my_iso A B) := to_fun.to_coe_fn

@[simp] lemma to_fun_eq_coe {f : my_iso A B} : f.to_fun = (f : A → B) := rfl

@[ext] theorem ext {f g : my_iso A B} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `my_iso` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : my_iso A B) (f' : A → B) (f_inv : B → A) (h : f' = ⇑f) : my_iso A B :=
{ to_fun := f',
  inv_fun := f_inv,
  left_inv := h.symm ▸ f.left_inv,
  right_inv := h.symm ▸ f.right_inv,
  map_op' := h.symm ▸ f.map_op' }

end my_iso
```

This file will then provide a `has_coe_to_fun` instance and various
extensionality and simp lemmas.

## Isomorphism classes extending `equiv_like`

The `equiv_like` design provides further benefits if you put in a bit more work.
The first step is to extend `equiv_like` to create a class of those types satisfying
the axioms of your new type of isomorphisms.
Continuing the example above:

```
section
set_option old_structure_cmd true

/-- `my_iso_class F A B` states that `F` is a type of `my_class.op`-preserving morphisms.
You should extend this class when you extend `my_iso`. -/
class my_iso_class (F : Type*) (A B : out_param $ Type*) [my_class A] [my_class B]
  extends equiv_like F A (λ _, B), my_hom_class F A B.

end

-- You can replace `my_iso.equiv_like` with the below instance:
instance : my_iso_class (my_iso A B) A B :=
{ coe := my_iso.to_fun,
  inv := my_iso.inv_fun,
  left_inv := my_iso.left_inv,
  right_inv := my_iso.right_inv,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := my_iso.map_op' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

The second step is to add instances of your new `my_iso_class` for all types extending `my_iso`.
Typically, you can just declare a new class analogous to `my_iso_class`:

```
structure cooler_iso (A B : Type*) [cool_class A] [cool_class B]
  extends my_iso A B :=
(map_cool' : to_fun cool_class.cool = cool_class.cool)

section
set_option old_structure_cmd true

class cooler_iso_class (F : Type*) (A B : out_param $ Type*) [cool_class A] [cool_class B]
  extends my_iso_class F A B :=
(map_cool : ∀ (f : F), f cool_class.cool = cool_class.cool)

end

@[simp] lemma map_cool {F A B : Type*} [cool_class A] [cool_class B] [cooler_iso_class F A B]
  (f : F) : f cool_class.cool = cool_class.cool :=
my_iso_class.map_op

-- You can also replace `my_iso.equiv_like` with the below instance:
instance : cool_iso_class (cool_iso A B) A B :=
{ coe := cool_iso.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := cool_iso.map_op',
  map_cool := cool_iso.map_cool' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : my_iso A B) : sorry := sorry
lemma do_something {F : Type*} [my_iso_class F A B] (f : F) : sorry := sorry
```

This means anything set up for `my_iso`s will automatically work for `cool_iso_class`es,
and defining `cool_iso_class` only takes a constant amount of effort,
instead of linearly increasing the work per `my_iso`-related declaration.

-/


/- warning: equiv_like -> EquivLike is a dubious translation:
lean 3 declaration is
  Sort.{u_1} -> (outParam.{succ u_2} Sort.{u_2}) -> (outParam.{succ u_3} Sort.{u_3}) -> Sort.{max 1 (imax u_1 u_2 u_3) (imax u_1 u_3 u_2)}
but is expected to have type
  Sort.{u_1} -> (outParam.{succ u_2} Sort.{u_2}) -> (outParam.{succ u_3} Sort.{u_3}) -> Sort.{max (max (max 1 u_1) u_2) u_3}
Case conversion may be inaccurate. Consider using '#align equiv_like EquivLikeₓ'. -/
/-- The class `equiv_like E α β` expresses that terms of type `E` have an
injective coercion to bijections between `α` and `β`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `zero_equiv_class`, `mul_equiv_class`, `monoid_equiv_class`, ....
-/
class EquivLike (E : Sort _) (α β : outParam (Sort _)) where
  coe : E → α → β
  inv : E → β → α
  left_inv : ∀ e, Function.LeftInverse (inv e) (coe e)
  right_inv : ∀ e, Function.RightInverse (inv e) (coe e)
  -- The `inv` hypothesis makes this easier to prove with `congr'`
  coe_injective' : ∀ e g, coe e = coe g → inv e = inv g → e = g
#align equiv_like EquivLike

namespace EquivLike

variable {E F α β γ : Sort _} [iE : EquivLike E α β] [iF : EquivLike F β γ]

include iE

/- warning: equiv_like.inv_injective -> EquivLike.inv_injective is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} [iE : EquivLike.{u_1 u_3 u_4} E α β], Function.Injective.{u_1 (imax u_4 u_3)} E (β -> α) (EquivLike.inv.{u_1 u_3 u_4} E α β iE)
but is expected to have type
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_2}} [iE : EquivLike.{u_1 u_3 u_2} E α β], Function.Injective.{u_1 (imax u_2 u_3)} E (β -> α) (EquivLike.inv.{u_1 u_3 u_2} E α β iE)
Case conversion may be inaccurate. Consider using '#align equiv_like.inv_injective EquivLike.inv_injectiveₓ'. -/
theorem inv_injective : Function.Injective (EquivLike.inv : E → β → α) := fun e g h =>
  coe_injective' e g ((right_inv e).eq_right_inverse (h.symm ▸ left_inv g)) h
#align equiv_like.inv_injective EquivLike.inv_injective

#print EquivLike.toEmbeddingLike /-
instance (priority := 100) toEmbeddingLike : EmbeddingLike E α β where
  coe := (coe : E → α → β)
  coe_injective' e g h := coe_injective' e g h ((left_inv e).eq_right_inverse (h.symm ▸ right_inv g))
  injective' e := (left_inv e).Injective
#align equiv_like.to_embedding_like EquivLike.toEmbeddingLike
-/

/- warning: equiv_like.injective -> EquivLike.injective is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (e : E), Function.Injective.{u_3 u_4} α β (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) e)
but is expected to have type
  forall {E : Sort.{u_3}} {α : Sort.{u_1}} {β : Sort.{u_2}} [iE : EquivLike.{u_3 u_1 u_2} E α β] (e : E), Function.Injective.{u_1 u_2} α β (FunLike.coe.{u_3 u_1 u_2} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_3 u_1 u_2} E α β (EquivLike.toEmbeddingLike.{u_3 u_1 u_2} E α β iE)) e)
Case conversion may be inaccurate. Consider using '#align equiv_like.injective EquivLike.injectiveₓ'. -/
protected theorem injective (e : E) : Function.Injective e :=
  EmbeddingLike.injective e
#align equiv_like.injective EquivLike.injective

/- warning: equiv_like.surjective -> EquivLike.surjective is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (e : E), Function.Surjective.{u_3 u_4} α β (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) e)
but is expected to have type
  forall {E : Sort.{u_3}} {α : Sort.{u_1}} {β : Sort.{u_2}} [iE : EquivLike.{u_3 u_1 u_2} E α β] (e : E), Function.Surjective.{u_1 u_2} α β (FunLike.coe.{u_3 u_1 u_2} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_3 u_1 u_2} E α β (EquivLike.toEmbeddingLike.{u_3 u_1 u_2} E α β iE)) e)
Case conversion may be inaccurate. Consider using '#align equiv_like.surjective EquivLike.surjectiveₓ'. -/
protected theorem surjective (e : E) : Function.Surjective e :=
  (right_inv e).Surjective
#align equiv_like.surjective EquivLike.surjective

/- warning: equiv_like.bijective -> EquivLike.bijective is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (e : E), Function.Bijective.{u_3 u_4} α β (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) e)
but is expected to have type
  forall {E : Sort.{u_3}} {α : Sort.{u_1}} {β : Sort.{u_2}} [iE : EquivLike.{u_3 u_1 u_2} E α β] (e : E), Function.Bijective.{u_1 u_2} α β (FunLike.coe.{u_3 u_1 u_2} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_3 u_1 u_2} E α β (EquivLike.toEmbeddingLike.{u_3 u_1 u_2} E α β iE)) e)
Case conversion may be inaccurate. Consider using '#align equiv_like.bijective EquivLike.bijectiveₓ'. -/
protected theorem bijective (e : E) : Function.Bijective (e : α → β) :=
  ⟨EquivLike.injective e, EquivLike.surjective e⟩
#align equiv_like.bijective EquivLike.bijective

/- warning: equiv_like.apply_eq_iff_eq -> EquivLike.apply_eq_iff_eq is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (f : E) {x : α} {y : α}, Iff (Eq.{u_4} β (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) f x) (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) f y)) (Eq.{u_3} α x y)
but is expected to have type
  forall {E : Sort.{u_2}} {α : Sort.{u_3}} {β : Sort.{u_1}} [iE : EquivLike.{u_2 u_3 u_1} E α β] (f : E) {x : α} {y : α}, Iff (Eq.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) x) (FunLike.coe.{u_2 u_3 u_1} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_2 u_3 u_1} E α β (EquivLike.toEmbeddingLike.{u_2 u_3 u_1} E α β iE)) f x) (FunLike.coe.{u_2 u_3 u_1} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_2 u_3 u_1} E α β (EquivLike.toEmbeddingLike.{u_2 u_3 u_1} E α β iE)) f y)) (Eq.{u_3} α x y)
Case conversion may be inaccurate. Consider using '#align equiv_like.apply_eq_iff_eq EquivLike.apply_eq_iff_eqₓ'. -/
theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f
#align equiv_like.apply_eq_iff_eq EquivLike.apply_eq_iff_eq

/- warning: equiv_like.injective_comp -> EquivLike.injective_comp is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} {γ : Sort.{u_5}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (e : E) (f : β -> γ), Iff (Function.Injective.{u_3 u_5} α γ (Function.comp.{u_3 u_4 u_5} α β γ f (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) e))) (Function.Injective.{u_4 u_5} β γ f)
but is expected to have type
  forall {E : Sort.{u_4}} {α : Sort.{u_1}} {β : Sort.{u_3}} {γ : Sort.{u_2}} [iE : EquivLike.{u_4 u_1 u_3} E α β] (e : E) (f : β -> γ), Iff (Function.Injective.{u_1 u_2} α γ (Function.comp.{u_1 u_3 u_2} α β γ f (FunLike.coe.{u_4 u_1 u_3} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_4 u_1 u_3} E α β (EquivLike.toEmbeddingLike.{u_4 u_1 u_3} E α β iE)) e))) (Function.Injective.{u_3 u_2} β γ f)
Case conversion may be inaccurate. Consider using '#align equiv_like.injective_comp EquivLike.injective_compₓ'. -/
@[simp]
theorem injective_comp (e : E) (f : β → γ) : Function.Injective (f ∘ e) ↔ Function.Injective f :=
  Function.Injective.of_comp_iff' f (EquivLike.bijective e)
#align equiv_like.injective_comp EquivLike.injective_comp

/- warning: equiv_like.surjective_comp -> EquivLike.surjective_comp is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} {γ : Sort.{u_5}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (e : E) (f : β -> γ), Iff (Function.Surjective.{u_3 u_5} α γ (Function.comp.{u_3 u_4 u_5} α β γ f (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) e))) (Function.Surjective.{u_4 u_5} β γ f)
but is expected to have type
  forall {E : Sort.{u_4}} {α : Sort.{u_1}} {β : Sort.{u_3}} {γ : Sort.{u_2}} [iE : EquivLike.{u_4 u_1 u_3} E α β] (e : E) (f : β -> γ), Iff (Function.Surjective.{u_1 u_2} α γ (Function.comp.{u_1 u_3 u_2} α β γ f (FunLike.coe.{u_4 u_1 u_3} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_4 u_1 u_3} E α β (EquivLike.toEmbeddingLike.{u_4 u_1 u_3} E α β iE)) e))) (Function.Surjective.{u_3 u_2} β γ f)
Case conversion may be inaccurate. Consider using '#align equiv_like.surjective_comp EquivLike.surjective_compₓ'. -/
@[simp]
theorem surjective_comp (e : E) (f : β → γ) : Function.Surjective (f ∘ e) ↔ Function.Surjective f :=
  (EquivLike.surjective e).of_comp_iff f
#align equiv_like.surjective_comp EquivLike.surjective_comp

/- warning: equiv_like.bijective_comp -> EquivLike.bijective_comp is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} {γ : Sort.{u_5}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (e : E) (f : β -> γ), Iff (Function.Bijective.{u_3 u_5} α γ (Function.comp.{u_3 u_4 u_5} α β γ f (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) e))) (Function.Bijective.{u_4 u_5} β γ f)
but is expected to have type
  forall {E : Sort.{u_4}} {α : Sort.{u_1}} {β : Sort.{u_3}} {γ : Sort.{u_2}} [iE : EquivLike.{u_4 u_1 u_3} E α β] (e : E) (f : β -> γ), Iff (Function.Bijective.{u_1 u_2} α γ (Function.comp.{u_1 u_3 u_2} α β γ f (FunLike.coe.{u_4 u_1 u_3} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_4 u_1 u_3} E α β (EquivLike.toEmbeddingLike.{u_4 u_1 u_3} E α β iE)) e))) (Function.Bijective.{u_3 u_2} β γ f)
Case conversion may be inaccurate. Consider using '#align equiv_like.bijective_comp EquivLike.bijective_compₓ'. -/
@[simp]
theorem bijective_comp (e : E) (f : β → γ) : Function.Bijective (f ∘ e) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff f
#align equiv_like.bijective_comp EquivLike.bijective_comp

/- warning: equiv_like.inv_apply_apply -> EquivLike.inv_apply_apply is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (e : E) (a : α), Eq.{u_3} α (EquivLike.inv.{u_1 u_3 u_4} E α β iE e (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) e a)) a
but is expected to have type
  forall {E : Sort.{u_2}} {α : Sort.{u_1}} {β : Sort.{u_3}} [iE : EquivLike.{u_2 u_1 u_3} E α β] (e : E) (a : α), Eq.{u_1} α (EquivLike.inv.{u_2 u_1 u_3} E α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) iE e (FunLike.coe.{u_2 u_1 u_3} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_2 u_1 u_3} E α β (EquivLike.toEmbeddingLike.{u_2 u_1 u_3} E α β iE)) e a)) a
Case conversion may be inaccurate. Consider using '#align equiv_like.inv_apply_apply EquivLike.inv_apply_applyₓ'. -/
/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `equiv_like`.
For concrete isomorphism types such as `equiv`, you should use `equiv.symm_apply_apply`
or its equivalent.

TODO: define a generic form of `equiv.symm`. -/
@[simp]
theorem inv_apply_apply (e : E) (a : α) : EquivLike.inv e (e a) = a :=
  left_inv _ _
#align equiv_like.inv_apply_apply EquivLike.inv_apply_apply

/- warning: equiv_like.apply_inv_apply -> EquivLike.apply_inv_apply is a dubious translation:
lean 3 declaration is
  forall {E : Sort.{u_1}} {α : Sort.{u_3}} {β : Sort.{u_4}} [iE : EquivLike.{u_1 u_3 u_4} E α β] (e : E) (b : β), Eq.{u_4} β (coeFn.{u_1 (imax u_3 u_4)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{u_1 u_3 u_4} E α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{u_1 u_3 u_4} E α β (EquivLike.toEmbeddingLike.{u_1 u_3 u_4} E α β iE))) e (EquivLike.inv.{u_1 u_3 u_4} E α β iE e b)) b
but is expected to have type
  forall {E : Sort.{u_2}} {α : Sort.{u_3}} {β : Sort.{u_1}} [iE : EquivLike.{u_2 u_3 u_1} E α β] (e : E) (b : β), Eq.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (EquivLike.inv.{u_2 u_3 u_1} E α β iE e b)) (FunLike.coe.{u_2 u_3 u_1} E α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{u_2 u_3 u_1} E α β (EquivLike.toEmbeddingLike.{u_2 u_3 u_1} E α β iE)) e (EquivLike.inv.{u_2 u_3 u_1} E α β iE e b)) b
Case conversion may be inaccurate. Consider using '#align equiv_like.apply_inv_apply EquivLike.apply_inv_applyₓ'. -/
/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `equiv_like`.
For concrete isomorphism types such as `equiv`, you should use `equiv.apply_symm_apply`
or its equivalent.

TODO: define a generic form of `equiv.symm`. -/
@[simp]
theorem apply_inv_apply (e : E) (b : β) : e (EquivLike.inv e b) = b :=
  right_inv _ _
#align equiv_like.apply_inv_apply EquivLike.apply_inv_apply

omit iE

include iF

/- warning: equiv_like.comp_injective -> EquivLike.comp_injective is a dubious translation:
lean 3 declaration is
  forall {F : Sort.{u_2}} {α : Sort.{u_3}} {β : Sort.{u_4}} {γ : Sort.{u_5}} [iF : EquivLike.{u_2 u_4 u_5} F β γ] (f : α -> β) (e : F), Iff (Function.Injective.{u_3 u_5} α γ (Function.comp.{u_3 u_4 u_5} α β γ (coeFn.{u_2 (imax u_4 u_5)} F (fun (_x : F) => β -> γ) (FunLike.hasCoeToFun.{u_2 u_4 u_5} F β (fun (_x : β) => γ) (EmbeddingLike.toFunLike.{u_2 u_4 u_5} F β γ (EquivLike.toEmbeddingLike.{u_2 u_4 u_5} F β γ iF))) e) f)) (Function.Injective.{u_3 u_4} α β f)
but is expected to have type
  forall {F : Sort.{u_4}} {α : Sort.{u_1}} {β : Sort.{u_3}} {γ : Sort.{u_2}} [iF : EquivLike.{u_4 u_3 u_2} F β γ] (f : α -> β) (e : F), Iff (Function.Injective.{u_1 u_2} α γ (Function.comp.{u_1 u_3 u_2} α β γ (FunLike.coe.{u_4 u_3 u_2} F β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{u_4 u_3 u_2} F β γ (EquivLike.toEmbeddingLike.{u_4 u_3 u_2} F β γ iF)) e) f)) (Function.Injective.{u_1 u_3} α β f)
Case conversion may be inaccurate. Consider using '#align equiv_like.comp_injective EquivLike.comp_injectiveₓ'. -/
theorem comp_injective (f : α → β) (e : F) : Function.Injective (e ∘ f) ↔ Function.Injective f :=
  EmbeddingLike.comp_injective f e
#align equiv_like.comp_injective EquivLike.comp_injective

/- warning: equiv_like.comp_surjective -> EquivLike.comp_surjective is a dubious translation:
lean 3 declaration is
  forall {F : Sort.{u_2}} {α : Sort.{u_3}} {β : Sort.{u_4}} {γ : Sort.{u_5}} [iF : EquivLike.{u_2 u_4 u_5} F β γ] (f : α -> β) (e : F), Iff (Function.Surjective.{u_3 u_5} α γ (Function.comp.{u_3 u_4 u_5} α β γ (coeFn.{u_2 (imax u_4 u_5)} F (fun (_x : F) => β -> γ) (FunLike.hasCoeToFun.{u_2 u_4 u_5} F β (fun (_x : β) => γ) (EmbeddingLike.toFunLike.{u_2 u_4 u_5} F β γ (EquivLike.toEmbeddingLike.{u_2 u_4 u_5} F β γ iF))) e) f)) (Function.Surjective.{u_3 u_4} α β f)
but is expected to have type
  forall {F : Sort.{u_4}} {α : Sort.{u_1}} {β : Sort.{u_3}} {γ : Sort.{u_2}} [iF : EquivLike.{u_4 u_3 u_2} F β γ] (f : α -> β) (e : F), Iff (Function.Surjective.{u_1 u_2} α γ (Function.comp.{u_1 u_3 u_2} α β γ (FunLike.coe.{u_4 u_3 u_2} F β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{u_4 u_3 u_2} F β γ (EquivLike.toEmbeddingLike.{u_4 u_3 u_2} F β γ iF)) e) f)) (Function.Surjective.{u_1 u_3} α β f)
Case conversion may be inaccurate. Consider using '#align equiv_like.comp_surjective EquivLike.comp_surjectiveₓ'. -/
@[simp]
theorem comp_surjective (f : α → β) (e : F) : Function.Surjective (e ∘ f) ↔ Function.Surjective f :=
  Function.Surjective.of_comp_iff' (EquivLike.bijective e) f
#align equiv_like.comp_surjective EquivLike.comp_surjective

/- warning: equiv_like.comp_bijective -> EquivLike.comp_bijective is a dubious translation:
lean 3 declaration is
  forall {F : Sort.{u_2}} {α : Sort.{u_3}} {β : Sort.{u_4}} {γ : Sort.{u_5}} [iF : EquivLike.{u_2 u_4 u_5} F β γ] (f : α -> β) (e : F), Iff (Function.Bijective.{u_3 u_5} α γ (Function.comp.{u_3 u_4 u_5} α β γ (coeFn.{u_2 (imax u_4 u_5)} F (fun (_x : F) => β -> γ) (FunLike.hasCoeToFun.{u_2 u_4 u_5} F β (fun (_x : β) => γ) (EmbeddingLike.toFunLike.{u_2 u_4 u_5} F β γ (EquivLike.toEmbeddingLike.{u_2 u_4 u_5} F β γ iF))) e) f)) (Function.Bijective.{u_3 u_4} α β f)
but is expected to have type
  forall {F : Sort.{u_4}} {α : Sort.{u_1}} {β : Sort.{u_3}} {γ : Sort.{u_2}} [iF : EquivLike.{u_4 u_3 u_2} F β γ] (f : α -> β) (e : F), Iff (Function.Bijective.{u_1 u_2} α γ (Function.comp.{u_1 u_3 u_2} α β γ (FunLike.coe.{u_4 u_3 u_2} F β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{u_4 u_3 u_2} F β γ (EquivLike.toEmbeddingLike.{u_4 u_3 u_2} F β γ iF)) e) f)) (Function.Bijective.{u_1 u_3} α β f)
Case conversion may be inaccurate. Consider using '#align equiv_like.comp_bijective EquivLike.comp_bijectiveₓ'. -/
@[simp]
theorem comp_bijective (f : α → β) (e : F) : Function.Bijective (e ∘ f) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff' f
#align equiv_like.comp_bijective EquivLike.comp_bijective

/-- This is not an instance to avoid slowing down every single `subsingleton` typeclass search.-/
theorem subsingleton_dom [Subsingleton β] : Subsingleton F :=
  ⟨fun f g => (FunLike.ext f g) fun x => (right_inv f).Injective <| Subsingleton.elim _ _⟩
#align equiv_like.subsingleton_dom EquivLike.subsingleton_dom

end EquivLike

