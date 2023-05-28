/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Sean Leather

! This file was ported from Lean 3 source module control.fold
! leanprover-community/mathlib commit 25a9423c6b2c8626e91c688bfd6c1d0a986a3e6e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Opposite
import Mathbin.Algebra.FreeMonoid.Basic
import Mathbin.Control.Traversable.Instances
import Mathbin.Control.Traversable.Lemmas
import Mathbin.CategoryTheory.Endomorphism
import Mathbin.CategoryTheory.Types
import Mathbin.CategoryTheory.Category.Kleisli

/-!

# List folds generalized to `traversable`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Informally, we can think of `foldl` as a special case of `traverse` where we do not care about the
reconstructed data structure and, in a state monad, we care about the final state.

The obvious way to define `foldl` would be to use the state monad but it
is nicer to reason about a more abstract interface with `fold_map` as a
primitive and `fold_map_hom` as a defining property.

```
def fold_map {α ω} [has_one ω] [has_mul ω] (f : α → ω) : t α → ω := ...

lemma fold_map_hom (α β)
  [monoid α] [monoid β] (f : α →* β)
  (g : γ → α) (x : t γ) :
  f (fold_map g x) = fold_map (f ∘ g) x :=
...
```

`fold_map` uses a monoid ω to accumulate a value for every element of
a data structure and `fold_map_hom` uses a monoid homomorphism to
substitute the monoid used by `fold_map`. The two are sufficient to
define `foldl`, `foldr` and `to_list`. `to_list` permits the
formulation of specifications in terms of operations on lists.

Each fold function can be defined using a specialized
monoid. `to_list` uses a free monoid represented as a list with
concatenation while `foldl` uses endofunctions together with function
composition.

The definition through monoids uses `traverse` together with the
applicative functor `const m` (where `m` is the monoid). As an
implementation, `const` guarantees that no resource is spent on
reconstructing the structure during traversal.

A special class could be defined for `foldable`, similarly to Haskell,
but the author cannot think of instances of `foldable` that are not also
`traversable`.
-/


universe u v

open ULift CategoryTheory MulOpposite

namespace Monoid

variable {m : Type u → Type u} [Monad m]

variable {α β : Type u}

#print Monoid.Foldl /-
/-- For a list, foldl f x [y₀,y₁] reduces as follows:

```
calc  foldl f x [y₀,y₁]
    = foldl f (f x y₀) [y₁]      : rfl
... = foldl f (f (f x y₀) y₁) [] : rfl
... = f (f x y₀) y₁              : rfl
```
with
```
f : α → β → α
x : α
[y₀,y₁] : list β
```

We can view the above as a composition of functions:
```
... = f (f x y₀) y₁              : rfl
... = flip f y₁ (flip f y₀ x)    : rfl
... = (flip f y₁ ∘ flip f y₀) x  : rfl
```

We can use traverse and const to construct this composition:
```
calc   const.run (traverse (λ y, const.mk' (flip f y)) [y₀,y₁]) x
     = const.run ((::) <$> const.mk' (flip f y₀) <*> traverse (λ y, const.mk' (flip f y)) [y₁]) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> traverse (λ y, const.mk' (flip f y)) [] )) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> pure [] )) x
...  = const.run ( ((::) <$> const.mk' (flip f y₁) <*> pure []) ∘
         ((::) <$> const.mk' (flip f y₀)) ) x
...  = const.run ( const.mk' (flip f y₁) ∘ const.mk' (flip f y₀) ) x
...  = const.run ( flip f y₁ ∘ flip f y₀ ) x
...  = f (f x y₀) y₁
```

And this is how `const` turns a monoid into an applicative functor and
how the monoid of endofunctions define `foldl`.
-/
@[reducible]
def Foldl (α : Type u) : Type u :=
  (End α)ᵐᵒᵖ
#align monoid.foldl Monoid.Foldl
-/

#print Monoid.Foldl.mk /-
def Foldl.mk (f : α → α) : Foldl α :=
  op f
#align monoid.foldl.mk Monoid.Foldl.mk
-/

#print Monoid.Foldl.get /-
def Foldl.get (x : Foldl α) : α → α :=
  unop x
#align monoid.foldl.get Monoid.Foldl.get
-/

/- warning: monoid.foldl.of_free_monoid -> Monoid.Foldl.ofFreeMonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}}, (β -> α -> β) -> (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}}, (β -> α -> β) -> (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β))))
Case conversion may be inaccurate. Consider using '#align monoid.foldl.of_free_monoid Monoid.Foldl.ofFreeMonoidₓ'. -/
@[simps]
def Foldl.ofFreeMonoid (f : β → α → β) : FreeMonoid α →* Monoid.Foldl β
    where
  toFun xs := op <| flip (List.foldl f) xs.toList
  map_one' := rfl
  map_mul' := by
    intros <;> simp only [FreeMonoid.toList_mul, flip, unop_op, List.foldl_append, op_inj] <;> rfl
#align monoid.foldl.of_free_monoid Monoid.Foldl.ofFreeMonoid

#print Monoid.Foldr /-
@[reducible]
def Foldr (α : Type u) : Type u :=
  End α
#align monoid.foldr Monoid.Foldr
-/

#print Monoid.Foldr.mk /-
def Foldr.mk (f : α → α) : Foldr α :=
  f
#align monoid.foldr.mk Monoid.Foldr.mk
-/

#print Monoid.Foldr.get /-
def Foldr.get (x : Foldr α) : α → α :=
  x
#align monoid.foldr.get Monoid.Foldr.get
-/

/- warning: monoid.foldr.of_free_monoid -> Monoid.Foldr.ofFreeMonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}}, (α -> β -> β) -> (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldr.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}}, (α -> β -> β) -> (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldr.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))
Case conversion may be inaccurate. Consider using '#align monoid.foldr.of_free_monoid Monoid.Foldr.ofFreeMonoidₓ'. -/
@[simps]
def Foldr.ofFreeMonoid (f : α → β → β) : FreeMonoid α →* Monoid.Foldr β
    where
  toFun xs := flip (List.foldr f) xs.toList
  map_one' := rfl
  map_mul' xs ys := funext fun z => List.foldr_append _ _ _ _
#align monoid.foldr.of_free_monoid Monoid.Foldr.ofFreeMonoid

#print Monoid.foldlM /-
@[reducible]
def foldlM (m : Type u → Type u) [Monad m] (α : Type u) : Type u :=
  MulOpposite <| End <| KleisliCat.mk m α
#align monoid.mfoldl Monoid.foldlM
-/

#print Monoid.foldlM.mk /-
def foldlM.mk (f : α → m α) : foldlM m α :=
  op f
#align monoid.mfoldl.mk Monoid.foldlM.mk
-/

#print Monoid.foldlM.get /-
def foldlM.get (x : foldlM m α) : α → m α :=
  unop x
#align monoid.mfoldl.get Monoid.foldlM.get
-/

/- warning: monoid.mfoldl.of_free_monoid -> Monoid.foldlM.ofFreeMonoid is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u1}} [_inst_1 : Monad.{u1, u1} m] {α : Type.{u1}} {β : Type.{u1}} [_inst_2 : LawfulMonad.{u1, u1} m _inst_1], (β -> α -> (m β)) -> (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.foldlM.{u1} m _inst_1 β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u1} m _inst_1) (CategoryTheory.KleisliCat.mk.{u1, u1} m β)) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u1} m _inst_1) (CategoryTheory.KleisliCat.mk.{u1, u1} m β)) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_1 _inst_2) (CategoryTheory.KleisliCat.mk.{u1, u1} m β)))))
but is expected to have type
  forall {m : Type.{u1} -> Type.{u1}} [_inst_1 : Monad.{u1, u1} m] {α : Type.{u1}} {β : Type.{u1}} [_inst_2 : LawfulMonad.{u1, u1} m _inst_1], (β -> α -> (m β)) -> (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.foldlM.{u1} m _inst_1 β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u1} m _inst_1) (CategoryTheory.KleisliCat.mk.{u1, u1} m β)) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u1} m _inst_1) (CategoryTheory.KleisliCat.mk.{u1, u1} m β)) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_1 _inst_2) (CategoryTheory.KleisliCat.mk.{u1, u1} m β)))))
Case conversion may be inaccurate. Consider using '#align monoid.mfoldl.of_free_monoid Monoid.foldlM.ofFreeMonoidₓ'. -/
@[simps]
def foldlM.ofFreeMonoid [LawfulMonad m] (f : β → α → m β) : FreeMonoid α →* Monoid.foldlM m β
    where
  toFun xs := op <| flip (List.foldlM f) xs.toList
  map_one' := rfl
  map_mul' := by intros <;> apply unop_injective <;> ext <;> apply List.foldlM_append
#align monoid.mfoldl.of_free_monoid Monoid.foldlM.ofFreeMonoid

#print Monoid.foldrM /-
@[reducible]
def foldrM (m : Type u → Type u) [Monad m] (α : Type u) : Type u :=
  End <| KleisliCat.mk m α
#align monoid.mfoldr Monoid.foldrM
-/

#print Monoid.foldrM.mk /-
def foldrM.mk (f : α → m α) : foldrM m α :=
  f
#align monoid.mfoldr.mk Monoid.foldrM.mk
-/

#print Monoid.foldrM.get /-
def foldrM.get (x : foldrM m α) : α → m α :=
  x
#align monoid.mfoldr.get Monoid.foldrM.get
-/

/- warning: monoid.mfoldr.of_free_monoid -> Monoid.foldrM.ofFreeMonoid is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u1}} [_inst_1 : Monad.{u1, u1} m] {α : Type.{u1}} {β : Type.{u1}} [_inst_2 : LawfulMonad.{u1, u1} m _inst_1], (α -> β -> (m β)) -> (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.foldrM.{u1} m _inst_1 β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} m _inst_1 β) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_1 _inst_2) (CategoryTheory.KleisliCat.mk.{u1, u1} m β))))
but is expected to have type
  forall {m : Type.{u1} -> Type.{u1}} [_inst_1 : Monad.{u1, u1} m] {α : Type.{u1}} {β : Type.{u1}} [_inst_2 : LawfulMonad.{u1, u1} m _inst_1], (α -> β -> (m β)) -> (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.foldrM.{u1} m _inst_1 β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} m _inst_1 β) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_1 _inst_2) (CategoryTheory.KleisliCat.mk.{u1, u1} m β))))
Case conversion may be inaccurate. Consider using '#align monoid.mfoldr.of_free_monoid Monoid.foldrM.ofFreeMonoidₓ'. -/
@[simps]
def foldrM.ofFreeMonoid [LawfulMonad m] (f : α → β → m β) : FreeMonoid α →* Monoid.foldrM m β
    where
  toFun xs := flip (List.foldrM f) xs.toList
  map_one' := rfl
  map_mul' := by intros <;> ext <;> apply List.foldrM_append
#align monoid.mfoldr.of_free_monoid Monoid.foldrM.ofFreeMonoid

end Monoid

namespace Traversable

open Monoid Functor

section Defs

variable {α β : Type u} {t : Type u → Type u} [Traversable t]

#print Traversable.foldMap /-
def foldMap {α ω} [One ω] [Mul ω] (f : α → ω) : t α → ω :=
  traverse (Const.mk' ∘ f)
#align traversable.fold_map Traversable.foldMap
-/

#print Traversable.foldl /-
def foldl (f : α → β → α) (x : α) (xs : t β) : α :=
  (foldMap (Foldl.mk ∘ flip f) xs).get x
#align traversable.foldl Traversable.foldl
-/

#print Traversable.foldr /-
def foldr (f : α → β → β) (x : β) (xs : t α) : β :=
  (foldMap (Foldr.mk ∘ f) xs).get x
#align traversable.foldr Traversable.foldr
-/

#print Traversable.toList /-
/-- Conceptually, `to_list` collects all the elements of a collection
in a list. This idea is formalized by

  `lemma to_list_spec (x : t α) : to_list x = fold_map free_monoid.mk x`.

The definition of `to_list` is based on `foldl` and `list.cons` for
speed. It is faster than using `fold_map free_monoid.mk` because, by
using `foldl` and `list.cons`, each insertion is done in constant
time. As a consequence, `to_list` performs in linear.

On the other hand, `fold_map free_monoid.mk` creates a singleton list
around each element and concatenates all the resulting lists. In
`xs ++ ys`, concatenation takes a time proportional to `length xs`. Since
the order in which concatenation is evaluated is unspecified, nothing
prevents each element of the traversable to be appended at the end
`xs ++ [x]` which would yield a `O(n²)` run time. -/
def toList : t α → List α :=
  List.reverse ∘ foldl (flip List.cons) []
#align traversable.to_list Traversable.toList
-/

#print Traversable.length /-
def length (xs : t α) : ℕ :=
  down <| foldl (fun l _ => up <| l.down + 1) (up 0) xs
#align traversable.length Traversable.length
-/

variable {m : Type u → Type u} [Monad m]

#print Traversable.foldlm /-
def foldlm (f : α → β → m α) (x : α) (xs : t β) : m α :=
  (foldMap (foldlM.mk ∘ flip f) xs).get x
#align traversable.mfoldl Traversable.foldlm
-/

#print Traversable.foldrm /-
def foldrm (f : α → β → m β) (x : β) (xs : t α) : m β :=
  (foldMap (foldrM.mk ∘ f) xs).get x
#align traversable.mfoldr Traversable.foldrm
-/

end Defs

section ApplicativeTransformation

variable {α β γ : Type u}

open Function hiding const

#print Traversable.mapFold /-
def mapFold [Monoid α] [Monoid β] (f : α →* β) : ApplicativeTransformation (Const α) (Const β)
    where
  app x := f
  preserves_seq' := by intros ; simp only [f.map_mul, (· <*> ·)]
  preserves_pure' := by intros ; simp only [f.map_one, pure]
#align traversable.map_fold Traversable.mapFold
-/

/- warning: traversable.free.map_eq_map -> Traversable.Free.map_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (xs : List.{u1} α), Eq.{succ u1} (List.{u1} β) (Functor.map.{u1, u1} (fun {α : Type.{u1}} => List.{u1} α) (Traversable.toFunctor.{u1} (fun {α : Type.{u1}} => List.{u1} α) List.traversable.{u1}) α β f xs) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (FreeMonoid.{u1} β) (List.{u1} β)) (fun (_x : Equiv.{succ u1, succ u1} (FreeMonoid.{u1} β) (List.{u1} β)) => (FreeMonoid.{u1} β) -> (List.{u1} β)) (Equiv.hasCoeToFun.{succ u1, succ u1} (FreeMonoid.{u1} β) (List.{u1} β)) (FreeMonoid.toList.{u1} β) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β))))) (fun (_x : MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β))))) => (FreeMonoid.{u1} α) -> (FreeMonoid.{u1} β)) (MonoidHom.hasCoeToFun.{u1, u1} (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β))))) (FreeMonoid.map.{u1, u1} α β f) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (List.{u1} α) (FreeMonoid.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (List.{u1} α) (FreeMonoid.{u1} α)) => (List.{u1} α) -> (FreeMonoid.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (List.{u1} α) (FreeMonoid.{u1} α)) (FreeMonoid.ofList.{u1} α) xs)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (xs : List.{u1} α), Eq.{succ u1} (List.{u1} β) (Functor.map.{u1, u1} List.{u1} List.instFunctorList.{u1} α β f xs) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (FreeMonoid.{u1} β) (List.{u1} β)) (FreeMonoid.{u1} β) (fun (_x : FreeMonoid.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : FreeMonoid.{u1} β) => List.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (FreeMonoid.{u1} β) (List.{u1} β)) (FreeMonoid.toList.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β))))) (FreeMonoid.{u1} α) (fun (_x : FreeMonoid.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : FreeMonoid.{u1} α) => FreeMonoid.{u1} β) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β))))) (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (MulOneClass.toMul.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))) (MulOneClass.toMul.{u1} (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β))))) (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (MonoidHom.monoidHomClass.{u1, u1} (FreeMonoid.{u1} α) (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β))))))) (FreeMonoid.map.{u1, u1} α β f) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (List.{u1} α) (FreeMonoid.{u1} α)) (List.{u1} α) (fun (_x : List.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : List.{u1} α) => FreeMonoid.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (List.{u1} α) (FreeMonoid.{u1} α)) (FreeMonoid.ofList.{u1} α) xs)))
Case conversion may be inaccurate. Consider using '#align traversable.free.map_eq_map Traversable.Free.map_eq_mapₓ'. -/
theorem Free.map_eq_map (f : α → β) (xs : List α) :
    f <$> xs = (FreeMonoid.map f (FreeMonoid.ofList xs)).toList :=
  rfl
#align traversable.free.map_eq_map Traversable.Free.map_eq_map

/- warning: traversable.foldl.unop_of_free_monoid -> Traversable.foldl.unop_ofFreeMonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : β -> α -> β) (xs : FreeMonoid.{u1} α) (a : β), Eq.{succ u1} β (MulOpposite.unop.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))) (fun (_x : MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))) => (FreeMonoid.{u1} α) -> (Monoid.Foldl.{u1} β)) (MonoidHom.hasCoeToFun.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))) (Monoid.Foldl.ofFreeMonoid.{u1} α β f) xs) a) (List.foldl.{u1, u1} β α f a (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (FreeMonoid.{u1} α) (List.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (FreeMonoid.{u1} α) (List.{u1} α)) => (FreeMonoid.{u1} α) -> (List.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (FreeMonoid.{u1} α) (List.{u1} α)) (FreeMonoid.toList.{u1} α) xs))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : β -> α -> β) (xs : FreeMonoid.{u1} α) (a : β), Eq.{succ u1} β (MulOpposite.unop.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))) (FreeMonoid.{u1} α) (fun (_x : FreeMonoid.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : FreeMonoid.{u1} α) => Monoid.Foldl.{u1} β) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))) (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (MulOneClass.toMul.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))) (MulOneClass.toMul.{u1} (Monoid.Foldl.{u1} β) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))) (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β))) (MonoidHom.monoidHomClass.{u1, u1} (FreeMonoid.{u1} α) (Monoid.Foldl.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) β) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} β)))))) (Monoid.Foldl.ofFreeMonoid.{u1} α β f) xs) a) (List.foldl.{u1, u1} β α f a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (FreeMonoid.{u1} α) (List.{u1} α)) (FreeMonoid.{u1} α) (fun (_x : FreeMonoid.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : FreeMonoid.{u1} α) => List.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (FreeMonoid.{u1} α) (List.{u1} α)) (FreeMonoid.toList.{u1} α) xs))
Case conversion may be inaccurate. Consider using '#align traversable.foldl.unop_of_free_monoid Traversable.foldl.unop_ofFreeMonoidₓ'. -/
theorem foldl.unop_ofFreeMonoid (f : β → α → β) (xs : FreeMonoid α) (a : β) :
    unop (Foldl.ofFreeMonoid f xs) a = List.foldl f a xs.toList :=
  rfl
#align traversable.foldl.unop_of_free_monoid Traversable.foldl.unop_ofFreeMonoid

variable (m : Type u → Type u) [Monad m] [LawfulMonad m]

variable {t : Type u → Type u} [Traversable t] [IsLawfulTraversable t]

open IsLawfulTraversable

/- warning: traversable.fold_map_hom -> Traversable.foldMap_hom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} {t : Type.{u1} -> Type.{u1}} [_inst_3 : Traversable.{u1} t] [_inst_4 : IsLawfulTraversable.{u1} t _inst_3] [_inst_5 : Monoid.{u1} α] [_inst_6 : Monoid.{u1} β] (f : MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) (g : γ -> α) (x : t γ), Eq.{succ u1} β (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) (fun (_x : MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) => α -> β) (MonoidHom.hasCoeToFun.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) f (Traversable.foldMap.{u1} (fun {γ : Type.{u1}} => t γ) _inst_3 γ α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_5)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_5)) g x)) (Traversable.foldMap.{u1} (fun {γ : Type.{u1}} => t γ) _inst_3 γ β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β _inst_6)) (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_6)) (Function.comp.{succ u1, succ u1, succ u1} γ α β (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) (fun (_x : MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) => α -> β) (MonoidHom.hasCoeToFun.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) f) g) x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} {t : Type.{u1} -> Type.{u1}} [_inst_3 : Traversable.{u1} t] [_inst_4 : IsLawfulTraversable.{u1} t _inst_3] [_inst_5 : Monoid.{u1} α] [_inst_6 : Monoid.{u1} β] (f : MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) (g : γ -> α) (x : t γ), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) (Traversable.foldMap.{u1} t _inst_3 γ α (Monoid.toOne.{u1} α _inst_5) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_5)) g x)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_5)) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_6)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6) (MonoidHom.monoidHomClass.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)))) f (Traversable.foldMap.{u1} t _inst_3 γ α (Monoid.toOne.{u1} α _inst_5) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_5)) g x)) (Traversable.foldMap.{u1} t _inst_3 γ β (Monoid.toOne.{u1} β _inst_6) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_6)) (Function.comp.{succ u1, succ u1, succ u1} γ α β (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_5)) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_6)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)) α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6) (MonoidHom.monoidHomClass.{u1, u1} α β (Monoid.toMulOneClass.{u1} α _inst_5) (Monoid.toMulOneClass.{u1} β _inst_6)))) f) g) x)
Case conversion may be inaccurate. Consider using '#align traversable.fold_map_hom Traversable.foldMap_homₓ'. -/
theorem foldMap_hom [Monoid α] [Monoid β] (f : α →* β) (g : γ → α) (x : t γ) :
    f (foldMap g x) = foldMap (f ∘ g) x :=
  calc
    f (foldMap g x) = f (traverse (Const.mk' ∘ g) x) := rfl
    _ = (mapFold f).app _ (traverse (Const.mk' ∘ g) x) := rfl
    _ = traverse ((mapFold f).app _ ∘ Const.mk' ∘ g) x := (naturality (mapFold f) _ _)
    _ = foldMap (f ∘ g) x := rfl
    
#align traversable.fold_map_hom Traversable.foldMap_hom

/- warning: traversable.fold_map_hom_free -> Traversable.foldMap_hom_free is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {t : Type.{u1} -> Type.{u1}} [_inst_3 : Traversable.{u1} t] [_inst_4 : IsLawfulTraversable.{u1} t _inst_3] [_inst_5 : Monoid.{u1} β] (f : MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (x : t α), Eq.{succ u1} β (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (fun (_x : MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) => (FreeMonoid.{u1} α) -> β) (MonoidHom.hasCoeToFun.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) f (Traversable.foldMap.{u1} (fun {α : Type.{u1}} => t α) _inst_3 α (FreeMonoid.{u1} α) (MulOneClass.toHasOne.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α))))) (MulOneClass.toHasMul.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α))))) (FreeMonoid.of.{u1} α) x)) (Traversable.foldMap.{u1} (fun {α : Type.{u1}} => t α) _inst_3 α β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β _inst_5)) (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_5)) (Function.comp.{succ u1, succ u1, succ u1} α (FreeMonoid.{u1} α) β (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (fun (_x : MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) => (FreeMonoid.{u1} α) -> β) (MonoidHom.hasCoeToFun.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) f) (FreeMonoid.of.{u1} α)) x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {t : Type.{u1} -> Type.{u1}} [_inst_3 : Traversable.{u1} t] [_inst_4 : IsLawfulTraversable.{u1} t _inst_3] [_inst_5 : Monoid.{u1} β] (f : MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (x : t α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : FreeMonoid.{u1} α) => β) (Traversable.foldMap.{u1} t _inst_3 α (FreeMonoid.{u1} α) (RightCancelMonoid.toOne.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))) (MulOneClass.toMul.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))) (FreeMonoid.of.{u1} α) x)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (FreeMonoid.{u1} α) (fun (_x : FreeMonoid.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : FreeMonoid.{u1} α) => β) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (FreeMonoid.{u1} α) β (MulOneClass.toMul.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_5)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5) (MonoidHom.monoidHomClass.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)))) f (Traversable.foldMap.{u1} t _inst_3 α (FreeMonoid.{u1} α) (RightCancelMonoid.toOne.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))) (MulOneClass.toMul.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))) (FreeMonoid.of.{u1} α) x)) (Traversable.foldMap.{u1} t _inst_3 α β (Monoid.toOne.{u1} β _inst_5) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_5)) (Function.comp.{succ u1, succ u1, succ u1} α (FreeMonoid.{u1} α) β (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (FreeMonoid.{u1} α) (fun (_x : FreeMonoid.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : FreeMonoid.{u1} α) => β) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (FreeMonoid.{u1} α) β (MulOneClass.toMul.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_5)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)) (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5) (MonoidHom.monoidHomClass.{u1, u1} (FreeMonoid.{u1} α) β (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Monoid.toMulOneClass.{u1} β _inst_5)))) f) (FreeMonoid.of.{u1} α)) x)
Case conversion may be inaccurate. Consider using '#align traversable.fold_map_hom_free Traversable.foldMap_hom_freeₓ'. -/
theorem foldMap_hom_free [Monoid β] (f : FreeMonoid α →* β) (x : t α) :
    f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of) x :=
  foldMap_hom f _ x
#align traversable.fold_map_hom_free Traversable.foldMap_hom_free

end ApplicativeTransformation

section Equalities

open IsLawfulTraversable

open List (cons)

variable {α β γ : Type u}

variable {t : Type u → Type u} [Traversable t] [IsLawfulTraversable t]

/- warning: traversable.foldl.of_free_monoid_comp_of -> Traversable.foldl.ofFreeMonoid_comp_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β -> α), Eq.{succ u1} (β -> (Monoid.Foldl.{u1} α)) (Function.comp.{succ u1, succ u1, succ u1} β (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)))) (fun (_x : MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)))) => (FreeMonoid.{u1} β) -> (Monoid.Foldl.{u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)))) (Monoid.Foldl.ofFreeMonoid.{u1} β α f)) (FreeMonoid.of.{u1} β)) (Function.comp.{succ u1, succ u1, succ u1} β (α -> α) (Monoid.Foldl.{u1} α) (Monoid.Foldl.mk.{u1} α) (flip.{succ u1, succ u1, succ u1} α β α f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β -> α), Eq.{succ u1} (β -> (Monoid.Foldl.{u1} α)) (Function.comp.{succ u1, succ u1, succ u1} β (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)))) (FreeMonoid.{u1} β) (fun (_x : FreeMonoid.{u1} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : FreeMonoid.{u1} β) => Monoid.Foldl.{u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)))) (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (MulOneClass.toMul.{u1} (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β))))) (MulOneClass.toMul.{u1} (Monoid.Foldl.{u1} α) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)))) (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))) (MonoidHom.monoidHomClass.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldl.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (MulOpposite.mulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (Monoid.toMulOneClass.{u1} (CategoryTheory.End.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)))))) (Monoid.Foldl.ofFreeMonoid.{u1} β α f)) (FreeMonoid.of.{u1} β)) (Function.comp.{succ u1, succ u1, succ u1} β (α -> α) (Monoid.Foldl.{u1} α) (Monoid.Foldl.mk.{u1} α) (flip.{succ u1, succ u1, succ u1} α β α f))
Case conversion may be inaccurate. Consider using '#align traversable.foldl.of_free_monoid_comp_of Traversable.foldl.ofFreeMonoid_comp_ofₓ'. -/
@[simp]
theorem foldl.ofFreeMonoid_comp_of (f : α → β → α) :
    Foldl.ofFreeMonoid f ∘ FreeMonoid.of = Foldl.mk ∘ flip f :=
  rfl
#align traversable.foldl.of_free_monoid_comp_of Traversable.foldl.ofFreeMonoid_comp_of

/- warning: traversable.foldr.of_free_monoid_comp_of -> Traversable.foldr.ofFreeMonoid_comp_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : β -> α -> α), Eq.{succ u1} (β -> (Monoid.Foldr.{u1} α)) (Function.comp.{succ u1, succ u1, succ u1} β (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))) (fun (_x : MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))) => (FreeMonoid.{u1} β) -> (Monoid.Foldr.{u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))) (Monoid.Foldr.ofFreeMonoid.{u1} β α f)) (FreeMonoid.of.{u1} β)) (Function.comp.{succ u1, succ u1, succ u1} β (α -> α) (Monoid.Foldr.{u1} α) (Monoid.Foldr.mk.{u1} α) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : β -> α -> α), Eq.{succ u1} (β -> (Monoid.Foldr.{u1} α)) (Function.comp.{succ u1, succ u1, succ u1} β (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))) (FreeMonoid.{u1} β) (fun (_x : FreeMonoid.{u1} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : FreeMonoid.{u1} β) => Monoid.Foldr.{u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))) (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (MulOneClass.toMul.{u1} (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β))))) (MulOneClass.toMul.{u1} (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))) (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α)) (MonoidHom.monoidHomClass.{u1, u1} (FreeMonoid.{u1} β) (Monoid.Foldr.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.Foldr.{u1} α) (CategoryTheory.End.monoid.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} α))))) (Monoid.Foldr.ofFreeMonoid.{u1} β α f)) (FreeMonoid.of.{u1} β)) (Function.comp.{succ u1, succ u1, succ u1} β (α -> α) (Monoid.Foldr.{u1} α) (Monoid.Foldr.mk.{u1} α) f)
Case conversion may be inaccurate. Consider using '#align traversable.foldr.of_free_monoid_comp_of Traversable.foldr.ofFreeMonoid_comp_ofₓ'. -/
@[simp]
theorem foldr.ofFreeMonoid_comp_of (f : β → α → α) :
    Foldr.ofFreeMonoid f ∘ FreeMonoid.of = Foldr.mk ∘ f :=
  rfl
#align traversable.foldr.of_free_monoid_comp_of Traversable.foldr.ofFreeMonoid_comp_of

/- warning: traversable.mfoldl.of_free_monoid_comp_of -> Traversable.foldlm.ofFreeMonoid_comp_of is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align traversable.mfoldl.of_free_monoid_comp_of Traversable.foldlm.ofFreeMonoid_comp_ofₓ'. -/
@[simp]
theorem foldlm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : α → β → m α) :
    foldlM.ofFreeMonoid f ∘ FreeMonoid.of = foldlM.mk ∘ flip f := by ext1 x;
  simp [(· ∘ ·), mfoldl.of_free_monoid, mfoldl.mk, flip]; rfl
#align traversable.mfoldl.of_free_monoid_comp_of Traversable.foldlm.ofFreeMonoid_comp_of

/- warning: traversable.mfoldr.of_free_monoid_comp_of -> Traversable.foldrm.ofFreeMonoid_comp_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_3 : Monad.{u1, u1} m] [_inst_4 : LawfulMonad.{u1, u1} m _inst_3] (f : β -> α -> (m α)), Eq.{succ u1} (β -> (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α)) (Function.comp.{succ u1, succ u1, succ u1} β (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} (fun {α : Type.{u1}} => m α)) (CategoryTheory.KleisliCat.category.{u1, u1} (fun {α : Type.{u1}} => m α) _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} (fun {α : Type.{u1}} => m α) α)))) (fun (_x : MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} (fun {α : Type.{u1}} => m α)) (CategoryTheory.KleisliCat.category.{u1, u1} (fun {α : Type.{u1}} => m α) _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} (fun {α : Type.{u1}} => m α) α)))) => (FreeMonoid.{u1} β) -> (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α)) (MonoidHom.hasCoeToFun.{u1, u1} (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.cancelMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} (fun {α : Type.{u1}} => m α)) (CategoryTheory.KleisliCat.category.{u1, u1} (fun {α : Type.{u1}} => m α) _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} (fun {α : Type.{u1}} => m α) α)))) (Monoid.foldrM.ofFreeMonoid.{u1} (fun {α : Type.{u1}} => m α) _inst_3 β α _inst_4 f)) (FreeMonoid.of.{u1} β)) (Function.comp.{succ u1, succ u1, succ u1} β (α -> (m α)) (Monoid.foldrM.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) (Monoid.foldrM.mk.{u1} (fun {α : Type.{u1}} => m α) _inst_3 α) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_3 : Monad.{u1, u1} m] [_inst_4 : LawfulMonad.{u1, u1} m _inst_3] (f : β -> α -> (m α)), Eq.{succ u1} (β -> (Monoid.foldrM.{u1} m _inst_3 α)) (Function.comp.{succ u1, succ u1, succ u1} β (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} m _inst_3 α) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} m _inst_3 α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} m _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} m α)))) (FreeMonoid.{u1} β) (fun (_x : FreeMonoid.{u1} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : FreeMonoid.{u1} β) => Monoid.foldrM.{u1} m _inst_3 α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} m _inst_3 α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} m _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} m α)))) (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} m _inst_3 α) (MulOneClass.toMul.{u1} (FreeMonoid.{u1} β) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β))))) (MulOneClass.toMul.{u1} (Monoid.foldrM.{u1} m _inst_3 α) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} m _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} m α)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} m _inst_3 α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} m _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} m α)))) (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} m _inst_3 α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} m _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} m α))) (MonoidHom.monoidHomClass.{u1, u1} (FreeMonoid.{u1} β) (Monoid.foldrM.{u1} m _inst_3 α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} β) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} β) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} β) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} β)))) (Monoid.toMulOneClass.{u1} (Monoid.foldrM.{u1} m _inst_3 α) (CategoryTheory.End.monoid.{u1, succ u1} (CategoryTheory.KleisliCat.{u1, u1} m) (CategoryTheory.KleisliCat.category.{u1, u1} m _inst_3 _inst_4) (CategoryTheory.KleisliCat.mk.{u1, u1} m α)))))) (Monoid.foldrM.ofFreeMonoid.{u1} m _inst_3 β α _inst_4 f)) (FreeMonoid.of.{u1} β)) (Function.comp.{succ u1, succ u1, succ u1} β (α -> (m α)) (Monoid.foldrM.{u1} m _inst_3 α) (Monoid.foldrM.mk.{u1} m _inst_3 α) f)
Case conversion may be inaccurate. Consider using '#align traversable.mfoldr.of_free_monoid_comp_of Traversable.foldrm.ofFreeMonoid_comp_ofₓ'. -/
@[simp]
theorem foldrm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : β → α → m α) :
    foldrM.ofFreeMonoid f ∘ FreeMonoid.of = foldrM.mk ∘ f := by ext;
  simp [(· ∘ ·), mfoldr.of_free_monoid, mfoldr.mk, flip]
#align traversable.mfoldr.of_free_monoid_comp_of Traversable.foldrm.ofFreeMonoid_comp_of

#print Traversable.toList_spec /-
theorem toList_spec (xs : t α) : toList xs = FreeMonoid.toList (foldMap FreeMonoid.of xs) :=
  Eq.symm <|
    calc
      FreeMonoid.toList (foldMap FreeMonoid.of xs) =
          FreeMonoid.toList (foldMap FreeMonoid.of xs).reverse.reverse :=
        by simp only [List.reverse_reverse]
      _ = FreeMonoid.toList (List.foldr cons [] (foldMap FreeMonoid.of xs).reverse).reverse := by
        simp only [List.foldr_eta]
      _ = (unop (Foldl.ofFreeMonoid (flip cons) (foldMap FreeMonoid.of xs)) []).reverse := by
        simp [flip, List.foldr_reverse, foldl.of_free_monoid, unop_op]
      _ = toList xs :=
        by
        rw [fold_map_hom_free (foldl.of_free_monoid (flip <| @cons α))]
        · simp only [to_list, foldl, List.reverse_inj, foldl.get, foldl.of_free_monoid_comp_of]
        · infer_instance
      
#align traversable.to_list_spec Traversable.toList_spec
-/

/- warning: traversable.fold_map_map -> Traversable.foldMap_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] [_inst_3 : Monoid.{u1} γ] (f : α -> β) (g : β -> γ) (xs : t α), Eq.{succ u1} γ (Traversable.foldMap.{u1} (fun {α : Type.{u1}} => t α) _inst_1 β γ (MulOneClass.toHasOne.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_3)) (MulOneClass.toHasMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_3)) g (Functor.map.{u1, u1} (fun {α : Type.{u1}} => t α) (Traversable.toFunctor.{u1} (fun {α : Type.{u1}} => t α) _inst_1) α β f xs)) (Traversable.foldMap.{u1} (fun {α : Type.{u1}} => t α) _inst_1 α γ (MulOneClass.toHasOne.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_3)) (MulOneClass.toHasMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_3)) (Function.comp.{succ u1, succ u1, succ u1} α β γ g f) xs)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] [_inst_3 : Monoid.{u1} γ] (f : α -> β) (g : β -> γ) (xs : t α), Eq.{succ u1} γ (Traversable.foldMap.{u1} t _inst_1 β γ (Monoid.toOne.{u1} γ _inst_3) (MulOneClass.toMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_3)) g (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) α β f xs)) (Traversable.foldMap.{u1} t _inst_1 α γ (Monoid.toOne.{u1} γ _inst_3) (MulOneClass.toMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_3)) (Function.comp.{succ u1, succ u1, succ u1} α β γ g f) xs)
Case conversion may be inaccurate. Consider using '#align traversable.fold_map_map Traversable.foldMap_mapₓ'. -/
theorem foldMap_map [Monoid γ] (f : α → β) (g : β → γ) (xs : t α) :
    foldMap g (f <$> xs) = foldMap (g ∘ f) xs := by simp only [fold_map, traverse_map]
#align traversable.fold_map_map Traversable.foldMap_map

#print Traversable.foldl_toList /-
theorem foldl_toList (f : α → β → α) (xs : t β) (x : α) :
    foldl f x xs = List.foldl f x (toList xs) :=
  by
  rw [← FreeMonoid.toList_ofList (to_list xs), ← foldl.unop_of_free_monoid]
  simp only [foldl, to_list_spec, fold_map_hom_free, foldl.of_free_monoid_comp_of, foldl.get,
    FreeMonoid.ofList_toList]
#align traversable.foldl_to_list Traversable.foldl_toList
-/

#print Traversable.foldr_toList /-
theorem foldr_toList (f : α → β → β) (xs : t α) (x : β) :
    foldr f x xs = List.foldr f x (toList xs) :=
  by
  change _ = foldr.of_free_monoid _ (FreeMonoid.ofList <| to_list xs) _
  rw [to_list_spec, foldr, foldr.get, FreeMonoid.ofList_toList, fold_map_hom_free,
    foldr.of_free_monoid_comp_of]
#align traversable.foldr_to_list Traversable.foldr_toList
-/

/- warning: traversable.to_list_map -> Traversable.toList_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] (f : α -> β) (xs : t α), Eq.{succ u1} (List.{u1} β) (Traversable.toList.{u1} β (fun {α : Type.{u1}} => t α) _inst_1 (Functor.map.{u1, u1} (fun {α : Type.{u1}} => t α) (Traversable.toFunctor.{u1} (fun {α : Type.{u1}} => t α) _inst_1) α β f xs)) (Functor.map.{u1, u1} List.{u1} (Traversable.toFunctor.{u1} List.{u1} List.traversable.{u1}) α β f (Traversable.toList.{u1} α (fun {α : Type.{u1}} => t α) _inst_1 xs))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] (f : α -> β) (xs : t α), Eq.{succ u1} (List.{u1} β) (Traversable.toList.{u1} β t _inst_1 (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) α β f xs)) (Functor.map.{u1, u1} List.{u1} List.instFunctorList.{u1} α β f (Traversable.toList.{u1} α t _inst_1 xs))
Case conversion may be inaccurate. Consider using '#align traversable.to_list_map Traversable.toList_mapₓ'. -/
/-

-/
theorem toList_map (f : α → β) (xs : t α) : toList (f <$> xs) = f <$> toList xs := by
  simp only [to_list_spec, free.map_eq_map, fold_map_hom, fold_map_map, FreeMonoid.ofList_toList,
    FreeMonoid.map_of, (· ∘ ·)]
#align traversable.to_list_map Traversable.toList_map

#print Traversable.foldl_map /-
@[simp]
theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : t β) :
    foldl f a (g <$> l) = foldl (fun x y => f x (g y)) a l := by
  simp only [foldl, fold_map_map, (· ∘ ·), flip]
#align traversable.foldl_map Traversable.foldl_map
-/

#print Traversable.foldr_map /-
@[simp]
theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : t β) :
    foldr f a (g <$> l) = foldr (f ∘ g) a l := by simp only [foldr, fold_map_map, (· ∘ ·), flip]
#align traversable.foldr_map Traversable.foldr_map
-/

#print Traversable.toList_eq_self /-
@[simp]
theorem toList_eq_self {xs : List α} : toList xs = xs :=
  by
  simp only [to_list_spec, fold_map, traverse]
  induction xs
  case nil => rfl
  case cons _ _ ih => conv_rhs => rw [← ih]; rfl
#align traversable.to_list_eq_self Traversable.toList_eq_self
-/

#print Traversable.length_toList /-
theorem length_toList {xs : t α} : length xs = List.length (toList xs) :=
  by
  unfold length
  rw [foldl_to_list]
  generalize to_list xs = ys
  let f (n : ℕ) (a : α) := n + 1
  trans List.foldl f 0 ys
  · generalize 0 = n
    induction' ys with _ _ ih generalizing n
    · simp only [List.foldl_nil]
    · simp only [List.foldl, ih (n + 1)]
  · induction' ys with _ tl ih
    · simp only [List.length, List.foldl_nil]
    · simp only [List.foldl, List.length]
      rw [← ih]
      exact tl.foldl_hom (fun x => x + 1) f f 0 fun n x => rfl
#align traversable.length_to_list Traversable.length_toList
-/

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]

#print Traversable.foldlm_toList /-
theorem foldlm_toList {f : α → β → m α} {x : α} {xs : t β} :
    foldlm f x xs = List.foldlM f x (toList xs) :=
  calc
    foldlm f x xs = unop (foldlM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs)) x := by
      simp only [mfoldl, to_list_spec, fold_map_hom_free (mfoldl.of_free_monoid f),
        mfoldl.of_free_monoid_comp_of, mfoldl.get, FreeMonoid.ofList_toList]
    _ = List.foldlM f x (toList xs) := by simp [mfoldl.of_free_monoid, unop_op, flip]
    
#align traversable.mfoldl_to_list Traversable.foldlm_toList
-/

#print Traversable.foldrm_toList /-
theorem foldrm_toList (f : α → β → m β) (x : β) (xs : t α) :
    foldrm f x xs = List.foldrM f x (toList xs) :=
  by
  change _ = mfoldr.of_free_monoid f (FreeMonoid.ofList <| to_list xs) x
  simp only [mfoldr, to_list_spec, fold_map_hom_free (mfoldr.of_free_monoid f),
    mfoldr.of_free_monoid_comp_of, mfoldr.get, FreeMonoid.ofList_toList]
#align traversable.mfoldr_to_list Traversable.foldrm_toList
-/

#print Traversable.foldlm_map /-
@[simp]
theorem foldlm_map (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) :
    foldlm f a (g <$> l) = foldlm (fun x y => f x (g y)) a l := by
  simp only [mfoldl, fold_map_map, (· ∘ ·), flip]
#align traversable.mfoldl_map Traversable.foldlm_map
-/

#print Traversable.foldrm_map /-
@[simp]
theorem foldrm_map (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) :
    foldrm f a (g <$> l) = foldrm (f ∘ g) a l := by simp only [mfoldr, fold_map_map, (· ∘ ·), flip]
#align traversable.mfoldr_map Traversable.foldrm_map
-/

end Equalities

end Traversable

