/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.free
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Control.Applicative
import Mathbin.Control.Traversable.Basic
import Mathbin.Logic.Equiv.Defs
import Mathbin.Data.List.Basic

/-!
# Free constructions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `free_magma α`: free magma (structure with binary operation without any axioms) over alphabet `α`,
  defined inductively, with traversable instance and decidable equality.
* `magma.assoc_quotient α`: quotient of a magma `α` by the associativity equivalence relation.
* `free_semigroup α`: free semigroup over alphabet `α`, defined as a structure with two fields
  `head : α` and `tail : list α` (i.e. nonempty lists), with traversable instance and decidable
  equality.
* `free_magma_assoc_quotient_equiv α`: isomorphism between `magma.assoc_quotient (free_magma α)` and
  `free_semigroup α`.
* `free_magma.lift`: the universal property of the free magma, expressing its adjointness.
-/


universe u v l

#print FreeMagma /-
/-- Free magma over a given alphabet. -/
inductive FreeMagma (α : Type u) : Type u
  | of : α → FreeMagma
  | mul : FreeMagma → FreeMagma → FreeMagma
  deriving DecidableEq
#align free_magma FreeMagma
-/

#print FreeAddMagma /-
/-- Free nonabelian additive magma over a given alphabet. -/
inductive FreeAddMagma (α : Type u) : Type u
  | of : α → FreeAddMagma
  | add : FreeAddMagma → FreeAddMagma → FreeAddMagma
  deriving DecidableEq
#align free_add_magma FreeAddMagma
-/

attribute [to_additive] FreeMagma

namespace FreeMagma

variable {α : Type u}

@[to_additive]
instance [Inhabited α] : Inhabited (FreeMagma α) :=
  ⟨of default⟩

@[to_additive]
instance : Mul (FreeMagma α) :=
  ⟨FreeMagma.mul⟩

attribute [match_pattern] Mul.mul

#print FreeMagma.mul_eq /-
@[simp, to_additive]
theorem mul_eq (x y : FreeMagma α) : mul x y = x * y :=
  rfl
#align free_magma.mul_eq FreeMagma.mul_eq
#align free_add_magma.add_eq FreeAddMagma.add_eq
-/

#print FreeMagma.recOnMul /-
/-- Recursor for `free_magma` using `x * y` instead of `free_magma.mul x y`. -/
@[elab_as_elim,
  to_additive "Recursor for `free_add_magma` using `x + y` instead of `free_add_magma.add x y`."]
def recOnMul {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (of x))
    (ih2 : ∀ x y, C x → C y → C (x * y)) : C x :=
  FreeMagma.recOn x ih1 ih2
#align free_magma.rec_on_mul FreeMagma.recOnMul
#align free_add_magma.rec_on_add FreeAddMagma.recOnAdd
-/

#print FreeMagma.hom_ext /-
@[ext, to_additive]
theorem hom_ext {β : Type v} [Mul β] {f g : FreeMagma α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
  FunLike.ext _ _ fun x =>
    recOnMul x (congr_fun h) <| by
      intros
      simp only [map_mul, *]
#align free_magma.hom_ext FreeMagma.hom_ext
#align free_add_magma.hom_ext FreeAddMagma.hom_ext
-/

end FreeMagma

#print FreeMagma.liftAux /-
/-- Lifts a function `α → β` to a magma homomorphism `free_magma α → β` given a magma `β`. -/
def FreeMagma.liftAux {α : Type u} {β : Type v} [Mul β] (f : α → β) : FreeMagma α → β
  | FreeMagma.of x => f x
  | x * y => x.liftAux * y.liftAux
#align free_magma.lift_aux FreeMagma.liftAux
-/

#print FreeAddMagma.liftAux /-
/-- Lifts a function `α → β` to an additive magma homomorphism `free_add_magma α → β` given
an additive magma `β`. -/
def FreeAddMagma.liftAux {α : Type u} {β : Type v} [Add β] (f : α → β) : FreeAddMagma α → β
  | FreeAddMagma.of x => f x
  | x + y => x.liftAux + y.liftAux
#align free_add_magma.lift_aux FreeAddMagma.liftAux
-/

attribute [to_additive FreeAddMagma.liftAux] FreeMagma.liftAux

namespace FreeMagma

section lift

variable {α : Type u} {β : Type v} [Mul β] (f : α → β)

#print FreeMagma.lift /-
/-- The universal property of the free magma expressing its adjointness. -/
@[to_additive "The universal property of the free additive magma expressing its adjointness.",
  simps symm_apply]
def lift : (α → β) ≃ (FreeMagma α →ₙ* β)
    where
  toFun f :=
    { toFun := liftAux f
      map_mul' := fun x y => rfl }
  invFun F := F ∘ of
  left_inv f := by
    ext
    rfl
  right_inv F := by
    ext
    rfl
#align free_magma.lift FreeMagma.lift
#align free_add_magma.lift FreeAddMagma.lift
-/

/- warning: free_magma.lift_of -> FreeMagma.lift_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] (f : α -> β) (x : α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1) (fun (_x : MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1) => (FreeMagma.{u1} α) -> β) (MulHom.hasCoeToFun.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1)) => (α -> β) -> (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1)) (FreeMagma.lift.{u1, u2} α β _inst_1) f) (FreeMagma.of.{u1} α x)) (f x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] (f : α -> β) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeMagma.{u1} α) => β) (FreeMagma.of.{u1} α x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) f) (FreeMagma.{u1} α) (fun (_x : FreeMagma.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeMagma.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) f) (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1 (MulHom.mulHomClass.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)) (α -> β) (fun (_x : α -> β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)) (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)) (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)))) (FreeMagma.lift.{u1, u2} α β _inst_1) f) (FreeMagma.of.{u1} α x)) (f x)
Case conversion may be inaccurate. Consider using '#align free_magma.lift_of FreeMagma.lift_ofₓ'. -/
@[simp, to_additive]
theorem lift_of (x) : lift f (of x) = f x :=
  rfl
#align free_magma.lift_of FreeMagma.lift_of
#align free_add_magma.lift_of FreeAddMagma.lift_of

/- warning: free_magma.lift_comp_of -> FreeMagma.lift_comp_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] (f : α -> β), Eq.{max (succ u1) (succ u2)} (α -> β) (Function.comp.{succ u1, succ u1, succ u2} α (FreeMagma.{u1} α) β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1) (fun (_x : MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1) => (FreeMagma.{u1} α) -> β) (MulHom.hasCoeToFun.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1)) => (α -> β) -> (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.hasMul.{u1} α) _inst_1)) (FreeMagma.lift.{u1, u2} α β _inst_1) f)) (FreeMagma.of.{u1} α)) f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] (f : α -> β), Eq.{max (succ u1) (succ u2)} (α -> β) (Function.comp.{succ u1, succ u1, succ u2} α (FreeMagma.{u1} α) β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) f) (FreeMagma.{u1} α) (fun (_x : FreeMagma.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeMagma.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) f) (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1 (MulHom.mulHomClass.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)) (α -> β) (fun (_x : α -> β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)) (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)) (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeMagma.{u1} α) β (FreeMagma.instMulFreeMagma.{u1} α) _inst_1)))) (FreeMagma.lift.{u1, u2} α β _inst_1) f)) (FreeMagma.of.{u1} α)) f
Case conversion may be inaccurate. Consider using '#align free_magma.lift_comp_of FreeMagma.lift_comp_ofₓ'. -/
@[simp, to_additive]
theorem lift_comp_of : lift f ∘ of = f :=
  rfl
#align free_magma.lift_comp_of FreeMagma.lift_comp_of
#align free_add_magma.lift_comp_of FreeAddMagma.lift_comp_of

#print FreeMagma.lift_comp_of' /-
@[simp, to_additive]
theorem lift_comp_of' (f : FreeMagma α →ₙ* β) : lift (f ∘ of) = f :=
  lift.apply_symm_apply f
#align free_magma.lift_comp_of' FreeMagma.lift_comp_of'
#align free_add_magma.lift_comp_of' FreeAddMagma.lift_comp_of'
-/

end lift

section Map

variable {α : Type u} {β : Type v} (f : α → β)

#print FreeMagma.map /-
/-- The unique magma homomorphism `free_magma α →ₙ* free_magma β` that sends
each `of x` to `of (f x)`. -/
@[to_additive
      "The unique additive magma homomorphism `free_add_magma α → free_add_magma β` that\nsends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMagma α →ₙ* FreeMagma β :=
  lift (of ∘ f)
#align free_magma.map FreeMagma.map
#align free_add_magma.map FreeAddMagma.map
-/

#print FreeMagma.map_of /-
@[simp, to_additive]
theorem map_of (x) : map f (of x) = of (f x) :=
  rfl
#align free_magma.map_of FreeMagma.map_of
#align free_add_magma.map_of FreeAddMagma.map_of
-/

end Map

section Category

variable {α β : Type u}

@[to_additive]
instance : Monad FreeMagma where
  pure _ := of
  bind _ _ x f := lift f x

/- warning: free_magma.rec_on_pure -> FreeMagma.recOnPure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {C : (FreeMagma.{u1} α) -> Sort.{u2}} (x : FreeMagma.{u1} α), (forall (x : α), C (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toHasPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α x)) -> (forall (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), (C x) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α)) x y))) -> (C x)
but is expected to have type
  forall {α : Type.{u1}} {C : (FreeMagma.{u1} α) -> Sort.{u2}} (x : FreeMagma.{u1} α), (forall (x : α), C (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α x)) -> (forall (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), (C x) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α)) x y))) -> (C x)
Case conversion may be inaccurate. Consider using '#align free_magma.rec_on_pure FreeMagma.recOnPureₓ'. -/
/-- Recursor on `free_magma` using `pure` instead of `of`. -/
@[elab_as_elim, to_additive "Recursor on `free_add_magma` using `pure` instead of `of`."]
protected def recOnPure {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (pure x))
    (ih2 : ∀ x y, C x → C y → C (x * y)) : C x :=
  FreeMagma.recOnMul x ih1 ih2
#align free_magma.rec_on_pure FreeMagma.recOnPure
#align free_add_magma.rec_on_pure FreeAddMagma.recOnPure

/- warning: free_magma.map_pure -> FreeMagma.map_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : α), Eq.{succ u1} (FreeMagma.{u1} β) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α β f (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toHasPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α x)) (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toHasPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) β (f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : α), Eq.{succ u1} (FreeMagma.{u1} β) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β f (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α x)) (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) β (f x))
Case conversion may be inaccurate. Consider using '#align free_magma.map_pure FreeMagma.map_pureₓ'. -/
@[simp, to_additive]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeMagma β) = pure (f x) :=
  rfl
#align free_magma.map_pure FreeMagma.map_pure
#align free_add_magma.map_pure FreeAddMagma.map_pure

/- warning: free_magma.map_mul' -> FreeMagma.map_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), Eq.{succ u1} (FreeMagma.{u1} β) (Functor.map.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) (Applicative.toFunctor.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) (Monad.toApplicative.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) FreeMagma.monad.{u1})) α β f (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α)) x y)) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.hasMul.{u1} β)) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α β f x) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α β f y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), Eq.{succ u1} (FreeMagma.{u1} β) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β f (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α)) x y)) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.instMulFreeMagma.{u1} β)) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β f x) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β f y))
Case conversion may be inaccurate. Consider using '#align free_magma.map_mul' FreeMagma.map_mul'ₓ'. -/
@[simp, to_additive]
theorem map_mul' (f : α → β) (x y : FreeMagma α) : f <$> (x * y) = f <$> x * f <$> y :=
  rfl
#align free_magma.map_mul' FreeMagma.map_mul'
#align free_add_magma.map_add' FreeAddMagma.map_add'

/- warning: free_magma.pure_bind -> FreeMagma.pure_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (FreeMagma.{u1} β)) (x : α), Eq.{succ u1} (FreeMagma.{u1} β) (Bind.bind.{u1, u1} FreeMagma.{u1} (Monad.toHasBind.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1}) α β (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toHasPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α x) f) (f x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (FreeMagma.{u1} β)) (x : α), Eq.{succ u1} (FreeMagma.{u1} β) (Bind.bind.{u1, u1} FreeMagma.{u1} (Monad.toBind.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1}) α β (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α x) f) (f x)
Case conversion may be inaccurate. Consider using '#align free_magma.pure_bind FreeMagma.pure_bindₓ'. -/
@[simp, to_additive]
theorem pure_bind (f : α → FreeMagma β) (x) : pure x >>= f = f x :=
  rfl
#align free_magma.pure_bind FreeMagma.pure_bind
#align free_add_magma.pure_bind FreeAddMagma.pure_bind

/- warning: free_magma.mul_bind -> FreeMagma.mul_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (FreeMagma.{u1} β)) (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), Eq.{succ u1} (FreeMagma.{u1} β) (Bind.bind.{u1, u1} FreeMagma.{u1} (Monad.toHasBind.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1}) α β (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α)) x y) f) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.hasMul.{u1} β)) (Bind.bind.{u1, u1} FreeMagma.{u1} (Monad.toHasBind.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1}) α β x f) (Bind.bind.{u1, u1} FreeMagma.{u1} (Monad.toHasBind.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1}) α β y f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (FreeMagma.{u1} β)) (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), Eq.{succ u1} (FreeMagma.{u1} β) (Bind.bind.{u1, u1} FreeMagma.{u1} (Monad.toBind.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1}) α β (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α)) x y) f) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.instMulFreeMagma.{u1} β)) (Bind.bind.{u1, u1} FreeMagma.{u1} (Monad.toBind.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1}) α β x f) (Bind.bind.{u1, u1} FreeMagma.{u1} (Monad.toBind.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1}) α β y f))
Case conversion may be inaccurate. Consider using '#align free_magma.mul_bind FreeMagma.mul_bindₓ'. -/
@[simp, to_additive]
theorem mul_bind (f : α → FreeMagma β) (x y : FreeMagma α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  rfl
#align free_magma.mul_bind FreeMagma.mul_bind
#align free_add_magma.add_bind FreeAddMagma.add_bind

/- warning: free_magma.pure_seq -> FreeMagma.pure_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> β} {x : FreeMagma.{u1} α}, Eq.{succ u1} (FreeMagma.{u1} β) (Seq.seq.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) (Applicative.toHasSeq.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) (Monad.toApplicative.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) FreeMagma.monad.{u1})) α β (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) (Applicative.toHasPure.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) (Monad.toApplicative.{u1, u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) FreeMagma.monad.{u1})) (α -> β) f) x) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α β f x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> β} {x : FreeMagma.{u1} α}, Eq.{succ u1} (FreeMagma.{u1} β) (Seq.seq.{u1, u1} FreeMagma.{u1} (Applicative.toSeq.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) (α -> β) f) (fun (x._@.Mathlib.Algebra.Free._hyg.1862 : Unit) => x)) (Functor.map.{u1, u1} FreeMagma.{u1} (Applicative.toFunctor.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β f x)
Case conversion may be inaccurate. Consider using '#align free_magma.pure_seq FreeMagma.pure_seqₓ'. -/
@[simp, to_additive]
theorem pure_seq {α β : Type u} {f : α → β} {x : FreeMagma α} : pure f <*> x = f <$> x :=
  rfl
#align free_magma.pure_seq FreeMagma.pure_seq
#align free_add_magma.pure_seq FreeAddMagma.pure_seq

/- warning: free_magma.mul_seq -> FreeMagma.mul_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {f : FreeMagma.{u1} (α -> β)} {g : FreeMagma.{u1} (α -> β)} {x : FreeMagma.{u1} α}, Eq.{succ u1} (FreeMagma.{u1} β) (Seq.seq.{u1, u1} FreeMagma.{u1} (Applicative.toHasSeq.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α β (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} (α -> β)) (FreeMagma.{u1} (α -> β)) (FreeMagma.{u1} (α -> β)) (instHMul.{u1} (FreeMagma.{u1} (α -> β)) (FreeMagma.hasMul.{u1} (α -> β))) f g) x) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.hasMul.{u1} β)) (Seq.seq.{u1, u1} FreeMagma.{u1} (Applicative.toHasSeq.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α β f x) (Seq.seq.{u1, u1} FreeMagma.{u1} (Applicative.toHasSeq.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α β g x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {f : FreeMagma.{u1} (α -> β)} {g : FreeMagma.{u1} (α -> β)} {x : FreeMagma.{u1} α}, Eq.{succ u1} (FreeMagma.{u1} β) (Seq.seq.{u1, u1} FreeMagma.{u1} (Applicative.toSeq.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} (α -> β)) (FreeMagma.{u1} (α -> β)) (FreeMagma.{u1} (α -> β)) (instHMul.{u1} (FreeMagma.{u1} (α -> β)) (FreeMagma.instMulFreeMagma.{u1} (α -> β))) f g) (fun (x._@.Mathlib.Algebra.Free._hyg.1904 : Unit) => x)) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.instMulFreeMagma.{u1} β)) (Seq.seq.{u1, u1} FreeMagma.{u1} (Applicative.toSeq.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β f (fun (x._@.Mathlib.Algebra.Free._hyg.1915 : Unit) => x)) (Seq.seq.{u1, u1} FreeMagma.{u1} (Applicative.toSeq.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α β g (fun (x._@.Mathlib.Algebra.Free._hyg.1925 : Unit) => x)))
Case conversion may be inaccurate. Consider using '#align free_magma.mul_seq FreeMagma.mul_seqₓ'. -/
@[simp, to_additive]
theorem mul_seq {α β : Type u} {f g : FreeMagma (α → β)} {x : FreeMagma α} :
    f * g <*> x = (f <*> x) * (g <*> x) :=
  rfl
#align free_magma.mul_seq FreeMagma.mul_seq
#align free_add_magma.add_seq FreeAddMagma.add_seq

@[to_additive]
instance : LawfulMonad FreeMagma.{u}
    where
  pure_bind _ _ _ _ := rfl
  bind_assoc α β γ x f g :=
    FreeMagma.recOnPure x (fun x => rfl) fun x y ih1 ih2 => by
      rw [mul_bind, mul_bind, mul_bind, ih1, ih2]
  id_map α x := FreeMagma.recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by rw [map_mul', ih1, ih2]

end Category

end FreeMagma

#print FreeMagma.traverse /-
/-- `free_magma` is traversable. -/
protected def FreeMagma.traverse {m : Type u → Type u} [Applicative m] {α β : Type u}
    (F : α → m β) : FreeMagma α → m (FreeMagma β)
  | FreeMagma.of x => FreeMagma.of <$> F x
  | x * y => (· * ·) <$> x.traverse <*> y.traverse
#align free_magma.traverse FreeMagma.traverse
-/

#print FreeAddMagma.traverse /-
/-- `free_add_magma` is traversable. -/
protected def FreeAddMagma.traverse {m : Type u → Type u} [Applicative m] {α β : Type u}
    (F : α → m β) : FreeAddMagma α → m (FreeAddMagma β)
  | FreeAddMagma.of x => FreeAddMagma.of <$> F x
  | x + y => (· + ·) <$> x.traverse <*> y.traverse
#align free_add_magma.traverse FreeAddMagma.traverse
-/

attribute [to_additive FreeAddMagma.traverse] FreeMagma.traverse

namespace FreeMagma

variable {α : Type u}

section Category

variable {β : Type u}

@[to_additive]
instance : Traversable FreeMagma :=
  ⟨@FreeMagma.traverse⟩

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

/- warning: free_magma.traverse_pure -> FreeMagma.traverse_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) (x : α), Eq.{succ u1} (m (FreeMagma.{u1} β)) (Traversable.traverse.{u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) FreeMagma.traversable.{u1} m _inst_1 α β F (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toHasPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) α x)) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) β (FreeMagma.{u1} β) (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toHasPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) β) (F x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) (x : α), Eq.{succ u1} (m (FreeMagma.{u1} β)) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.instTraversableFreeMagma.{u1} m _inst_1 α β F (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α x)) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) β (FreeMagma.{u1} β) (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) β) (F x))
Case conversion may be inaccurate. Consider using '#align free_magma.traverse_pure FreeMagma.traverse_pureₓ'. -/
@[simp, to_additive]
theorem traverse_pure (x) : traverse F (pure x : FreeMagma α) = pure <$> F x :=
  rfl
#align free_magma.traverse_pure FreeMagma.traverse_pure
#align free_add_magma.traverse_pure FreeAddMagma.traverse_pure

/- warning: free_magma.traverse_pure' -> FreeMagma.traverse_pure' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)), Eq.{succ u1} (α -> (m (FreeMagma.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} α (FreeMagma.{u1} α) (m (FreeMagma.{u1} β)) (Traversable.traverse.{u1} (fun {β : Type.{u1}} => FreeMagma.{u1} β) FreeMagma.traversable.{u1} m _inst_1 α β F) (Pure.pure.{u1, u1} (fun {β : Type.{u1}} => FreeMagma.{u1} β) (Applicative.toHasPure.{u1, u1} (fun {β : Type.{u1}} => FreeMagma.{u1} β) (Monad.toApplicative.{u1, u1} (fun {β : Type.{u1}} => FreeMagma.{u1} β) FreeMagma.monad.{u1})) α)) (fun (x : α) => Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) β (FreeMagma.{u1} β) (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toHasPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.monad.{u1})) β) (F x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)), Eq.{succ u1} (α -> (m (FreeMagma.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} α (FreeMagma.{u1} α) (m (FreeMagma.{u1} β)) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.instTraversableFreeMagma.{u1} m _inst_1 α β F) (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) α)) (fun (x : α) => Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) β (FreeMagma.{u1} β) (Pure.pure.{u1, u1} FreeMagma.{u1} (Applicative.toPure.{u1, u1} FreeMagma.{u1} (Monad.toApplicative.{u1, u1} FreeMagma.{u1} FreeMagma.instMonadFreeMagma.{u1})) β) (F x))
Case conversion may be inaccurate. Consider using '#align free_magma.traverse_pure' FreeMagma.traverse_pure'ₓ'. -/
@[simp, to_additive]
theorem traverse_pure' : traverse F ∘ pure = fun x => (pure <$> F x : m (FreeMagma β)) :=
  rfl
#align free_magma.traverse_pure' FreeMagma.traverse_pure'
#align free_add_magma.traverse_pure' FreeAddMagma.traverse_pure'

/- warning: free_magma.traverse_mul -> FreeMagma.traverse_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), Eq.{succ u1} (m (FreeMagma.{u1} β)) (Traversable.traverse.{u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) FreeMagma.traversable.{u1} m _inst_1 α β F (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α)) x y)) (Seq.seq.{u1, u1} m (Applicative.toHasSeq.{u1, u1} m _inst_1) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) (FreeMagma.{u1} β) ((FreeMagma.{u1} β) -> (FreeMagma.{u1} β)) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.hasMul.{u1} β))) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.traversable.{u1} m _inst_1 α β F x)) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.traversable.{u1} m _inst_1 α β F y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), Eq.{succ u1} (m (FreeMagma.{u1} β)) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.instTraversableFreeMagma.{u1} m _inst_1 α β F (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α)) x y)) (Seq.seq.{u1, u1} m (Applicative.toSeq.{u1, u1} m _inst_1) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) (FreeMagma.{u1} β) ((FreeMagma.{u1} β) -> (FreeMagma.{u1} β)) (fun (x._@.Mathlib.Algebra.Free._hyg.2506 : FreeMagma.{u1} β) (x._@.Mathlib.Algebra.Free._hyg.2508 : FreeMagma.{u1} β) => HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.instMulFreeMagma.{u1} β)) x._@.Mathlib.Algebra.Free._hyg.2506 x._@.Mathlib.Algebra.Free._hyg.2508) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.instTraversableFreeMagma.{u1} m _inst_1 α β F x)) (fun (x._@.Mathlib.Algebra.Free._hyg.2525 : Unit) => Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.instTraversableFreeMagma.{u1} m _inst_1 α β F y))
Case conversion may be inaccurate. Consider using '#align free_magma.traverse_mul FreeMagma.traverse_mulₓ'. -/
@[simp, to_additive]
theorem traverse_mul (x y : FreeMagma α) :
    traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y :=
  rfl
#align free_magma.traverse_mul FreeMagma.traverse_mul
#align free_add_magma.traverse_add FreeAddMagma.traverse_add

/- warning: free_magma.traverse_mul' -> FreeMagma.traverse_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)), Eq.{succ u1} ((FreeMagma.{u1} α) -> (FreeMagma.{u1} α) -> (m (FreeMagma.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} (FreeMagma.{u1} α) ((FreeMagma.{u1} α) -> (FreeMagma.{u1} α)) ((FreeMagma.{u1} α) -> (m (FreeMagma.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (m (FreeMagma.{u1} β)) (Traversable.traverse.{u1} (fun {α : Type.{u1}} => FreeMagma.{u1} α) FreeMagma.traversable.{u1} m _inst_1 α β F)) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α)))) (fun (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α) => Seq.seq.{u1, u1} m (Applicative.toHasSeq.{u1, u1} m _inst_1) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) (FreeMagma.{u1} β) ((FreeMagma.{u1} β) -> (FreeMagma.{u1} β)) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.hasMul.{u1} β))) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.traversable.{u1} m _inst_1 α β F x)) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.traversable.{u1} m _inst_1 α β F y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)), Eq.{succ u1} ((FreeMagma.{u1} α) -> (FreeMagma.{u1} α) -> (m (FreeMagma.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} (FreeMagma.{u1} α) ((FreeMagma.{u1} α) -> (FreeMagma.{u1} α)) ((FreeMagma.{u1} α) -> (m (FreeMagma.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (m (FreeMagma.{u1} β)) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.instTraversableFreeMagma.{u1} m _inst_1 α β F)) (Mul.mul.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α))) (fun (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α) => Seq.seq.{u1, u1} m (Applicative.toSeq.{u1, u1} m _inst_1) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) (FreeMagma.{u1} β) ((FreeMagma.{u1} β) -> (FreeMagma.{u1} β)) (fun (x._@.Mathlib.Algebra.Free._hyg.2574 : FreeMagma.{u1} β) (x._@.Mathlib.Algebra.Free._hyg.2576 : FreeMagma.{u1} β) => HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} β) (FreeMagma.{u1} β) (FreeMagma.{u1} β) (instHMul.{u1} (FreeMagma.{u1} β) (FreeMagma.instMulFreeMagma.{u1} β)) x._@.Mathlib.Algebra.Free._hyg.2574 x._@.Mathlib.Algebra.Free._hyg.2576) (Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.instTraversableFreeMagma.{u1} m _inst_1 α β F x)) (fun (x._@.Mathlib.Algebra.Free._hyg.2593 : Unit) => Traversable.traverse.{u1} FreeMagma.{u1} FreeMagma.instTraversableFreeMagma.{u1} m _inst_1 α β F y))
Case conversion may be inaccurate. Consider using '#align free_magma.traverse_mul' FreeMagma.traverse_mul'ₓ'. -/
@[simp, to_additive]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ @Mul.mul (FreeMagma α) _ = fun x y =>
      (· * ·) <$> traverse F x <*> traverse F y :=
  rfl
#align free_magma.traverse_mul' FreeMagma.traverse_mul'
#align free_add_magma.traverse_add' FreeAddMagma.traverse_add'

#print FreeMagma.traverse_eq /-
@[simp, to_additive]
theorem traverse_eq (x) : FreeMagma.traverse F x = traverse F x :=
  rfl
#align free_magma.traverse_eq FreeMagma.traverse_eq
#align free_add_magma.traverse_eq FreeAddMagma.traverse_eq
-/

/- warning: free_magma.mul_map_seq -> FreeMagma.mul_map_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (FreeMagma.{u1} α)) (Seq.seq.{u1, u1} (id.{succ (succ u1)} Type.{u1}) (Applicative.toHasSeq.{u1, u1} (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1})) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (Functor.map.{u1, u1} (id.{succ (succ u1)} Type.{u1}) (Traversable.toFunctor.{u1} (id.{succ (succ u1)} Type.{u1}) id.traversable.{u1}) (FreeMagma.{u1} α) ((FreeMagma.{u1} α) -> (FreeMagma.{u1} α)) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α))) x) y) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α)) x y)
but is expected to have type
  forall {α : Type.{u1}} (x : FreeMagma.{u1} α) (y : FreeMagma.{u1} α), Eq.{succ u1} (Id.{u1} (FreeMagma.{u1} α)) (Seq.seq.{u1, u1} Id.{u1} (Applicative.toSeq.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (Functor.map.{u1, u1} Id.{u1} (Traversable.toFunctor.{u1} Id.{u1} instTraversableId.{u1}) (FreeMagma.{u1} α) ((FreeMagma.{u1} α) -> (FreeMagma.{u1} α)) (fun (x._@.Mathlib.Algebra.Free._hyg.2662 : FreeMagma.{u1} α) (x._@.Mathlib.Algebra.Free._hyg.2664 : FreeMagma.{u1} α) => HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α)) x._@.Mathlib.Algebra.Free._hyg.2662 x._@.Mathlib.Algebra.Free._hyg.2664) x) (fun (x._@.Mathlib.Algebra.Free._hyg.2679 : Unit) => y)) (HMul.hMul.{u1, u1, u1} (FreeMagma.{u1} α) (FreeMagma.{u1} α) (FreeMagma.{u1} α) (instHMul.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α)) x y)
Case conversion may be inaccurate. Consider using '#align free_magma.mul_map_seq FreeMagma.mul_map_seqₓ'. -/
@[simp, to_additive]
theorem mul_map_seq (x y : FreeMagma α) :
    ((· * ·) <$> x <*> y : id (FreeMagma α)) = (x * y : FreeMagma α) :=
  rfl
#align free_magma.mul_map_seq FreeMagma.mul_map_seq
#align free_add_magma.add_map_seq FreeAddMagma.add_map_seq

@[to_additive]
instance : IsLawfulTraversable FreeMagma.{u} :=
  {
    FreeMagma.lawfulMonad with
    id_traverse := fun α x =>
      FreeMagma.recOnPure x (fun x => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, mul_map_seq]
    comp_traverse := fun F G hf1 hg1 hf2 hg2 α β γ f g x =>
      FreeMagma.recOnPure x
        (fun x => by skip <;> simp only [traverse_pure, traverse_pure', functor_norm])
        fun x y ih1 ih2 => by
        skip <;> rw [traverse_mul, ih1, ih2, traverse_mul] <;>
          simp only [traverse_mul', functor_norm]
    naturality := fun F G hf1 hg1 hf2 hg2 η α β f x =>
      FreeMagma.recOnPure x (fun x => by simp only [traverse_pure, functor_norm]) fun x y ih1 ih2 =>
        by simp only [traverse_mul, functor_norm] <;> rw [ih1, ih2]
    traverse_eq_map_id := fun α β f x =>
      FreeMagma.recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq] <;> rfl }

end Category

end FreeMagma

/- warning: free_magma.repr -> FreeMagma.repr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Repr.{u1} α], (FreeMagma.{u1} α) -> String
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Repr.{u1} α], (FreeMagma.{u1} α) -> Std.Format
Case conversion may be inaccurate. Consider using '#align free_magma.repr FreeMagma.reprₓ'. -/
/-- Representation of an element of a free magma. -/
protected def FreeMagma.repr {α : Type u} [Repr α] : FreeMagma α → String
  | FreeMagma.of x => repr x
  | x * y => "( " ++ x.repr ++ " * " ++ y.repr ++ " )"
#align free_magma.repr FreeMagma.repr

/- warning: free_add_magma.repr -> FreeAddMagma.repr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Repr.{u1} α], (FreeAddMagma.{u1} α) -> String
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Repr.{u1} α], (FreeAddMagma.{u1} α) -> Std.Format
Case conversion may be inaccurate. Consider using '#align free_add_magma.repr FreeAddMagma.reprₓ'. -/
/-- Representation of an element of a free additive magma. -/
protected def FreeAddMagma.repr {α : Type u} [Repr α] : FreeAddMagma α → String
  | FreeAddMagma.of x => repr x
  | x + y => "( " ++ x.repr ++ " + " ++ y.repr ++ " )"
#align free_add_magma.repr FreeAddMagma.repr

attribute [to_additive FreeAddMagma.repr] FreeMagma.repr

@[to_additive]
instance {α : Type u} [Repr α] : Repr (FreeMagma α) :=
  ⟨FreeMagma.repr⟩

#print FreeMagma.length /-
/-- Length of an element of a free magma. -/
@[simp]
def FreeMagma.length {α : Type u} : FreeMagma α → ℕ
  | FreeMagma.of x => 1
  | x * y => x.length + y.length
#align free_magma.length FreeMagma.length
-/

#print FreeAddMagma.length /-
/-- Length of an element of a free additive magma. -/
@[simp]
def FreeAddMagma.length {α : Type u} : FreeAddMagma α → ℕ
  | FreeAddMagma.of x => 1
  | x + y => x.length + y.length
#align free_add_magma.length FreeAddMagma.length
-/

attribute [to_additive FreeAddMagma.length] FreeMagma.length

#print AddMagma.AssocRel /-
/-- Associativity relations for an additive magma. -/
inductive AddMagma.AssocRel (α : Type u) [Add α] : α → α → Prop
  | intro : ∀ x y z, AddMagma.AssocRel (x + y + z) (x + (y + z))
  | left : ∀ w x y z, AddMagma.AssocRel (w + (x + y + z)) (w + (x + (y + z)))
#align add_magma.assoc_rel AddMagma.AssocRel
-/

#print Magma.AssocRel /-
/-- Associativity relations for a magma. -/
@[to_additive AddMagma.AssocRel "Associativity relations for an additive magma."]
inductive Magma.AssocRel (α : Type u) [Mul α] : α → α → Prop
  | intro : ∀ x y z, Magma.AssocRel (x * y * z) (x * (y * z))
  | left : ∀ w x y z, Magma.AssocRel (w * (x * y * z)) (w * (x * (y * z)))
#align magma.assoc_rel Magma.AssocRel
#align add_magma.assoc_rel AddMagma.AssocRel
-/

namespace Magma

#print Magma.AssocQuotient /-
/-- Semigroup quotient of a magma. -/
@[to_additive AddMagma.FreeAddSemigroup "Additive semigroup quotient of an additive magma."]
def AssocQuotient (α : Type u) [Mul α] : Type u :=
  Quot <| AssocRel α
#align magma.assoc_quotient Magma.AssocQuotient
#align add_magma.free_add_semigroup AddMagma.FreeAddSemigroup
-/

namespace AssocQuotient

variable {α : Type u} [Mul α]

#print Magma.AssocQuotient.quot_mk_assoc /-
@[to_additive]
theorem quot_mk_assoc (x y z : α) : Quot.mk (AssocRel α) (x * y * z) = Quot.mk _ (x * (y * z)) :=
  Quot.sound (AssocRel.intro _ _ _)
#align magma.assoc_quotient.quot_mk_assoc Magma.AssocQuotient.quot_mk_assoc
#align add_magma.free_add_semigroup.quot_mk_assoc AddMagma.FreeAddSemigroup.quot_mk_assoc
-/

#print Magma.AssocQuotient.quot_mk_assoc_left /-
@[to_additive]
theorem quot_mk_assoc_left (x y z w : α) :
    Quot.mk (AssocRel α) (x * (y * z * w)) = Quot.mk _ (x * (y * (z * w))) :=
  Quot.sound (AssocRel.left _ _ _ _)
#align magma.assoc_quotient.quot_mk_assoc_left Magma.AssocQuotient.quot_mk_assoc_left
#align add_magma.free_add_semigroup.quot_mk_assoc_left AddMagma.FreeAddSemigroup.quot_mk_assoc_left
-/

@[to_additive]
instance : Semigroup (AssocQuotient α)
    where
  mul x y := by
    refine' Quot.liftOn₂ x y (fun x y => Quot.mk _ (x * y)) _ _
    · rintro a b₁ b₂ (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only
      · exact quot_mk_assoc_left _ _ _ _
      · rw [← quot_mk_assoc, quot_mk_assoc_left, quot_mk_assoc]
    · rintro a₁ a₂ b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only
      · simp only [quot_mk_assoc, quot_mk_assoc_left]
      ·
        rw [quot_mk_assoc, quot_mk_assoc, quot_mk_assoc_left, quot_mk_assoc_left,
          quot_mk_assoc_left, ← quot_mk_assoc c d, ← quot_mk_assoc c d, quot_mk_assoc_left]
  mul_assoc x y z := Quot.induction_on₃ x y z fun p q r => quot_mk_assoc p q r

/- warning: magma.assoc_quotient.of -> Magma.AssocQuotient.of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], MulHom.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], MulHom.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align magma.assoc_quotient.of Magma.AssocQuotient.ofₓ'. -/
/-- Embedding from magma to its free semigroup. -/
@[to_additive "Embedding from additive magma to its free additive semigroup."]
def of : α →ₙ* AssocQuotient α :=
  ⟨Quot.mk _, fun x y => rfl⟩
#align magma.assoc_quotient.of Magma.AssocQuotient.of
#align add_magma.free_add_semigroup.of AddMagma.FreeAddSemigroup.of

@[to_additive]
instance [Inhabited α] : Inhabited (AssocQuotient α) :=
  ⟨of default⟩

#print Magma.AssocQuotient.induction_on /-
@[elab_as_elim, to_additive]
protected theorem induction_on {C : AssocQuotient α → Prop} (x : AssocQuotient α)
    (ih : ∀ x, C (of x)) : C x :=
  Quot.inductionOn x ih
#align magma.assoc_quotient.induction_on Magma.AssocQuotient.induction_on
#align add_magma.free_add_semigroup.induction_on AddMagma.FreeAddSemigroup.induction_on
-/

section lift

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

/- warning: magma.assoc_quotient.hom_ext -> Magma.AssocQuotient.hom_ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β] {f : MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2)} {g : MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2)}, (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2) f (Magma.AssocQuotient.of.{u1} α _inst_1)) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2) g (Magma.AssocQuotient.of.{u1} α _inst_1))) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2)) f g)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β] {f : MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)} {g : MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)}, (Eq.{max (succ u1) (succ u2)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2) f (Magma.AssocQuotient.of.{u1} α _inst_1)) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2) g (Magma.AssocQuotient.of.{u1} α _inst_1))) -> (Eq.{max (succ u1) (succ u2)} (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) f g)
Case conversion may be inaccurate. Consider using '#align magma.assoc_quotient.hom_ext Magma.AssocQuotient.hom_extₓ'. -/
@[ext, to_additive]
theorem hom_ext {f g : AssocQuotient α →ₙ* β} (h : f.comp of = g.comp of) : f = g :=
  FunLike.ext _ _ fun x => AssocQuotient.induction_on x <| FunLike.congr_fun h
#align magma.assoc_quotient.hom_ext Magma.AssocQuotient.hom_ext
#align add_magma.free_add_semigroup.hom_ext AddMagma.FreeAddSemigroup.hom_ext

/- warning: magma.assoc_quotient.lift -> Magma.AssocQuotient.lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align magma.assoc_quotient.lift Magma.AssocQuotient.liftₓ'. -/
/-- Lifts a magma homomorphism `α → β` to a semigroup homomorphism `magma.assoc_quotient α → β`
given a semigroup `β`. -/
@[to_additive
      "Lifts an additive magma homomorphism `α → β` to an additive semigroup homomorphism\n`add_magma.assoc_quotient α → β` given an additive semigroup `β`.",
  simps symm_apply]
def lift : (α →ₙ* β) ≃ (AssocQuotient α →ₙ* β)
    where
  toFun f :=
    { toFun := fun x =>
        Quot.liftOn x f <| by
          rintro a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only [map_mul, mul_assoc]
      map_mul' := fun x y => Quot.induction_on₂ x y (map_mul f) }
  invFun f := f.comp of
  left_inv f := FunLike.ext _ _ fun x => rfl
  right_inv f := hom_ext <| FunLike.ext _ _ fun x => rfl
#align magma.assoc_quotient.lift Magma.AssocQuotient.lift
#align add_magma.free_add_semigroup.lift AddMagma.FreeAddSemigroup.lift

/- warning: magma.assoc_quotient.lift_of -> Magma.AssocQuotient.lift_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (x : α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2)) (fun (_x : MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2)) => (Magma.AssocQuotient.{u1} α _inst_1) -> β) (MulHom.hasCoeToFun.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2)) (coeFn.{max 1 (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) => (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) -> (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (Magma.AssocQuotient.lift.{u1, u2} α _inst_1 β _inst_2) f) (coeFn.{succ u1, succ u1} (MulHom.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1))) (fun (_x : MulHom.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1))) => α -> (Magma.AssocQuotient.{u1} α _inst_1)) (MulHom.hasCoeToFun.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1))) (Magma.AssocQuotient.of.{u1} α _inst_1) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (fun (_x : MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) => α -> β) (MulHom.hasCoeToFun.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) f x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Magma.AssocQuotient.{u1} α _inst_1) => β) (FunLike.coe.{succ u1, succ u1, succ u1} (MulHom.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1))) α (fun (a : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Magma.AssocQuotient.{u1} α _inst_1) a) (MulHomClass.toFunLike.{u1, u1, u1} (MulHom.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1))) α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (MulHom.mulHomClass.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)))) (Magma.AssocQuotient.of.{u1} α _inst_1) x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) f) (Magma.AssocQuotient.{u1} α _inst_1) (fun (_x : Magma.AssocQuotient.{u1} α _inst_1) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Magma.AssocQuotient.{u1} α _inst_1) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) f) (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2) (MulHom.mulHomClass.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (fun (_x : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))))) (Magma.AssocQuotient.lift.{u1, u2} α _inst_1 β _inst_2) f) (FunLike.coe.{succ u1, succ u1, succ u1} (MulHom.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Magma.AssocQuotient.{u1} α _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MulHom.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1))) α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (MulHom.mulHomClass.{u1, u1} α (Magma.AssocQuotient.{u1} α _inst_1) _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)))) (Magma.AssocQuotient.of.{u1} α _inst_1) x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) α β _inst_1 (Semigroup.toMul.{u2} β _inst_2) (MulHom.mulHomClass.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2))) f x)
Case conversion may be inaccurate. Consider using '#align magma.assoc_quotient.lift_of Magma.AssocQuotient.lift_ofₓ'. -/
@[simp, to_additive]
theorem lift_of (x : α) : lift f (of x) = f x :=
  rfl
#align magma.assoc_quotient.lift_of Magma.AssocQuotient.lift_of
#align add_magma.free_add_semigroup.lift_of AddMagma.FreeAddSemigroup.lift_of

/- warning: magma.assoc_quotient.lift_comp_of -> Magma.AssocQuotient.lift_comp_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)), Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2) (coeFn.{max 1 (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) => (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) -> (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (Magma.AssocQuotient.lift.{u1, u2} α _inst_1 β _inst_2) f) (Magma.AssocQuotient.of.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)), Eq.{max (succ u1) (succ u2)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (fun (_x : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))))) (Magma.AssocQuotient.lift.{u1, u2} α _inst_1 β _inst_2) f) (Magma.AssocQuotient.of.{u1} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align magma.assoc_quotient.lift_comp_of Magma.AssocQuotient.lift_comp_ofₓ'. -/
@[simp, to_additive]
theorem lift_comp_of : (lift f).comp of = f :=
  lift.symm_apply_apply f
#align magma.assoc_quotient.lift_comp_of Magma.AssocQuotient.lift_comp_of
#align add_magma.free_add_semigroup.lift_comp_of AddMagma.FreeAddSemigroup.lift_comp_of

/- warning: magma.assoc_quotient.lift_comp_of' -> Magma.AssocQuotient.lift_comp_of' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β] (f : MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2)), Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2)) (coeFn.{max 1 (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) => (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) -> (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toHasMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2))) (Magma.AssocQuotient.lift.{u1, u2} α _inst_1 β _inst_2) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} β _inst_2) f (Magma.AssocQuotient.of.{u1} α _inst_1))) f
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Semigroup.{u2} β] (f : MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2) f (Magma.AssocQuotient.of.{u1} α _inst_1))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (fun (_x : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) => MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))) (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2)) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (Semigroup.toMul.{u2} β _inst_2)) (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) β (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2))))) (Magma.AssocQuotient.lift.{u1, u2} α _inst_1 β _inst_2) (MulHom.comp.{u1, u1, u2} α (Magma.AssocQuotient.{u1} α _inst_1) β _inst_1 (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} β _inst_2) f (Magma.AssocQuotient.of.{u1} α _inst_1))) f
Case conversion may be inaccurate. Consider using '#align magma.assoc_quotient.lift_comp_of' Magma.AssocQuotient.lift_comp_of'ₓ'. -/
@[simp, to_additive]
theorem lift_comp_of' (f : AssocQuotient α →ₙ* β) : lift (f.comp of) = f :=
  lift.apply_symm_apply f
#align magma.assoc_quotient.lift_comp_of' Magma.AssocQuotient.lift_comp_of'
#align add_magma.free_add_semigroup.lift_comp_of' AddMagma.FreeAddSemigroup.lift_comp_of'

end lift

variable {β : Type v} [Mul β] (f : α →ₙ* β)

/- warning: magma.assoc_quotient.map -> Magma.AssocQuotient.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Mul.{u2} β], (MulHom.{u1, u2} α β _inst_1 _inst_2) -> (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.{u2} β _inst_2) (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.semigroup.{u1} α _inst_1)) (Semigroup.toHasMul.{u2} (Magma.AssocQuotient.{u2} β _inst_2) (Magma.AssocQuotient.semigroup.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {β : Type.{u2}} [_inst_2 : Mul.{u2} β], (MulHom.{u1, u2} α β _inst_1 _inst_2) -> (MulHom.{u1, u2} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.{u2} β _inst_2) (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} α _inst_1) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} α _inst_1)) (Semigroup.toMul.{u2} (Magma.AssocQuotient.{u2} β _inst_2) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align magma.assoc_quotient.map Magma.AssocQuotient.mapₓ'. -/
/-- From a magma homomorphism `α →ₙ* β` to a semigroup homomorphism
`magma.assoc_quotient α →ₙ* magma.assoc_quotient β`. -/
@[to_additive
      "From an additive magma homomorphism `α → β` to an additive semigroup homomorphism\n`add_magma.assoc_quotient α → add_magma.assoc_quotient β`."]
def map : AssocQuotient α →ₙ* AssocQuotient β :=
  lift (of.comp f)
#align magma.assoc_quotient.map Magma.AssocQuotient.map
#align add_magma.free_add_semigroup.map AddMagma.FreeAddSemigroup.map

#print Magma.AssocQuotient.map_of /-
@[simp, to_additive]
theorem map_of (x) : map f (of x) = of (f x) :=
  rfl
#align magma.assoc_quotient.map_of Magma.AssocQuotient.map_of
#align add_magma.free_add_semigroup.map_of AddMagma.FreeAddSemigroup.map_of
-/

end AssocQuotient

end Magma

#print FreeAddSemigroup /-
/-- Free additive semigroup over a given alphabet. -/
@[ext]
structure FreeAddSemigroup (α : Type u) where
  head : α
  tail : List α
#align free_add_semigroup FreeAddSemigroup
-/

#print FreeSemigroup /-
/-- Free semigroup over a given alphabet. -/
@[ext, to_additive]
structure FreeSemigroup (α : Type u) where
  head : α
  tail : List α
#align free_semigroup FreeSemigroup
#align free_add_semigroup FreeAddSemigroup
-/

namespace FreeSemigroup

variable {α : Type u}

@[to_additive]
instance : Semigroup (FreeSemigroup α)
    where
  mul L1 L2 := ⟨L1.1, L1.2 ++ L2.1 :: L2.2⟩
  mul_assoc L1 L2 L3 := ext _ _ rfl <| List.append_assoc _ _ _

/- warning: free_semigroup.head_mul -> FreeSemigroup.head_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} α (FreeSemigroup.head.{u1} α (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) x y)) (FreeSemigroup.head.{u1} α x)
but is expected to have type
  forall {α : Type.{u1}} (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} α (FreeSemigroup.head.{u1} α (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) x y)) (FreeSemigroup.head.{u1} α x)
Case conversion may be inaccurate. Consider using '#align free_semigroup.head_mul FreeSemigroup.head_mulₓ'. -/
@[simp, to_additive]
theorem head_mul (x y : FreeSemigroup α) : (x * y).1 = x.1 :=
  rfl
#align free_semigroup.head_mul FreeSemigroup.head_mul
#align free_add_semigroup.head_add FreeAddSemigroup.head_add

/- warning: free_semigroup.tail_mul -> FreeSemigroup.tail_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (List.{u1} α) (FreeSemigroup.tail.{u1} α (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) x y)) (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) (FreeSemigroup.tail.{u1} α x) (List.cons.{u1} α (FreeSemigroup.head.{u1} α y) (FreeSemigroup.tail.{u1} α y)))
but is expected to have type
  forall {α : Type.{u1}} (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (List.{u1} α) (FreeSemigroup.tail.{u1} α (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) x y)) (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) (FreeSemigroup.tail.{u1} α x) (List.cons.{u1} α (FreeSemigroup.head.{u1} α y) (FreeSemigroup.tail.{u1} α y)))
Case conversion may be inaccurate. Consider using '#align free_semigroup.tail_mul FreeSemigroup.tail_mulₓ'. -/
@[simp, to_additive]
theorem tail_mul (x y : FreeSemigroup α) : (x * y).2 = x.2 ++ y.1 :: y.2 :=
  rfl
#align free_semigroup.tail_mul FreeSemigroup.tail_mul
#align free_add_semigroup.tail_add FreeAddSemigroup.tail_add

/- warning: free_semigroup.mk_mul_mk -> FreeSemigroup.mk_mul_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (y : α) (L1 : List.{u1} α) (L2 : List.{u1} α), Eq.{succ u1} (FreeSemigroup.{u1} α) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) (FreeSemigroup.mk.{u1} α x L1) (FreeSemigroup.mk.{u1} α y L2)) (FreeSemigroup.mk.{u1} α x (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) L1 (List.cons.{u1} α y L2)))
but is expected to have type
  forall {α : Type.{u1}} (x : α) (y : α) (L1 : List.{u1} α) (L2 : List.{u1} α), Eq.{succ u1} (FreeSemigroup.{u1} α) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) (FreeSemigroup.mk.{u1} α x L1) (FreeSemigroup.mk.{u1} α y L2)) (FreeSemigroup.mk.{u1} α x (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) L1 (List.cons.{u1} α y L2)))
Case conversion may be inaccurate. Consider using '#align free_semigroup.mk_mul_mk FreeSemigroup.mk_mul_mkₓ'. -/
@[simp, to_additive]
theorem mk_mul_mk (x y : α) (L1 L2 : List α) : mk x L1 * mk y L2 = mk x (L1 ++ y :: L2) :=
  rfl
#align free_semigroup.mk_mul_mk FreeSemigroup.mk_mul_mk
#align free_add_semigroup.mk_add_mk FreeAddSemigroup.mk_add_mk

#print FreeSemigroup.of /-
/-- The embedding `α → free_semigroup α`. -/
@[to_additive "The embedding `α → free_add_semigroup α`.", simps]
def of (x : α) : FreeSemigroup α :=
  ⟨x, []⟩
#align free_semigroup.of FreeSemigroup.of
#align free_add_semigroup.of FreeAddSemigroup.of
-/

#print FreeSemigroup.length /-
/-- Length of an element of free semigroup. -/
@[to_additive "Length of an element of free additive semigroup"]
def length (x : FreeSemigroup α) : ℕ :=
  x.tail.length + 1
#align free_semigroup.length FreeSemigroup.length
#align free_add_semigroup.length FreeAddSemigroup.length
-/

/- warning: free_semigroup.length_mul -> FreeSemigroup.length_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{1} Nat (FreeSemigroup.length.{u1} α (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) x y)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (FreeSemigroup.length.{u1} α x) (FreeSemigroup.length.{u1} α y))
but is expected to have type
  forall {α : Type.{u1}} (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{1} Nat (FreeSemigroup.length.{u1} α (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) x y)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (FreeSemigroup.length.{u1} α x) (FreeSemigroup.length.{u1} α y))
Case conversion may be inaccurate. Consider using '#align free_semigroup.length_mul FreeSemigroup.length_mulₓ'. -/
@[simp, to_additive]
theorem length_mul (x y : FreeSemigroup α) : (x * y).length = x.length + y.length := by
  simp [length, ← add_assoc, add_right_comm]
#align free_semigroup.length_mul FreeSemigroup.length_mul
#align free_add_semigroup.length_add FreeAddSemigroup.length_add

#print FreeSemigroup.length_of /-
@[simp, to_additive]
theorem length_of (x : α) : (of x).length = 1 :=
  rfl
#align free_semigroup.length_of FreeSemigroup.length_of
#align free_add_semigroup.length_of FreeAddSemigroup.length_of
-/

@[to_additive]
instance [Inhabited α] : Inhabited (FreeSemigroup α) :=
  ⟨of default⟩

/- warning: free_semigroup.rec_on_mul -> FreeSemigroup.recOnMul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {C : (FreeSemigroup.{u1} α) -> Sort.{u2}} (x : FreeSemigroup.{u1} α), (forall (x : α), C (FreeSemigroup.of.{u1} α x)) -> (forall (x : α) (y : FreeSemigroup.{u1} α), (C (FreeSemigroup.of.{u1} α x)) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) (FreeSemigroup.of.{u1} α x) y))) -> (C x)
but is expected to have type
  forall {α : Type.{u1}} {C : (FreeSemigroup.{u1} α) -> Sort.{u2}} (x : FreeSemigroup.{u1} α), (forall (x : α), C (FreeSemigroup.of.{u1} α x)) -> (forall (x : α) (y : FreeSemigroup.{u1} α), (C (FreeSemigroup.of.{u1} α x)) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) (FreeSemigroup.of.{u1} α x) y))) -> (C x)
Case conversion may be inaccurate. Consider using '#align free_semigroup.rec_on_mul FreeSemigroup.recOnMulₓ'. -/
/-- Recursor for free semigroup using `of` and `*`. -/
@[elab_as_elim, to_additive "Recursor for free additive semigroup using `of` and `+`."]
protected def recOnMul {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (of x))
    (ih2 : ∀ x y, C (of x) → C y → C (of x * y)) : C x :=
  FreeSemigroup.recOn x fun f s =>
    List.recOn s ih1 (fun hd tl ih f => ih2 f ⟨hd, tl⟩ (ih1 f) (ih hd)) f
#align free_semigroup.rec_on_mul FreeSemigroup.recOnMul
#align free_add_semigroup.rec_on_add FreeAddSemigroup.recOnAdd

/- warning: free_semigroup.hom_ext -> FreeSemigroup.hom_ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] {f : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1} {g : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1}, (Eq.{max (succ u1) (succ u2)} (α -> β) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1) (fun (_x : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1) => (FreeSemigroup.{u1} α) -> β) (MulHom.hasCoeToFun.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1) f) (FreeSemigroup.of.{u1} α)) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1) (fun (_x : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1) => (FreeSemigroup.{u1} α) -> β) (MulHom.hasCoeToFun.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1) g) (FreeSemigroup.of.{u1} α))) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) _inst_1) f g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u2} β] {f : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1} {g : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1}, (Eq.{max (succ u1) (succ u2)} (α -> β) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1) (FreeSemigroup.{u1} α) (fun (_x : FreeSemigroup.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeSemigroup.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1) (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1 (MulHom.mulHomClass.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1)) f) (FreeSemigroup.of.{u1} α)) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1) (FreeSemigroup.{u1} α) (fun (_x : FreeSemigroup.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeSemigroup.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1) (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1 (MulHom.mulHomClass.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1)) g) (FreeSemigroup.of.{u1} α))) -> (Eq.{max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) _inst_1) f g)
Case conversion may be inaccurate. Consider using '#align free_semigroup.hom_ext FreeSemigroup.hom_extₓ'. -/
@[ext, to_additive]
theorem hom_ext {β : Type v} [Mul β] {f g : FreeSemigroup α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
  FunLike.ext _ _ fun x =>
    FreeSemigroup.recOnMul x (congr_fun h) fun x y hx hy => by simp only [map_mul, *]
#align free_semigroup.hom_ext FreeSemigroup.hom_ext
#align free_add_semigroup.hom_ext FreeAddSemigroup.hom_ext

section lift

variable {β : Type v} [Semigroup β] (f : α → β)

/- warning: free_semigroup.lift -> FreeSemigroup.lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semigroup.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semigroup.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))
Case conversion may be inaccurate. Consider using '#align free_semigroup.lift FreeSemigroup.liftₓ'. -/
/-- Lifts a function `α → β` to a semigroup homomorphism `free_semigroup α → β` given
a semigroup `β`. -/
@[to_additive
      "Lifts a function `α → β` to an additive semigroup homomorphism\n`free_add_semigroup α → β` given an additive semigroup `β`.",
  simps symm_apply]
def lift : (α → β) ≃ (FreeSemigroup α →ₙ* β)
    where
  toFun f :=
    { toFun := fun x => x.2.foldl (fun a b => a * f b) (f x.1)
      map_mul' := fun x y => by
        simp only [head_mul, tail_mul, ← List.foldl_map f, List.foldl_append, List.foldl_cons,
          List.foldl_assoc] }
  invFun f := f ∘ of
  left_inv f := rfl
  right_inv f := hom_ext rfl
#align free_semigroup.lift FreeSemigroup.lift
#align free_add_semigroup.lift FreeAddSemigroup.lift

/- warning: free_semigroup.lift_of -> FreeSemigroup.lift_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semigroup.{u2} β] (f : α -> β) (x : α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) (fun (_x : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) => (FreeSemigroup.{u1} α) -> β) (MulHom.hasCoeToFun.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) => (α -> β) -> (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (FreeSemigroup.lift.{u1, u2} α β _inst_1) f) (FreeSemigroup.of.{u1} α x)) (f x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semigroup.{u2} β] (f : α -> β) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeSemigroup.{u1} α) => β) (FreeSemigroup.of.{u1} α x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) f) (FreeSemigroup.{u1} α) (fun (_x : FreeSemigroup.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeSemigroup.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) f) (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1) (MulHom.mulHomClass.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (fun (_x : α -> β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))))) (FreeSemigroup.lift.{u1, u2} α β _inst_1) f) (FreeSemigroup.of.{u1} α x)) (f x)
Case conversion may be inaccurate. Consider using '#align free_semigroup.lift_of FreeSemigroup.lift_ofₓ'. -/
@[simp, to_additive]
theorem lift_of (x : α) : lift f (of x) = f x :=
  rfl
#align free_semigroup.lift_of FreeSemigroup.lift_of
#align free_add_semigroup.lift_of FreeAddSemigroup.lift_of

/- warning: free_semigroup.lift_comp_of -> FreeSemigroup.lift_comp_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semigroup.{u2} β] (f : α -> β), Eq.{max (succ u1) (succ u2)} (α -> β) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) (fun (_x : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) => (FreeSemigroup.{u1} α) -> β) (MulHom.hasCoeToFun.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) => (α -> β) -> (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (FreeSemigroup.lift.{u1, u2} α β _inst_1) f)) (FreeSemigroup.of.{u1} α)) f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semigroup.{u2} β] (f : α -> β), Eq.{max (succ u1) (succ u2)} (α -> β) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) f) (FreeSemigroup.{u1} α) (fun (_x : FreeSemigroup.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeSemigroup.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) f) (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1) (MulHom.mulHomClass.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (fun (_x : α -> β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))))) (FreeSemigroup.lift.{u1, u2} α β _inst_1) f)) (FreeSemigroup.of.{u1} α)) f
Case conversion may be inaccurate. Consider using '#align free_semigroup.lift_comp_of FreeSemigroup.lift_comp_ofₓ'. -/
@[simp, to_additive]
theorem lift_comp_of : lift f ∘ of = f :=
  rfl
#align free_semigroup.lift_comp_of FreeSemigroup.lift_comp_of
#align free_add_semigroup.lift_comp_of FreeAddSemigroup.lift_comp_of

/- warning: free_semigroup.lift_comp_of' -> FreeSemigroup.lift_comp_of' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semigroup.{u2} β] (f : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)), Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) => (α -> β) -> (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1))) (FreeSemigroup.lift.{u1, u2} α β _inst_1) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) (fun (_x : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) => (FreeSemigroup.{u1} α) -> β) (MulHom.hasCoeToFun.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} β _inst_1)) f) (FreeSemigroup.of.{u1} α))) f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semigroup.{u2} β] (f : MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (FreeSemigroup.{u1} α) (fun (a : FreeSemigroup.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeSemigroup.{u1} α) => β) a) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1) (MulHom.mulHomClass.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) f) (FreeSemigroup.of.{u1} α))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (fun (_x : α -> β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α -> β) => MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> β) (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))))) (FreeSemigroup.lift.{u1, u2} α β _inst_1) (Function.comp.{succ u1, succ u1, succ u2} α (FreeSemigroup.{u1} α) β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (FreeSemigroup.{u1} α) (fun (_x : FreeSemigroup.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : FreeSemigroup.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1)) (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1) (MulHom.mulHomClass.{u1, u2} (FreeSemigroup.{u1} α) β (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} β _inst_1))) f) (FreeSemigroup.of.{u1} α))) f
Case conversion may be inaccurate. Consider using '#align free_semigroup.lift_comp_of' FreeSemigroup.lift_comp_of'ₓ'. -/
@[simp, to_additive]
theorem lift_comp_of' (f : FreeSemigroup α →ₙ* β) : lift (f ∘ of) = f :=
  hom_ext rfl
#align free_semigroup.lift_comp_of' FreeSemigroup.lift_comp_of'
#align free_add_semigroup.lift_comp_of' FreeAddSemigroup.lift_comp_of'

#print FreeSemigroup.lift_of_mul /-
@[to_additive]
theorem lift_of_mul (x y) : lift f (of x * y) = f x * lift f y := by rw [map_mul, lift_of]
#align free_semigroup.lift_of_mul FreeSemigroup.lift_of_mul
#align free_add_semigroup.lift_of_add FreeAddSemigroup.lift_of_add
-/

end lift

section Map

variable {β : Type v} (f : α → β)

/- warning: free_semigroup.map -> FreeSemigroup.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (MulHom.{u1, u2} (FreeSemigroup.{u1} α) (FreeSemigroup.{u2} β) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} (FreeSemigroup.{u2} β) (FreeSemigroup.semigroup.{u2} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (MulHom.{u1, u2} (FreeSemigroup.{u1} α) (FreeSemigroup.{u2} β) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} (FreeSemigroup.{u2} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u2} β)))
Case conversion may be inaccurate. Consider using '#align free_semigroup.map FreeSemigroup.mapₓ'. -/
/-- The unique semigroup homomorphism that sends `of x` to `of (f x)`. -/
@[to_additive "The unique additive semigroup homomorphism that sends `of x` to `of (f x)`."]
def map : FreeSemigroup α →ₙ* FreeSemigroup β :=
  lift <| of ∘ f
#align free_semigroup.map FreeSemigroup.map
#align free_add_semigroup.map FreeAddSemigroup.map

#print FreeSemigroup.map_of /-
@[simp, to_additive]
theorem map_of (x) : map f (of x) = of (f x) :=
  rfl
#align free_semigroup.map_of FreeSemigroup.map_of
#align free_add_semigroup.map_of FreeAddSemigroup.map_of
-/

#print FreeSemigroup.length_map /-
@[simp, to_additive]
theorem length_map (x) : (map f x).length = x.length :=
  FreeSemigroup.recOnMul x (fun x => rfl) fun x y hx hy => by simp only [map_mul, length_mul, *]
#align free_semigroup.length_map FreeSemigroup.length_map
#align free_add_semigroup.length_map FreeAddSemigroup.length_map
-/

end Map

section Category

variable {β : Type u}

@[to_additive]
instance : Monad FreeSemigroup where
  pure _ := of
  bind _ _ x f := lift f x

/- warning: free_semigroup.rec_on_pure -> FreeSemigroup.recOnPure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {C : (FreeSemigroup.{u1} α) -> Sort.{u2}} (x : FreeSemigroup.{u1} α), (forall (x : α), C (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α x)) -> (forall (x : α) (y : FreeSemigroup.{u1} α), (C (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α x)) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α x) y))) -> (C x)
but is expected to have type
  forall {α : Type.{u1}} {C : (FreeSemigroup.{u1} α) -> Sort.{u2}} (x : FreeSemigroup.{u1} α), (forall (x : α), C (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α x)) -> (forall (x : α) (y : FreeSemigroup.{u1} α), (C (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α x)) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α x) y))) -> (C x)
Case conversion may be inaccurate. Consider using '#align free_semigroup.rec_on_pure FreeSemigroup.recOnPureₓ'. -/
/-- Recursor that uses `pure` instead of `of`. -/
@[elab_as_elim, to_additive "Recursor that uses `pure` instead of `of`."]
def recOnPure {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (pure x))
    (ih2 : ∀ x y, C (pure x) → C y → C (pure x * y)) : C x :=
  FreeSemigroup.recOnMul x ih1 ih2
#align free_semigroup.rec_on_pure FreeSemigroup.recOnPure
#align free_add_semigroup.rec_on_pure FreeAddSemigroup.recOnPure

/- warning: free_semigroup.map_pure -> FreeSemigroup.map_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : α), Eq.{succ u1} (FreeSemigroup.{u1} β) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α β f (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α x)) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) β (f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : α), Eq.{succ u1} (FreeSemigroup.{u1} β) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β f (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α x)) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) β (f x))
Case conversion may be inaccurate. Consider using '#align free_semigroup.map_pure FreeSemigroup.map_pureₓ'. -/
@[simp, to_additive]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeSemigroup β) = pure (f x) :=
  rfl
#align free_semigroup.map_pure FreeSemigroup.map_pure
#align free_add_semigroup.map_pure FreeAddSemigroup.map_pure

/- warning: free_semigroup.map_mul' -> FreeSemigroup.map_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (FreeSemigroup.{u1} β) (Functor.map.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) (Applicative.toFunctor.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) (Monad.toApplicative.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) FreeSemigroup.monad.{u1})) α β f (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) x y)) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.semigroup.{u1} β))) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α β f x) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α β f y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (FreeSemigroup.{u1} β) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β f (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) x y)) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} β))) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β f x) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β f y))
Case conversion may be inaccurate. Consider using '#align free_semigroup.map_mul' FreeSemigroup.map_mul'ₓ'. -/
@[simp, to_additive]
theorem map_mul' (f : α → β) (x y : FreeSemigroup α) : f <$> (x * y) = f <$> x * f <$> y :=
  map_mul (map f) _ _
#align free_semigroup.map_mul' FreeSemigroup.map_mul'
#align free_add_semigroup.map_add' FreeAddSemigroup.map_add'

/- warning: free_semigroup.pure_bind -> FreeSemigroup.pure_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (FreeSemigroup.{u1} β)) (x : α), Eq.{succ u1} (FreeSemigroup.{u1} β) (Bind.bind.{u1, u1} FreeSemigroup.{u1} (Monad.toHasBind.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1}) α β (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α x) f) (f x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (FreeSemigroup.{u1} β)) (x : α), Eq.{succ u1} (FreeSemigroup.{u1} β) (Bind.bind.{u1, u1} FreeSemigroup.{u1} (Monad.toBind.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1}) α β (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α x) f) (f x)
Case conversion may be inaccurate. Consider using '#align free_semigroup.pure_bind FreeSemigroup.pure_bindₓ'. -/
@[simp, to_additive]
theorem pure_bind (f : α → FreeSemigroup β) (x) : pure x >>= f = f x :=
  rfl
#align free_semigroup.pure_bind FreeSemigroup.pure_bind
#align free_add_semigroup.pure_bind FreeAddSemigroup.pure_bind

/- warning: free_semigroup.mul_bind -> FreeSemigroup.mul_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (FreeSemigroup.{u1} β)) (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (FreeSemigroup.{u1} β) (Bind.bind.{u1, u1} FreeSemigroup.{u1} (Monad.toHasBind.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1}) α β (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) x y) f) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.semigroup.{u1} β))) (Bind.bind.{u1, u1} FreeSemigroup.{u1} (Monad.toHasBind.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1}) α β x f) (Bind.bind.{u1, u1} FreeSemigroup.{u1} (Monad.toHasBind.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1}) α β y f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (FreeSemigroup.{u1} β)) (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (FreeSemigroup.{u1} β) (Bind.bind.{u1, u1} FreeSemigroup.{u1} (Monad.toBind.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1}) α β (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) x y) f) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} β))) (Bind.bind.{u1, u1} FreeSemigroup.{u1} (Monad.toBind.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1}) α β x f) (Bind.bind.{u1, u1} FreeSemigroup.{u1} (Monad.toBind.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1}) α β y f))
Case conversion may be inaccurate. Consider using '#align free_semigroup.mul_bind FreeSemigroup.mul_bindₓ'. -/
@[simp, to_additive]
theorem mul_bind (f : α → FreeSemigroup β) (x y : FreeSemigroup α) :
    x * y >>= f = (x >>= f) * (y >>= f) :=
  map_mul (lift f) _ _
#align free_semigroup.mul_bind FreeSemigroup.mul_bind
#align free_add_semigroup.add_bind FreeAddSemigroup.add_bind

/- warning: free_semigroup.pure_seq -> FreeSemigroup.pure_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> β} {x : FreeSemigroup.{u1} α}, Eq.{succ u1} (FreeSemigroup.{u1} β) (Seq.seq.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) (Applicative.toHasSeq.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) (Monad.toApplicative.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) FreeSemigroup.monad.{u1})) α β (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) (Applicative.toHasPure.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) (Monad.toApplicative.{u1, u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) FreeSemigroup.monad.{u1})) (α -> β) f) x) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α β f x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {f : α -> β} {x : FreeSemigroup.{u1} α}, Eq.{succ u1} (FreeSemigroup.{u1} β) (Seq.seq.{u1, u1} FreeSemigroup.{u1} (Applicative.toSeq.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) (α -> β) f) (fun (x._@.Mathlib.Algebra.Free._hyg.5485 : Unit) => x)) (Functor.map.{u1, u1} FreeSemigroup.{u1} (Applicative.toFunctor.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β f x)
Case conversion may be inaccurate. Consider using '#align free_semigroup.pure_seq FreeSemigroup.pure_seqₓ'. -/
@[simp, to_additive]
theorem pure_seq {f : α → β} {x : FreeSemigroup α} : pure f <*> x = f <$> x :=
  rfl
#align free_semigroup.pure_seq FreeSemigroup.pure_seq
#align free_add_semigroup.pure_seq FreeAddSemigroup.pure_seq

/- warning: free_semigroup.mul_seq -> FreeSemigroup.mul_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {f : FreeSemigroup.{u1} (α -> β)} {g : FreeSemigroup.{u1} (α -> β)} {x : FreeSemigroup.{u1} α}, Eq.{succ u1} (FreeSemigroup.{u1} β) (Seq.seq.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasSeq.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α β (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} (α -> β)) (FreeSemigroup.{u1} (α -> β)) (FreeSemigroup.{u1} (α -> β)) (instHMul.{u1} (FreeSemigroup.{u1} (α -> β)) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} (α -> β)) (FreeSemigroup.semigroup.{u1} (α -> β)))) f g) x) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.semigroup.{u1} β))) (Seq.seq.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasSeq.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α β f x) (Seq.seq.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasSeq.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α β g x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {f : FreeSemigroup.{u1} (α -> β)} {g : FreeSemigroup.{u1} (α -> β)} {x : FreeSemigroup.{u1} α}, Eq.{succ u1} (FreeSemigroup.{u1} β) (Seq.seq.{u1, u1} FreeSemigroup.{u1} (Applicative.toSeq.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} (α -> β)) (FreeSemigroup.{u1} (α -> β)) (FreeSemigroup.{u1} (α -> β)) (instHMul.{u1} (FreeSemigroup.{u1} (α -> β)) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} (α -> β)) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} (α -> β)))) f g) (fun (x._@.Mathlib.Algebra.Free._hyg.5525 : Unit) => x)) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} β))) (Seq.seq.{u1, u1} FreeSemigroup.{u1} (Applicative.toSeq.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β f (fun (x._@.Mathlib.Algebra.Free._hyg.5536 : Unit) => x)) (Seq.seq.{u1, u1} FreeSemigroup.{u1} (Applicative.toSeq.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α β g (fun (x._@.Mathlib.Algebra.Free._hyg.5546 : Unit) => x)))
Case conversion may be inaccurate. Consider using '#align free_semigroup.mul_seq FreeSemigroup.mul_seqₓ'. -/
@[simp, to_additive]
theorem mul_seq {f g : FreeSemigroup (α → β)} {x : FreeSemigroup α} :
    f * g <*> x = (f <*> x) * (g <*> x) :=
  mul_bind _ _ _
#align free_semigroup.mul_seq FreeSemigroup.mul_seq
#align free_add_semigroup.add_seq FreeAddSemigroup.add_seq

@[to_additive]
instance : LawfulMonad FreeSemigroup.{u}
    where
  pure_bind _ _ _ _ := rfl
  bind_assoc α β γ x f g :=
    recOnPure x (fun x => rfl) fun x y ih1 ih2 => by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]
  id_map α x := recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by rw [map_mul', ih1, ih2]

#print FreeSemigroup.traverse /-
/-- `free_semigroup` is traversable. -/
@[to_additive "`free_add_semigroup` is traversable."]
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (F : α → m β)
    (x : FreeSemigroup α) : m (FreeSemigroup β) :=
  recOnPure x (fun x => pure <$> F x) fun x y ihx ihy => (· * ·) <$> ihx <*> ihy
#align free_semigroup.traverse FreeSemigroup.traverse
#align free_add_semigroup.traverse FreeAddSemigroup.traverse
-/

@[to_additive]
instance : Traversable FreeSemigroup :=
  ⟨@FreeSemigroup.traverse⟩

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

/- warning: free_semigroup.traverse_pure -> FreeSemigroup.traverse_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) (x : α), Eq.{succ u1} (m (FreeSemigroup.{u1} β)) (Traversable.traverse.{u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) FreeSemigroup.traversable.{u1} m _inst_1 α β F (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) α x)) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) β (FreeSemigroup.{u1} β) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) β) (F x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) (x : α), Eq.{succ u1} (m (FreeSemigroup.{u1} β)) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.instTraversableFreeSemigroup.{u1} m _inst_1 α β F (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α x)) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) β (FreeSemigroup.{u1} β) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) β) (F x))
Case conversion may be inaccurate. Consider using '#align free_semigroup.traverse_pure FreeSemigroup.traverse_pureₓ'. -/
@[simp, to_additive]
theorem traverse_pure (x) : traverse F (pure x : FreeSemigroup α) = pure <$> F x :=
  rfl
#align free_semigroup.traverse_pure FreeSemigroup.traverse_pure
#align free_add_semigroup.traverse_pure FreeAddSemigroup.traverse_pure

/- warning: free_semigroup.traverse_pure' -> FreeSemigroup.traverse_pure' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)), Eq.{succ u1} (α -> (m (FreeSemigroup.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} α (FreeSemigroup.{u1} α) (m (FreeSemigroup.{u1} β)) (Traversable.traverse.{u1} (fun {β : Type.{u1}} => FreeSemigroup.{u1} β) FreeSemigroup.traversable.{u1} m _inst_1 α β F) (Pure.pure.{u1, u1} (fun {β : Type.{u1}} => FreeSemigroup.{u1} β) (Applicative.toHasPure.{u1, u1} (fun {β : Type.{u1}} => FreeSemigroup.{u1} β) (Monad.toApplicative.{u1, u1} (fun {β : Type.{u1}} => FreeSemigroup.{u1} β) FreeSemigroup.monad.{u1})) α)) (fun (x : α) => Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) β (FreeSemigroup.{u1} β) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toHasPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.monad.{u1})) β) (F x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)), Eq.{succ u1} (α -> (m (FreeSemigroup.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} α (FreeSemigroup.{u1} α) (m (FreeSemigroup.{u1} β)) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.instTraversableFreeSemigroup.{u1} m _inst_1 α β F) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) α)) (fun (x : α) => Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) β (FreeSemigroup.{u1} β) (Pure.pure.{u1, u1} FreeSemigroup.{u1} (Applicative.toPure.{u1, u1} FreeSemigroup.{u1} (Monad.toApplicative.{u1, u1} FreeSemigroup.{u1} FreeSemigroup.instMonadFreeSemigroup.{u1})) β) (F x))
Case conversion may be inaccurate. Consider using '#align free_semigroup.traverse_pure' FreeSemigroup.traverse_pure'ₓ'. -/
@[simp, to_additive]
theorem traverse_pure' : traverse F ∘ pure = fun x => (pure <$> F x : m (FreeSemigroup β)) :=
  rfl
#align free_semigroup.traverse_pure' FreeSemigroup.traverse_pure'
#align free_add_semigroup.traverse_pure' FreeAddSemigroup.traverse_pure'

section

variable [LawfulApplicative m]

/- warning: free_semigroup.traverse_mul -> FreeSemigroup.traverse_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) [_inst_2 : LawfulApplicative.{u1, u1} m _inst_1] (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (m (FreeSemigroup.{u1} β)) (Traversable.traverse.{u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) FreeSemigroup.traversable.{u1} m _inst_1 α β F (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) x y)) (Seq.seq.{u1, u1} m (Applicative.toHasSeq.{u1, u1} m _inst_1) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) (FreeSemigroup.{u1} β) ((FreeSemigroup.{u1} β) -> (FreeSemigroup.{u1} β)) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.semigroup.{u1} β)))) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.traversable.{u1} m _inst_1 α β F x)) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.traversable.{u1} m _inst_1 α β F y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) [_inst_2 : LawfulApplicative.{u1, u1} m _inst_1] (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (m (FreeSemigroup.{u1} β)) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.instTraversableFreeSemigroup.{u1} m _inst_1 α β F (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) x y)) (Seq.seq.{u1, u1} m (Applicative.toSeq.{u1, u1} m _inst_1) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) (FreeSemigroup.{u1} β) ((FreeSemigroup.{u1} β) -> (FreeSemigroup.{u1} β)) (fun (x._@.Mathlib.Algebra.Free._hyg.5973 : FreeSemigroup.{u1} β) (x._@.Mathlib.Algebra.Free._hyg.5975 : FreeSemigroup.{u1} β) => HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} β))) x._@.Mathlib.Algebra.Free._hyg.5973 x._@.Mathlib.Algebra.Free._hyg.5975) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.instTraversableFreeSemigroup.{u1} m _inst_1 α β F x)) (fun (x._@.Mathlib.Algebra.Free._hyg.5992 : Unit) => Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.instTraversableFreeSemigroup.{u1} m _inst_1 α β F y))
Case conversion may be inaccurate. Consider using '#align free_semigroup.traverse_mul FreeSemigroup.traverse_mulₓ'. -/
@[simp, to_additive]
theorem traverse_mul (x y : FreeSemigroup α) :
    traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y :=
  let ⟨x, L1⟩ := x
  let ⟨y, L2⟩ := y
  List.recOn L1 (fun x => rfl)
    (fun hd tl ih x =>
      show
        (· * ·) <$> pure <$> F x <*> traverse F (mk hd tl * mk y L2) =
          (· * ·) <$> ((· * ·) <$> pure <$> F x <*> traverse F (mk hd tl)) <*> traverse F (mk y L2)
        by rw [ih] <;> simp only [(· ∘ ·), (mul_assoc _ _ _).symm, functor_norm])
    x
#align free_semigroup.traverse_mul FreeSemigroup.traverse_mul
#align free_add_semigroup.traverse_add FreeAddSemigroup.traverse_add

/- warning: free_semigroup.traverse_mul' -> FreeSemigroup.traverse_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) [_inst_2 : LawfulApplicative.{u1, u1} m _inst_1], Eq.{succ u1} ((FreeSemigroup.{u1} α) -> (FreeSemigroup.{u1} α) -> (m (FreeSemigroup.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} (FreeSemigroup.{u1} α) ((FreeSemigroup.{u1} α) -> (FreeSemigroup.{u1} α)) ((FreeSemigroup.{u1} α) -> (m (FreeSemigroup.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (m (FreeSemigroup.{u1} β)) (Traversable.traverse.{u1} (fun {α : Type.{u1}} => FreeSemigroup.{u1} α) FreeSemigroup.traversable.{u1} m _inst_1 α β F)) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))))) (fun (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α) => Seq.seq.{u1, u1} m (Applicative.toHasSeq.{u1, u1} m _inst_1) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) (FreeSemigroup.{u1} β) ((FreeSemigroup.{u1} β) -> (FreeSemigroup.{u1} β)) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.semigroup.{u1} β)))) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.traversable.{u1} m _inst_1 α β F x)) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.traversable.{u1} m _inst_1 α β F y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {m : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} m] (F : α -> (m β)) [_inst_2 : LawfulApplicative.{u1, u1} m _inst_1], Eq.{succ u1} ((FreeSemigroup.{u1} α) -> (FreeSemigroup.{u1} α) -> (m (FreeSemigroup.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} (FreeSemigroup.{u1} α) ((FreeSemigroup.{u1} α) -> (FreeSemigroup.{u1} α)) ((FreeSemigroup.{u1} α) -> (m (FreeSemigroup.{u1} β))) (Function.comp.{succ u1, succ u1, succ u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (m (FreeSemigroup.{u1} β)) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.instTraversableFreeSemigroup.{u1} m _inst_1 α β F)) (Mul.mul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)))) (fun (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α) => Seq.seq.{u1, u1} m (Applicative.toSeq.{u1, u1} m _inst_1) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (Functor.map.{u1, u1} m (Applicative.toFunctor.{u1, u1} m _inst_1) (FreeSemigroup.{u1} β) ((FreeSemigroup.{u1} β) -> (FreeSemigroup.{u1} β)) (fun (x._@.Mathlib.Algebra.Free._hyg.6268 : FreeSemigroup.{u1} β) (x._@.Mathlib.Algebra.Free._hyg.6270 : FreeSemigroup.{u1} β) => HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (FreeSemigroup.{u1} β) (instHMul.{u1} (FreeSemigroup.{u1} β) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} β))) x._@.Mathlib.Algebra.Free._hyg.6268 x._@.Mathlib.Algebra.Free._hyg.6270) (Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.instTraversableFreeSemigroup.{u1} m _inst_1 α β F x)) (fun (x._@.Mathlib.Algebra.Free._hyg.6287 : Unit) => Traversable.traverse.{u1} FreeSemigroup.{u1} FreeSemigroup.instTraversableFreeSemigroup.{u1} m _inst_1 α β F y))
Case conversion may be inaccurate. Consider using '#align free_semigroup.traverse_mul' FreeSemigroup.traverse_mul'ₓ'. -/
@[simp, to_additive]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ @Mul.mul (FreeSemigroup α) _ = fun x y =>
      (· * ·) <$> traverse F x <*> traverse F y :=
  funext fun x => funext fun y => traverse_mul F x y
#align free_semigroup.traverse_mul' FreeSemigroup.traverse_mul'
#align free_add_semigroup.traverse_add' FreeAddSemigroup.traverse_add'

end

#print FreeSemigroup.traverse_eq /-
@[simp, to_additive]
theorem traverse_eq (x) : FreeSemigroup.traverse F x = traverse F x :=
  rfl
#align free_semigroup.traverse_eq FreeSemigroup.traverse_eq
#align free_add_semigroup.traverse_eq FreeAddSemigroup.traverse_eq
-/

/- warning: free_semigroup.mul_map_seq -> FreeSemigroup.mul_map_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (FreeSemigroup.{u1} α)) (Seq.seq.{u1, u1} (id.{succ (succ u1)} Type.{u1}) (Applicative.toHasSeq.{u1, u1} (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1})) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (Functor.map.{u1, u1} (id.{succ (succ u1)} Type.{u1}) (Traversable.toFunctor.{u1} (id.{succ (succ u1)} Type.{u1}) id.traversable.{u1}) (FreeSemigroup.{u1} α) ((FreeSemigroup.{u1} α) -> (FreeSemigroup.{u1} α)) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)))) x) y) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))) x y)
but is expected to have type
  forall {α : Type.{u1}} (x : FreeSemigroup.{u1} α) (y : FreeSemigroup.{u1} α), Eq.{succ u1} (Id.{u1} (FreeSemigroup.{u1} α)) (Seq.seq.{u1, u1} Id.{u1} (Applicative.toSeq.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (Functor.map.{u1, u1} Id.{u1} (Traversable.toFunctor.{u1} Id.{u1} instTraversableId.{u1}) (FreeSemigroup.{u1} α) ((FreeSemigroup.{u1} α) -> (FreeSemigroup.{u1} α)) (fun (x._@.Mathlib.Algebra.Free._hyg.6368 : FreeSemigroup.{u1} α) (x._@.Mathlib.Algebra.Free._hyg.6370 : FreeSemigroup.{u1} α) => HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) x._@.Mathlib.Algebra.Free._hyg.6368 x._@.Mathlib.Algebra.Free._hyg.6370) x) (fun (x._@.Mathlib.Algebra.Free._hyg.6385 : Unit) => y)) (HMul.hMul.{u1, u1, u1} (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u1} α) (instHMul.{u1} (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))) x y)
Case conversion may be inaccurate. Consider using '#align free_semigroup.mul_map_seq FreeSemigroup.mul_map_seqₓ'. -/
@[simp, to_additive]
theorem mul_map_seq (x y : FreeSemigroup α) :
    ((· * ·) <$> x <*> y : id (FreeSemigroup α)) = (x * y : FreeSemigroup α) :=
  rfl
#align free_semigroup.mul_map_seq FreeSemigroup.mul_map_seq
#align free_add_semigroup.add_map_seq FreeAddSemigroup.add_map_seq

@[to_additive]
instance : IsLawfulTraversable FreeSemigroup.{u} :=
  {
    FreeSemigroup.lawfulMonad with
    id_traverse := fun α x =>
      FreeSemigroup.recOnMul x (fun x => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, mul_map_seq]
    comp_traverse := fun F G hf1 hg1 hf2 hg2 α β γ f g x =>
      recOnPure x (fun x => by skip <;> simp only [traverse_pure, traverse_pure', functor_norm])
        fun x y ih1 ih2 => by
        skip <;> rw [traverse_mul, ih1, ih2, traverse_mul] <;>
          simp only [traverse_mul', functor_norm]
    naturality := fun F G hf1 hg1 hf2 hg2 η α β f x =>
      recOnPure x (fun x => by simp only [traverse_pure, functor_norm]) fun x y ih1 ih2 => by
        skip <;> simp only [traverse_mul, functor_norm] <;> rw [ih1, ih2]
    traverse_eq_map_id := fun α β f x =>
      FreeSemigroup.recOnMul x (fun _ => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq] <;> rfl }

end Category

@[to_additive]
instance [DecidableEq α] : DecidableEq (FreeSemigroup α) := fun x y =>
  decidable_of_iff' _ (ext_iff _ _)

end FreeSemigroup

namespace FreeMagma

variable {α : Type u} {β : Type v}

/- warning: free_magma.to_free_semigroup -> FreeMagma.toFreeSemigroup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, MulHom.{u1, u1} (FreeMagma.{u1} α) (FreeSemigroup.{u1} α) (FreeMagma.hasMul.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, MulHom.{u1, u1} (FreeMagma.{u1} α) (FreeSemigroup.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))
Case conversion may be inaccurate. Consider using '#align free_magma.to_free_semigroup FreeMagma.toFreeSemigroupₓ'. -/
/-- The canonical multiplicative morphism from `free_magma α` to `free_semigroup α`. -/
@[to_additive "The canonical additive morphism from `free_add_magma α` to `free_add_semigroup α`."]
def toFreeSemigroup : FreeMagma α →ₙ* FreeSemigroup α :=
  FreeMagma.lift FreeSemigroup.of
#align free_magma.to_free_semigroup FreeMagma.toFreeSemigroup
#align free_add_magma.to_free_add_semigroup FreeAddMagma.toFreeAddSemigroup

#print FreeMagma.toFreeSemigroup_of /-
@[simp, to_additive]
theorem toFreeSemigroup_of (x : α) : toFreeSemigroup (of x) = FreeSemigroup.of x :=
  rfl
#align free_magma.to_free_semigroup_of FreeMagma.toFreeSemigroup_of
-/

#print FreeMagma.toFreeSemigroup_comp_of /-
@[simp, to_additive]
theorem toFreeSemigroup_comp_of : @toFreeSemigroup α ∘ of = FreeSemigroup.of :=
  rfl
#align free_magma.to_free_semigroup_comp_of FreeMagma.toFreeSemigroup_comp_of
-/

/- warning: free_magma.to_free_semigroup_comp_map -> FreeMagma.toFreeSemigroup_comp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} (FreeMagma.{u1} α) (FreeSemigroup.{u2} β) (FreeMagma.hasMul.{u1} α) (Semigroup.toHasMul.{u2} (FreeSemigroup.{u2} β) (FreeSemigroup.semigroup.{u2} β))) (MulHom.comp.{u1, u2, u2} (FreeMagma.{u1} α) (FreeMagma.{u2} β) (FreeSemigroup.{u2} β) (FreeMagma.hasMul.{u1} α) (FreeMagma.hasMul.{u2} β) (Semigroup.toHasMul.{u2} (FreeSemigroup.{u2} β) (FreeSemigroup.semigroup.{u2} β)) (FreeMagma.toFreeSemigroup.{u2} β) (FreeMagma.map.{u1, u2} α β f)) (MulHom.comp.{u1, u1, u2} (FreeMagma.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u2} β) (FreeMagma.hasMul.{u1} α) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α)) (Semigroup.toHasMul.{u2} (FreeSemigroup.{u2} β) (FreeSemigroup.semigroup.{u2} β)) (FreeSemigroup.map.{u1, u2} α β f) (FreeMagma.toFreeSemigroup.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{max (succ u1) (succ u2)} (MulHom.{u1, u2} (FreeMagma.{u1} α) (FreeSemigroup.{u2} β) (FreeMagma.instMulFreeMagma.{u1} α) (Semigroup.toMul.{u2} (FreeSemigroup.{u2} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u2} β))) (MulHom.comp.{u1, u2, u2} (FreeMagma.{u1} α) (FreeMagma.{u2} β) (FreeSemigroup.{u2} β) (FreeMagma.instMulFreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u2} β) (Semigroup.toMul.{u2} (FreeSemigroup.{u2} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u2} β)) (FreeMagma.toFreeSemigroup.{u2} β) (FreeMagma.map.{u1, u2} α β f)) (MulHom.comp.{u1, u1, u2} (FreeMagma.{u1} α) (FreeSemigroup.{u1} α) (FreeSemigroup.{u2} β) (FreeMagma.instMulFreeMagma.{u1} α) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α)) (Semigroup.toMul.{u2} (FreeSemigroup.{u2} β) (FreeSemigroup.instSemigroupFreeSemigroup.{u2} β)) (FreeSemigroup.map.{u1, u2} α β f) (FreeMagma.toFreeSemigroup.{u1} α))
Case conversion may be inaccurate. Consider using '#align free_magma.to_free_semigroup_comp_map FreeMagma.toFreeSemigroup_comp_mapₓ'. -/
@[to_additive]
theorem toFreeSemigroup_comp_map (f : α → β) :
    toFreeSemigroup.comp (map f) = (FreeSemigroup.map f).comp toFreeSemigroup :=
  by
  ext1
  rfl
#align free_magma.to_free_semigroup_comp_map FreeMagma.toFreeSemigroup_comp_map

#print FreeMagma.toFreeSemigroup_map /-
@[to_additive]
theorem toFreeSemigroup_map (f : α → β) (x : FreeMagma α) :
    (map f x).toFreeSemigroup = FreeSemigroup.map f x.toFreeSemigroup :=
  FunLike.congr_fun (toFreeSemigroup_comp_map f) x
#align free_magma.to_free_semigroup_map FreeMagma.toFreeSemigroup_map
-/

#print FreeMagma.length_toFreeSemigroup /-
@[simp, to_additive]
theorem length_toFreeSemigroup (x : FreeMagma α) : x.toFreeSemigroup.length = x.length :=
  FreeMagma.recOnMul x (fun x => rfl) fun x y hx hy => by
    rw [map_mul, FreeSemigroup.length_mul, length, hx, hy]
#align free_magma.length_to_free_semigroup FreeMagma.length_toFreeSemigroup
-/

end FreeMagma

/- warning: free_magma_assoc_quotient_equiv -> FreeMagmaAssocQuotientEquiv is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), MulEquiv.{u1, u1} (Magma.AssocQuotient.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α)) (FreeSemigroup.{u1} α) (Semigroup.toHasMul.{u1} (Magma.AssocQuotient.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α)) (Magma.AssocQuotient.semigroup.{u1} (FreeMagma.{u1} α) (FreeMagma.hasMul.{u1} α))) (Semigroup.toHasMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.semigroup.{u1} α))
but is expected to have type
  forall (α : Type.{u1}), MulEquiv.{u1, u1} (Magma.AssocQuotient.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α)) (FreeSemigroup.{u1} α) (Semigroup.toMul.{u1} (Magma.AssocQuotient.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α)) (Magma.AssocQuotient.instSemigroupAssocQuotient.{u1} (FreeMagma.{u1} α) (FreeMagma.instMulFreeMagma.{u1} α))) (Semigroup.toMul.{u1} (FreeSemigroup.{u1} α) (FreeSemigroup.instSemigroupFreeSemigroup.{u1} α))
Case conversion may be inaccurate. Consider using '#align free_magma_assoc_quotient_equiv FreeMagmaAssocQuotientEquivₓ'. -/
/-- Isomorphism between `magma.assoc_quotient (free_magma α)` and `free_semigroup α`. -/
@[to_additive
      "Isomorphism between\n`add_magma.assoc_quotient (free_add_magma α)` and `free_add_semigroup α`."]
def FreeMagmaAssocQuotientEquiv (α : Type u) :
    Magma.AssocQuotient (FreeMagma α) ≃* FreeSemigroup α :=
  (Magma.AssocQuotient.lift FreeMagma.toFreeSemigroup).toMulEquiv
    (FreeSemigroup.lift (Magma.AssocQuotient.of ∘ FreeMagma.of))
    (by
      ext
      rfl)
    (by
      ext1
      rfl)
#align free_magma_assoc_quotient_equiv FreeMagmaAssocQuotientEquiv

