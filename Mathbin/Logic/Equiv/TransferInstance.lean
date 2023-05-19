/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module logic.equiv.transfer_instance
! leanprover-community/mathlib commit 86d1873c01a723aba6788f0b9051ae3d23b4c1c3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Equiv
import Mathbin.Algebra.Field.Basic
import Mathbin.Logic.Equiv.Defs

/-!
# Transfer algebraic structures across `equiv`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

### Implementation details

When adding new definitions that transfer type-classes across an equivalence, please mark them
`@[reducible]`. See note [reducible non-instances].

## Tags

equiv, group, ring, field, module, algebra
-/


universe u v

variable {α : Type u} {β : Type v}

namespace Equiv

section Instances

variable (e : α ≃ β)

#print Equiv.One /-
/-- Transfer `has_one` across an `equiv` -/
@[reducible, to_additive "Transfer `has_zero` across an `equiv`"]
protected def One [One β] : One α :=
  ⟨e.symm 1⟩
#align equiv.has_one Equiv.One
#align equiv.has_zero Equiv.Zero
-/

#print Equiv.one_def /-
@[to_additive]
theorem one_def [One β] : @One.one _ (Equiv.One e) = e.symm 1 :=
  rfl
#align equiv.one_def Equiv.one_def
#align equiv.zero_def Equiv.zero_def
-/

#print Equiv.Mul /-
/-- Transfer `has_mul` across an `equiv` -/
@[reducible, to_additive "Transfer `has_add` across an `equiv`"]
protected def Mul [Mul β] : Mul α :=
  ⟨fun x y => e.symm (e x * e y)⟩
#align equiv.has_mul Equiv.Mul
#align equiv.has_add Equiv.Add
-/

#print Equiv.mul_def /-
@[to_additive]
theorem mul_def [Mul β] (x y : α) : @Mul.mul _ (Equiv.Mul e) x y = e.symm (e x * e y) :=
  rfl
#align equiv.mul_def Equiv.mul_def
#align equiv.add_def Equiv.add_def
-/

#print Equiv.Div /-
/-- Transfer `has_div` across an `equiv` -/
@[reducible, to_additive "Transfer `has_sub` across an `equiv`"]
protected def Div [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩
#align equiv.has_div Equiv.Div
#align equiv.has_sub Equiv.Sub
-/

#print Equiv.div_def /-
@[to_additive]
theorem div_def [Div β] (x y : α) : @Div.div _ (Equiv.Div e) x y = e.symm (e x / e y) :=
  rfl
#align equiv.div_def Equiv.div_def
#align equiv.sub_def Equiv.sub_def
-/

#print Equiv.Inv /-
/-- Transfer `has_inv` across an `equiv` -/
@[reducible, to_additive "Transfer `has_neg` across an `equiv`"]
protected def Inv [Inv β] : Inv α :=
  ⟨fun x => e.symm (e x)⁻¹⟩
#align equiv.has_inv Equiv.Inv
#align equiv.has_neg Equiv.Neg
-/

#print Equiv.inv_def /-
@[to_additive]
theorem inv_def [Inv β] (x : α) : @Inv.inv _ (Equiv.Inv e) x = e.symm (e x)⁻¹ :=
  rfl
#align equiv.inv_def Equiv.inv_def
#align equiv.neg_def Equiv.neg_def
-/

#print Equiv.SMul /-
/-- Transfer `has_smul` across an `equiv` -/
@[reducible]
protected def SMul (R : Type _) [SMul R β] : SMul R α :=
  ⟨fun r x => e.symm (r • e x)⟩
#align equiv.has_smul Equiv.SMul
-/

/- warning: equiv.smul_def -> Equiv.smul_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) {R : Type.{u3}} [_inst_1 : SMul.{u3, u2} R β] (r : R) (x : α), Eq.{succ u1} α (SMul.smul.{u3, u1} R α (Equiv.SMul.{u1, u2, u3} α β e R _inst_1) r x) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e) (SMul.smul.{u3, u2} R β _inst_1 r (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} (e : Equiv.{succ u2, succ u3} α β) {R : Type.{u1}} [_inst_1 : SMul.{u1, u3} R β] (r : R) (x : α), Eq.{succ u2} α (HSMul.hSMul.{u1, u2, u2} R α α (instHSMul.{u1, u2} R α (Equiv.SMul.{u2, u3, u1} α β e R _inst_1)) r x) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Equiv.{succ u3, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} β α) (Equiv.symm.{succ u2, succ u3} α β e) (HSMul.hSMul.{u1, u3, u3} R ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) x) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) x) (instHSMul.{u1, u3} R ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) x) _inst_1) r (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (Equiv.{succ u2, succ u3} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u3} α β) e x)))
Case conversion may be inaccurate. Consider using '#align equiv.smul_def Equiv.smul_defₓ'. -/
theorem smul_def {R : Type _} [SMul R β] (r : R) (x : α) :
    @SMul.smul _ _ (e.SMul R) r x = e.symm (r • e x) :=
  rfl
#align equiv.smul_def Equiv.smul_def

#print Equiv.Pow /-
/-- Transfer `has_pow` across an `equiv` -/
@[reducible, to_additive SMul]
protected def Pow (N : Type _) [Pow β N] : Pow α N :=
  ⟨fun x n => e.symm (e x ^ n)⟩
#align equiv.has_pow Equiv.Pow
#align equiv.has_smul Equiv.SMul
-/

/- warning: equiv.pow_def -> Equiv.pow_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) {N : Type.{u3}} [_inst_1 : Pow.{u2, u3} β N] (n : N) (x : α), Eq.{succ u1} α (HPow.hPow.{u1, u3, u1} α N α (instHPow.{u1, u3} α N (Equiv.Pow.{u1, u2, u3} α β e N _inst_1)) x n) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e) (HPow.hPow.{u2, u3, u2} β N β (instHPow.{u2, u3} β N _inst_1) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e x) n))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} (e : Equiv.{succ u2, succ u3} α β) {N : Type.{u1}} [_inst_1 : Pow.{u3, u1} β N] (n : N) (x : α), Eq.{succ u2} α (HPow.hPow.{u2, u1, u2} α N α (instHPow.{u2, u1} α N (Equiv.Pow.{u2, u3, u1} α β e N _inst_1)) x n) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Equiv.{succ u3, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} β α) (Equiv.symm.{succ u2, succ u3} α β e) (HPow.hPow.{u3, u1, u3} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) x) N ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) x) (instHPow.{u3, u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) x) N _inst_1) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (Equiv.{succ u2, succ u3} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u3} α β) e x) n))
Case conversion may be inaccurate. Consider using '#align equiv.pow_def Equiv.pow_defₓ'. -/
theorem pow_def {N : Type _} [Pow β N] (n : N) (x : α) :
    @Pow.pow _ _ (e.Pow N) x n = e.symm (e x ^ n) :=
  rfl
#align equiv.pow_def Equiv.pow_def

#print Equiv.mulEquiv /-
/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β`
where the multiplicative structure on `α` is
the one obtained by transporting a multiplicative structure on `β` back along `e`.
-/
@[to_additive
      "An equivalence `e : α ≃ β` gives a additive equivalence `α ≃+ β`\nwhere the additive structure on `α` is\nthe one obtained by transporting an additive structure on `β` back along `e`."]
def mulEquiv (e : α ≃ β) [Mul β] :
    letI := Equiv.Mul e
    α ≃* β :=
  by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        apply e.symm.injective
        simp }
#align equiv.mul_equiv Equiv.mulEquiv
#align equiv.add_equiv Equiv.addEquiv
-/

/- warning: equiv.mul_equiv_apply -> Equiv.mulEquiv_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) [_inst_1 : Mul.{u2} β] (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (let _inst : Mul.{u1} α := Equiv.Mul.{u1, u2} α β e _inst_1; MulEquiv.{u1, u2} α β _inst _inst_1) (fun (_x : MulEquiv.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1) => α -> β) (MulEquiv.hasCoeToFun.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1) (Equiv.mulEquiv.{u1, u2} α β e _inst_1) a) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) [_inst_1 : Mul.{u2} β] (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulEquiv.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (MulEquiv.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (MulEquiv.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1) α β (MulEquivClass.toEquivLike.{max u1 u2, u1, u2} (MulEquiv.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1) α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1)))) (Equiv.mulEquiv.{u1, u2} α β e _inst_1) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} α β) e a)
Case conversion may be inaccurate. Consider using '#align equiv.mul_equiv_apply Equiv.mulEquiv_applyₓ'. -/
@[simp, to_additive]
theorem mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a :=
  rfl
#align equiv.mul_equiv_apply Equiv.mulEquiv_apply
#align equiv.add_equiv_apply Equiv.addEquiv_apply

/- warning: equiv.mul_equiv_symm_apply -> Equiv.mulEquiv_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) [_inst_1 : Mul.{u2} β] (b : β), let _inst : Mul.{u1} α := Equiv.Mul.{u1, u2} α β e _inst_1; Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1)) (fun (_x : MulEquiv.{u2, u1} β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1)) => β -> α) (MulEquiv.hasCoeToFun.{u2, u1} β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1)) (MulEquiv.symm.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1 (Equiv.mulEquiv.{u1, u2} α β e _inst_1)) b) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e) b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) [_inst_1 : Mul.{u2} β] (b : β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) b) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1)) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1)) β α (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1)) β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} β α _inst_1 (Equiv.Mul.{u1, u2} α β e _inst_1))))) (MulEquiv.symm.{u1, u2} α β (Equiv.Mul.{u1, u2} α β e _inst_1) _inst_1 (Equiv.mulEquiv.{u1, u2} α β e _inst_1)) b) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} β α) β (fun (a : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) a) (Equiv.instFunLikeEquiv.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e) b)
Case conversion may be inaccurate. Consider using '#align equiv.mul_equiv_symm_apply Equiv.mulEquiv_symm_applyₓ'. -/
@[to_additive]
theorem mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.Mul e
    (MulEquiv e).symm b = e.symm b :=
  by intros ; rfl
#align equiv.mul_equiv_symm_apply Equiv.mulEquiv_symm_apply
#align equiv.add_equiv_symm_apply Equiv.addEquiv_symm_apply

/- warning: equiv.ring_equiv -> Equiv.ringEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) [_inst_1 : Add.{u2} β] [_inst_2 : Mul.{u2} β], let _inst : Add.{u1} α := Equiv.Add.{u1, u2} α β e _inst_1; let _inst_3 : Mul.{u1} α := Equiv.Mul.{u1, u2} α β e _inst_2; RingEquiv.{u1, u2} α β _inst_3 _inst _inst_2 _inst_1
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) [_inst_1 : Add.{u2} β] [_inst_2 : Mul.{u2} β], let _inst : Add.{u1} α := Equiv.Add.{u1, u2} α β e _inst_1; let _inst_3 : Mul.{u1} α := Equiv.Mul.{u1, u2} α β e _inst_2; RingEquiv.{u1, u2} α β _inst_3 _inst_2 _inst _inst_1
Case conversion may be inaccurate. Consider using '#align equiv.ring_equiv Equiv.ringEquivₓ'. -/
/-- An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] :
    by
    letI := Equiv.Add e
    letI := Equiv.Mul e
    exact α ≃+* β := by
  intros
  exact
    {
      e with
      map_add' := fun x y => by
        apply e.symm.injective
        simp
      map_mul' := fun x y => by
        apply e.symm.injective
        simp }
#align equiv.ring_equiv Equiv.ringEquiv

#print Equiv.ringEquiv_apply /-
@[simp]
theorem ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : (ringEquiv e) a = e a :=
  rfl
#align equiv.ring_equiv_apply Equiv.ringEquiv_apply
-/

#print Equiv.ringEquiv_symm_apply /-
theorem ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) :
    by
    letI := Equiv.Add e
    letI := Equiv.Mul e
    exact (RingEquiv e).symm b = e.symm b := by intros ; rfl
#align equiv.ring_equiv_symm_apply Equiv.ringEquiv_symm_apply
-/

#print Equiv.semigroup /-
/-- Transfer `semigroup` across an `equiv` -/
@[reducible, to_additive "Transfer `add_semigroup` across an `equiv`"]
protected def semigroup [Semigroup β] : Semigroup α :=
  by
  let mul := e.Mul
  skip <;> apply e.injective.semigroup _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semigroup Equiv.semigroup
#align equiv.add_semigroup Equiv.addSemigroup
-/

#print Equiv.semigroupWithZero /-
/-- Transfer `semigroup_with_zero` across an `equiv` -/
@[reducible]
protected def semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α :=
  by
  let mul := e.Mul
  let zero := e.Zero
  skip <;> apply e.injective.semigroup_with_zero _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semigroup_with_zero Equiv.semigroupWithZero
-/

#print Equiv.commSemigroup /-
/-- Transfer `comm_semigroup` across an `equiv` -/
@[reducible, to_additive "Transfer `add_comm_semigroup` across an `equiv`"]
protected def commSemigroup [CommSemigroup β] : CommSemigroup α :=
  by
  let mul := e.Mul
  skip <;> apply e.injective.comm_semigroup _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_semigroup Equiv.commSemigroup
#align equiv.add_comm_semigroup Equiv.addCommSemigroup
-/

#print Equiv.mulZeroClass /-
/-- Transfer `mul_zero_class` across an `equiv` -/
@[reducible]
protected def mulZeroClass [MulZeroClass β] : MulZeroClass α :=
  by
  let zero := e.Zero
  let mul := e.Mul
  skip <;> apply e.injective.mul_zero_class _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_zero_class Equiv.mulZeroClass
-/

#print Equiv.mulOneClass /-
/-- Transfer `mul_one_class` across an `equiv` -/
@[reducible, to_additive "Transfer `add_zero_class` across an `equiv`"]
protected def mulOneClass [MulOneClass β] : MulOneClass α :=
  by
  let one := e.One
  let mul := e.Mul
  skip <;> apply e.injective.mul_one_class _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_one_class Equiv.mulOneClass
#align equiv.add_zero_class Equiv.addZeroClass
-/

#print Equiv.mulZeroOneClass /-
/-- Transfer `mul_zero_one_class` across an `equiv` -/
@[reducible]
protected def mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α :=
  by
  let zero := e.Zero
  let one := e.One
  let mul := e.Mul
  skip <;> apply e.injective.mul_zero_one_class _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.mul_zero_one_class Equiv.mulZeroOneClass
-/

#print Equiv.monoid /-
/-- Transfer `monoid` across an `equiv` -/
@[reducible, to_additive "Transfer `add_monoid` across an `equiv`"]
protected def monoid [Monoid β] : Monoid α :=
  by
  let one := e.One
  let mul := e.Mul
  let pow := e.Pow ℕ
  skip <;> apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.monoid Equiv.monoid
#align equiv.add_monoid Equiv.addMonoid
-/

#print Equiv.commMonoid /-
/-- Transfer `comm_monoid` across an `equiv` -/
@[reducible, to_additive "Transfer `add_comm_monoid` across an `equiv`"]
protected def commMonoid [CommMonoid β] : CommMonoid α :=
  by
  let one := e.One
  let mul := e.Mul
  let pow := e.Pow ℕ
  skip <;> apply e.injective.comm_monoid _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_monoid Equiv.commMonoid
#align equiv.add_comm_monoid Equiv.addCommMonoid
-/

#print Equiv.group /-
/-- Transfer `group` across an `equiv` -/
@[reducible, to_additive "Transfer `add_group` across an `equiv`"]
protected def group [Group β] : Group α :=
  by
  let one := e.One
  let mul := e.Mul
  let inv := e.Inv
  let div := e.Div
  let npow := e.Pow ℕ
  let zpow := e.Pow ℤ
  skip <;> apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.group Equiv.group
#align equiv.add_group Equiv.addGroup
-/

#print Equiv.commGroup /-
/-- Transfer `comm_group` across an `equiv` -/
@[reducible, to_additive "Transfer `add_comm_group` across an `equiv`"]
protected def commGroup [CommGroup β] : CommGroup α :=
  by
  let one := e.One
  let mul := e.Mul
  let inv := e.Inv
  let div := e.Div
  let npow := e.Pow ℕ
  let zpow := e.Pow ℤ
  skip <;> apply e.injective.comm_group _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_group Equiv.commGroup
#align equiv.add_comm_group Equiv.addCommGroup
-/

#print Equiv.nonUnitalNonAssocSemiring /-
/-- Transfer `non_unital_non_assoc_semiring` across an `equiv` -/
@[reducible]
protected def nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let nsmul := e.SMul ℕ
  skip <;> apply e.injective.non_unital_non_assoc_semiring _ <;> intros <;>
    exact e.apply_symm_apply _
#align equiv.non_unital_non_assoc_semiring Equiv.nonUnitalNonAssocSemiring
-/

#print Equiv.nonUnitalSemiring /-
/-- Transfer `non_unital_semiring` across an `equiv` -/
@[reducible]
protected def nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let nsmul := e.SMul ℕ
  skip <;> apply e.injective.non_unital_semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_semiring Equiv.nonUnitalSemiring
-/

#print Equiv.addMonoidWithOne /-
/-- Transfer `add_monoid_with_one` across an `equiv` -/
@[reducible]
protected def addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.AddMonoid, e.One with
    natCast := fun n => e.symm n
    natCast_zero := show e.symm _ = _ by simp [zero_def]
    natCast_succ := fun n => show e.symm _ = e.symm (e (e.symm _) + _) by simp [add_def, one_def] }
#align equiv.add_monoid_with_one Equiv.addMonoidWithOne
-/

#print Equiv.addGroupWithOne /-
/-- Transfer `add_group_with_one` across an `equiv` -/
@[reducible]
protected def addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.AddMonoidWithOne,
    e.AddGroup with
    intCast := fun n => e.symm n
    intCast_ofNat := fun n => by rw [Int.cast_ofNat] <;> rfl
    intCast_negSucc := fun n =>
      congr_arg e.symm <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }
#align equiv.add_group_with_one Equiv.addGroupWithOne
-/

#print Equiv.nonAssocSemiring /-
/-- Transfer `non_assoc_semiring` across an `equiv` -/
@[reducible]
protected def nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α :=
  by
  let mul := e.Mul
  let add_monoid_with_one := e.AddMonoidWithOne
  skip <;> apply e.injective.non_assoc_semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_assoc_semiring Equiv.nonAssocSemiring
-/

#print Equiv.semiring /-
/-- Transfer `semiring` across an `equiv` -/
@[reducible]
protected def semiring [Semiring β] : Semiring α :=
  by
  let mul := e.Mul
  let add_monoid_with_one := e.AddMonoidWithOne
  let npow := e.Pow ℕ
  skip <;> apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.semiring Equiv.semiring
-/

#print Equiv.nonUnitalCommSemiring /-
/-- Transfer `non_unital_comm_semiring` across an `equiv` -/
@[reducible]
protected def nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let nsmul := e.SMul ℕ
  skip <;> apply e.injective.non_unital_comm_semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_comm_semiring Equiv.nonUnitalCommSemiring
-/

#print Equiv.commSemiring /-
/-- Transfer `comm_semiring` across an `equiv` -/
@[reducible]
protected def commSemiring [CommSemiring β] : CommSemiring α :=
  by
  let mul := e.Mul
  let add_monoid_with_one := e.AddMonoidWithOne
  let npow := e.Pow ℕ
  skip <;> apply e.injective.comm_semiring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_semiring Equiv.commSemiring
-/

#print Equiv.nonUnitalNonAssocRing /-
/-- Transfer `non_unital_non_assoc_ring` across an `equiv` -/
@[reducible]
protected def nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let neg := e.Neg
  let sub := e.Sub
  let nsmul := e.SMul ℕ
  let zsmul := e.SMul ℤ
  skip <;> apply e.injective.non_unital_non_assoc_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_non_assoc_ring Equiv.nonUnitalNonAssocRing
-/

#print Equiv.nonUnitalRing /-
/-- Transfer `non_unital_ring` across an `equiv` -/
@[reducible]
protected def nonUnitalRing [NonUnitalRing β] : NonUnitalRing α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let neg := e.Neg
  let sub := e.Sub
  let nsmul := e.SMul ℕ
  let zsmul := e.SMul ℤ
  skip <;> apply e.injective.non_unital_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_ring Equiv.nonUnitalRing
-/

#print Equiv.nonAssocRing /-
/-- Transfer `non_assoc_ring` across an `equiv` -/
@[reducible]
protected def nonAssocRing [NonAssocRing β] : NonAssocRing α :=
  by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.Mul
  skip <;> apply e.injective.non_assoc_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_assoc_ring Equiv.nonAssocRing
-/

#print Equiv.ring /-
/-- Transfer `ring` across an `equiv` -/
@[reducible]
protected def ring [Ring β] : Ring α := by
  let mul := e.Mul
  let add_group_with_one := e.AddGroupWithOne
  let npow := e.Pow ℕ
  skip <;> apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.ring Equiv.ring
-/

#print Equiv.nonUnitalCommRing /-
/-- Transfer `non_unital_comm_ring` across an `equiv` -/
@[reducible]
protected def nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α :=
  by
  let zero := e.Zero
  let add := e.Add
  let mul := e.Mul
  let neg := e.Neg
  let sub := e.Sub
  let nsmul := e.SMul ℕ
  let zsmul := e.SMul ℤ
  skip <;> apply e.injective.non_unital_comm_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.non_unital_comm_ring Equiv.nonUnitalCommRing
-/

#print Equiv.commRing /-
/-- Transfer `comm_ring` across an `equiv` -/
@[reducible]
protected def commRing [CommRing β] : CommRing α :=
  by
  let mul := e.Mul
  let add_group_with_one := e.AddGroupWithOne
  let npow := e.Pow ℕ
  skip <;> apply e.injective.comm_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.comm_ring Equiv.commRing
-/

#print Equiv.nontrivial /-
/-- Transfer `nontrivial` across an `equiv` -/
@[reducible]
protected theorem nontrivial [Nontrivial β] : Nontrivial α :=
  e.Surjective.Nontrivial
#align equiv.nontrivial Equiv.nontrivial
-/

/- warning: equiv.is_domain -> Equiv.isDomain is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] [_inst_3 : IsDomain.{u2} β (Ring.toSemiring.{u2} β _inst_2)], (RingEquiv.{u1, u2} α β (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (Distrib.toHasMul.{u2} β (Ring.toDistrib.{u2} β _inst_2)) (Distrib.toHasAdd.{u2} β (Ring.toDistrib.{u2} β _inst_2))) -> (IsDomain.{u1} α (Ring.toSemiring.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] [_inst_3 : IsDomain.{u2} β (Ring.toSemiring.{u2} β _inst_2)], (RingEquiv.{u1, u2} α β (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (NonUnitalNonAssocRing.toMul.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2))) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) (Distrib.toAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2)))))) -> (IsDomain.{u1} α (Ring.toSemiring.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align equiv.is_domain Equiv.isDomainₓ'. -/
/-- Transfer `is_domain` across an `equiv` -/
@[reducible]
protected theorem isDomain [Ring α] [Ring β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.isDomain e.toRingHom e.Injective
#align equiv.is_domain Equiv.isDomain

/- warning: equiv.has_rat_cast -> Equiv.RatCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (Equiv.{succ u1, succ u2} α β) -> (forall [_inst_1 : HasRatCast.{u2} β], HasRatCast.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Equiv.{succ u1, succ u2} α β) -> (forall [_inst_1 : RatCast.{u2} β], RatCast.{u1} α)
Case conversion may be inaccurate. Consider using '#align equiv.has_rat_cast Equiv.RatCastₓ'. -/
/-- Transfer `has_rat_cast` across an `equiv` -/
@[reducible]
protected def RatCast [HasRatCast β] : HasRatCast α where ratCast n := e.symm n
#align equiv.has_rat_cast Equiv.RatCast

#print Equiv.divisionRing /-
/-- Transfer `division_ring` across an `equiv` -/
@[reducible]
protected def divisionRing [DivisionRing β] : DivisionRing α :=
  by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.Mul
  let inv := e.Inv
  let div := e.Div
  let mul := e.Mul
  let npow := e.Pow ℕ
  let zpow := e.Pow ℤ
  let rat_cast := e.HasRatCast
  let qsmul := e.SMul ℚ
  skip <;> apply e.injective.division_ring _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.division_ring Equiv.divisionRing
-/

#print Equiv.field /-
/-- Transfer `field` across an `equiv` -/
@[reducible]
protected def field [Field β] : Field α :=
  by
  let add_group_with_one := e.AddGroupWithOne
  let mul := e.Mul
  let neg := e.Neg
  let inv := e.Inv
  let div := e.Div
  let mul := e.Mul
  let npow := e.Pow ℕ
  let zpow := e.Pow ℤ
  let rat_cast := e.HasRatCast
  let qsmul := e.SMul ℚ
  skip <;> apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _
#align equiv.field Equiv.field
-/

section R

variable (R : Type _)

include R

section

variable [Monoid R]

#print Equiv.mulAction /-
/-- Transfer `mul_action` across an `equiv` -/
@[reducible]
protected def mulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { e.SMul R with
    one_smul := by simp [smul_def]
    mul_smul := by simp [smul_def, mul_smul] }
#align equiv.mul_action Equiv.mulAction
-/

#print Equiv.distribMulAction /-
/-- Transfer `distrib_mul_action` across an `equiv` -/
@[reducible]
protected def distribMulAction (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [DistribMulAction R β], DistribMulAction R α :=
  by
  intros
  letI := Equiv.addCommMonoid e
  exact
    ({ Equiv.mulAction R e with
        smul_zero := by simp [zero_def, smul_def]
        smul_add := by simp [add_def, smul_def, smul_add] } :
      DistribMulAction R α)
#align equiv.distrib_mul_action Equiv.distribMulAction
-/

end

section

variable [Semiring R]

#print Equiv.module /-
/-- Transfer `module` across an `equiv` -/
@[reducible]
protected def module (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [Module R β], Module R α :=
  by
  intros
  exact
    ({
        Equiv.distribMulAction R
          e with
        zero_smul := by simp [zero_def, smul_def]
        add_smul := by simp [add_def, smul_def, add_smul] } :
      Module R α)
#align equiv.module Equiv.module
-/

#print Equiv.linearEquiv /-
/-- An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    by
    letI := Equiv.addCommMonoid e
    letI := Equiv.module R e
    exact α ≃ₗ[R] β := by
  intros
  exact
    { Equiv.addEquiv e with
      map_smul' := fun r x => by
        apply e.symm.injective
        simp
        rfl }
#align equiv.linear_equiv Equiv.linearEquiv
-/

end

section

variable [CommSemiring R]

#print Equiv.algebra /-
/-- Transfer `algebra` across an `equiv` -/
@[reducible]
protected def algebra (e : α ≃ β) [Semiring β] :
    letI := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α :=
  by
  intros
  fapply RingHom.toAlgebra'
  · exact ((RingEquiv e).symm : β →+* α).comp (algebraMap R β)
  · intro r x
    simp only [Function.comp_apply, RingHom.coe_comp]
    have p := ring_equiv_symm_apply e
    dsimp at p
    erw [p]
    clear p
    apply (RingEquiv e).Injective
    simp only [(RingEquiv e).map_mul]
    simp [Algebra.commutes]
#align equiv.algebra Equiv.algebra
-/

#print Equiv.algEquiv /-
/-- An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] :
    by
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp
        rfl }
#align equiv.alg_equiv Equiv.algEquiv
-/

end

end R

end Instances

end Equiv

