/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module logic.equiv.basic
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Defs
import Mathbin.Data.Option.Basic
import Mathbin.Data.Prod.Basic
import Mathbin.Data.Sigma.Basic
import Mathbin.Data.Subtype
import Mathbin.Data.Sum.Basic
import Mathbin.Logic.Function.Conjugate

/-!
# Equivalence between types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we continue the work on equivalences begun in `logic/equiv/defs.lean`, defining

* canonical isomorphisms between various types: e.g.,

  - `equiv.sum_equiv_sigma_bool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b : bool, cond b α β`;

  - `equiv.prod_sum_distrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

* operations on equivalences: e.g.,

  - `equiv.prod_congr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `prod.map`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

## Tags

equivalence, congruence, bijective map
-/


open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace Equiv

#print Equiv.pprodEquivProd /-
/-- `pprod α β` is equivalent to `α × β` -/
@[simps apply symmApply]
def pprodEquivProd {α β : Type _} : PProd α β ≃ α × β
    where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun ⟨x, y⟩ => rfl
  right_inv := fun ⟨x, y⟩ => rfl
#align equiv.pprod_equiv_prod Equiv.pprodEquivProd
-/

#print Equiv.pprodCongr /-
/-- Product of two equivalences, in terms of `pprod`. If `α ≃ β` and `γ ≃ δ`, then
`pprod α γ ≃ pprod β δ`. -/
@[congr, simps apply]
def pprodCongr {δ : Sort z} (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PProd α γ ≃ PProd β δ
    where
  toFun x := ⟨e₁ x.1, e₂ x.2⟩
  invFun x := ⟨e₁.symm x.1, e₂.symm x.2⟩
  left_inv := fun ⟨x, y⟩ => by simp
  right_inv := fun ⟨x, y⟩ => by simp
#align equiv.pprod_congr Equiv.pprodCongr
-/

/- warning: equiv.pprod_prod -> Equiv.pprodProd is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {β₁ : Sort.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}}, (Equiv.{u1, succ u3} α₁ α₂) -> (Equiv.{u2, succ u4} β₁ β₂) -> (Equiv.{max 1 u1 u2, max (succ u3) (succ u4)} (PProd.{u1, u2} α₁ β₁) (Prod.{u3, u4} α₂ β₂))
but is expected to have type
  forall {α₁ : Sort.{u1}} {β₁ : Type.{u2}} {α₂ : Sort.{u3}} {β₂ : Type.{u4}}, (Equiv.{u1, succ u2} α₁ β₁) -> (Equiv.{u3, succ u4} α₂ β₂) -> (Equiv.{max (max 1 u3) u1, max (succ u4) (succ u2)} (PProd.{u1, u3} α₁ α₂) (Prod.{u2, u4} β₁ β₂))
Case conversion may be inaccurate. Consider using '#align equiv.pprod_prod Equiv.pprodProdₓ'. -/
/-- Combine two equivalences using `pprod` in the domain and `prod` in the codomain. -/
@[simps apply symmApply]
def pprodProd {α₁ β₁ : Sort _} {α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    PProd α₁ β₁ ≃ α₂ × β₂ :=
  (ea.pprodCongr eb).trans pprodEquivProd
#align equiv.pprod_prod Equiv.pprodProd

/- warning: equiv.prod_pprod -> Equiv.prodPProd is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Sort.{u3}} {β₂ : Sort.{u4}}, (Equiv.{succ u1, u3} α₁ α₂) -> (Equiv.{succ u2, u4} β₁ β₂) -> (Equiv.{max (succ u1) (succ u2), max 1 u3 u4} (Prod.{u1, u2} α₁ β₁) (PProd.{u3, u4} α₂ β₂))
but is expected to have type
  forall {α₁ : Type.{u1}} {β₁ : Sort.{u2}} {α₂ : Type.{u3}} {β₂ : Sort.{u4}}, (Equiv.{succ u1, u2} α₁ β₁) -> (Equiv.{succ u3, u4} α₂ β₂) -> (Equiv.{max (succ u3) (succ u1), max (max 1 u4) u2} (Prod.{u1, u3} α₁ α₂) (PProd.{u2, u4} β₁ β₂))
Case conversion may be inaccurate. Consider using '#align equiv.prod_pprod Equiv.prodPProdₓ'. -/
/-- Combine two equivalences using `pprod` in the codomain and `prod` in the domain. -/
@[simps apply symmApply]
def prodPProd {α₁ β₁ : Type _} {α₂ β₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    α₁ × β₁ ≃ PProd α₂ β₂ :=
  (ea.symm.pprodProd eb.symm).symm
#align equiv.prod_pprod Equiv.prodPProd

#print Equiv.pprodEquivProdPLift /-
/-- `pprod α β` is equivalent to `plift α × plift β` -/
@[simps apply symmApply]
def pprodEquivProdPLift {α β : Sort _} : PProd α β ≃ PLift α × PLift β :=
  Equiv.plift.symm.pprodProd Equiv.plift.symm
#align equiv.pprod_equiv_prod_plift Equiv.pprodEquivProdPLift
-/

/- warning: equiv.prod_congr -> Equiv.prodCongr is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}}, (Equiv.{succ u1, succ u3} α₁ α₂) -> (Equiv.{succ u2, succ u4} β₁ β₂) -> (Equiv.{max (succ u1) (succ u2), max (succ u3) (succ u4)} (Prod.{u1, u2} α₁ β₁) (Prod.{u3, u4} α₂ β₂))
but is expected to have type
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}}, (Equiv.{succ u1, succ u2} α₁ β₁) -> (Equiv.{succ u3, succ u4} α₂ β₂) -> (Equiv.{max (succ u3) (succ u1), max (succ u4) (succ u2)} (Prod.{u1, u3} α₁ α₂) (Prod.{u2, u4} β₁ β₂))
Case conversion may be inaccurate. Consider using '#align equiv.prod_congr Equiv.prodCongrₓ'. -/
/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. This is
`prod.map` as an equivalence. -/
@[congr, simps apply]
def prodCongr {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
  ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm, fun ⟨a, b⟩ => by simp, fun ⟨a, b⟩ => by simp⟩
#align equiv.prod_congr Equiv.prodCongr

/- warning: equiv.prod_congr_symm -> Equiv.prodCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}} (e₁ : Equiv.{succ u1, succ u3} α₁ α₂) (e₂ : Equiv.{succ u2, succ u4} β₁ β₂), Eq.{max 1 (max (max (succ u3) (succ u4)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ u3) (succ u4)} (Equiv.{max (succ u3) (succ u4), max (succ u1) (succ u2)} (Prod.{u3, u4} α₂ β₂) (Prod.{u1, u2} α₁ β₁)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u3) (succ u4)} (Prod.{u1, u2} α₁ β₁) (Prod.{u3, u4} α₂ β₂) (Equiv.prodCongr.{u1, u2, u3, u4} α₁ β₁ α₂ β₂ e₁ e₂)) (Equiv.prodCongr.{u3, u4, u1, u2} α₂ β₂ α₁ β₁ (Equiv.symm.{succ u1, succ u3} α₁ α₂ e₁) (Equiv.symm.{succ u2, succ u4} β₁ β₂ e₂))
but is expected to have type
  forall {α₁ : Type.{u4}} {β₁ : Type.{u3}} {α₂ : Type.{u2}} {β₂ : Type.{u1}} (e₁ : Equiv.{succ u4, succ u3} α₁ β₁) (e₂ : Equiv.{succ u2, succ u1} α₂ β₂), Eq.{max (max (max (succ u1) (succ u2)) (succ u3)) (succ u4)} (Equiv.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (Prod.{u3, u1} β₁ β₂) (Prod.{u4, u2} α₁ α₂)) (Equiv.symm.{max (succ u2) (succ u4), max (succ u1) (succ u3)} (Prod.{u4, u2} α₁ α₂) (Prod.{u3, u1} β₁ β₂) (Equiv.prodCongr.{u4, u3, u2, u1} α₁ β₁ α₂ β₂ e₁ e₂)) (Equiv.prodCongr.{u3, u4, u1, u2} β₁ α₁ β₂ α₂ (Equiv.symm.{succ u4, succ u3} α₁ β₁ e₁) (Equiv.symm.{succ u2, succ u1} α₂ β₂ e₂))
Case conversion may be inaccurate. Consider using '#align equiv.prod_congr_symm Equiv.prodCongr_symmₓ'. -/
@[simp]
theorem prodCongr_symm {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (prodCongr e₁ e₂).symm = prodCongr e₁.symm e₂.symm :=
  rfl
#align equiv.prod_congr_symm Equiv.prodCongr_symm

#print Equiv.prodComm /-
/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. This is `prod.swap` as an
equivalence.-/
def prodComm (α β : Type _) : α × β ≃ β × α :=
  ⟨Prod.swap, Prod.swap, Prod.swap_swap, Prod.swap_swap⟩
#align equiv.prod_comm Equiv.prodComm
-/

/- warning: equiv.coe_prod_comm -> Equiv.coe_prodComm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{max (max (succ u1) (succ u2)) (succ u2) (succ u1)} ((Prod.{u1, u2} α β) -> (Prod.{u2, u1} β α)) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α)) => (Prod.{u1, u2} α β) -> (Prod.{u2, u1} β α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α)) (Equiv.prodComm.{u1, u2} α β)) (Prod.swap.{u1, u2} α β)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : Prod.{u2, u1} α β), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α β) => Prod.{u1, u2} β α) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α)) (Prod.{u2, u1} α β) (fun (_x : Prod.{u2, u1} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α β) => Prod.{u1, u2} β α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α)) (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α)) (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α)))) (Equiv.prodComm.{u2, u1} α β)) (Prod.swap.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align equiv.coe_prod_comm Equiv.coe_prodCommₓ'. -/
@[simp]
theorem coe_prodComm (α β : Type _) : ⇑(prodComm α β) = Prod.swap :=
  rfl
#align equiv.coe_prod_comm Equiv.coe_prodComm

/- warning: equiv.prod_comm_apply -> Equiv.prodComm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (x : Prod.{u1, u2} α β), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α)) => (Prod.{u1, u2} α β) -> (Prod.{u2, u1} β α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α)) (Equiv.prodComm.{u1, u2} α β) x) (Prod.swap.{u1, u2} α β x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (x : Prod.{u2, u1} α β), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α β) => Prod.{u1, u2} β α) x) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α)) (Prod.{u2, u1} α β) (fun (_x : Prod.{u2, u1} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α β) => Prod.{u1, u2} β α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α)) (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α)) (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α)))) (Equiv.prodComm.{u2, u1} α β) x) (Prod.swap.{u2, u1} α β x)
Case conversion may be inaccurate. Consider using '#align equiv.prod_comm_apply Equiv.prodComm_applyₓ'. -/
@[simp]
theorem prodComm_apply {α β : Type _} (x : α × β) : prodComm α β x = x.swap :=
  rfl
#align equiv.prod_comm_apply Equiv.prodComm_apply

/- warning: equiv.prod_comm_symm -> Equiv.prodComm_symm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{max 1 (max (max (succ u2) (succ u1)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Equiv.prodComm.{u1, u2} α β)) (Equiv.prodComm.{u2, u1} β α)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}), Eq.{max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u1, u2} β α) (Prod.{u2, u1} α β)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Equiv.prodComm.{u2, u1} α β)) (Equiv.prodComm.{u1, u2} β α)
Case conversion may be inaccurate. Consider using '#align equiv.prod_comm_symm Equiv.prodComm_symmₓ'. -/
@[simp]
theorem prodComm_symm (α β) : (prodComm α β).symm = prodComm β α :=
  rfl
#align equiv.prod_comm_symm Equiv.prodComm_symm

#print Equiv.prodAssoc /-
/-- Type product is associative up to an equivalence. -/
@[simps]
def prodAssoc (α β γ : Sort _) : (α × β) × γ ≃ α × β × γ :=
  ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨a, b⟩, c⟩ => rfl,
    fun ⟨a, ⟨b, c⟩⟩ => rfl⟩
#align equiv.prod_assoc Equiv.prodAssoc
-/

#print Equiv.curry /-
/-- Functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps (config := { fullyApplied := false })]
def curry (α β γ : Type _) : (α × β → γ) ≃ (α → β → γ)
    where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
#align equiv.curry Equiv.curry
-/

section

/- warning: equiv.prod_punit -> Equiv.prodPUnit is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u2}), Equiv.{max (succ u2) (succ u1), succ u2} (Prod.{u2, u1} α PUnit.{succ u1}) α
but is expected to have type
  forall (α : Type.{u1}), Equiv.{max (succ u2) (succ u1), succ u1} (Prod.{u1, u2} α PUnit.{succ u2}) α
Case conversion may be inaccurate. Consider using '#align equiv.prod_punit Equiv.prodPUnitₓ'. -/
/-- `punit` is a right identity for type product up to an equivalence. -/
@[simps]
def prodPUnit (α : Type _) : α × PUnit.{u + 1} ≃ α :=
  ⟨fun p => p.1, fun a => (a, PUnit.unit), fun ⟨_, PUnit.unit⟩ => rfl, fun a => rfl⟩
#align equiv.prod_punit Equiv.prodPUnit

/- warning: equiv.punit_prod -> Equiv.punitProd is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u2}), Equiv.{max (succ u1) (succ u2), succ u2} (Prod.{u1, u2} PUnit.{succ u1} α) α
but is expected to have type
  forall (α : Type.{u1}), Equiv.{max (succ u1) (succ u2), succ u1} (Prod.{u2, u1} PUnit.{succ u2} α) α
Case conversion may be inaccurate. Consider using '#align equiv.punit_prod Equiv.punitProdₓ'. -/
/-- `punit` is a left identity for type product up to an equivalence. -/
@[simps]
def punitProd (α : Type _) : PUnit.{u + 1} × α ≃ α :=
  calc
    PUnit × α ≃ α × PUnit := prodComm _ _
    _ ≃ α := prodPUnit _
    
#align equiv.punit_prod Equiv.punitProd

/- warning: equiv.prod_unique -> Equiv.prodUnique is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u_1}) (β : Type.{u_2}) [_inst_1 : Unique.{succ u_2} β], Equiv.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_1, u_2} α β) α
but is expected to have type
  forall (α : Type.{u_1}) (β : Type.{u_2}) [_inst_1 : Unique.{succ u_2} β], Equiv.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_1, u_2} α β) α
Case conversion may be inaccurate. Consider using '#align equiv.prod_unique Equiv.prodUniqueₓ'. -/
/-- Any `unique` type is a right identity for type product up to equivalence. -/
def prodUnique (α β : Type _) [Unique β] : α × β ≃ α :=
  ((Equiv.refl α).prodCongr <| equivPUnit β).trans <| prodPUnit α
#align equiv.prod_unique Equiv.prodUnique

/- warning: equiv.coe_prod_unique -> Equiv.coe_prodUnique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_2} β], Eq.{max (succ u_1) (succ u_2)} ((Prod.{u_1, u_2} α β) -> α) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Equiv.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_1, u_2} α β) α) (fun (_x : Equiv.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_1, u_2} α β) α) => (Prod.{u_1, u_2} α β) -> α) (Equiv.hasCoeToFun.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_1, u_2} α β) α) (Equiv.prodUnique.{u_1, u_2, u_3} α β _inst_1)) (Prod.fst.{u_1, u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_1} α], Eq.{max (succ u_1) (succ u_2)} (forall (ᾰ : Prod.{u_2, u_1} β α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u_2, u_1} β α) => β) ᾰ) (FunLike.coe.{max (succ u_1) (succ u_2), max (succ u_1) (succ u_2), succ u_2} (Equiv.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β) (Prod.{u_2, u_1} β α) (fun (_x : Prod.{u_2, u_1} β α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u_2, u_1} β α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), max (succ u_1) (succ u_2), succ u_2} (Equiv.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β) (Prod.{u_2, u_1} β α) β (EquivLike.toEmbeddingLike.{max (succ u_1) (succ u_2), max (succ u_1) (succ u_2), succ u_2} (Equiv.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β) (Prod.{u_2, u_1} β α) β (Equiv.instEquivLikeEquiv.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β))) (Equiv.prodUnique.{u_2, u_1} β α _inst_1)) (Prod.fst.{u_2, u_1} β α)
Case conversion may be inaccurate. Consider using '#align equiv.coe_prod_unique Equiv.coe_prodUniqueₓ'. -/
@[simp]
theorem coe_prodUnique {α β : Type _} [Unique β] : ⇑(prodUnique α β) = Prod.fst :=
  rfl
#align equiv.coe_prod_unique Equiv.coe_prodUnique

/- warning: equiv.prod_unique_apply -> Equiv.prodUnique_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_2} β] (x : Prod.{u_1, u_2} α β), Eq.{succ u_1} α (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Equiv.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_1, u_2} α β) α) (fun (_x : Equiv.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_1, u_2} α β) α) => (Prod.{u_1, u_2} α β) -> α) (Equiv.hasCoeToFun.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_1, u_2} α β) α) (Equiv.prodUnique.{u_1, u_2, u_3} α β _inst_1) x) (Prod.fst.{u_1, u_2} α β x)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_1} α] (x : Prod.{u_2, u_1} β α), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u_2, u_1} β α) => β) x) (FunLike.coe.{max (succ u_1) (succ u_2), max (succ u_1) (succ u_2), succ u_2} (Equiv.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β) (Prod.{u_2, u_1} β α) (fun (_x : Prod.{u_2, u_1} β α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u_2, u_1} β α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), max (succ u_1) (succ u_2), succ u_2} (Equiv.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β) (Prod.{u_2, u_1} β α) β (EquivLike.toEmbeddingLike.{max (succ u_1) (succ u_2), max (succ u_1) (succ u_2), succ u_2} (Equiv.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β) (Prod.{u_2, u_1} β α) β (Equiv.instEquivLikeEquiv.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β))) (Equiv.prodUnique.{u_2, u_1} β α _inst_1) x) (Prod.fst.{u_2, u_1} β α x)
Case conversion may be inaccurate. Consider using '#align equiv.prod_unique_apply Equiv.prodUnique_applyₓ'. -/
theorem prodUnique_apply {α β : Type _} [Unique β] (x : α × β) : prodUnique α β x = x.1 :=
  rfl
#align equiv.prod_unique_apply Equiv.prodUnique_apply

/- warning: equiv.prod_unique_symm_apply -> Equiv.prodUnique_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_2} β] (x : α), Eq.{max (succ u_1) (succ u_2)} (Prod.{u_1, u_2} α β) (coeFn.{max 1 (succ u_1) (succ u_2), max (succ u_1) (succ u_2)} (Equiv.{succ u_1, max (succ u_1) (succ u_2)} α (Prod.{u_1, u_2} α β)) (fun (_x : Equiv.{succ u_1, max (succ u_1) (succ u_2)} α (Prod.{u_1, u_2} α β)) => α -> (Prod.{u_1, u_2} α β)) (Equiv.hasCoeToFun.{succ u_1, max (succ u_1) (succ u_2)} α (Prod.{u_1, u_2} α β)) (Equiv.symm.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_1, u_2} α β) α (Equiv.prodUnique.{u_1, u_2, u_3} α β _inst_1)) x) (Prod.mk.{u_1, u_2} α β x (Inhabited.default.{succ u_2} β (Unique.inhabited.{succ u_2} β _inst_1)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_1} α] (x : β), Eq.{max (succ u_1) (succ u_2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Prod.{u_2, u_1} β α) x) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_2, max (succ u_1) (succ u_2)} (Equiv.{succ u_2, max (succ u_1) (succ u_2)} β (Prod.{u_2, u_1} β α)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Prod.{u_2, u_1} β α) _x) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_2, max (succ u_1) (succ u_2)} (Equiv.{succ u_2, max (succ u_1) (succ u_2)} β (Prod.{u_2, u_1} β α)) β (Prod.{u_2, u_1} β α) (EquivLike.toEmbeddingLike.{max (succ u_1) (succ u_2), succ u_2, max (succ u_1) (succ u_2)} (Equiv.{succ u_2, max (succ u_1) (succ u_2)} β (Prod.{u_2, u_1} β α)) β (Prod.{u_2, u_1} β α) (Equiv.instEquivLikeEquiv.{succ u_2, max (succ u_1) (succ u_2)} β (Prod.{u_2, u_1} β α)))) (Equiv.symm.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_2, u_1} β α) β (Equiv.prodUnique.{u_2, u_1} β α _inst_1)) x) (Prod.mk.{u_2, u_1} β α x (Inhabited.default.{succ u_1} α (Unique.instInhabited.{succ u_1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align equiv.prod_unique_symm_apply Equiv.prodUnique_symm_applyₓ'. -/
@[simp]
theorem prodUnique_symm_apply {α β : Type _} [Unique β] (x : α) :
    (prodUnique α β).symm x = (x, default) :=
  rfl
#align equiv.prod_unique_symm_apply Equiv.prodUnique_symm_apply

/- warning: equiv.unique_prod -> Equiv.uniqueProd is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u_1}) (β : Type.{u_2}) [_inst_1 : Unique.{succ u_2} β], Equiv.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_2, u_1} β α) α
but is expected to have type
  forall (α : Type.{u_1}) (β : Type.{u_2}) [_inst_1 : Unique.{succ u_2} β], Equiv.{max (succ u_1) (succ u_2), succ u_1} (Prod.{u_2, u_1} β α) α
Case conversion may be inaccurate. Consider using '#align equiv.unique_prod Equiv.uniqueProdₓ'. -/
/-- Any `unique` type is a left identity for type product up to equivalence. -/
def uniqueProd (α β : Type _) [Unique β] : β × α ≃ α :=
  ((equivPUnit β).prodCongr <| Equiv.refl α).trans <| punitProd α
#align equiv.unique_prod Equiv.uniqueProd

/- warning: equiv.coe_unique_prod -> Equiv.coe_uniqueProd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_2} β], Eq.{max (succ u_2) (succ u_1)} ((Prod.{u_2, u_1} β α) -> α) (coeFn.{max 1 (succ u_2) (succ u_1), max (succ u_2) (succ u_1)} (Equiv.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_2, u_1} β α) α) (fun (_x : Equiv.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_2, u_1} β α) α) => (Prod.{u_2, u_1} β α) -> α) (Equiv.hasCoeToFun.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_2, u_1} β α) α) (Equiv.uniqueProd.{u_1, u_2, u_3} α β _inst_1)) (Prod.snd.{u_2, u_1} β α)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_1} α], Eq.{max (succ u_2) (succ u_1)} (forall (ᾰ : Prod.{u_1, u_2} α β), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u_1, u_2} α β) => β) ᾰ) (FunLike.coe.{max (succ u_2) (succ u_1), max (succ u_2) (succ u_1), succ u_2} (Equiv.{max (succ u_2) (succ u_1), succ u_2} (Prod.{u_1, u_2} α β) β) (Prod.{u_1, u_2} α β) (fun (_x : Prod.{u_1, u_2} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u_1, u_2} α β) => β) _x) (EmbeddingLike.toFunLike.{max (succ u_2) (succ u_1), max (succ u_2) (succ u_1), succ u_2} (Equiv.{max (succ u_2) (succ u_1), succ u_2} (Prod.{u_1, u_2} α β) β) (Prod.{u_1, u_2} α β) β (EquivLike.toEmbeddingLike.{max (succ u_2) (succ u_1), max (succ u_2) (succ u_1), succ u_2} (Equiv.{max (succ u_2) (succ u_1), succ u_2} (Prod.{u_1, u_2} α β) β) (Prod.{u_1, u_2} α β) β (Equiv.instEquivLikeEquiv.{max (succ u_2) (succ u_1), succ u_2} (Prod.{u_1, u_2} α β) β))) (Equiv.uniqueProd.{u_2, u_1} β α _inst_1)) (Prod.snd.{u_1, u_2} α β)
Case conversion may be inaccurate. Consider using '#align equiv.coe_unique_prod Equiv.coe_uniqueProdₓ'. -/
@[simp]
theorem coe_uniqueProd {α β : Type _} [Unique β] : ⇑(uniqueProd α β) = Prod.snd :=
  rfl
#align equiv.coe_unique_prod Equiv.coe_uniqueProd

/- warning: equiv.unique_prod_apply -> Equiv.uniqueProd_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_2} β] (x : Prod.{u_2, u_1} β α), Eq.{succ u_1} α (coeFn.{max 1 (succ u_2) (succ u_1), max (succ u_2) (succ u_1)} (Equiv.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_2, u_1} β α) α) (fun (_x : Equiv.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_2, u_1} β α) α) => (Prod.{u_2, u_1} β α) -> α) (Equiv.hasCoeToFun.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_2, u_1} β α) α) (Equiv.uniqueProd.{u_1, u_2, u_3} α β _inst_1) x) (Prod.snd.{u_2, u_1} β α x)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_1} α] (x : Prod.{u_1, u_2} α β), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u_1, u_2} α β) => β) x) (FunLike.coe.{max (succ u_2) (succ u_1), max (succ u_2) (succ u_1), succ u_2} (Equiv.{max (succ u_2) (succ u_1), succ u_2} (Prod.{u_1, u_2} α β) β) (Prod.{u_1, u_2} α β) (fun (_x : Prod.{u_1, u_2} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u_1, u_2} α β) => β) _x) (EmbeddingLike.toFunLike.{max (succ u_2) (succ u_1), max (succ u_2) (succ u_1), succ u_2} (Equiv.{max (succ u_2) (succ u_1), succ u_2} (Prod.{u_1, u_2} α β) β) (Prod.{u_1, u_2} α β) β (EquivLike.toEmbeddingLike.{max (succ u_2) (succ u_1), max (succ u_2) (succ u_1), succ u_2} (Equiv.{max (succ u_2) (succ u_1), succ u_2} (Prod.{u_1, u_2} α β) β) (Prod.{u_1, u_2} α β) β (Equiv.instEquivLikeEquiv.{max (succ u_2) (succ u_1), succ u_2} (Prod.{u_1, u_2} α β) β))) (Equiv.uniqueProd.{u_2, u_1} β α _inst_1) x) (Prod.snd.{u_1, u_2} α β x)
Case conversion may be inaccurate. Consider using '#align equiv.unique_prod_apply Equiv.uniqueProd_applyₓ'. -/
theorem uniqueProd_apply {α β : Type _} [Unique β] (x : β × α) : uniqueProd α β x = x.2 :=
  rfl
#align equiv.unique_prod_apply Equiv.uniqueProd_apply

/- warning: equiv.unique_prod_symm_apply -> Equiv.uniqueProd_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_2} β] (x : α), Eq.{max (succ u_2) (succ u_1)} (Prod.{u_2, u_1} β α) (coeFn.{max 1 (succ u_2) (succ u_1), max (succ u_2) (succ u_1)} (Equiv.{succ u_1, max (succ u_2) (succ u_1)} α (Prod.{u_2, u_1} β α)) (fun (_x : Equiv.{succ u_1, max (succ u_2) (succ u_1)} α (Prod.{u_2, u_1} β α)) => α -> (Prod.{u_2, u_1} β α)) (Equiv.hasCoeToFun.{succ u_1, max (succ u_2) (succ u_1)} α (Prod.{u_2, u_1} β α)) (Equiv.symm.{max (succ u_2) (succ u_1), succ u_1} (Prod.{u_2, u_1} β α) α (Equiv.uniqueProd.{u_1, u_2, u_3} α β _inst_1)) x) (Prod.mk.{u_2, u_1} β α (Inhabited.default.{succ u_2} β (Unique.inhabited.{succ u_2} β _inst_1)) x)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Unique.{succ u_1} α] (x : β), Eq.{max (succ u_1) (succ u_2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Prod.{u_1, u_2} α β) x) (FunLike.coe.{max (succ u_1) (succ u_2), succ u_2, max (succ u_1) (succ u_2)} (Equiv.{succ u_2, max (succ u_1) (succ u_2)} β (Prod.{u_1, u_2} α β)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Prod.{u_1, u_2} α β) _x) (EmbeddingLike.toFunLike.{max (succ u_1) (succ u_2), succ u_2, max (succ u_1) (succ u_2)} (Equiv.{succ u_2, max (succ u_1) (succ u_2)} β (Prod.{u_1, u_2} α β)) β (Prod.{u_1, u_2} α β) (EquivLike.toEmbeddingLike.{max (succ u_1) (succ u_2), succ u_2, max (succ u_1) (succ u_2)} (Equiv.{succ u_2, max (succ u_1) (succ u_2)} β (Prod.{u_1, u_2} α β)) β (Prod.{u_1, u_2} α β) (Equiv.instEquivLikeEquiv.{succ u_2, max (succ u_1) (succ u_2)} β (Prod.{u_1, u_2} α β)))) (Equiv.symm.{max (succ u_1) (succ u_2), succ u_2} (Prod.{u_1, u_2} α β) β (Equiv.uniqueProd.{u_2, u_1} β α _inst_1)) x) (Prod.mk.{u_1, u_2} α β (Inhabited.default.{succ u_1} α (Unique.instInhabited.{succ u_1} α _inst_1)) x)
Case conversion may be inaccurate. Consider using '#align equiv.unique_prod_symm_apply Equiv.uniqueProd_symm_applyₓ'. -/
@[simp]
theorem uniqueProd_symm_apply {α β : Type _} [Unique β] (x : α) :
    (uniqueProd α β).symm x = (default, x) :=
  rfl
#align equiv.unique_prod_symm_apply Equiv.uniqueProd_symm_apply

#print Equiv.prodEmpty /-
/-- `empty` type is a right absorbing element for type product up to an equivalence. -/
def prodEmpty (α : Type _) : α × Empty ≃ Empty :=
  equivEmpty _
#align equiv.prod_empty Equiv.prodEmpty
-/

#print Equiv.emptyProd /-
/-- `empty` type is a left absorbing element for type product up to an equivalence. -/
def emptyProd (α : Type _) : Empty × α ≃ Empty :=
  equivEmpty _
#align equiv.empty_prod Equiv.emptyProd
-/

#print Equiv.prodPEmpty /-
/-- `pempty` type is a right absorbing element for type product up to an equivalence. -/
def prodPEmpty (α : Type _) : α × PEmpty ≃ PEmpty :=
  equivPEmpty _
#align equiv.prod_pempty Equiv.prodPEmpty
-/

#print Equiv.pemptyProd /-
/-- `pempty` type is a left absorbing element for type product up to an equivalence. -/
def pemptyProd (α : Type _) : PEmpty × α ≃ PEmpty :=
  equivPEmpty _
#align equiv.pempty_prod Equiv.pemptyProd
-/

end

section

open Sum

#print Equiv.psumEquivSum /-
/-- `psum` is equivalent to `sum`. -/
def psumEquivSum (α β : Type _) : PSum α β ≃ Sum α β
    where
  toFun s := PSum.casesOn s inl inr
  invFun := Sum.elim PSum.inl PSum.inr
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl
#align equiv.psum_equiv_sum Equiv.psumEquivSum
-/

/- warning: equiv.sum_congr -> Equiv.sumCongr is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}}, (Equiv.{succ u1, succ u3} α₁ α₂) -> (Equiv.{succ u2, succ u4} β₁ β₂) -> (Equiv.{max (succ u1) (succ u2), max (succ u3) (succ u4)} (Sum.{u1, u2} α₁ β₁) (Sum.{u3, u4} α₂ β₂))
but is expected to have type
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}}, (Equiv.{succ u1, succ u2} α₁ β₁) -> (Equiv.{succ u3, succ u4} α₂ β₂) -> (Equiv.{max (succ u3) (succ u1), max (succ u4) (succ u2)} (Sum.{u1, u3} α₁ α₂) (Sum.{u2, u4} β₁ β₂))
Case conversion may be inaccurate. Consider using '#align equiv.sum_congr Equiv.sumCongrₓ'. -/
/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. This is `sum.map` as an equivalence. -/
@[simps apply]
def sumCongr {α₁ β₁ α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : Sum α₁ β₁ ≃ Sum α₂ β₂ :=
  ⟨Sum.map ea eb, Sum.map ea.symm eb.symm, fun x => by simp, fun x => by simp⟩
#align equiv.sum_congr Equiv.sumCongr

#print Equiv.psumCongr /-
/-- If `α ≃ α'` and `β ≃ β'`, then `psum α β ≃ psum α' β'`. -/
def psumCongr {δ : Sort z} (e₁ : α ≃ β) (e₂ : γ ≃ δ) : PSum α γ ≃ PSum β δ
    where
  toFun x := PSum.casesOn x (PSum.inl ∘ e₁) (PSum.inr ∘ e₂)
  invFun x := PSum.casesOn x (PSum.inl ∘ e₁.symm) (PSum.inr ∘ e₂.symm)
  left_inv := by rintro (x | x) <;> simp
  right_inv := by rintro (x | x) <;> simp
#align equiv.psum_congr Equiv.psumCongr
-/

/- warning: equiv.psum_sum -> Equiv.psumSum is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {β₁ : Sort.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}}, (Equiv.{u1, succ u3} α₁ α₂) -> (Equiv.{u2, succ u4} β₁ β₂) -> (Equiv.{max 1 u1 u2, max (succ u3) (succ u4)} (PSum.{u1, u2} α₁ β₁) (Sum.{u3, u4} α₂ β₂))
but is expected to have type
  forall {α₁ : Sort.{u1}} {β₁ : Type.{u2}} {α₂ : Sort.{u3}} {β₂ : Type.{u4}}, (Equiv.{u1, succ u2} α₁ β₁) -> (Equiv.{u3, succ u4} α₂ β₂) -> (Equiv.{max (max 1 u3) u1, max (succ u4) (succ u2)} (PSum.{u1, u3} α₁ α₂) (Sum.{u2, u4} β₁ β₂))
Case conversion may be inaccurate. Consider using '#align equiv.psum_sum Equiv.psumSumₓ'. -/
/-- Combine two `equiv`s using `psum` in the domain and `sum` in the codomain. -/
def psumSum {α₁ β₁ : Sort _} {α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    PSum α₁ β₁ ≃ Sum α₂ β₂ :=
  (ea.psumCongr eb).trans (psumEquivSum _ _)
#align equiv.psum_sum Equiv.psumSum

/- warning: equiv.sum_psum -> Equiv.sumPSum is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Sort.{u3}} {β₂ : Sort.{u4}}, (Equiv.{succ u1, u3} α₁ α₂) -> (Equiv.{succ u2, u4} β₁ β₂) -> (Equiv.{max (succ u1) (succ u2), max 1 u3 u4} (Sum.{u1, u2} α₁ β₁) (PSum.{u3, u4} α₂ β₂))
but is expected to have type
  forall {α₁ : Type.{u1}} {β₁ : Sort.{u2}} {α₂ : Type.{u3}} {β₂ : Sort.{u4}}, (Equiv.{succ u1, u2} α₁ β₁) -> (Equiv.{succ u3, u4} α₂ β₂) -> (Equiv.{max (succ u3) (succ u1), max (max 1 u4) u2} (Sum.{u1, u3} α₁ α₂) (PSum.{u2, u4} β₁ β₂))
Case conversion may be inaccurate. Consider using '#align equiv.sum_psum Equiv.sumPSumₓ'. -/
/-- Combine two `equiv`s using `sum` in the domain and `psum` in the codomain. -/
def sumPSum {α₁ β₁ : Type _} {α₂ β₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    Sum α₁ β₁ ≃ PSum α₂ β₂ :=
  (ea.symm.psumSum eb.symm).symm
#align equiv.sum_psum Equiv.sumPSum

/- warning: equiv.sum_congr_trans -> Equiv.sumCongr_trans is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} {γ₁ : Type.{u5}} {γ₂ : Type.{u6}} (e : Equiv.{succ u1, succ u3} α₁ β₁) (f : Equiv.{succ u2, succ u4} α₂ β₂) (g : Equiv.{succ u3, succ u5} β₁ γ₁) (h : Equiv.{succ u4, succ u6} β₂ γ₂), Eq.{max 1 (max (max (succ u1) (succ u2)) (succ u5) (succ u6)) (max (succ u5) (succ u6)) (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u5) (succ u6)} (Sum.{u1, u2} α₁ α₂) (Sum.{u5, u6} γ₁ γ₂)) (Equiv.trans.{max (succ u1) (succ u2), max (succ u3) (succ u4), max (succ u5) (succ u6)} (Sum.{u1, u2} α₁ α₂) (Sum.{u3, u4} β₁ β₂) (Sum.{u5, u6} γ₁ γ₂) (Equiv.sumCongr.{u1, u2, u3, u4} α₁ α₂ β₁ β₂ e f) (Equiv.sumCongr.{u3, u4, u5, u6} β₁ β₂ γ₁ γ₂ g h)) (Equiv.sumCongr.{u1, u2, u5, u6} α₁ α₂ γ₁ γ₂ (Equiv.trans.{succ u1, succ u3, succ u5} α₁ β₁ γ₁ e g) (Equiv.trans.{succ u2, succ u4, succ u6} α₂ β₂ γ₂ f h))
but is expected to have type
  forall {α₁ : Type.{u6}} {α₂ : Type.{u5}} {β₁ : Type.{u4}} {β₂ : Type.{u3}} {γ₁ : Type.{u2}} {γ₂ : Type.{u1}} (e : Equiv.{succ u6, succ u5} α₁ α₂) (f : Equiv.{succ u4, succ u3} β₁ β₂) (g : Equiv.{succ u5, succ u2} α₂ γ₁) (h : Equiv.{succ u3, succ u1} β₂ γ₂), Eq.{max (max (max (succ u4) (succ u6)) (succ u1)) (succ u2)} (Equiv.{max (succ u4) (succ u6), max (succ u1) (succ u2)} (Sum.{u6, u4} α₁ β₁) (Sum.{u2, u1} γ₁ γ₂)) (Equiv.trans.{max (succ u4) (succ u6), max (succ u3) (succ u5), max (succ u1) (succ u2)} (Sum.{u6, u4} α₁ β₁) (Sum.{u5, u3} α₂ β₂) (Sum.{u2, u1} γ₁ γ₂) (Equiv.sumCongr.{u6, u5, u4, u3} α₁ α₂ β₁ β₂ e f) (Equiv.sumCongr.{u5, u2, u3, u1} α₂ γ₁ β₂ γ₂ g h)) (Equiv.sumCongr.{u6, u2, u4, u1} α₁ γ₁ β₁ γ₂ (Equiv.trans.{succ u6, succ u5, succ u2} α₁ α₂ γ₁ e g) (Equiv.trans.{succ u4, succ u3, succ u1} β₁ β₂ γ₂ f h))
Case conversion may be inaccurate. Consider using '#align equiv.sum_congr_trans Equiv.sumCongr_transₓ'. -/
@[simp]
theorem sumCongr_trans {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort _} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁)
    (h : β₂ ≃ γ₂) :
    (Equiv.sumCongr e f).trans (Equiv.sumCongr g h) = Equiv.sumCongr (e.trans g) (f.trans h) :=
  by
  ext i
  cases i <;> rfl
#align equiv.sum_congr_trans Equiv.sumCongr_trans

/- warning: equiv.sum_congr_symm -> Equiv.sumCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (e : Equiv.{succ u1, succ u2} α β) (f : Equiv.{succ u3, succ u4} γ δ), Eq.{max 1 (max (max (succ u2) (succ u4)) (succ u1) (succ u3)) (max (succ u1) (succ u3)) (succ u2) (succ u4)} (Equiv.{max (succ u2) (succ u4), max (succ u1) (succ u3)} (Sum.{u2, u4} β δ) (Sum.{u1, u3} α γ)) (Equiv.symm.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (Sum.{u1, u3} α γ) (Sum.{u2, u4} β δ) (Equiv.sumCongr.{u1, u3, u2, u4} α γ β δ e f)) (Equiv.sumCongr.{u2, u4, u1, u3} β δ α γ (Equiv.symm.{succ u1, succ u2} α β e) (Equiv.symm.{succ u3, succ u4} γ δ f))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} (e : Equiv.{succ u4, succ u3} α β) (f : Equiv.{succ u2, succ u1} γ δ), Eq.{max (max (max (succ u1) (succ u2)) (succ u3)) (succ u4)} (Equiv.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (Sum.{u3, u1} β δ) (Sum.{u4, u2} α γ)) (Equiv.symm.{max (succ u2) (succ u4), max (succ u1) (succ u3)} (Sum.{u4, u2} α γ) (Sum.{u3, u1} β δ) (Equiv.sumCongr.{u4, u3, u2, u1} α β γ δ e f)) (Equiv.sumCongr.{u3, u4, u1, u2} β α δ γ (Equiv.symm.{succ u4, succ u3} α β e) (Equiv.symm.{succ u2, succ u1} γ δ f))
Case conversion may be inaccurate. Consider using '#align equiv.sum_congr_symm Equiv.sumCongr_symmₓ'. -/
@[simp]
theorem sumCongr_symm {α β γ δ : Sort _} (e : α ≃ β) (f : γ ≃ δ) :
    (Equiv.sumCongr e f).symm = Equiv.sumCongr e.symm f.symm :=
  rfl
#align equiv.sum_congr_symm Equiv.sumCongr_symm

/- warning: equiv.sum_congr_refl -> Equiv.sumCongr_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (Equiv.sumCongr.{u1, u2, u1, u2} α β α β (Equiv.refl.{succ u1} α) (Equiv.refl.{succ u2} β)) (Equiv.refl.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (Sum.{u2, u1} α β)) (Equiv.sumCongr.{u2, u2, u1, u1} α α β β (Equiv.refl.{succ u2} α) (Equiv.refl.{succ u1} β)) (Equiv.refl.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align equiv.sum_congr_refl Equiv.sumCongr_reflₓ'. -/
@[simp]
theorem sumCongr_refl {α β : Sort _} :
    Equiv.sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (Sum α β) :=
  by
  ext i
  cases i <;> rfl
#align equiv.sum_congr_refl Equiv.sumCongr_refl

namespace Perm

#print Equiv.Perm.sumCongr /-
/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
@[reducible]
def sumCongr {α β : Type _} (ea : Equiv.Perm α) (eb : Equiv.Perm β) : Equiv.Perm (Sum α β) :=
  Equiv.sumCongr ea eb
#align equiv.perm.sum_congr Equiv.Perm.sumCongr
-/

/- warning: equiv.perm.sum_congr_apply -> Equiv.Perm.sumCongr_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (ea : Equiv.Perm.{succ u1} α) (eb : Equiv.Perm.{succ u2} β) (x : Sum.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) => (Sum.{u1, u2} α β) -> (Sum.{u1, u2} α β)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (Equiv.Perm.sumCongr.{u1, u2} α β ea eb) x) (Sum.map.{u1, u2, u1, u2} α α β β (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) ea) (coeFn.{succ u2, succ u2} (Equiv.Perm.{succ u2} β) (fun (_x : Equiv.{succ u2, succ u2} β β) => β -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} β β) eb) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (ea : Equiv.Perm.{succ u2} α) (eb : Equiv.Perm.{succ u1} β) (x : Sum.{u2, u1} α β), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u2, u1} α β) => Sum.{u2, u1} α β) x) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Sum.{u2, u1} α β) (fun (_x : Sum.{u2, u1} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u2, u1} α β) => Sum.{u2, u1} α β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Sum.{u2, u1} α β) (Sum.{u2, u1} α β) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Sum.{u2, u1} α β) (Sum.{u2, u1} α β) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (Sum.{u2, u1} α β)))) (Equiv.Perm.sumCongr.{u2, u1} α β ea eb) x) (Sum.map.{u2, u1, u2, u1} α α β β (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.Perm.{succ u2} α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.Perm.{succ u2} α) α α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.Perm.{succ u2} α) α α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α α))) ea) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} β) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} β) β β (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} β) β β (Equiv.instEquivLikeEquiv.{succ u1, succ u1} β β))) eb) x)
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_apply Equiv.Perm.sumCongr_applyₓ'. -/
@[simp]
theorem sumCongr_apply {α β : Type _} (ea : Equiv.Perm α) (eb : Equiv.Perm β) (x : Sum α β) :
    sumCongr ea eb x = Sum.map (⇑ea) (⇑eb) x :=
  Equiv.sumCongr_apply ea eb x
#align equiv.perm.sum_congr_apply Equiv.Perm.sumCongr_apply

/- warning: equiv.perm.sum_congr_trans -> Equiv.Perm.sumCongr_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.Perm.{succ u1} α) (f : Equiv.Perm.{succ u2} β) (g : Equiv.Perm.{succ u1} α) (h : Equiv.Perm.{succ u2} β), Eq.{max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (Equiv.trans.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Equiv.Perm.sumCongr.{u1, u2} α β e f) (Equiv.Perm.sumCongr.{u1, u2} α β g h)) (Equiv.Perm.sumCongr.{u1, u2} α β (Equiv.trans.{succ u1, succ u1, succ u1} α α α e g) (Equiv.trans.{succ u2, succ u2, succ u2} β β β f h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.Perm.{succ u2} α) (f : Equiv.Perm.{succ u1} β) (g : Equiv.Perm.{succ u2} α) (h : Equiv.Perm.{succ u1} β), Eq.{max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (Sum.{u2, u1} α β)) (Equiv.trans.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (Sum.{u2, u1} α β) (Sum.{u2, u1} α β) (Equiv.Perm.sumCongr.{u2, u1} α β e f) (Equiv.Perm.sumCongr.{u2, u1} α β g h)) (Equiv.Perm.sumCongr.{u2, u1} α β (Equiv.trans.{succ u2, succ u2, succ u2} α α α e g) (Equiv.trans.{succ u1, succ u1, succ u1} β β β f h))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_trans Equiv.Perm.sumCongr_transₓ'. -/
@[simp]
theorem sumCongr_trans {α β : Sort _} (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α)
    (h : Equiv.Perm β) : (sumCongr e f).trans (sumCongr g h) = sumCongr (e.trans g) (f.trans h) :=
  Equiv.sumCongr_trans e f g h
#align equiv.perm.sum_congr_trans Equiv.Perm.sumCongr_trans

/- warning: equiv.perm.sum_congr_symm -> Equiv.Perm.sumCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.Perm.{succ u1} α) (f : Equiv.Perm.{succ u2} β), Eq.{max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Equiv.Perm.sumCongr.{u1, u2} α β e f)) (Equiv.Perm.sumCongr.{u1, u2} α β (Equiv.symm.{succ u1, succ u1} α α e) (Equiv.symm.{succ u2, succ u2} β β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.Perm.{succ u2} α) (f : Equiv.Perm.{succ u1} β), Eq.{max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (Sum.{u2, u1} α β)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (Sum.{u2, u1} α β) (Equiv.Perm.sumCongr.{u2, u1} α β e f)) (Equiv.Perm.sumCongr.{u2, u1} α β (Equiv.symm.{succ u2, succ u2} α α e) (Equiv.symm.{succ u1, succ u1} β β f))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_symm Equiv.Perm.sumCongr_symmₓ'. -/
@[simp]
theorem sumCongr_symm {α β : Sort _} (e : Equiv.Perm α) (f : Equiv.Perm β) :
    (sumCongr e f).symm = sumCongr e.symm f.symm :=
  Equiv.sumCongr_symm e f
#align equiv.perm.sum_congr_symm Equiv.Perm.sumCongr_symm

/- warning: equiv.perm.sum_congr_refl -> Equiv.Perm.sumCongr_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max 1 (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.sumCongr.{u1, u2} α β (Equiv.refl.{succ u1} α) (Equiv.refl.{succ u2} β)) (Equiv.refl.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.sumCongr.{u2, u1} α β (Equiv.refl.{succ u2} α) (Equiv.refl.{succ u1} β)) (Equiv.refl.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_refl Equiv.Perm.sumCongr_reflₓ'. -/
@[simp]
theorem sumCongr_refl {α β : Sort _} :
    sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (Sum α β) :=
  Equiv.sumCongr_refl
#align equiv.perm.sum_congr_refl Equiv.Perm.sumCongr_refl

end Perm

#print Equiv.boolEquivPUnitSumPUnit /-
/-- `bool` is equivalent the sum of two `punit`s. -/
def boolEquivPUnitSumPUnit : Bool ≃ Sum PUnit.{u + 1} PUnit.{v + 1} :=
  ⟨fun b => cond b (inr PUnit.unit) (inl PUnit.unit), Sum.elim (fun _ => false) fun _ => true,
    fun b => by cases b <;> rfl, fun s => by rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩
#align equiv.bool_equiv_punit_sum_punit Equiv.boolEquivPUnitSumPUnit
-/

#print Equiv.sumComm /-
/-- Sum of types is commutative up to an equivalence. This is `sum.swap` as an equivalence. -/
@[simps (config := { fullyApplied := false }) apply]
def sumComm (α β : Type _) : Sum α β ≃ Sum β α :=
  ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩
#align equiv.sum_comm Equiv.sumComm
-/

/- warning: equiv.sum_comm_symm -> Equiv.sumComm_symm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{max 1 (max (max (succ u2) (succ u1)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (Sum.{u2, u1} β α) (Sum.{u1, u2} α β)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Sum.{u1, u2} α β) (Sum.{u2, u1} β α) (Equiv.sumComm.{u1, u2} α β)) (Equiv.sumComm.{u2, u1} β α)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}), Eq.{max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u1, u2} β α) (Sum.{u2, u1} α β)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (Sum.{u1, u2} β α) (Equiv.sumComm.{u2, u1} α β)) (Equiv.sumComm.{u1, u2} β α)
Case conversion may be inaccurate. Consider using '#align equiv.sum_comm_symm Equiv.sumComm_symmₓ'. -/
@[simp]
theorem sumComm_symm (α β) : (sumComm α β).symm = sumComm β α :=
  rfl
#align equiv.sum_comm_symm Equiv.sumComm_symm

#print Equiv.sumAssoc /-
/-- Sum of types is associative up to an equivalence. -/
def sumAssoc (α β γ : Type _) : Sum (Sum α β) γ ≃ Sum α (Sum β γ) :=
  ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
    Sum.elim (Sum.inl ∘ Sum.inl) <| Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr, by
    rintro (⟨_ | _⟩ | _) <;> rfl, by rintro (_ | ⟨_ | _⟩) <;> rfl⟩
#align equiv.sum_assoc Equiv.sumAssoc
-/

/- warning: equiv.sum_assoc_apply_inl_inl -> Equiv.sumAssoc_apply_inl_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : α), Eq.{max (succ u1) (succ (max u2 u3))} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (coeFn.{max 1 (max (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3))) (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3), max (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3))} (Equiv.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) => (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) -> (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.sumAssoc.{u1, u2, u3} α β γ) (Sum.inl.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.inl.{u1, u2} α β a))) (Sum.inl.{u1, max u2 u3} α (Sum.{u2, u3} β γ) a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (a : α), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.inl.{max u2 u3, u1} (Sum.{u3, u2} α β) γ (Sum.inl.{u3, u2} α β a))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (fun (_x : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) _x) (EmbeddingLike.toFunLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (EquivLike.toEmbeddingLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Equiv.instEquivLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))))) (Equiv.sumAssoc.{u3, u2, u1} α β γ) (Sum.inl.{max u2 u3, u1} (Sum.{u3, u2} α β) γ (Sum.inl.{u3, u2} α β a))) (Sum.inl.{u3, max u1 u2} α (Sum.{u2, u1} β γ) a)
Case conversion may be inaccurate. Consider using '#align equiv.sum_assoc_apply_inl_inl Equiv.sumAssoc_apply_inl_inlₓ'. -/
@[simp]
theorem sumAssoc_apply_inl_inl {α β γ} (a) : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl
#align equiv.sum_assoc_apply_inl_inl Equiv.sumAssoc_apply_inl_inl

/- warning: equiv.sum_assoc_apply_inl_inr -> Equiv.sumAssoc_apply_inl_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (b : β), Eq.{max (succ u1) (succ (max u2 u3))} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (coeFn.{max 1 (max (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3))) (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3), max (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3))} (Equiv.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) => (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) -> (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.sumAssoc.{u1, u2, u3} α β γ) (Sum.inl.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.inr.{u1, u2} α β b))) (Sum.inr.{u1, max u2 u3} α (Sum.{u2, u3} β γ) (Sum.inl.{u2, u3} β γ b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (b : β), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.inl.{max u2 u3, u1} (Sum.{u3, u2} α β) γ (Sum.inr.{u3, u2} α β b))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (fun (_x : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) _x) (EmbeddingLike.toFunLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (EquivLike.toEmbeddingLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Equiv.instEquivLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))))) (Equiv.sumAssoc.{u3, u2, u1} α β γ) (Sum.inl.{max u2 u3, u1} (Sum.{u3, u2} α β) γ (Sum.inr.{u3, u2} α β b))) (Sum.inr.{u3, max u1 u2} α (Sum.{u2, u1} β γ) (Sum.inl.{u2, u1} β γ b))
Case conversion may be inaccurate. Consider using '#align equiv.sum_assoc_apply_inl_inr Equiv.sumAssoc_apply_inl_inrₓ'. -/
@[simp]
theorem sumAssoc_apply_inl_inr {α β γ} (b) : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl
#align equiv.sum_assoc_apply_inl_inr Equiv.sumAssoc_apply_inl_inr

/- warning: equiv.sum_assoc_apply_inr -> Equiv.sumAssoc_apply_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (c : γ), Eq.{max (succ u1) (succ (max u2 u3))} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (coeFn.{max 1 (max (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3))) (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3), max (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3))} (Equiv.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) => (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) -> (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.sumAssoc.{u1, u2, u3} α β γ) (Sum.inr.{max u1 u2, u3} (Sum.{u1, u2} α β) γ c)) (Sum.inr.{u1, max u2 u3} α (Sum.{u2, u3} β γ) (Sum.inr.{u2, u3} β γ c))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (c : γ), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.inr.{max u2 u3, u1} (Sum.{u3, u2} α β) γ c)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (fun (_x : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) => Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) _x) (EmbeddingLike.toFunLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (EquivLike.toEmbeddingLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Equiv.instEquivLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ))))) (Equiv.sumAssoc.{u3, u2, u1} α β γ) (Sum.inr.{max u2 u3, u1} (Sum.{u3, u2} α β) γ c)) (Sum.inr.{u3, max u1 u2} α (Sum.{u2, u1} β γ) (Sum.inr.{u2, u1} β γ c))
Case conversion may be inaccurate. Consider using '#align equiv.sum_assoc_apply_inr Equiv.sumAssoc_apply_inrₓ'. -/
@[simp]
theorem sumAssoc_apply_inr {α β γ} (c) : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl
#align equiv.sum_assoc_apply_inr Equiv.sumAssoc_apply_inr

/- warning: equiv.sum_assoc_symm_apply_inl -> Equiv.sumAssoc_symm_apply_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : α), Eq.{max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (coeFn.{max 1 (max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)) (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3)), max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (fun (_x : Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) => (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) -> (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.hasCoeToFun.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.symm.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Equiv.sumAssoc.{u1, u2, u3} α β γ)) (Sum.inl.{u1, max u2 u3} α (Sum.{u2, u3} β γ) a)) (Sum.inl.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.inl.{u1, u2} α β a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (a : α), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.inl.{u3, max u1 u2} α (Sum.{u2, u1} β γ) a)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (fun (_x : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) _x) (EmbeddingLike.toFunLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (EquivLike.toEmbeddingLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Equiv.instEquivLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)))) (Equiv.symm.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Equiv.sumAssoc.{u3, u2, u1} α β γ)) (Sum.inl.{u3, max u1 u2} α (Sum.{u2, u1} β γ) a)) (Sum.inl.{max u2 u3, u1} (Sum.{u3, u2} α β) γ (Sum.inl.{u3, u2} α β a))
Case conversion may be inaccurate. Consider using '#align equiv.sum_assoc_symm_apply_inl Equiv.sumAssoc_symm_apply_inlₓ'. -/
@[simp]
theorem sumAssoc_symm_apply_inl {α β γ} (a) : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl
#align equiv.sum_assoc_symm_apply_inl Equiv.sumAssoc_symm_apply_inl

/- warning: equiv.sum_assoc_symm_apply_inr_inl -> Equiv.sumAssoc_symm_apply_inr_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (b : β), Eq.{max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (coeFn.{max 1 (max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)) (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3)), max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (fun (_x : Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) => (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) -> (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.hasCoeToFun.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.symm.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Equiv.sumAssoc.{u1, u2, u3} α β γ)) (Sum.inr.{u1, max u2 u3} α (Sum.{u2, u3} β γ) (Sum.inl.{u2, u3} β γ b))) (Sum.inl.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.inr.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (b : β), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.inr.{u3, max u1 u2} α (Sum.{u2, u1} β γ) (Sum.inl.{u2, u1} β γ b))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (fun (_x : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) _x) (EmbeddingLike.toFunLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (EquivLike.toEmbeddingLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Equiv.instEquivLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)))) (Equiv.symm.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Equiv.sumAssoc.{u3, u2, u1} α β γ)) (Sum.inr.{u3, max u1 u2} α (Sum.{u2, u1} β γ) (Sum.inl.{u2, u1} β γ b))) (Sum.inl.{max u2 u3, u1} (Sum.{u3, u2} α β) γ (Sum.inr.{u3, u2} α β b))
Case conversion may be inaccurate. Consider using '#align equiv.sum_assoc_symm_apply_inr_inl Equiv.sumAssoc_symm_apply_inr_inlₓ'. -/
@[simp]
theorem sumAssoc_symm_apply_inr_inl {α β γ} (b) :
    (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl
#align equiv.sum_assoc_symm_apply_inr_inl Equiv.sumAssoc_symm_apply_inr_inl

/- warning: equiv.sum_assoc_symm_apply_inr_inr -> Equiv.sumAssoc_symm_apply_inr_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (c : γ), Eq.{max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (coeFn.{max 1 (max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)) (max (succ (max u1 u2)) (succ u3)) (succ u1) (succ (max u2 u3)), max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (fun (_x : Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) => (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) -> (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.hasCoeToFun.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.symm.{max (succ (max u1 u2)) (succ u3), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Equiv.sumAssoc.{u1, u2, u3} α β γ)) (Sum.inr.{u1, max u2 u3} α (Sum.{u2, u3} β γ) (Sum.inr.{u2, u3} β γ c))) (Sum.inr.{max u1 u2, u3} (Sum.{u1, u2} α β) γ c)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (c : γ), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.inr.{u3, max u1 u2} α (Sum.{u2, u1} β γ) (Sum.inr.{u2, u1} β γ c))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (fun (_x : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) _x) (EmbeddingLike.toFunLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (EquivLike.toEmbeddingLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Equiv.instEquivLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ)))) (Equiv.symm.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Sum.{max u2 u3, u1} (Sum.{u3, u2} α β) γ) (Sum.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Equiv.sumAssoc.{u3, u2, u1} α β γ)) (Sum.inr.{u3, max u1 u2} α (Sum.{u2, u1} β γ) (Sum.inr.{u2, u1} β γ c))) (Sum.inr.{max u2 u3, u1} (Sum.{u3, u2} α β) γ c)
Case conversion may be inaccurate. Consider using '#align equiv.sum_assoc_symm_apply_inr_inr Equiv.sumAssoc_symm_apply_inr_inrₓ'. -/
@[simp]
theorem sumAssoc_symm_apply_inr_inr {α β γ} (c) : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl
#align equiv.sum_assoc_symm_apply_inr_inr Equiv.sumAssoc_symm_apply_inr_inr

#print Equiv.sumEmpty /-
/-- Sum with `empty` is equivalent to the original type. -/
@[simps symmApply]
def sumEmpty (α β : Type _) [IsEmpty β] : Sum α β ≃ α :=
  ⟨Sum.elim id isEmptyElim, inl, fun s =>
    by
    rcases s with (_ | x)
    rfl
    exact isEmptyElim x, fun a => rfl⟩
#align equiv.sum_empty Equiv.sumEmpty
-/

/- warning: equiv.sum_empty_apply_inl -> Equiv.sumEmpty_apply_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : IsEmpty.{succ u2} β] (a : α), Eq.{succ u1} α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α β) α) (fun (_x : Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α β) α) => (Sum.{u1, u2} α β) -> α) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α β) α) (Equiv.sumEmpty.{u1, u2} α β _inst_1) (Sum.inl.{u1, u2} α β a)) a
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : IsEmpty.{succ u2} α] (a : β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u1, u2} β α) => β) (Sum.inl.{u1, u2} β α a)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u1} (Equiv.{max (succ u2) (succ u1), succ u1} (Sum.{u1, u2} β α) β) (Sum.{u1, u2} β α) (fun (_x : Sum.{u1, u2} β α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u1, u2} β α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u1} (Equiv.{max (succ u2) (succ u1), succ u1} (Sum.{u1, u2} β α) β) (Sum.{u1, u2} β α) β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u1} (Equiv.{max (succ u2) (succ u1), succ u1} (Sum.{u1, u2} β α) β) (Sum.{u1, u2} β α) β (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), succ u1} (Sum.{u1, u2} β α) β))) (Equiv.sumEmpty.{u1, u2} β α _inst_1) (Sum.inl.{u1, u2} β α a)) a
Case conversion may be inaccurate. Consider using '#align equiv.sum_empty_apply_inl Equiv.sumEmpty_apply_inlₓ'. -/
@[simp]
theorem sumEmpty_apply_inl {α β : Type _} [IsEmpty β] (a : α) : sumEmpty α β (Sum.inl a) = a :=
  rfl
#align equiv.sum_empty_apply_inl Equiv.sumEmpty_apply_inl

#print Equiv.emptySum /-
/-- The sum of `empty` with any `Sort*` is equivalent to the right summand. -/
@[simps symmApply]
def emptySum (α β : Type _) [IsEmpty α] : Sum α β ≃ β :=
  (sumComm _ _).trans <| sumEmpty _ _
#align equiv.empty_sum Equiv.emptySum
-/

/- warning: equiv.empty_sum_apply_inr -> Equiv.emptySum_apply_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : IsEmpty.{succ u1} α] (b : β), Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), succ u2} (Sum.{u1, u2} α β) β) (fun (_x : Equiv.{max (succ u1) (succ u2), succ u2} (Sum.{u1, u2} α β) β) => (Sum.{u1, u2} α β) -> β) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ u2} (Sum.{u1, u2} α β) β) (Equiv.emptySum.{u1, u2} α β _inst_1) (Sum.inr.{u1, u2} α β b)) b
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : IsEmpty.{succ u2} α] (b : β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u2, u1} α β) => β) (Sum.inr.{u2, u1} α β b)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u1} (Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u2, u1} α β) β) (Sum.{u2, u1} α β) (fun (_x : Sum.{u2, u1} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u2, u1} α β) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u1} (Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u2, u1} α β) β) (Sum.{u2, u1} α β) β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u1} (Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u2, u1} α β) β) (Sum.{u2, u1} α β) β (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), succ u1} (Sum.{u2, u1} α β) β))) (Equiv.emptySum.{u2, u1} α β _inst_1) (Sum.inr.{u2, u1} α β b)) b
Case conversion may be inaccurate. Consider using '#align equiv.empty_sum_apply_inr Equiv.emptySum_apply_inrₓ'. -/
@[simp]
theorem emptySum_apply_inr {α β : Type _} [IsEmpty α] (b : β) : emptySum α β (Sum.inr b) = b :=
  rfl
#align equiv.empty_sum_apply_inr Equiv.emptySum_apply_inr

/- warning: equiv.option_equiv_sum_punit -> Equiv.optionEquivSumPUnit is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u2}), Equiv.{succ u2, max (succ u2) (succ u1)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})
but is expected to have type
  forall (α : Type.{u1}), Equiv.{succ u1, max (succ u2) (succ u1)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})
Case conversion may be inaccurate. Consider using '#align equiv.option_equiv_sum_punit Equiv.optionEquivSumPUnitₓ'. -/
/-- `option α` is equivalent to `α ⊕ punit` -/
def optionEquivSumPUnit (α : Type _) : Option α ≃ Sum α PUnit.{u + 1} :=
  ⟨fun o => o.elim (inr PUnit.unit) inl, fun s => s.elim some fun _ => none, fun o => by
    cases o <;> rfl, fun s => by rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩
#align equiv.option_equiv_sum_punit Equiv.optionEquivSumPUnit

/- warning: equiv.option_equiv_sum_punit_none -> Equiv.optionEquivSumPUnit_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α PUnit.{succ u2}) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) (fun (_x : Equiv.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) => (Option.{u1} α) -> (Sum.{u1, u2} α PUnit.{succ u2})) (Equiv.hasCoeToFun.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) (Equiv.optionEquivSumPUnit.{u2, u1} α) (Option.none.{u1} α)) (Sum.inr.{u1, u2} α PUnit.{succ u2} PUnit.unit.{succ u2})
but is expected to have type
  forall {α : Type.{u2}}, Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Option.{u2} α) => Sum.{u2, u1} α PUnit.{succ u1}) (Option.none.{u2} α)) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (fun (_x : Option.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Option.{u2} α) => Sum.{u2, u1} α PUnit.{succ u1}) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1}) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1}) (Equiv.instEquivLikeEquiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})))) (Equiv.optionEquivSumPUnit.{u2, u1} α) (Option.none.{u2} α)) (Sum.inr.{u2, u1} α PUnit.{succ u1} PUnit.unit.{succ u1})
Case conversion may be inaccurate. Consider using '#align equiv.option_equiv_sum_punit_none Equiv.optionEquivSumPUnit_noneₓ'. -/
@[simp]
theorem optionEquivSumPUnit_none {α} : optionEquivSumPUnit α none = Sum.inr PUnit.unit :=
  rfl
#align equiv.option_equiv_sum_punit_none Equiv.optionEquivSumPUnit_none

/- warning: equiv.option_equiv_sum_punit_some -> Equiv.optionEquivSumPUnit_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α), Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α PUnit.{succ u2}) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) (fun (_x : Equiv.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) => (Option.{u1} α) -> (Sum.{u1, u2} α PUnit.{succ u2})) (Equiv.hasCoeToFun.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) (Equiv.optionEquivSumPUnit.{u2, u1} α) (Option.some.{u1} α a)) (Sum.inl.{u1, u2} α PUnit.{succ u2} a)
but is expected to have type
  forall {α : Type.{u2}} (a : α), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Option.{u2} α) => Sum.{u2, u1} α PUnit.{succ u1}) (Option.some.{u2} α a)) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (fun (_x : Option.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Option.{u2} α) => Sum.{u2, u1} α PUnit.{succ u1}) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1}) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1}) (Equiv.instEquivLikeEquiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})))) (Equiv.optionEquivSumPUnit.{u2, u1} α) (Option.some.{u2} α a)) (Sum.inl.{u2, u1} α PUnit.{succ u1} a)
Case conversion may be inaccurate. Consider using '#align equiv.option_equiv_sum_punit_some Equiv.optionEquivSumPUnit_someₓ'. -/
@[simp]
theorem optionEquivSumPUnit_some {α} (a) : optionEquivSumPUnit α (some a) = Sum.inl a :=
  rfl
#align equiv.option_equiv_sum_punit_some Equiv.optionEquivSumPUnit_some

/- warning: equiv.option_equiv_sum_punit_coe -> Equiv.optionEquivSumPUnit_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α), Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α PUnit.{succ u2}) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) (fun (_x : Equiv.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) => (Option.{u1} α) -> (Sum.{u1, u2} α PUnit.{succ u2})) (Equiv.hasCoeToFun.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2})) (Equiv.optionEquivSumPUnit.{u2, u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a)) (Sum.inl.{u1, u2} α PUnit.{succ u2} a)
but is expected to have type
  forall {α : Type.{u2}} (a : α), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Option.{u2} α) => Sum.{u2, u1} α PUnit.{succ u1}) (Option.some.{u2} α a)) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (fun (_x : Option.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Option.{u2} α) => Sum.{u2, u1} α PUnit.{succ u1}) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1}) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (Equiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})) (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1}) (Equiv.instEquivLikeEquiv.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1})))) (Equiv.optionEquivSumPUnit.{u2, u1} α) (Option.some.{u2} α a)) (Sum.inl.{u2, u1} α PUnit.{succ u1} a)
Case conversion may be inaccurate. Consider using '#align equiv.option_equiv_sum_punit_coe Equiv.optionEquivSumPUnit_coeₓ'. -/
@[simp]
theorem optionEquivSumPUnit_coe {α} (a : α) : optionEquivSumPUnit α a = Sum.inl a :=
  rfl
#align equiv.option_equiv_sum_punit_coe Equiv.optionEquivSumPUnit_coe

/- warning: equiv.option_equiv_sum_punit_symm_inl -> Equiv.optionEquivSumPUnit_symm_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α), Eq.{succ u1} (Option.{u1} α) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α PUnit.{succ u2}) (Option.{u1} α)) (fun (_x : Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α PUnit.{succ u2}) (Option.{u1} α)) => (Sum.{u1, u2} α PUnit.{succ u2}) -> (Option.{u1} α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α PUnit.{succ u2}) (Option.{u1} α)) (Equiv.symm.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2}) (Equiv.optionEquivSumPUnit.{u2, u1} α)) (Sum.inl.{u1, u2} α PUnit.{succ u2} a)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a)
but is expected to have type
  forall {α : Type.{u2}} (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u2, u1} α PUnit.{succ u1}) => Option.{u2} α) (Sum.inl.{u2, u1} α PUnit.{succ u1} a)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u2} (Equiv.{max (succ u1) (succ u2), succ u2} (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α)) (Sum.{u2, u1} α PUnit.{succ u1}) (fun (_x : Sum.{u2, u1} α PUnit.{succ u1}) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u2, u1} α PUnit.{succ u1}) => Option.{u2} α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u2} (Equiv.{max (succ u1) (succ u2), succ u2} (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α)) (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u2} (Equiv.{max (succ u1) (succ u2), succ u2} (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α)) (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), succ u2} (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α)))) (Equiv.symm.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1}) (Equiv.optionEquivSumPUnit.{u2, u1} α)) (Sum.inl.{u2, u1} α PUnit.{succ u1} a)) (Option.some.{u2} α a)
Case conversion may be inaccurate. Consider using '#align equiv.option_equiv_sum_punit_symm_inl Equiv.optionEquivSumPUnit_symm_inlₓ'. -/
@[simp]
theorem optionEquivSumPUnit_symm_inl {α} (a) : (optionEquivSumPUnit α).symm (Sum.inl a) = a :=
  rfl
#align equiv.option_equiv_sum_punit_symm_inl Equiv.optionEquivSumPUnit_symm_inl

/- warning: equiv.option_equiv_sum_punit_symm_inr -> Equiv.optionEquivSumPUnit_symm_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : PUnit.{succ u2}), Eq.{succ u1} (Option.{u1} α) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α PUnit.{succ u2}) (Option.{u1} α)) (fun (_x : Equiv.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α PUnit.{succ u2}) (Option.{u1} α)) => (Sum.{u1, u2} α PUnit.{succ u2}) -> (Option.{u1} α)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ u1} (Sum.{u1, u2} α PUnit.{succ u2}) (Option.{u1} α)) (Equiv.symm.{succ u1, max (succ u1) (succ u2)} (Option.{u1} α) (Sum.{u1, u2} α PUnit.{succ u2}) (Equiv.optionEquivSumPUnit.{u2, u1} α)) (Sum.inr.{u1, u2} α PUnit.{succ u2} a)) (Option.none.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} (a : PUnit.{succ u1}), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u2, u1} α PUnit.{succ u1}) => Option.{u2} α) (Sum.inr.{u2, u1} α PUnit.{succ u1} a)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u2} (Equiv.{max (succ u1) (succ u2), succ u2} (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α)) (Sum.{u2, u1} α PUnit.{succ u1}) (fun (_x : Sum.{u2, u1} α PUnit.{succ u1}) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{u2, u1} α PUnit.{succ u1}) => Option.{u2} α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u2} (Equiv.{max (succ u1) (succ u2), succ u2} (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α)) (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u2} (Equiv.{max (succ u1) (succ u2), succ u2} (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α)) (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), succ u2} (Sum.{u2, u1} α PUnit.{succ u1}) (Option.{u2} α)))) (Equiv.symm.{succ u2, max (succ u1) (succ u2)} (Option.{u2} α) (Sum.{u2, u1} α PUnit.{succ u1}) (Equiv.optionEquivSumPUnit.{u2, u1} α)) (Sum.inr.{u2, u1} α PUnit.{succ u1} a)) (Option.none.{u2} α)
Case conversion may be inaccurate. Consider using '#align equiv.option_equiv_sum_punit_symm_inr Equiv.optionEquivSumPUnit_symm_inrₓ'. -/
@[simp]
theorem optionEquivSumPUnit_symm_inr {α} (a) : (optionEquivSumPUnit α).symm (Sum.inr a) = none :=
  rfl
#align equiv.option_equiv_sum_punit_symm_inr Equiv.optionEquivSumPUnit_symm_inr

#print Equiv.optionIsSomeEquiv /-
/-- The set of `x : option α` such that `is_some x` is equivalent to `α`. -/
@[simps]
def optionIsSomeEquiv (α : Type _) : { x : Option α // x.isSome } ≃ α
    where
  toFun o := Option.get o.2
  invFun x := ⟨some x, by decide⟩
  left_inv o := Subtype.eq <| Option.some_get _
  right_inv x := Option.get_some _ _
#align equiv.option_is_some_equiv Equiv.optionIsSomeEquiv
-/

#print Equiv.piOptionEquivProd /-
/-- The product over `option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps]
def piOptionEquivProd {α : Type _} {β : Option α → Type _} :
    (∀ a : Option α, β a) ≃ β none × ∀ a : α, β (some a)
    where
  toFun f := (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl
  right_inv x := by simp
#align equiv.pi_option_equiv_prod Equiv.piOptionEquivProd
-/

#print Equiv.sumEquivSigmaBool /-
/-- `α ⊕ β` is equivalent to a `sigma`-type over `bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot by used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ulift` to work around this
difficulty. -/
def sumEquivSigmaBool (α β : Type u) : Sum α β ≃ Σb : Bool, cond b α β :=
  ⟨fun s => s.elim (fun x => ⟨true, x⟩) fun x => ⟨false, x⟩, fun s =>
    match s with
    | ⟨tt, a⟩ => inl a
    | ⟨ff, b⟩ => inr b,
    fun s => by cases s <;> rfl, fun s => by rcases s with ⟨_ | _, _⟩ <;> rfl⟩
#align equiv.sum_equiv_sigma_bool Equiv.sumEquivSigmaBool
-/

#print Equiv.sigmaFiberEquiv /-
-- See also `equiv.sigma_preimage_equiv`.
/-- `sigma_fiber_equiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simps]
def sigmaFiberEquiv {α β : Type _} (f : α → β) : (Σy : β, { x // f x = y }) ≃ α :=
  ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨y, x, rfl⟩ => rfl, fun x => rfl⟩
#align equiv.sigma_fiber_equiv Equiv.sigmaFiberEquiv
-/

end

section SumCompl

#print Equiv.sumCompl /-
/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtype_or_equiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `is_compl p q`.  -/
def sumCompl {α : Type _} (p : α → Prop) [DecidablePred p] : Sum { a // p a } { a // ¬p a } ≃ α
    where
  toFun := Sum.elim coe coe
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp <;> [rw [dif_pos], rw [dif_neg]]
  right_inv a := by
    dsimp
    split_ifs <;> rfl
#align equiv.sum_compl Equiv.sumCompl
-/

#print Equiv.sumCompl_apply_inl /-
@[simp]
theorem sumCompl_apply_inl {α : Type _} (p : α → Prop) [DecidablePred p] (x : { a // p a }) :
    sumCompl p (Sum.inl x) = x :=
  rfl
#align equiv.sum_compl_apply_inl Equiv.sumCompl_apply_inl
-/

#print Equiv.sumCompl_apply_inr /-
@[simp]
theorem sumCompl_apply_inr {α : Type _} (p : α → Prop) [DecidablePred p] (x : { a // ¬p a }) :
    sumCompl p (Sum.inr x) = x :=
  rfl
#align equiv.sum_compl_apply_inr Equiv.sumCompl_apply_inr
-/

#print Equiv.sumCompl_apply_symm_of_pos /-
@[simp]
theorem sumCompl_apply_symm_of_pos {α : Type _} (p : α → Prop) [DecidablePred p] (a : α) (h : p a) :
    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
  dif_pos h
#align equiv.sum_compl_apply_symm_of_pos Equiv.sumCompl_apply_symm_of_pos
-/

#print Equiv.sumCompl_apply_symm_of_neg /-
@[simp]
theorem sumCompl_apply_symm_of_neg {α : Type _} (p : α → Prop) [DecidablePred p] (a : α)
    (h : ¬p a) : (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
  dif_neg h
#align equiv.sum_compl_apply_symm_of_neg Equiv.sumCompl_apply_symm_of_neg
-/

#print Equiv.subtypeCongr /-
/-- Combines an `equiv` between two subtypes with an `equiv` between their complements to form a
  permutation. -/
def subtypeCongr {α : Type _} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) : Perm α :=
  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))
#align equiv.subtype_congr Equiv.subtypeCongr
-/

open Equiv

variable {ε : Type _} {p : ε → Prop} [DecidablePred p]

variable (ep ep' : Perm { a // p a }) (en en' : Perm { a // ¬p a })

#print Equiv.Perm.subtypeCongr /-
/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
def Perm.subtypeCongr : Equiv.Perm ε :=
  permCongr (sumCompl p) (sumCongr ep en)
#align equiv.perm.subtype_congr Equiv.Perm.subtypeCongr
-/

#print Equiv.Perm.subtypeCongr.apply /-
theorem Perm.subtypeCongr.apply (a : ε) :
    ep.subtypeCongr en a = if h : p a then ep ⟨a, h⟩ else en ⟨a, h⟩ := by
  by_cases h : p a <;> simp [perm.subtype_congr, h]
#align equiv.perm.subtype_congr.apply Equiv.Perm.subtypeCongr.apply
-/

#print Equiv.Perm.subtypeCongr.left_apply /-
@[simp]
theorem Perm.subtypeCongr.left_apply {a : ε} (h : p a) : ep.subtypeCongr en a = ep ⟨a, h⟩ := by
  simp [perm.subtype_congr.apply, h]
#align equiv.perm.subtype_congr.left_apply Equiv.Perm.subtypeCongr.left_apply
-/

#print Equiv.Perm.subtypeCongr.left_apply_subtype /-
@[simp]
theorem Perm.subtypeCongr.left_apply_subtype (a : { a // p a }) : ep.subtypeCongr en a = ep a :=
  by
  convert perm.subtype_congr.left_apply _ _ a.property
  simp
#align equiv.perm.subtype_congr.left_apply_subtype Equiv.Perm.subtypeCongr.left_apply_subtype
-/

#print Equiv.Perm.subtypeCongr.right_apply /-
@[simp]
theorem Perm.subtypeCongr.right_apply {a : ε} (h : ¬p a) : ep.subtypeCongr en a = en ⟨a, h⟩ := by
  simp [perm.subtype_congr.apply, h]
#align equiv.perm.subtype_congr.right_apply Equiv.Perm.subtypeCongr.right_apply
-/

#print Equiv.Perm.subtypeCongr.right_apply_subtype /-
@[simp]
theorem Perm.subtypeCongr.right_apply_subtype (a : { a // ¬p a }) : ep.subtypeCongr en a = en a :=
  by
  convert perm.subtype_congr.right_apply _ _ a.property
  simp
#align equiv.perm.subtype_congr.right_apply_subtype Equiv.Perm.subtypeCongr.right_apply_subtype
-/

#print Equiv.Perm.subtypeCongr.refl /-
@[simp]
theorem Perm.subtypeCongr.refl :
    Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε :=
  by
  ext x
  by_cases h : p x <;> simp [h]
#align equiv.perm.subtype_congr.refl Equiv.Perm.subtypeCongr.refl
-/

#print Equiv.Perm.subtypeCongr.symm /-
@[simp]
theorem Perm.subtypeCongr.symm : (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm :=
  by
  ext x
  by_cases h : p x
  · have : p (ep.symm ⟨x, h⟩) := Subtype.property _
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this]
  · have : ¬p (en.symm ⟨x, h⟩) := Subtype.property (en.symm _)
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this]
#align equiv.perm.subtype_congr.symm Equiv.Perm.subtypeCongr.symm
-/

#print Equiv.Perm.subtypeCongr.trans /-
@[simp]
theorem Perm.subtypeCongr.trans :
    (ep.subtypeCongr en).trans (ep'.subtypeCongr en') =
      Perm.subtypeCongr (ep.trans ep') (en.trans en') :=
  by
  ext x
  by_cases h : p x
  · have : p (ep ⟨x, h⟩) := Subtype.property _
    simp [perm.subtype_congr.apply, h, this]
  · have : ¬p (en ⟨x, h⟩) := Subtype.property (en _)
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this]
#align equiv.perm.subtype_congr.trans Equiv.Perm.subtypeCongr.trans
-/

end SumCompl

section SubtypePreimage

variable (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β)

#print Equiv.subtypePreimage /-
/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtypePreimage : { x : α → β // x ∘ coe = x₀ } ≃ ({ a // ¬p a } → β)
    where
  toFun (x : { x : α → β // x ∘ coe = x₀ }) a := (x : α → β) a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨a, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.val_injective <|
      funext fun a => by
        dsimp
        split_ifs <;> [rw [← hx], skip] <;> rfl
  right_inv x :=
    funext fun ⟨a, h⟩ =>
      show dite (p a) _ _ = _ by
        dsimp
        rw [dif_neg h]
#align equiv.subtype_preimage Equiv.subtypePreimage
-/

/- warning: equiv.subtype_preimage_symm_apply_coe_pos -> Equiv.subtypePreimage_symm_apply_coe_pos is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (p : α -> Prop) [_inst_1 : DecidablePred.{u1} α p] (x₀ : (Subtype.{u1} α (fun (a : α) => p a)) -> β) (x : (Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (a : α) (h : p a), Eq.{u2} β ((fun (a : Sort.{max 1 (imax u1 u2)}) (b : Sort.{imax u1 u2}) [self : HasLiftT.{max 1 (imax u1 u2), imax u1 u2} a b] => self.0) (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) (α -> β) (HasLiftT.mk.{max 1 (imax u1 u2), imax u1 u2} (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) (α -> β) (CoeTCₓ.coe.{max 1 (imax u1 u2), imax u1 u2} (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) (α -> β) (coeBase.{max 1 (imax u1 u2), imax u1 u2} (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) (α -> β) (coeSubtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))))) (coeFn.{max 1 (max (imax (max 1 u1) u2) 1 (imax u1 u2)) (imax (max 1 (imax u1 u2)) (max 1 u1) u2), max (imax (max 1 u1) u2) 1 (imax u1 u2)} (Equiv.{imax (max 1 u1) u2, max 1 (imax u1 u2)} ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))) (fun (_x : Equiv.{imax (max 1 u1) u2, max 1 (imax u1 u2)} ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))) => ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) -> (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))) (Equiv.hasCoeToFun.{imax (max 1 u1) u2, max 1 (imax u1 u2)} ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))) (Equiv.symm.{max 1 (imax u1 u2), imax (max 1 u1) u2} (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (Equiv.subtypePreimage.{u1, u2} α β p (fun (a : α) => _inst_1 a) x₀)) x) a) (x₀ (Subtype.mk.{u1} α (fun (a : α) => p a) a h))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{u2} α p] (x₀ : (Subtype.{u2} α (fun (a : α) => p a)) -> β) (x : (Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (a : α) (h : p a), Eq.{u1} β (Subtype.val.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀) (FunLike.coe.{max (max 1 (imax u2 u1)) (imax (max 1 u2) u1), imax (max 1 u2) u1, max 1 (imax u2 u1)} (Equiv.{imax (max 1 u2) u1, max 1 (imax u2 u1)} ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀))) ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (fun (_x : (Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : (Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) => Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀)) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u2 u1)) (imax (max 1 u2) u1), imax (max 1 u2) u1, max 1 (imax u2 u1)} (Equiv.{imax (max 1 u2) u1, max 1 (imax u2 u1)} ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀))) ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀)) (EquivLike.toEmbeddingLike.{max (max 1 (imax u2 u1)) (imax (max 1 u2) u1), imax (max 1 u2) u1, max 1 (imax u2 u1)} (Equiv.{imax (max 1 u2) u1, max 1 (imax u2 u1)} ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀))) ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀)) (Equiv.instEquivLikeEquiv.{imax (max 1 u2) u1, max 1 (imax u2 u1)} ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀))))) (Equiv.symm.{max 1 (imax u2 u1), imax (max 1 u2) u1} (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀)) ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Equiv.subtypePreimage.{u2, u1} α β p (fun (a : α) => _inst_1 a) x₀)) x) a) (x₀ (Subtype.mk.{u2} α (fun (a : α) => p a) a h))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_preimage_symm_apply_coe_pos Equiv.subtypePreimage_symm_apply_coe_posₓ'. -/
theorem subtypePreimage_symm_apply_coe_pos (x : { a // ¬p a } → β) (a : α) (h : p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
  dif_pos h
#align equiv.subtype_preimage_symm_apply_coe_pos Equiv.subtypePreimage_symm_apply_coe_pos

/- warning: equiv.subtype_preimage_symm_apply_coe_neg -> Equiv.subtypePreimage_symm_apply_coe_neg is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (p : α -> Prop) [_inst_1 : DecidablePred.{u1} α p] (x₀ : (Subtype.{u1} α (fun (a : α) => p a)) -> β) (x : (Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (a : α) (h : Not (p a)), Eq.{u2} β ((fun (a : Sort.{max 1 (imax u1 u2)}) (b : Sort.{imax u1 u2}) [self : HasLiftT.{max 1 (imax u1 u2), imax u1 u2} a b] => self.0) (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) (α -> β) (HasLiftT.mk.{max 1 (imax u1 u2), imax u1 u2} (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) (α -> β) (CoeTCₓ.coe.{max 1 (imax u1 u2), imax u1 u2} (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) (α -> β) (coeBase.{max 1 (imax u1 u2), imax u1 u2} (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) (α -> β) (coeSubtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))))) (coeFn.{max 1 (max (imax (max 1 u1) u2) 1 (imax u1 u2)) (imax (max 1 (imax u1 u2)) (max 1 u1) u2), max (imax (max 1 u1) u2) 1 (imax u1 u2)} (Equiv.{imax (max 1 u1) u2, max 1 (imax u1 u2)} ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))) (fun (_x : Equiv.{imax (max 1 u1) u2, max 1 (imax u1 u2)} ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))) => ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) -> (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))) (Equiv.hasCoeToFun.{imax (max 1 u1) u2, max 1 (imax u1 u2)} ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀))) (Equiv.symm.{max 1 (imax u1 u2), imax (max 1 u1) u2} (Subtype.{imax u1 u2} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} α (fun (a : α) => p a)) α β x ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (a : α) => p a)) α (coeSubtype.{u1} α (fun (a : α) => p a))))))) x₀)) ((Subtype.{u1} α (fun (a : α) => Not (p a))) -> β) (Equiv.subtypePreimage.{u1, u2} α β p (fun (a : α) => _inst_1 a) x₀)) x) a) (x (Subtype.mk.{u1} α (fun (a : α) => Not (p a)) a h))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{u2} α p] (x₀ : (Subtype.{u2} α (fun (a : α) => p a)) -> β) (x : (Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (a : α) (h : Not (p a)), Eq.{u1} β (Subtype.val.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀) (FunLike.coe.{max (max 1 (imax u2 u1)) (imax (max 1 u2) u1), imax (max 1 u2) u1, max 1 (imax u2 u1)} (Equiv.{imax (max 1 u2) u1, max 1 (imax u2 u1)} ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀))) ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (fun (_x : (Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : (Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) => Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀)) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u2 u1)) (imax (max 1 u2) u1), imax (max 1 u2) u1, max 1 (imax u2 u1)} (Equiv.{imax (max 1 u2) u1, max 1 (imax u2 u1)} ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀))) ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀)) (EquivLike.toEmbeddingLike.{max (max 1 (imax u2 u1)) (imax (max 1 u2) u1), imax (max 1 u2) u1, max 1 (imax u2 u1)} (Equiv.{imax (max 1 u2) u1, max 1 (imax u2 u1)} ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀))) ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀)) (Equiv.instEquivLikeEquiv.{imax (max 1 u2) u1, max 1 (imax u2 u1)} ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀))))) (Equiv.symm.{max 1 (imax u2 u1), imax (max 1 u2) u1} (Subtype.{imax u2 u1} (α -> β) (fun (x : α -> β) => Eq.{imax (max 1 u2) u1} ((Subtype.{u2} α (fun (a : α) => p a)) -> β) (Function.comp.{max 1 u2, u2, u1} (Subtype.{u2} α (fun (a : α) => p a)) α β x (Subtype.val.{u2} α (fun (a : α) => p a))) x₀)) ((Subtype.{u2} α (fun (a : α) => Not (p a))) -> β) (Equiv.subtypePreimage.{u2, u1} α β p (fun (a : α) => _inst_1 a) x₀)) x) a) (x (Subtype.mk.{u2} α (fun (a : α) => Not (p a)) a h))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_preimage_symm_apply_coe_neg Equiv.subtypePreimage_symm_apply_coe_negₓ'. -/
theorem subtypePreimage_symm_apply_coe_neg (x : { a // ¬p a } → β) (a : α) (h : ¬p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
  dif_neg h
#align equiv.subtype_preimage_symm_apply_coe_neg Equiv.subtypePreimage_symm_apply_coe_neg

end SubtypePreimage

section

#print Equiv.piCongrRight /-
/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Π a, β₁ a` and
`Π a, β₂ a`. -/
def piCongrRight {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) : (∀ a, β₁ a) ≃ ∀ a, β₂ a :=
  ⟨fun H a => F a (H a), fun H a => (F a).symm (H a), fun H => funext <| by simp, fun H =>
    funext <| by simp⟩
#align equiv.Pi_congr_right Equiv.piCongrRight
-/

#print Equiv.piComm /-
/-- Given `φ : α → β → Sort*`, we have an equivalence between `Π a b, φ a b` and `Π b a, φ a b`.
This is `function.swap` as an `equiv`. -/
@[simps apply]
def piComm {α β} (φ : α → β → Sort _) : (∀ a b, φ a b) ≃ ∀ b a, φ a b :=
  ⟨swap, swap, fun x => rfl, fun y => rfl⟩
#align equiv.Pi_comm Equiv.piComm
-/

/- warning: equiv.Pi_comm_symm -> Equiv.piComm_symm is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {φ : α -> β -> Sort.{u3}}, Eq.{max 1 (imax (imax u2 u1 u3) u1 u2 u3) (imax (imax u1 u2 u3) u2 u1 u3)} (Equiv.{imax u2 u1 u3, imax u1 u2 u3} (forall (b : β) (a : α), φ a b) (forall (a : α) (b : β), φ a b)) (Equiv.symm.{imax u1 u2 u3, imax u2 u1 u3} (forall (a : α) (b : β), φ a b) (forall (b : β) (a : α), φ a b) (Equiv.piComm.{u1, u2, u3} α β φ)) (Equiv.piComm.{u2, u1, u3} β α (Function.swap.{u1, u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => Sort.{u3}) φ))
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {φ : α -> β -> Sort.{u1}}, Eq.{max (max 1 (imax u3 u2 u1)) (imax u2 u3 u1)} (Equiv.{imax u2 u3 u1, imax u3 u2 u1} (forall (b : β) (a : α), φ a b) (forall (a : α) (b : β), φ a b)) (Equiv.symm.{imax u3 u2 u1, imax u2 u3 u1} (forall (a : α) (b : β), φ a b) (forall (b : β) (a : α), φ a b) (Equiv.piComm.{u3, u2, u1} α β φ)) (Equiv.piComm.{u2, u3, u1} β α (Function.swap.{u3, u2, succ u1} α β (fun (ᾰ : α) (ᾰ : β) => Sort.{u1}) φ))
Case conversion may be inaccurate. Consider using '#align equiv.Pi_comm_symm Equiv.piComm_symmₓ'. -/
@[simp]
theorem piComm_symm {α β} {φ : α → β → Sort _} : (piComm φ).symm = (Pi_comm <| swap φ) :=
  rfl
#align equiv.Pi_comm_symm Equiv.piComm_symm

#print Equiv.piCurry /-
/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `sigma.curry` and `sigma.uncurry` together as an equiv. -/
def piCurry {α} {β : α → Sort _} (γ : ∀ a, β a → Sort _) : (∀ x : Σi, β i, γ x.1 x.2) ≃ ∀ a b, γ a b
    where
  toFun := Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry
#align equiv.Pi_curry Equiv.piCurry
-/

end

section ProdCongr

variable {α₁ β₁ β₂ : Type _} (e : α₁ → β₁ ≃ β₂)

#print Equiv.prodCongrLeft /-
/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
def prodCongrLeft : β₁ × α₁ ≃ β₂ × α₁
    where
  toFun ab := ⟨e ab.2 ab.1, ab.2⟩
  invFun ab := ⟨(e ab.2).symm ab.1, ab.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    simp
  right_inv := by
    rintro ⟨a, b⟩
    simp
#align equiv.prod_congr_left Equiv.prodCongrLeft
-/

/- warning: equiv.prod_congr_left_apply -> Equiv.prodCongrLeft_apply is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {β₂ : Type.{u3}} (e : α₁ -> (Equiv.{succ u2, succ u3} β₁ β₂)) (b : β₁) (a : α₁), Eq.{max (succ u3) (succ u1)} (Prod.{u3, u1} β₂ α₁) (coeFn.{max 1 (max (max (succ u2) (succ u1)) (succ u3) (succ u1)) (max (succ u3) (succ u1)) (succ u2) (succ u1), max (max (succ u2) (succ u1)) (succ u3) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u3) (succ u1)} (Prod.{u2, u1} β₁ α₁) (Prod.{u3, u1} β₂ α₁)) (fun (_x : Equiv.{max (succ u2) (succ u1), max (succ u3) (succ u1)} (Prod.{u2, u1} β₁ α₁) (Prod.{u3, u1} β₂ α₁)) => (Prod.{u2, u1} β₁ α₁) -> (Prod.{u3, u1} β₂ α₁)) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), max (succ u3) (succ u1)} (Prod.{u2, u1} β₁ α₁) (Prod.{u3, u1} β₂ α₁)) (Equiv.prodCongrLeft.{u1, u2, u3} α₁ β₁ β₂ e) (Prod.mk.{u2, u1} β₁ α₁ b a)) (Prod.mk.{u3, u1} β₂ α₁ (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} β₁ β₂) (fun (_x : Equiv.{succ u2, succ u3} β₁ β₂) => β₁ -> β₂) (Equiv.hasCoeToFun.{succ u2, succ u3} β₁ β₂) (e a) b) a)
but is expected to have type
  forall {α₁ : Type.{u2}} {β₁ : Type.{u1}} {β₂ : Type.{u3}} (e : α₁ -> (Equiv.{succ u1, succ u3} β₁ β₂)) (b : β₁) (a : α₁), Eq.{max (succ u3) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u1, u2} β₁ α₁) => Prod.{u3, u2} β₂ α₁) (Prod.mk.{u1, u2} β₁ α₁ b a)) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), max (succ u1) (succ u2), max (succ u3) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u3)} (Prod.{u1, u2} β₁ α₁) (Prod.{u3, u2} β₂ α₁)) (Prod.{u1, u2} β₁ α₁) (fun (_x : Prod.{u1, u2} β₁ α₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u1, u2} β₁ α₁) => Prod.{u3, u2} β₂ α₁) _x) (EmbeddingLike.toFunLike.{max (max (succ u3) (succ u1)) (succ u2), max (succ u1) (succ u2), max (succ u3) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u3)} (Prod.{u1, u2} β₁ α₁) (Prod.{u3, u2} β₂ α₁)) (Prod.{u1, u2} β₁ α₁) (Prod.{u3, u2} β₂ α₁) (EquivLike.toEmbeddingLike.{max (max (succ u3) (succ u1)) (succ u2), max (succ u1) (succ u2), max (succ u3) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u3)} (Prod.{u1, u2} β₁ α₁) (Prod.{u3, u2} β₂ α₁)) (Prod.{u1, u2} β₁ α₁) (Prod.{u3, u2} β₂ α₁) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), max (succ u3) (succ u2)} (Prod.{u1, u2} β₁ α₁) (Prod.{u3, u2} β₂ α₁)))) (Equiv.prodCongrLeft.{u2, u1, u3} α₁ β₁ β₂ e) (Prod.mk.{u1, u2} β₁ α₁ b a)) (Prod.mk.{u3, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₁) => β₂) b) α₁ (FunLike.coe.{max (succ u3) (succ u1), succ u1, succ u3} (Equiv.{succ u1, succ u3} β₁ β₂) β₁ (fun (_x : β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₁) => β₂) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u1, succ u3} (Equiv.{succ u1, succ u3} β₁ β₂) β₁ β₂ (EquivLike.toEmbeddingLike.{max (succ u3) (succ u1), succ u1, succ u3} (Equiv.{succ u1, succ u3} β₁ β₂) β₁ β₂ (Equiv.instEquivLikeEquiv.{succ u1, succ u3} β₁ β₂))) (e a) b) a)
Case conversion may be inaccurate. Consider using '#align equiv.prod_congr_left_apply Equiv.prodCongrLeft_applyₓ'. -/
@[simp]
theorem prodCongrLeft_apply (b : β₁) (a : α₁) : prodCongrLeft e (b, a) = (e a b, a) :=
  rfl
#align equiv.prod_congr_left_apply Equiv.prodCongrLeft_apply

/- warning: equiv.prod_congr_refl_right -> Equiv.prodCongr_refl_right is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {β₂ : Type.{u3}} (e : Equiv.{succ u2, succ u3} β₁ β₂), Eq.{max 1 (max (max (succ u2) (succ u1)) (succ u3) (succ u1)) (max (succ u3) (succ u1)) (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u3) (succ u1)} (Prod.{u2, u1} β₁ α₁) (Prod.{u3, u1} β₂ α₁)) (Equiv.prodCongr.{u2, u1, u3, u1} β₁ α₁ β₂ α₁ e (Equiv.refl.{succ u1} α₁)) (Equiv.prodCongrLeft.{u1, u2, u3} α₁ β₁ β₂ (fun (_x : α₁) => e))
but is expected to have type
  forall {α₁ : Type.{u1}} {β₁ : Type.{u3}} {β₂ : Type.{u2}} (e : Equiv.{succ u3, succ u2} β₁ β₂), Eq.{max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u2)} (Prod.{u3, u1} β₁ α₁) (Prod.{u2, u1} β₂ α₁)) (Equiv.prodCongr.{u3, u2, u1, u1} β₁ β₂ α₁ α₁ e (Equiv.refl.{succ u1} α₁)) (Equiv.prodCongrLeft.{u1, u3, u2} α₁ β₁ β₂ (fun (_x : α₁) => e))
Case conversion may be inaccurate. Consider using '#align equiv.prod_congr_refl_right Equiv.prodCongr_refl_rightₓ'. -/
theorem prodCongr_refl_right (e : β₁ ≃ β₂) :
    prodCongr e (Equiv.refl α₁) = prodCongrLeft fun _ => e :=
  by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.prod_congr_refl_right Equiv.prodCongr_refl_right

#print Equiv.prodCongrRight /-
/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
def prodCongrRight : α₁ × β₁ ≃ α₁ × β₂
    where
  toFun ab := ⟨ab.1, e ab.1 ab.2⟩
  invFun ab := ⟨ab.1, (e ab.1).symm ab.2⟩
  left_inv := by
    rintro ⟨a, b⟩
    simp
  right_inv := by
    rintro ⟨a, b⟩
    simp
#align equiv.prod_congr_right Equiv.prodCongrRight
-/

/- warning: equiv.prod_congr_right_apply -> Equiv.prodCongrRight_apply is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {β₂ : Type.{u3}} (e : α₁ -> (Equiv.{succ u2, succ u3} β₁ β₂)) (a : α₁) (b : β₁), Eq.{max (succ u1) (succ u3)} (Prod.{u1, u3} α₁ β₂) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u1) (succ u3)) (max (succ u1) (succ u3)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u3)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u3} α₁ β₂)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u3)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u3} α₁ β₂)) => (Prod.{u1, u2} α₁ β₁) -> (Prod.{u1, u3} α₁ β₂)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u3)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u3} α₁ β₂)) (Equiv.prodCongrRight.{u1, u2, u3} α₁ β₁ β₂ e) (Prod.mk.{u1, u2} α₁ β₁ a b)) (Prod.mk.{u1, u3} α₁ β₂ a (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} β₁ β₂) (fun (_x : Equiv.{succ u2, succ u3} β₁ β₂) => β₁ -> β₂) (Equiv.hasCoeToFun.{succ u2, succ u3} β₁ β₂) (e a) b))
but is expected to have type
  forall {α₁ : Type.{u2}} {β₁ : Type.{u1}} {β₂ : Type.{u3}} (e : α₁ -> (Equiv.{succ u1, succ u3} β₁ β₂)) (a : α₁) (b : β₁), Eq.{max (succ u3) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α₁ β₁) => Prod.{u2, u3} α₁ β₂) (Prod.mk.{u2, u1} α₁ β₁ a b)) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), max (succ u1) (succ u2), max (succ u3) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u3) (succ u2)} (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u3} α₁ β₂)) (Prod.{u2, u1} α₁ β₁) (fun (_x : Prod.{u2, u1} α₁ β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α₁ β₁) => Prod.{u2, u3} α₁ β₂) _x) (EmbeddingLike.toFunLike.{max (max (succ u3) (succ u1)) (succ u2), max (succ u1) (succ u2), max (succ u3) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u3) (succ u2)} (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u3} α₁ β₂)) (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u3} α₁ β₂) (EquivLike.toEmbeddingLike.{max (max (succ u3) (succ u1)) (succ u2), max (succ u1) (succ u2), max (succ u3) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u3) (succ u2)} (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u3} α₁ β₂)) (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u3} α₁ β₂) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), max (succ u3) (succ u2)} (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u3} α₁ β₂)))) (Equiv.prodCongrRight.{u2, u1, u3} α₁ β₁ β₂ e) (Prod.mk.{u2, u1} α₁ β₁ a b)) (Prod.mk.{u2, u3} α₁ ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₁) => β₂) b) a (FunLike.coe.{max (succ u3) (succ u1), succ u1, succ u3} (Equiv.{succ u1, succ u3} β₁ β₂) β₁ (fun (_x : β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₁) => β₂) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u1, succ u3} (Equiv.{succ u1, succ u3} β₁ β₂) β₁ β₂ (EquivLike.toEmbeddingLike.{max (succ u3) (succ u1), succ u1, succ u3} (Equiv.{succ u1, succ u3} β₁ β₂) β₁ β₂ (Equiv.instEquivLikeEquiv.{succ u1, succ u3} β₁ β₂))) (e a) b))
Case conversion may be inaccurate. Consider using '#align equiv.prod_congr_right_apply Equiv.prodCongrRight_applyₓ'. -/
@[simp]
theorem prodCongrRight_apply (a : α₁) (b : β₁) : prodCongrRight e (a, b) = (a, e a b) :=
  rfl
#align equiv.prod_congr_right_apply Equiv.prodCongrRight_apply

/- warning: equiv.prod_congr_refl_left -> Equiv.prodCongr_refl_left is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {β₂ : Type.{u3}} (e : Equiv.{succ u2, succ u3} β₁ β₂), Eq.{max 1 (max (max (succ u1) (succ u2)) (succ u1) (succ u3)) (max (succ u1) (succ u3)) (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u3)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u3} α₁ β₂)) (Equiv.prodCongr.{u1, u2, u1, u3} α₁ β₁ α₁ β₂ (Equiv.refl.{succ u1} α₁) e) (Equiv.prodCongrRight.{u1, u2, u3} α₁ β₁ β₂ (fun (_x : α₁) => e))
but is expected to have type
  forall {α₁ : Type.{u1}} {β₁ : Type.{u3}} {β₂ : Type.{u2}} (e : Equiv.{succ u3, succ u2} β₁ β₂), Eq.{max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u2) (succ u1)} (Prod.{u1, u3} α₁ β₁) (Prod.{u1, u2} α₁ β₂)) (Equiv.prodCongr.{u1, u1, u3, u2} α₁ α₁ β₁ β₂ (Equiv.refl.{succ u1} α₁) e) (Equiv.prodCongrRight.{u1, u3, u2} α₁ β₁ β₂ (fun (_x : α₁) => e))
Case conversion may be inaccurate. Consider using '#align equiv.prod_congr_refl_left Equiv.prodCongr_refl_leftₓ'. -/
theorem prodCongr_refl_left (e : β₁ ≃ β₂) :
    prodCongr (Equiv.refl α₁) e = prodCongrRight fun _ => e :=
  by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.prod_congr_refl_left Equiv.prodCongr_refl_left

#print Equiv.prodCongrLeft_trans_prodComm /-
@[simp]
theorem prodCongrLeft_trans_prodComm :
    (prodCongrLeft e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrRight e) :=
  by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.prod_congr_left_trans_prod_comm Equiv.prodCongrLeft_trans_prodComm
-/

#print Equiv.prodCongrRight_trans_prodComm /-
@[simp]
theorem prodCongrRight_trans_prodComm :
    (prodCongrRight e).trans (prodComm _ _) = (prodComm _ _).trans (prodCongrLeft e) :=
  by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.prod_congr_right_trans_prod_comm Equiv.prodCongrRight_trans_prodComm
-/

#print Equiv.sigmaCongrRight_sigmaEquivProd /-
theorem sigmaCongrRight_sigmaEquivProd :
    (sigmaCongrRight e).trans (sigmaEquivProd α₁ β₂) =
      (sigmaEquivProd α₁ β₁).trans (prodCongrRight e) :=
  by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.sigma_congr_right_sigma_equiv_prod Equiv.sigmaCongrRight_sigmaEquivProd
-/

/- warning: equiv.sigma_equiv_prod_sigma_congr_right -> Equiv.sigmaEquivProd_sigmaCongrRight is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {β₂ : Type.{u3}} (e : α₁ -> (Equiv.{succ u2, succ u3} β₁ β₂)), Eq.{max 1 (max (max (succ u1) (succ u2)) (succ u1) (succ u3)) (max (succ u1) (succ u3)) (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u3)} (Prod.{u1, u2} α₁ β₁) (Sigma.{u1, u3} α₁ (fun (a : α₁) => β₂))) (Equiv.trans.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u3)} (Prod.{u1, u2} α₁ β₁) (Sigma.{u1, u2} α₁ (fun (_x : α₁) => β₁)) (Sigma.{u1, u3} α₁ (fun (a : α₁) => β₂)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u1, u2} α₁ (fun (_x : α₁) => β₁)) (Prod.{u1, u2} α₁ β₁) (Equiv.sigmaEquivProd.{u1, u2} α₁ β₁)) (Equiv.sigmaCongrRight.{u1, u2, u3} α₁ (fun (_x : α₁) => β₁) (fun (ᾰ : α₁) => β₂) e)) (Equiv.trans.{max (succ u1) (succ u2), max (succ u1) (succ u3), max (succ u1) (succ u3)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u3} α₁ β₂) (Sigma.{u1, u3} α₁ (fun (a : α₁) => β₂)) (Equiv.prodCongrRight.{u1, u2, u3} α₁ β₁ β₂ e) (Equiv.symm.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Sigma.{u1, u3} α₁ (fun (_x : α₁) => β₂)) (Prod.{u1, u3} α₁ β₂) (Equiv.sigmaEquivProd.{u1, u3} α₁ β₂)))
but is expected to have type
  forall {α₁ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u1}} (e : α₁ -> (Equiv.{succ u3, succ u1} β₁ β₂)), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Equiv.{max (succ u3) (succ u2), max (succ u2) (succ u1)} (Prod.{u2, u3} α₁ β₁) (Sigma.{u2, u1} α₁ (fun (a : α₁) => β₂))) (Equiv.trans.{max (succ u3) (succ u2), max (succ u3) (succ u2), max (succ u2) (succ u1)} (Prod.{u2, u3} α₁ β₁) (Sigma.{u2, u3} α₁ (fun (_x : α₁) => β₁)) (Sigma.{u2, u1} α₁ (fun (a : α₁) => β₂)) (Equiv.symm.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (Sigma.{u2, u3} α₁ (fun (_x : α₁) => β₁)) (Prod.{u2, u3} α₁ β₁) (Equiv.sigmaEquivProd.{u2, u3} α₁ β₁)) (Equiv.sigmaCongrRight.{u2, u3, u1} α₁ (fun (_x : α₁) => β₁) (fun (ᾰ : α₁) => β₂) e)) (Equiv.trans.{max (succ u3) (succ u2), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Prod.{u2, u3} α₁ β₁) (Prod.{u2, u1} α₁ β₂) (Sigma.{u2, u1} α₁ (fun (a : α₁) => β₂)) (Equiv.prodCongrRight.{u2, u3, u1} α₁ β₁ β₂ e) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Sigma.{u2, u1} α₁ (fun (_x : α₁) => β₂)) (Prod.{u2, u1} α₁ β₂) (Equiv.sigmaEquivProd.{u2, u1} α₁ β₂)))
Case conversion may be inaccurate. Consider using '#align equiv.sigma_equiv_prod_sigma_congr_right Equiv.sigmaEquivProd_sigmaCongrRightₓ'. -/
theorem sigmaEquivProd_sigmaCongrRight :
    (sigmaEquivProd α₁ β₁).symm.trans (sigmaCongrRight e) =
      (prodCongrRight e).trans (sigmaEquivProd α₁ β₂).symm :=
  by
  ext ⟨a, b⟩ : 1
  simp
#align equiv.sigma_equiv_prod_sigma_congr_right Equiv.sigmaEquivProd_sigmaCongrRight

/- warning: equiv.of_fiber_equiv -> Equiv.ofFiberEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> γ} {g : β -> γ}, (forall (c : γ), Equiv.{succ u1, succ u2} (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u3} γ (f a) c)) (Subtype.{succ u2} β (fun (b : β) => Eq.{succ u3} γ (g b) c))) -> (Equiv.{succ u1, succ u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : γ -> β}, (forall (c : β), Equiv.{succ u1, succ u3} (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) c)) (Subtype.{succ u3} γ (fun (b : γ) => Eq.{succ u2} β (g b) c))) -> (Equiv.{succ u1, succ u3} α γ)
Case conversion may be inaccurate. Consider using '#align equiv.of_fiber_equiv Equiv.ofFiberEquivₓ'. -/
-- See also `equiv.of_preimage_equiv`.
/-- A family of equivalences between fibers gives an equivalence between domains. -/
@[simps]
def ofFiberEquiv {α β γ : Type _} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) : α ≃ β :=
  (sigmaFiberEquiv f).symm.trans <| (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)
#align equiv.of_fiber_equiv Equiv.ofFiberEquiv

/- warning: equiv.of_fiber_equiv_map -> Equiv.ofFiberEquiv_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> γ} {g : β -> γ} (e : forall (c : γ), Equiv.{succ u1, succ u2} (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u3} γ (f a) c)) (Subtype.{succ u2} β (fun (b : β) => Eq.{succ u3} γ (g b) c))) (a : α), Eq.{succ u3} γ (g (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) (Equiv.ofFiberEquiv.{u1, u2, u3} α β γ (fun (a : α) => f a) (fun (b : β) => g b) e) a)) (f a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> γ} {g : β -> γ} (e : forall (c : γ), Equiv.{succ u3, succ u2} (Subtype.{succ u3} α (fun (a : α) => Eq.{succ u1} γ (f a) c)) (Subtype.{succ u2} β (fun (b : β) => Eq.{succ u1} γ (g b) c))) (a : α), Eq.{succ u1} γ (g (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α β (Equiv.instEquivLikeEquiv.{succ u3, succ u2} α β))) (Equiv.ofFiberEquiv.{u3, u1, u2} α γ β (fun (a : α) => f a) (fun (b : β) => g b) e) a)) (f a)
Case conversion may be inaccurate. Consider using '#align equiv.of_fiber_equiv_map Equiv.ofFiberEquiv_mapₓ'. -/
theorem ofFiberEquiv_map {α β γ} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) (a : α) : g (ofFiberEquiv e a) = f a :=
  (_ : { b // g b = _ }).Prop
#align equiv.of_fiber_equiv_map Equiv.ofFiberEquiv_map

/- warning: equiv.prod_shear -> Equiv.prodShear is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}}, (Equiv.{succ u1, succ u3} α₁ α₂) -> (α₁ -> (Equiv.{succ u2, succ u4} β₁ β₂)) -> (Equiv.{max (succ u1) (succ u2), max (succ u3) (succ u4)} (Prod.{u1, u2} α₁ β₁) (Prod.{u3, u4} α₂ β₂))
but is expected to have type
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}}, (Equiv.{succ u1, succ u4} α₁ β₂) -> (α₁ -> (Equiv.{succ u2, succ u3} β₁ α₂)) -> (Equiv.{max (succ u2) (succ u1), max (succ u3) (succ u4)} (Prod.{u1, u2} α₁ β₁) (Prod.{u4, u3} β₂ α₂))
Case conversion may be inaccurate. Consider using '#align equiv.prod_shear Equiv.prodShearₓ'. -/
/-- A variation on `equiv.prod_congr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simps (config := { fullyApplied := false })]
def prodShear {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂
    where
  toFun := fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2)
  invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂ <| e₁.symm y.1).symm y.2)
  left_inv := by
    rintro ⟨x₁, y₁⟩
    simp only [symm_apply_apply]
  right_inv := by
    rintro ⟨x₁, y₁⟩
    simp only [apply_symm_apply]
#align equiv.prod_shear Equiv.prodShear

end ProdCongr

namespace Perm

variable {α₁ β₁ β₂ : Type _} [DecidableEq α₁] (a : α₁) (e : Perm β₁)

#print Equiv.Perm.prodExtendRight /-
/-- `prod_extend_right a e` extends `e : perm β` to `perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
def prodExtendRight : Perm (α₁ × β₁)
    where
  toFun ab := if ab.fst = a then (a, e ab.snd) else ab
  invFun ab := if ab.fst = a then (a, e.symm ab.snd) else ab
  left_inv := by
    rintro ⟨k', x⟩
    dsimp only
    split_ifs with h <;> simp [h]
  right_inv := by
    rintro ⟨k', x⟩
    dsimp only
    split_ifs with h <;> simp [h]
#align equiv.perm.prod_extend_right Equiv.Perm.prodExtendRight
-/

#print Equiv.Perm.prodExtendRight_apply_eq /-
@[simp]
theorem prodExtendRight_apply_eq (b : β₁) : prodExtendRight a e (a, b) = (a, e b) :=
  if_pos rfl
#align equiv.perm.prod_extend_right_apply_eq Equiv.Perm.prodExtendRight_apply_eq
-/

/- warning: equiv.perm.prod_extend_right_apply_ne -> Equiv.Perm.prodExtendRight_apply_ne is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α₁] (e : Equiv.Perm.{succ u2} β₁) {a : α₁} {a' : α₁}, (Ne.{succ u1} α₁ a' a) -> (forall (b : β₁), Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} α₁ β₁) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Prod.{u1, u2} α₁ β₁)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u2} α₁ β₁)) => (Prod.{u1, u2} α₁ β₁) -> (Prod.{u1, u2} α₁ β₁)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u2} α₁ β₁)) (Equiv.Perm.prodExtendRight.{u1, u2} α₁ β₁ (fun (a : α₁) (b : α₁) => _inst_1 a b) a e) (Prod.mk.{u1, u2} α₁ β₁ a' b)) (Prod.mk.{u1, u2} α₁ β₁ a' b))
but is expected to have type
  forall {α₁ : Type.{u2}} {β₁ : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α₁] (e : Equiv.Perm.{succ u1} β₁) {a : α₁} {a' : α₁}, (Ne.{succ u2} α₁ a' a) -> (forall (b : β₁), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α₁ β₁) => Prod.{u2, u1} α₁ β₁) (Prod.mk.{u2, u1} α₁ β₁ a' b)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Prod.{u2, u1} α₁ β₁)) (Prod.{u2, u1} α₁ β₁) (fun (_x : Prod.{u2, u1} α₁ β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α₁ β₁) => Prod.{u2, u1} α₁ β₁) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Prod.{u2, u1} α₁ β₁)) (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u1} α₁ β₁) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Prod.{u2, u1} α₁ β₁)) (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u1} α₁ β₁) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u1} α₁ β₁)))) (Equiv.Perm.prodExtendRight.{u2, u1} α₁ β₁ (fun (a : α₁) (b : α₁) => _inst_1 a b) a e) (Prod.mk.{u2, u1} α₁ β₁ a' b)) (Prod.mk.{u2, u1} α₁ β₁ a' b))
Case conversion may be inaccurate. Consider using '#align equiv.perm.prod_extend_right_apply_ne Equiv.Perm.prodExtendRight_apply_neₓ'. -/
theorem prodExtendRight_apply_ne {a a' : α₁} (h : a' ≠ a) (b : β₁) :
    prodExtendRight a e (a', b) = (a', b) :=
  if_neg h
#align equiv.perm.prod_extend_right_apply_ne Equiv.Perm.prodExtendRight_apply_ne

#print Equiv.Perm.eq_of_prodExtendRight_ne /-
theorem eq_of_prodExtendRight_ne {e : Perm β₁} {a a' : α₁} {b : β₁}
    (h : prodExtendRight a e (a', b) ≠ (a', b)) : a' = a :=
  by
  contrapose! h
  exact prod_extend_right_apply_ne _ h _
#align equiv.perm.eq_of_prod_extend_right_ne Equiv.Perm.eq_of_prodExtendRight_ne
-/

/- warning: equiv.perm.fst_prod_extend_right -> Equiv.Perm.fst_prodExtendRight is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α₁] (a : α₁) (e : Equiv.Perm.{succ u2} β₁) (ab : Prod.{u1, u2} α₁ β₁), Eq.{succ u1} α₁ (Prod.fst.{u1, u2} α₁ β₁ (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Prod.{u1, u2} α₁ β₁)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u2} α₁ β₁)) => (Prod.{u1, u2} α₁ β₁) -> (Prod.{u1, u2} α₁ β₁)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u1, u2} α₁ β₁) (Prod.{u1, u2} α₁ β₁)) (Equiv.Perm.prodExtendRight.{u1, u2} α₁ β₁ (fun (a : α₁) (b : α₁) => _inst_1 a b) a e) ab)) (Prod.fst.{u1, u2} α₁ β₁ ab)
but is expected to have type
  forall {α₁ : Type.{u2}} {β₁ : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α₁] (a : α₁) (e : Equiv.Perm.{succ u1} β₁) (ab : Prod.{u2, u1} α₁ β₁), Eq.{succ u2} α₁ (Prod.fst.{u2, u1} α₁ β₁ (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Prod.{u2, u1} α₁ β₁)) (Prod.{u2, u1} α₁ β₁) (fun (_x : Prod.{u2, u1} α₁ β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α₁ β₁) => Prod.{u2, u1} α₁ β₁) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Prod.{u2, u1} α₁ β₁)) (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u1} α₁ β₁) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Prod.{u2, u1} α₁ β₁)) (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u1} α₁ β₁) (Equiv.instEquivLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prod.{u2, u1} α₁ β₁) (Prod.{u2, u1} α₁ β₁)))) (Equiv.Perm.prodExtendRight.{u2, u1} α₁ β₁ (fun (a : α₁) (b : α₁) => _inst_1 a b) a e) ab)) (Prod.fst.{u2, u1} α₁ β₁ ab)
Case conversion may be inaccurate. Consider using '#align equiv.perm.fst_prod_extend_right Equiv.Perm.fst_prodExtendRightₓ'. -/
@[simp]
theorem fst_prodExtendRight (ab : α₁ × β₁) : (prodExtendRight a e ab).fst = ab.fst :=
  by
  rw [prod_extend_right, coe_fn_mk]
  split_ifs with h
  · rw [h]
  · rfl
#align equiv.perm.fst_prod_extend_right Equiv.Perm.fst_prodExtendRight

end Perm

section

#print Equiv.arrowProdEquivProdArrow /-
/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrowProdEquivProdArrow (α β γ : Type _) : (γ → α × β) ≃ (γ → α) × (γ → β) :=
  ⟨fun f => (fun c => (f c).1, fun c => (f c).2), fun p c => (p.1 c, p.2 c), fun f =>
    funext fun c => Prod.mk.eta, fun p => by
    cases p
    rfl⟩
#align equiv.arrow_prod_equiv_prod_arrow Equiv.arrowProdEquivProdArrow
-/

open Sum

#print Equiv.sumArrowEquivProdArrow /-
/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sumArrowEquivProdArrow (α β γ : Type _) : (Sum α β → γ) ≃ (α → γ) × (β → γ) :=
  ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2, fun f => by ext ⟨⟩ <;> rfl, fun p =>
    by
    cases p
    rfl⟩
#align equiv.sum_arrow_equiv_prod_arrow Equiv.sumArrowEquivProdArrow
-/

/- warning: equiv.sum_arrow_equiv_prod_arrow_apply_fst -> Equiv.sumArrowEquivProdArrow_apply_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : (Sum.{u1, u2} α β) -> γ) (a : α), Eq.{succ u3} γ (Prod.fst.{max u1 u3, max u2 u3} (α -> γ) (β -> γ) (coeFn.{max 1 (max (max (max (succ u1) (succ u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3))) (max (succ (max u1 u3)) (succ (max u2 u3))) (max (succ u1) (succ u2)) (succ u3), max (max (max (succ u1) (succ u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3))} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} ((Sum.{u1, u2} α β) -> γ) (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ))) (fun (_x : Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} ((Sum.{u1, u2} α β) -> γ) (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ))) => ((Sum.{u1, u2} α β) -> γ) -> (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ))) (Equiv.hasCoeToFun.{max (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} ((Sum.{u1, u2} α β) -> γ) (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ))) (Equiv.sumArrowEquivProdArrow.{u1, u2, u3} α β γ) f) a) (f (Sum.inl.{u1, u2} α β a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : (Sum.{u3, u2} α β) -> γ) (a : α), Eq.{succ u1} γ (Prod.fst.{max u3 u1, max u2 u1} (α -> γ) (β -> γ) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (succ (max u2 u1)) (succ (max u3 u1))} ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ))) ((Sum.{u3, u2} α β) -> γ) (fun (_x : (Sum.{u3, u2} α β) -> γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : (Sum.{u3, u2} α β) -> γ) => Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ)) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (succ (max u2 u1)) (succ (max u3 u1))} ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ))) ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ)) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (succ (max u2 u1)) (succ (max u3 u1))} ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ))) ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ)) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ))))) (Equiv.sumArrowEquivProdArrow.{u3, u2, u1} α β γ) f) a) (f (Sum.inl.{u3, u2} α β a))
Case conversion may be inaccurate. Consider using '#align equiv.sum_arrow_equiv_prod_arrow_apply_fst Equiv.sumArrowEquivProdArrow_apply_fstₓ'. -/
@[simp]
theorem sumArrowEquivProdArrow_apply_fst {α β γ} (f : Sum α β → γ) (a : α) :
    (sumArrowEquivProdArrow α β γ f).1 a = f (inl a) :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_apply_fst Equiv.sumArrowEquivProdArrow_apply_fst

/- warning: equiv.sum_arrow_equiv_prod_arrow_apply_snd -> Equiv.sumArrowEquivProdArrow_apply_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : (Sum.{u1, u2} α β) -> γ) (b : β), Eq.{succ u3} γ (Prod.snd.{max u1 u3, max u2 u3} (α -> γ) (β -> γ) (coeFn.{max 1 (max (max (max (succ u1) (succ u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3))) (max (succ (max u1 u3)) (succ (max u2 u3))) (max (succ u1) (succ u2)) (succ u3), max (max (max (succ u1) (succ u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3))} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} ((Sum.{u1, u2} α β) -> γ) (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ))) (fun (_x : Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} ((Sum.{u1, u2} α β) -> γ) (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ))) => ((Sum.{u1, u2} α β) -> γ) -> (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ))) (Equiv.hasCoeToFun.{max (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} ((Sum.{u1, u2} α β) -> γ) (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ))) (Equiv.sumArrowEquivProdArrow.{u1, u2, u3} α β γ) f) b) (f (Sum.inr.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : (Sum.{u3, u2} α β) -> γ) (b : β), Eq.{succ u1} γ (Prod.snd.{max u3 u1, max u2 u1} (α -> γ) (β -> γ) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (succ (max u2 u1)) (succ (max u3 u1))} ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ))) ((Sum.{u3, u2} α β) -> γ) (fun (_x : (Sum.{u3, u2} α β) -> γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : (Sum.{u3, u2} α β) -> γ) => Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ)) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (succ (max u2 u1)) (succ (max u3 u1))} ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ))) ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ)) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (succ (max u2 u1)) (succ (max u3 u1))} ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ))) ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ)) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u3, u2} α β) -> γ) (Prod.{max u3 u1, max u2 u1} (α -> γ) (β -> γ))))) (Equiv.sumArrowEquivProdArrow.{u3, u2, u1} α β γ) f) b) (f (Sum.inr.{u3, u2} α β b))
Case conversion may be inaccurate. Consider using '#align equiv.sum_arrow_equiv_prod_arrow_apply_snd Equiv.sumArrowEquivProdArrow_apply_sndₓ'. -/
@[simp]
theorem sumArrowEquivProdArrow_apply_snd {α β γ} (f : Sum α β → γ) (b : β) :
    (sumArrowEquivProdArrow α β γ f).2 b = f (inr b) :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_apply_snd Equiv.sumArrowEquivProdArrow_apply_snd

/- warning: equiv.sum_arrow_equiv_prod_arrow_symm_apply_inl -> Equiv.sumArrowEquivProdArrow_symm_apply_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> γ) (g : β -> γ) (a : α), Eq.{succ u3} γ (coeFn.{max 1 (max (max (succ (max u1 u3)) (succ (max u2 u3))) (max (succ u1) (succ u2)) (succ u3)) (max (max (succ u1) (succ u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ (max u1 u3)) (succ (max u2 u3))) (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ u1) (succ u2)) (succ u3)} (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) ((Sum.{u1, u2} α β) -> γ)) (fun (_x : Equiv.{max (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ u1) (succ u2)) (succ u3)} (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) ((Sum.{u1, u2} α β) -> γ)) => (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) -> (Sum.{u1, u2} α β) -> γ) (Equiv.hasCoeToFun.{max (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ u1) (succ u2)) (succ u3)} (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) ((Sum.{u1, u2} α β) -> γ)) (Equiv.symm.{max (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} ((Sum.{u1, u2} α β) -> γ) (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) (Equiv.sumArrowEquivProdArrow.{u1, u2, u3} α β γ)) (Prod.mk.{max u1 u3, max u2 u3} (α -> γ) (β -> γ) f g) (Sum.inl.{u1, u2} α β a)) (f a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β) (g : γ -> β) (a : α), Eq.{succ u2} β (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β)) (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) (fun (_x : Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) => (Sum.{u3, u1} α γ) -> β) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β)) (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β)) (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β)))) (Equiv.symm.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} ((Sum.{u3, u1} α γ) -> β) (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) (Equiv.sumArrowEquivProdArrow.{u3, u1, u2} α γ β)) (Prod.mk.{max u2 u3, max u2 u1} (α -> β) (γ -> β) f g) (Sum.inl.{u3, u1} α γ a)) (f a)
Case conversion may be inaccurate. Consider using '#align equiv.sum_arrow_equiv_prod_arrow_symm_apply_inl Equiv.sumArrowEquivProdArrow_symm_apply_inlₓ'. -/
@[simp]
theorem sumArrowEquivProdArrow_symm_apply_inl {α β γ} (f : α → γ) (g : β → γ) (a : α) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inl a) = f a :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_symm_apply_inl Equiv.sumArrowEquivProdArrow_symm_apply_inl

/- warning: equiv.sum_arrow_equiv_prod_arrow_symm_apply_inr -> Equiv.sumArrowEquivProdArrow_symm_apply_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> γ) (g : β -> γ) (b : β), Eq.{succ u3} γ (coeFn.{max 1 (max (max (succ (max u1 u3)) (succ (max u2 u3))) (max (succ u1) (succ u2)) (succ u3)) (max (max (succ u1) (succ u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ (max u1 u3)) (succ (max u2 u3))) (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ u1) (succ u2)) (succ u3)} (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) ((Sum.{u1, u2} α β) -> γ)) (fun (_x : Equiv.{max (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ u1) (succ u2)) (succ u3)} (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) ((Sum.{u1, u2} α β) -> γ)) => (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) -> (Sum.{u1, u2} α β) -> γ) (Equiv.hasCoeToFun.{max (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ u1) (succ u2)) (succ u3)} (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) ((Sum.{u1, u2} α β) -> γ)) (Equiv.symm.{max (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} ((Sum.{u1, u2} α β) -> γ) (Prod.{max u1 u3, max u2 u3} (α -> γ) (β -> γ)) (Equiv.sumArrowEquivProdArrow.{u1, u2, u3} α β γ)) (Prod.mk.{max u1 u3, max u2 u3} (α -> γ) (β -> γ) f g) (Sum.inr.{u1, u2} α β b)) (g b)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β) (g : γ -> β) (b : γ), Eq.{succ u2} β (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β)) (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) (fun (_x : Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) => (Sum.{u3, u1} α γ) -> β) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β)) (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β)) (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) ((Sum.{u3, u1} α γ) -> β)))) (Equiv.symm.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} ((Sum.{u3, u1} α γ) -> β) (Prod.{max u3 u2, max u1 u2} (α -> β) (γ -> β)) (Equiv.sumArrowEquivProdArrow.{u3, u1, u2} α γ β)) (Prod.mk.{max u2 u3, max u2 u1} (α -> β) (γ -> β) f g) (Sum.inr.{u3, u1} α γ b)) (g b)
Case conversion may be inaccurate. Consider using '#align equiv.sum_arrow_equiv_prod_arrow_symm_apply_inr Equiv.sumArrowEquivProdArrow_symm_apply_inrₓ'. -/
@[simp]
theorem sumArrowEquivProdArrow_symm_apply_inr {α β γ} (f : α → γ) (g : β → γ) (b : β) :
    ((sumArrowEquivProdArrow α β γ).symm (f, g)) (inr b) = g b :=
  rfl
#align equiv.sum_arrow_equiv_prod_arrow_symm_apply_inr Equiv.sumArrowEquivProdArrow_symm_apply_inr

#print Equiv.sumProdDistrib /-
/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sumProdDistrib (α β γ : Sort _) : Sum α β × γ ≃ Sum (α × γ) (β × γ) :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2), fun s =>
    s.elim (Prod.map inl id) (Prod.map inr id), by rintro ⟨_ | _, _⟩ <;> rfl, by
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩
#align equiv.sum_prod_distrib Equiv.sumProdDistrib
-/

/- warning: equiv.sum_prod_distrib_apply_left -> Equiv.sumProdDistrib_apply_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : α) (c : γ), Eq.{max (succ (max u1 u3)) (succ (max u2 u3))} (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (coeFn.{max 1 (max (max (succ (max u1 u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3))) (max (succ (max u1 u3)) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3), max (max (succ (max u1 u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3))} (Equiv.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ))) => (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) -> (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ))) (Equiv.sumProdDistrib.{u1, u2, u3} α β γ) (Prod.mk.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.inl.{u1, u2} α β a) c)) (Sum.inl.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ) (Prod.mk.{u1, u3} α γ a c))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (a : α) (c : β), Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) => Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Prod.mk.{max u1 u3, u2} (Sum.{u3, u1} α γ) β (Sum.inl.{u3, u1} α γ a) c)) (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (succ u2) (succ (max u1 u3)), max (succ (max u2 u1)) (succ (max u2 u3))} (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β))) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (fun (_x : Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) => Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (succ u2) (succ (max u1 u3)), max (succ (max u2 u1)) (succ (max u2 u3))} (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β))) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (succ u2) (succ (max u1 u3)), max (succ (max u2 u1)) (succ (max u2 u3))} (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β))) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β))))) (Equiv.sumProdDistrib.{u3, u1, u2} α γ β) (Prod.mk.{max u1 u3, u2} (Sum.{u3, u1} α γ) β (Sum.inl.{u3, u1} α γ a) c)) (Sum.inl.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β) (Prod.mk.{u3, u2} α β a c))
Case conversion may be inaccurate. Consider using '#align equiv.sum_prod_distrib_apply_left Equiv.sumProdDistrib_apply_leftₓ'. -/
@[simp]
theorem sumProdDistrib_apply_left {α β γ} (a : α) (c : γ) :
    sumProdDistrib α β γ (Sum.inl a, c) = Sum.inl (a, c) :=
  rfl
#align equiv.sum_prod_distrib_apply_left Equiv.sumProdDistrib_apply_left

/- warning: equiv.sum_prod_distrib_apply_right -> Equiv.sumProdDistrib_apply_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (b : β) (c : γ), Eq.{max (succ (max u1 u3)) (succ (max u2 u3))} (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (coeFn.{max 1 (max (max (succ (max u1 u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3))) (max (succ (max u1 u3)) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3), max (max (succ (max u1 u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3))} (Equiv.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ))) => (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) -> (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ))) (Equiv.sumProdDistrib.{u1, u2, u3} α β γ) (Prod.mk.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.inr.{u1, u2} α β b) c)) (Sum.inr.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ) (Prod.mk.{u2, u3} β γ b c))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (b : α) (c : β), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) => Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Prod.mk.{max u3 u1, u2} (Sum.{u1, u3} γ α) β (Sum.inr.{u1, u3} γ α b) c)) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (succ u2) (succ (max u3 u1)), max (succ (max u2 u3)) (succ (max u2 u1))} (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β))) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (fun (_x : Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) => Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (succ u2) (succ (max u3 u1)), max (succ (max u2 u3)) (succ (max u2 u1))} (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β))) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (succ u2) (succ (max u3 u1)), max (succ (max u2 u3)) (succ (max u2 u1))} (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β))) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β))))) (Equiv.sumProdDistrib.{u1, u3, u2} γ α β) (Prod.mk.{max u3 u1, u2} (Sum.{u1, u3} γ α) β (Sum.inr.{u1, u3} γ α b) c)) (Sum.inr.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β) (Prod.mk.{u3, u2} α β b c))
Case conversion may be inaccurate. Consider using '#align equiv.sum_prod_distrib_apply_right Equiv.sumProdDistrib_apply_rightₓ'. -/
@[simp]
theorem sumProdDistrib_apply_right {α β γ} (b : β) (c : γ) :
    sumProdDistrib α β γ (Sum.inr b, c) = Sum.inr (b, c) :=
  rfl
#align equiv.sum_prod_distrib_apply_right Equiv.sumProdDistrib_apply_right

/- warning: equiv.sum_prod_distrib_symm_apply_left -> Equiv.sumProdDistrib_symm_apply_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : Prod.{u1, u3} α γ), Eq.{max (succ (max u1 u2)) (succ u3)} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (coeFn.{max 1 (max (max (succ (max u1 u3)) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)) (max (succ (max u1 u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ (max u1 u3)) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)} (Equiv.{max (succ (max u1 u3)) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (fun (_x : Equiv.{max (succ (max u1 u3)) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) => (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) -> (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.hasCoeToFun.{max (succ (max u1 u3)) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.symm.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Equiv.sumProdDistrib.{u1, u2, u3} α β γ)) (Sum.inl.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ) a)) (Prod.mk.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.inl.{u1, u2} α β (Prod.fst.{u1, u3} α γ a)) (Prod.snd.{u1, u3} α γ a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (a : Prod.{u3, u2} α β), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) => Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Sum.inl.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β) a)) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β)) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (fun (_x : Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) => Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β)) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β)) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β)))) (Equiv.symm.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Prod.{max u1 u3, u2} (Sum.{u3, u1} α γ) β) (Sum.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β)) (Equiv.sumProdDistrib.{u3, u1, u2} α γ β)) (Sum.inl.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β) a)) (Prod.mk.{max u1 u3, u2} (Sum.{u3, u1} α γ) β (Sum.inl.{u3, u1} α γ (Prod.fst.{u3, u2} α β a)) (Prod.snd.{u3, u2} α β a))
Case conversion may be inaccurate. Consider using '#align equiv.sum_prod_distrib_symm_apply_left Equiv.sumProdDistrib_symm_apply_leftₓ'. -/
@[simp]
theorem sumProdDistrib_symm_apply_left {α β γ} (a : α × γ) :
    (sumProdDistrib α β γ).symm (inl a) = (inl a.1, a.2) :=
  rfl
#align equiv.sum_prod_distrib_symm_apply_left Equiv.sumProdDistrib_symm_apply_left

/- warning: equiv.sum_prod_distrib_symm_apply_right -> Equiv.sumProdDistrib_symm_apply_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (b : Prod.{u2, u3} β γ), Eq.{max (succ (max u1 u2)) (succ u3)} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (coeFn.{max 1 (max (max (succ (max u1 u3)) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)) (max (succ (max u1 u2)) (succ u3)) (succ (max u1 u3)) (succ (max u2 u3)), max (max (succ (max u1 u3)) (succ (max u2 u3))) (succ (max u1 u2)) (succ u3)} (Equiv.{max (succ (max u1 u3)) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (fun (_x : Equiv.{max (succ (max u1 u3)) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) => (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) -> (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.hasCoeToFun.{max (succ (max u1 u3)) (succ (max u2 u3)), max (succ (max u1 u2)) (succ u3)} (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ)) (Equiv.symm.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Equiv.sumProdDistrib.{u1, u2, u3} α β γ)) (Sum.inr.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ) b)) (Prod.mk.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.inr.{u1, u2} α β (Prod.fst.{u2, u3} β γ b)) (Prod.snd.{u2, u3} β γ b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (b : Prod.{u3, u2} α β), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) => Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Sum.inr.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β) b)) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β)) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (fun (_x : Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) => Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β)) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β)) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β)))) (Equiv.symm.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Prod.{max u3 u1, u2} (Sum.{u1, u3} γ α) β) (Sum.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β)) (Equiv.sumProdDistrib.{u1, u3, u2} γ α β)) (Sum.inr.{max u2 u1, max u2 u3} (Prod.{u1, u2} γ β) (Prod.{u3, u2} α β) b)) (Prod.mk.{max u3 u1, u2} (Sum.{u1, u3} γ α) β (Sum.inr.{u1, u3} γ α (Prod.fst.{u3, u2} α β b)) (Prod.snd.{u3, u2} α β b))
Case conversion may be inaccurate. Consider using '#align equiv.sum_prod_distrib_symm_apply_right Equiv.sumProdDistrib_symm_apply_rightₓ'. -/
@[simp]
theorem sumProdDistrib_symm_apply_right {α β γ} (b : β × γ) :
    (sumProdDistrib α β γ).symm (inr b) = (inr b.1, b.2) :=
  rfl
#align equiv.sum_prod_distrib_symm_apply_right Equiv.sumProdDistrib_symm_apply_right

#print Equiv.prodSumDistrib /-
/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prodSumDistrib (α β γ : Sort _) : α × Sum β γ ≃ Sum (α × β) (α × γ) :=
  calc
    α × Sum β γ ≃ Sum β γ × α := prodComm _ _
    _ ≃ Sum (β × α) (γ × α) := sumProdDistrib _ _ _
    _ ≃ Sum (α × β) (α × γ) := sumCongr (prodComm _ _) (prodComm _ _)
    
#align equiv.prod_sum_distrib Equiv.prodSumDistrib
-/

/- warning: equiv.prod_sum_distrib_apply_left -> Equiv.prodSumDistrib_apply_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : α) (b : β), Eq.{max (succ (max u1 u2)) (succ (max u1 u3))} (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (coeFn.{max 1 (max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ (max u1 u3))) (max (succ (max u1 u2)) (succ (max u1 u3))) (succ u1) (succ (max u2 u3)), max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ (max u1 u3))} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ))) (fun (_x : Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ))) => (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) -> (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ))) (Equiv.hasCoeToFun.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ))) (Equiv.prodSumDistrib.{u1, u2, u3} α β γ) (Prod.mk.{u1, max u2 u3} α (Sum.{u2, u3} β γ) a (Sum.inl.{u2, u3} β γ b))) (Sum.inl.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (a : α) (b : β), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Prod.mk.{u3, max u1 u2} α (Sum.{u2, u1} β γ) a (Sum.inl.{u2, u1} β γ b))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ))) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (fun (_x : Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) => Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) _x) (EmbeddingLike.toFunLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ))) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (EquivLike.toEmbeddingLike.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ))) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Equiv.instEquivLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ))))) (Equiv.prodSumDistrib.{u3, u2, u1} α β γ) (Prod.mk.{u3, max u1 u2} α (Sum.{u2, u1} β γ) a (Sum.inl.{u2, u1} β γ b))) (Sum.inl.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ) (Prod.mk.{u3, u2} α β a b))
Case conversion may be inaccurate. Consider using '#align equiv.prod_sum_distrib_apply_left Equiv.prodSumDistrib_apply_leftₓ'. -/
@[simp]
theorem prodSumDistrib_apply_left {α β γ} (a : α) (b : β) :
    prodSumDistrib α β γ (a, Sum.inl b) = Sum.inl (a, b) :=
  rfl
#align equiv.prod_sum_distrib_apply_left Equiv.prodSumDistrib_apply_left

/- warning: equiv.prod_sum_distrib_apply_right -> Equiv.prodSumDistrib_apply_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : α) (c : γ), Eq.{max (succ (max u1 u2)) (succ (max u1 u3))} (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (coeFn.{max 1 (max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ (max u1 u3))) (max (succ (max u1 u2)) (succ (max u1 u3))) (succ u1) (succ (max u2 u3)), max (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ (max u1 u3))} (Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ))) (fun (_x : Equiv.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ))) => (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) -> (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ))) (Equiv.hasCoeToFun.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ))) (Equiv.prodSumDistrib.{u1, u2, u3} α β γ) (Prod.mk.{u1, max u2 u3} α (Sum.{u2, u3} β γ) a (Sum.inr.{u2, u3} β γ c))) (Sum.inr.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ) (Prod.mk.{u1, u3} α γ a c))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (a : α) (c : β), Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) => Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Prod.mk.{u3, max u2 u1} α (Sum.{u1, u2} γ β) a (Sum.inr.{u1, u2} γ β c))) (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (succ (max u2 u1)) (succ u3), max (succ (max u2 u3)) (succ (max u1 u3))} (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β))) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (fun (_x : Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) => Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (succ (max u2 u1)) (succ u3), max (succ (max u2 u3)) (succ (max u1 u3))} (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β))) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (succ (max u2 u1)) (succ u3), max (succ (max u2 u3)) (succ (max u1 u3))} (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β))) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β))))) (Equiv.prodSumDistrib.{u3, u1, u2} α γ β) (Prod.mk.{u3, max u2 u1} α (Sum.{u1, u2} γ β) a (Sum.inr.{u1, u2} γ β c))) (Sum.inr.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β) (Prod.mk.{u3, u2} α β a c))
Case conversion may be inaccurate. Consider using '#align equiv.prod_sum_distrib_apply_right Equiv.prodSumDistrib_apply_rightₓ'. -/
@[simp]
theorem prodSumDistrib_apply_right {α β γ} (a : α) (c : γ) :
    prodSumDistrib α β γ (a, Sum.inr c) = Sum.inr (a, c) :=
  rfl
#align equiv.prod_sum_distrib_apply_right Equiv.prodSumDistrib_apply_right

/- warning: equiv.prod_sum_distrib_symm_apply_left -> Equiv.prodSumDistrib_symm_apply_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : Prod.{u1, u2} α β), Eq.{max (succ u1) (succ (max u2 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (coeFn.{max 1 (max (max (succ (max u1 u2)) (succ (max u1 u3))) (succ u1) (succ (max u2 u3))) (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ (max u1 u3)), max (max (succ (max u1 u2)) (succ (max u1 u3))) (succ u1) (succ (max u2 u3))} (Equiv.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) => (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) -> (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.symm.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Equiv.prodSumDistrib.{u1, u2, u3} α β γ)) (Sum.inl.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ) a)) (Prod.mk.{u1, max u2 u3} α (Sum.{u2, u3} β γ) (Prod.fst.{u1, u2} α β a) (Sum.inl.{u2, u3} β γ (Prod.snd.{u1, u2} α β a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (a : Prod.{u3, u2} α β), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) => Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.inl.{max u2 u3, max u3 u1} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ) a)) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (fun (_x : Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) => Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ))) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ))))) (Equiv.symm.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Prod.{u3, max u1 u2} α (Sum.{u2, u1} β γ)) (Sum.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ)) (Equiv.prodSumDistrib.{u3, u2, u1} α β γ)) (Sum.inl.{max u2 u3, max u3 u1} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ) a)) (Prod.mk.{u3, max u1 u2} α (Sum.{u2, u1} β γ) (Prod.fst.{u3, u2} α β a) (Sum.inl.{u2, u1} β γ (Prod.snd.{u3, u2} α β a)))
Case conversion may be inaccurate. Consider using '#align equiv.prod_sum_distrib_symm_apply_left Equiv.prodSumDistrib_symm_apply_leftₓ'. -/
@[simp]
theorem prodSumDistrib_symm_apply_left {α β γ} (a : α × β) :
    (prodSumDistrib α β γ).symm (inl a) = (a.1, inl a.2) :=
  rfl
#align equiv.prod_sum_distrib_symm_apply_left Equiv.prodSumDistrib_symm_apply_left

/- warning: equiv.prod_sum_distrib_symm_apply_right -> Equiv.prodSumDistrib_symm_apply_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : Prod.{u1, u3} α γ), Eq.{max (succ u1) (succ (max u2 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (coeFn.{max 1 (max (max (succ (max u1 u2)) (succ (max u1 u3))) (succ u1) (succ (max u2 u3))) (max (succ u1) (succ (max u2 u3))) (succ (max u1 u2)) (succ (max u1 u3)), max (max (succ (max u1 u2)) (succ (max u1 u3))) (succ u1) (succ (max u2 u3))} (Equiv.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) => (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) -> (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ u1) (succ (max u2 u3))} (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ))) (Equiv.symm.{max (succ u1) (succ (max u2 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Equiv.prodSumDistrib.{u1, u2, u3} α β γ)) (Sum.inr.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ) a)) (Prod.mk.{u1, max u2 u3} α (Sum.{u2, u3} β γ) (Prod.fst.{u1, u3} α γ a) (Sum.inr.{u2, u3} β γ (Prod.snd.{u1, u3} α γ a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (a : Prod.{u3, u2} α β), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) => Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Sum.inr.{max u3 u1, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β) a)) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β))) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (fun (_x : Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) => Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) _x) (EmbeddingLike.toFunLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β))) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (EquivLike.toEmbeddingLike.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Equiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β))) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Equiv.instEquivLikeEquiv.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β))))) (Equiv.symm.{max (max (succ u2) (succ u3)) (succ u1), max (max (succ u2) (succ u3)) (succ u1)} (Prod.{u3, max u2 u1} α (Sum.{u1, u2} γ β)) (Sum.{max u1 u3, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β)) (Equiv.prodSumDistrib.{u3, u1, u2} α γ β)) (Sum.inr.{max u3 u1, max u2 u3} (Prod.{u3, u1} α γ) (Prod.{u3, u2} α β) a)) (Prod.mk.{u3, max u2 u1} α (Sum.{u1, u2} γ β) (Prod.fst.{u3, u2} α β a) (Sum.inr.{u1, u2} γ β (Prod.snd.{u3, u2} α β a)))
Case conversion may be inaccurate. Consider using '#align equiv.prod_sum_distrib_symm_apply_right Equiv.prodSumDistrib_symm_apply_rightₓ'. -/
@[simp]
theorem prodSumDistrib_symm_apply_right {α β γ} (a : α × γ) :
    (prodSumDistrib α β γ).symm (inr a) = (a.1, inr a.2) :=
  rfl
#align equiv.prod_sum_distrib_symm_apply_right Equiv.prodSumDistrib_symm_apply_right

#print Equiv.sigmaSumDistrib /-
/-- An indexed sum of disjoint sums of types is equivalent to the sum of the indexed sums. -/
@[simps]
def sigmaSumDistrib {ι : Type _} (α β : ι → Type _) :
    (Σi, Sum (α i) (β i)) ≃ Sum (Σi, α i) (Σi, β i) :=
  ⟨fun p => p.2.map (Sigma.mk p.1) (Sigma.mk p.1),
    Sum.elim (Sigma.map id fun _ => Sum.inl) (Sigma.map id fun _ => Sum.inr), fun p => by
    rcases p with ⟨i, a | b⟩ <;> rfl, fun p => by rcases p with (⟨i, a⟩ | ⟨i, b⟩) <;> rfl⟩
#align equiv.sigma_sum_distrib Equiv.sigmaSumDistrib
-/

#print Equiv.sigmaProdDistrib /-
/-- The product of an indexed sum of types (formally, a `sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigmaProdDistrib {ι : Type _} (α : ι → Type _) (β : Type _) : (Σi, α i) × β ≃ Σi, α i × β :=
  ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2), fun p =>
    by
    rcases p with ⟨⟨_, _⟩, _⟩
    rfl, fun p => by
    rcases p with ⟨_, ⟨_, _⟩⟩
    rfl⟩
#align equiv.sigma_prod_distrib Equiv.sigmaProdDistrib
-/

#print Equiv.sigmaNatSucc /-
/-- An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`. -/
def sigmaNatSucc (f : ℕ → Type u) : (Σn, f n) ≃ Sum (f 0) (Σn, f (n + 1)) :=
  ⟨fun x =>
    @Sigma.casesOn ℕ f (fun _ => Sum (f 0) (Σn, f (n + 1))) x fun n =>
      @Nat.casesOn (fun i => f i → Sum (f 0) (Σn : ℕ, f (n + 1))) n (fun x : f 0 => Sum.inl x)
        fun (n : ℕ) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by
    rintro (x | ⟨n, x⟩) <;> rfl⟩
#align equiv.sigma_nat_succ Equiv.sigmaNatSucc
-/

#print Equiv.boolProdEquivSum /-
/-- The product `bool × α` is equivalent to `α ⊕ α`. -/
@[simps]
def boolProdEquivSum (α : Type u) : Bool × α ≃ Sum α α
    where
  toFun p := cond p.1 (inr p.2) (inl p.2)
  invFun := Sum.elim (Prod.mk false) (Prod.mk true)
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl
#align equiv.bool_prod_equiv_sum Equiv.boolProdEquivSum
-/

#print Equiv.boolArrowEquivProd /-
/-- The function type `bool → α` is equivalent to `α × α`. -/
@[simps]
def boolArrowEquivProd (α : Type u) : (Bool → α) ≃ α × α
    where
  toFun f := (f true, f false)
  invFun p b := cond b p.1 p.2
  left_inv f := funext <| Bool.forall_bool.2 ⟨rfl, rfl⟩
  right_inv := fun ⟨x, y⟩ => rfl
#align equiv.bool_arrow_equiv_prod Equiv.boolArrowEquivProd
-/

end

section

open Sum Nat

#print Equiv.natEquivNatSumPUnit /-
/-- The set of natural numbers is equivalent to `ℕ ⊕ punit`. -/
def natEquivNatSumPUnit : ℕ ≃ Sum ℕ PUnit.{u + 1}
    where
  toFun n := Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl
#align equiv.nat_equiv_nat_sum_punit Equiv.natEquivNatSumPUnit
-/

#print Equiv.natSumPUnitEquivNat /-
/-- `ℕ ⊕ punit` is equivalent to `ℕ`. -/
def natSumPUnitEquivNat : Sum ℕ PUnit.{u + 1} ≃ ℕ :=
  natEquivNatSumPUnit.symm
#align equiv.nat_sum_punit_equiv_nat Equiv.natSumPUnitEquivNat
-/

#print Equiv.intEquivNatSumNat /-
/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def intEquivNatSumNat : ℤ ≃ Sum ℕ ℕ
    where
  toFun z := Int.casesOn z inl inr
  invFun := Sum.elim coe Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
  right_inv := by rintro (m | n) <;> rfl
#align equiv.int_equiv_nat_sum_nat Equiv.intEquivNatSumNat
-/

end

#print Equiv.listEquivOfEquiv /-
/-- An equivalence between `α` and `β` generates an equivalence between `list α` and `list β`. -/
def listEquivOfEquiv {α β : Type _} (e : α ≃ β) : List α ≃ List β
    where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]
#align equiv.list_equiv_of_equiv Equiv.listEquivOfEquiv
-/

#print Equiv.uniqueCongr /-
/-- If `α` is equivalent to `β`, then `unique α` is equivalent to `unique β`. -/
def uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β
    where
  toFun h := @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv.unique_congr Equiv.uniqueCongr
-/

/- warning: equiv.is_empty_congr -> Equiv.isEmpty_congr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, (Equiv.{u1, u2} α β) -> (Iff (IsEmpty.{u1} α) (IsEmpty.{u2} β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, (Equiv.{u2, u1} α β) -> (Iff (IsEmpty.{u2} α) (IsEmpty.{u1} β))
Case conversion may be inaccurate. Consider using '#align equiv.is_empty_congr Equiv.isEmpty_congrₓ'. -/
/-- If `α` is equivalent to `β`, then `is_empty α` is equivalent to `is_empty β`. -/
theorem isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @Function.isEmpty _ _ h e.symm, fun h => @Function.isEmpty _ _ h e⟩
#align equiv.is_empty_congr Equiv.isEmpty_congr

/- warning: equiv.is_empty -> Equiv.isEmpty is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, (Equiv.{u1, u2} α β) -> (forall [_inst_1 : IsEmpty.{u2} β], IsEmpty.{u1} α)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, (Equiv.{u2, u1} α β) -> (forall [_inst_1 : IsEmpty.{u1} β], IsEmpty.{u2} α)
Case conversion may be inaccurate. Consider using '#align equiv.is_empty Equiv.isEmptyₓ'. -/
protected theorem isEmpty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.is_empty_congr.mpr ‹_›
#align equiv.is_empty Equiv.isEmpty

section

open Subtype

#print Equiv.subtypeEquiv /-
/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `perm.subtype_perm`. -/
def subtypeEquiv {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) :
    { a : α // p a } ≃ { b : β // q b }
    where
  toFun a := ⟨e a, (h _).mp a.Prop⟩
  invFun b := ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.Prop)⟩
  left_inv a := Subtype.ext <| by simp
  right_inv b := Subtype.ext <| by simp
#align equiv.subtype_equiv Equiv.subtypeEquiv
-/

#print Equiv.subtypeEquiv_refl /-
@[simp]
theorem subtypeEquiv_refl {p : α → Prop} (h : ∀ a, p a ↔ p (Equiv.refl _ a) := fun a => Iff.rfl) :
    (Equiv.refl α).subtypeEquiv h = Equiv.refl { a : α // p a } :=
  by
  ext
  rfl
#align equiv.subtype_equiv_refl Equiv.subtypeEquiv_refl
-/

/- warning: equiv.subtype_equiv_symm -> Equiv.subtypeEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : α -> Prop} {q : β -> Prop} (e : Equiv.{u1, u2} α β) (h : forall (a : α), Iff (p a) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e a))), Eq.{max 1 (max (max 1 u2) 1 u1) (max 1 u1) 1 u2} (Equiv.{max 1 u2, max 1 u1} (Subtype.{u2} β (fun (b : β) => q b)) (Subtype.{u1} α (fun (a : α) => p a))) (Equiv.symm.{max 1 u1, max 1 u2} (Subtype.{u1} α (fun (a : α) => p a)) (Subtype.{u2} β (fun (b : β) => q b)) (Equiv.subtypeEquiv.{u1, u2} α β (fun (a : α) => p a) q e h)) (Equiv.subtypeEquiv.{u2, u1} β α (fun (b : β) => q b) (fun (a : α) => p a) (Equiv.symm.{u1, u2} α β e) (fun (a : β) => Eq.mpr.{0} (Iff (q a) (p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a))) (Iff (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a))) (p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a))) ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) (b : Prop) (b_1 : Prop) (e_2 : Eq.{1} Prop b b_1) => congr.{1, 1} Prop Prop (Iff a) (Iff a_1) b b_1 (congr_arg.{1, 1} Prop (Prop -> Prop) a a_1 Iff e_1) e_2) (q a) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a))) ((fun (ᾰ : β) (ᾰ_1 : β) (e_1 : Eq.{u2} β ᾰ ᾰ_1) => congr_arg.{u2, 1} β Prop ᾰ ᾰ_1 q e_1) a (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a)) (Eq.symm.{u2} β (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a)) a (Equiv.apply_symm_apply.{u1, u2} α β e a))) (p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a)) (p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a)) (rfl.{1} Prop (p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a)))) (Iff.symm (p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a)) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a))) (h (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a)))))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {p : α -> Prop} {q : β -> Prop} (e : Equiv.{u2, u1} α β) (h : forall (a : α), Iff (p a) (q (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e a))), Eq.{max (max 1 u2) u1} (Equiv.{max 1 u1, max 1 u2} (Subtype.{u1} β (fun (b : β) => q b)) (Subtype.{u2} α (fun (a : α) => p a))) (Equiv.symm.{max 1 u2, max 1 u1} (Subtype.{u2} α (fun (a : α) => p a)) (Subtype.{u1} β (fun (b : β) => q b)) (Equiv.subtypeEquiv.{u2, u1} α β (fun (a : α) => p a) q e h)) (Equiv.subtypeEquiv.{u1, u2} β α (fun (b : β) => q b) (fun (a : α) => p a) (Equiv.symm.{u2, u1} α β e) (fun (a : β) => Eq.mpr.{0} (Iff (q a) (p (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a))) (Iff (q (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a))) (p (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a))) ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) => Eq.rec.{0, 1} Prop a (fun (a_1 : Prop) (e_a : Eq.{1} Prop a a_1) => forall (b : Prop) (b_1 : Prop), (Eq.{1} Prop b b_1) -> (Eq.{1} Prop (Iff a b) (Iff a_1 b_1))) (fun (b : Prop) (b_1 : Prop) (e_b : Eq.{1} Prop b b_1) => Eq.rec.{0, 1} Prop b (fun (b_1 : Prop) (e_b : Eq.{1} Prop b b_1) => Eq.{1} Prop (Iff a b) (Iff a b_1)) (Eq.refl.{1} Prop (Iff a b)) b_1 e_b) a_1 e_1) (q a) (q (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a))) ((fun (ᾰ : β) (ᾰ_1 : β) (e_1 : Eq.{u1} β ᾰ ᾰ_1) => Eq.rec.{0, u1} β ᾰ (fun (a._@.Mathlib.Logic.Equiv.Basic._hyg.9516 : β) (e_a._@.Mathlib.Logic.Equiv.Basic._hyg.9516 : Eq.{u1} β ᾰ a._@.Mathlib.Logic.Equiv.Basic._hyg.9516) => Eq.{1} Prop (q ᾰ) (q a._@.Mathlib.Logic.Equiv.Basic._hyg.9516)) (Eq.refl.{1} Prop (q ᾰ)) ᾰ_1 e_1) a (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a)) (Eq.symm.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a)) (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a)) a (Equiv.apply_symm_apply.{u2, u1} α β e a))) (p (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a)) (p (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a)) (Eq.refl.{1} Prop (p (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a)))) (Iff.symm (p (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a)) (q (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a))) (h (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) a)))))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_symm Equiv.subtypeEquiv_symmₓ'. -/
@[simp]
theorem subtypeEquiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) :
    (e.subtypeEquiv h).symm =
      e.symm.subtypeEquiv fun a => by
        convert (h <| e.symm a).symm
        exact (e.apply_symm_apply a).symm :=
  rfl
#align equiv.subtype_equiv_symm Equiv.subtypeEquiv_symm

/- warning: equiv.subtype_equiv_trans -> Equiv.subtypeEquiv_trans is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (e : Equiv.{u1, u2} α β) (f : Equiv.{u2, u3} β γ) (h : forall (a : α), Iff (p a) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e a))) (h' : forall (b : β), Iff (q b) (r (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} β γ) (fun (_x : Equiv.{u2, u3} β γ) => β -> γ) (Equiv.hasCoeToFun.{u2, u3} β γ) f b))), Eq.{max 1 (max (max 1 u1) 1 u3) (max 1 u3) 1 u1} (Equiv.{max 1 u1, max 1 u3} (Subtype.{u1} α (fun (a : α) => p a)) (Subtype.{u3} γ (fun (b : γ) => r b))) (Equiv.trans.{max 1 u1, max 1 u2, max 1 u3} (Subtype.{u1} α (fun (a : α) => p a)) (Subtype.{u2} β (fun (b : β) => q b)) (Subtype.{u3} γ (fun (b : γ) => r b)) (Equiv.subtypeEquiv.{u1, u2} α β (fun (a : α) => p a) q e h) (Equiv.subtypeEquiv.{u2, u3} β γ (fun (b : β) => q b) r f h')) (Equiv.subtypeEquiv.{u1, u3} α γ (fun (a : α) => p a) (fun (b : γ) => r b) (Equiv.trans.{u1, u2, u3} α β γ e f) (fun (a : α) => Iff.trans (p a) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e a)) (r (coeFn.{max 1 (imax u1 u3) (imax u3 u1), imax u1 u3} (Equiv.{u1, u3} α γ) (fun (_x : Equiv.{u1, u3} α γ) => α -> γ) (Equiv.hasCoeToFun.{u1, u3} α γ) (Equiv.trans.{u1, u2, u3} α β γ e f) a)) (h a) (h' (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e a))))
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (e : Equiv.{u3, u2} α β) (f : Equiv.{u2, u1} β γ) (h : forall (a : α), Iff (p a) (q (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) e a))) (h' : forall (b : β), Iff (q b) (r (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} β γ) β γ (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} β γ) β γ (Equiv.instEquivLikeEquiv.{u2, u1} β γ))) f b))), Eq.{max (max 1 u3) u1} (Equiv.{max 1 u3, max 1 u1} (Subtype.{u3} α (fun (a : α) => p a)) (Subtype.{u1} γ (fun (b : γ) => r b))) (Equiv.trans.{max 1 u3, max 1 u2, max 1 u1} (Subtype.{u3} α (fun (a : α) => p a)) (Subtype.{u2} β (fun (b : β) => q b)) (Subtype.{u1} γ (fun (b : γ) => r b)) (Equiv.subtypeEquiv.{u3, u2} α β (fun (a : α) => p a) q e h) (Equiv.subtypeEquiv.{u2, u1} β γ (fun (b : β) => q b) r f h')) (Equiv.subtypeEquiv.{u3, u1} α γ (fun (a : α) => p a) r (Equiv.trans.{u3, u2, u1} α β γ e f) (fun (a : α) => Iff.trans (p a) (q (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) e a)) (r (FunLike.coe.{max (max 1 u3) u1, u3, u1} (Equiv.{u3, u1} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u1, u3, u1} (Equiv.{u3, u1} α γ) α γ (EquivLike.toEmbeddingLike.{max (max 1 u3) u1, u3, u1} (Equiv.{u3, u1} α γ) α γ (Equiv.instEquivLikeEquiv.{u3, u1} α γ))) (Equiv.trans.{u3, u2, u1} α β γ e f) a)) (h a) (h' (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) e a))))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_trans Equiv.subtypeEquiv_transₓ'. -/
@[simp]
theorem subtypeEquiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ)
    (h : ∀ a : α, p a ↔ q (e a)) (h' : ∀ b : β, q b ↔ r (f b)) :
    (e.subtypeEquiv h).trans (f.subtypeEquiv h') =
      (e.trans f).subtypeEquiv fun a => (h a).trans (h' <| e a) :=
  rfl
#align equiv.subtype_equiv_trans Equiv.subtypeEquiv_trans

/- warning: equiv.subtype_equiv_apply -> Equiv.subtypeEquiv_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : α -> Prop} {q : β -> Prop} (e : Equiv.{u1, u2} α β) (h : forall (a : α), Iff (p a) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e a))) (x : Subtype.{u1} α (fun (x : α) => p x)), Eq.{max 1 u2} (Subtype.{u2} β (fun (b : β) => q b)) (coeFn.{max 1 (max (max 1 u1) 1 u2) (max 1 u2) 1 u1, max (max 1 u1) 1 u2} (Equiv.{max 1 u1, max 1 u2} (Subtype.{u1} α (fun (a : α) => (fun (a : α) => p a) a)) (Subtype.{u2} β (fun (b : β) => q b))) (fun (_x : Equiv.{max 1 u1, max 1 u2} (Subtype.{u1} α (fun (a : α) => (fun (a : α) => p a) a)) (Subtype.{u2} β (fun (b : β) => q b))) => (Subtype.{u1} α (fun (a : α) => (fun (a : α) => p a) a)) -> (Subtype.{u2} β (fun (b : β) => q b))) (Equiv.hasCoeToFun.{max 1 u1, max 1 u2} (Subtype.{u1} α (fun (a : α) => (fun (a : α) => p a) a)) (Subtype.{u2} β (fun (b : β) => q b))) (Equiv.subtypeEquiv.{u1, u2} α β (fun (a : α) => p a) q e h) x) (Subtype.mk.{u2} β (fun (b : β) => q b) (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (x : α) => p x)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (coeSubtype.{u1} α (fun (x : α) => p x))))) x)) (Iff.mp (p ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (x : α) => p x)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (coeSubtype.{u1} α (fun (x : α) => p x))))) x)) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (x : α) => p x)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (coeSubtype.{u1} α (fun (x : α) => p x))))) x))) (h ((fun (a : Sort.{max 1 u1}) (b : Sort.{u1}) [self : HasLiftT.{max 1 u1, u1} a b] => self.0) (Subtype.{u1} α (fun (x : α) => p x)) α (HasLiftT.mk.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (CoeTCₓ.coe.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (coeBase.{max 1 u1, u1} (Subtype.{u1} α (fun (x : α) => p x)) α (coeSubtype.{u1} α (fun (x : α) => p x))))) x)) (Subtype.property.{u1} α (fun (x : α) => p x) x)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {p : α -> Prop} {q : β -> Prop} (e : Equiv.{u2, u1} α β) (h : forall (a : α), Iff (p a) (q (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e a))) (x : Subtype.{u2} α (fun (x : α) => p x)), Eq.{max 1 u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subtype.{u2} α (fun (a : α) => p a)) => Subtype.{u1} β (fun (b : β) => q b)) x) (FunLike.coe.{max (max 1 u2) u1, max 1 u2, max 1 u1} (Equiv.{max 1 u2, max 1 u1} (Subtype.{u2} α (fun (a : α) => p a)) (Subtype.{u1} β (fun (b : β) => q b))) (Subtype.{u2} α (fun (a : α) => p a)) (fun (_x : Subtype.{u2} α (fun (a : α) => p a)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subtype.{u2} α (fun (a : α) => p a)) => Subtype.{u1} β (fun (b : β) => q b)) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, max 1 u2, max 1 u1} (Equiv.{max 1 u2, max 1 u1} (Subtype.{u2} α (fun (a : α) => p a)) (Subtype.{u1} β (fun (b : β) => q b))) (Subtype.{u2} α (fun (a : α) => p a)) (Subtype.{u1} β (fun (a : β) => q a)) (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, max 1 u2, max 1 u1} (Equiv.{max 1 u2, max 1 u1} (Subtype.{u2} α (fun (a : α) => p a)) (Subtype.{u1} β (fun (b : β) => q b))) (Subtype.{u2} α (fun (a : α) => p a)) (Subtype.{u1} β (fun (b : β) => q b)) (Equiv.instEquivLikeEquiv.{max 1 u2, max 1 u1} (Subtype.{u2} α (fun (a : α) => p a)) (Subtype.{u1} β (fun (b : β) => q b))))) (Equiv.subtypeEquiv.{u2, u1} α β (fun (a : α) => p a) q e h) x) (Subtype.mk.{u1} β (fun (b : β) => q b) (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e (Subtype.val.{u2} α (fun (x : α) => p x) x)) (Iff.mp (p (Subtype.val.{u2} α (fun (x : α) => p x) x)) (q (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e (Subtype.val.{u2} α (fun (x : α) => p x) x))) (h (Subtype.val.{u2} α (fun (x : α) => p x) x)) (Subtype.property.{u2} α (fun (x : α) => p x) x)))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_apply Equiv.subtypeEquiv_applyₓ'. -/
@[simp]
theorem subtypeEquiv_apply {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a))
    (x : { x // p x }) : e.subtypeEquiv h x = ⟨e x, (h _).1 x.2⟩ :=
  rfl
#align equiv.subtype_equiv_apply Equiv.subtypeEquiv_apply

#print Equiv.subtypeEquivRight /-
/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps]
def subtypeEquivRight {p q : α → Prop} (e : ∀ x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtypeEquiv (Equiv.refl _) e
#align equiv.subtype_equiv_right Equiv.subtypeEquivRight
-/

/- warning: equiv.subtype_equiv_of_subtype -> Equiv.subtypeEquivOfSubtype is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : β -> Prop} (e : Equiv.{u1, u2} α β), Equiv.{max 1 u1, max 1 u2} (Subtype.{u1} α (fun (a : α) => p (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e a))) (Subtype.{u2} β (fun (b : β) => p b))
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : α -> Prop} (e : Equiv.{u2, u1} β α), Equiv.{max 1 u2, max 1 u1} (Subtype.{u2} β (fun (a : β) => p (FunLike.coe.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} β α) β α (Equiv.instEquivLikeEquiv.{u2, u1} β α))) e a))) (Subtype.{u1} α (fun (b : α) => p b))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_of_subtype Equiv.subtypeEquivOfSubtypeₓ'. -/
/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtypeEquivOfSubtype {p : β → Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
  subtypeEquiv e <| by simp
#align equiv.subtype_equiv_of_subtype Equiv.subtypeEquivOfSubtype

#print Equiv.subtypeEquivOfSubtype' /-
/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtypeEquivOfSubtype' {p : α → Prop} (e : α ≃ β) :
    { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtypeEquivOfSubtype.symm
#align equiv.subtype_equiv_of_subtype' Equiv.subtypeEquivOfSubtype'
-/

/- warning: equiv.subtype_equiv_prop -> Equiv.subtypeEquivProp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {q : α -> Prop}, (Eq.{succ u1} (α -> Prop) p q) -> (Equiv.{succ u1, succ u1} (Subtype.{succ u1} α p) (Subtype.{succ u1} α q))
but is expected to have type
  forall {α : Sort.{u1}} {p : α -> Prop} {q : α -> Prop}, (Eq.{max 1 u1} (α -> Prop) p q) -> (Equiv.{max 1 u1, max 1 u1} (Subtype.{u1} α p) (Subtype.{u1} α q))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_prop Equiv.subtypeEquivPropₓ'. -/
/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtypeEquivProp {α : Type _} {p q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtypeEquiv (Equiv.refl α) fun a => h ▸ Iff.rfl
#align equiv.subtype_equiv_prop Equiv.subtypeEquivProp

/- warning: equiv.subtype_subtype_equiv_subtype_exists -> Equiv.subtypeSubtypeEquivSubtypeExists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) (q : (Subtype.{succ u1} α p) -> Prop), Equiv.{succ u1, succ u1} (Subtype.{succ u1} (Subtype.{succ u1} α p) q) (Subtype.{succ u1} α (fun (a : α) => Exists.{0} (p a) (fun (h : p a) => q (Subtype.mk.{succ u1} α p a h))))
but is expected to have type
  forall {α : Sort.{u1}} (p : α -> Prop) (q : (Subtype.{u1} α p) -> Prop), Equiv.{max 1 u1, max 1 u1} (Subtype.{max 1 u1} (Subtype.{u1} α p) q) (Subtype.{u1} α (fun (a : α) => Exists.{0} (p a) (fun (h : p a) => q (Subtype.mk.{u1} α p a h))))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_subtype_equiv_subtype_exists Equiv.subtypeSubtypeEquivSubtypeExistsₓ'. -/
/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
def subtypeSubtypeEquivSubtypeExists {α : Type u} (p : α → Prop) (q : Subtype p → Prop) :
    Subtype q ≃ { a : α // ∃ h : p a, q ⟨a, h⟩ } :=
  ⟨fun a =>
    ⟨a, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨a, ha⟩, h⟩ => rfl, fun ⟨a, h₁, h₂⟩ => rfl⟩
#align equiv.subtype_subtype_equiv_subtype_exists Equiv.subtypeSubtypeEquivSubtypeExists

/- warning: equiv.subtype_subtype_equiv_subtype_inter -> Equiv.subtypeSubtypeEquivSubtypeInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) (q : α -> Prop), Equiv.{succ u1, succ u1} (Subtype.{succ u1} (Subtype.{succ u1} α p) (fun (x : Subtype.{succ u1} α p) => q (Subtype.val.{succ u1} α p x))) (Subtype.{succ u1} α (fun (x : α) => And (p x) (q x)))
but is expected to have type
  forall {α : Sort.{u1}} (p : α -> Prop) (q : α -> Prop), Equiv.{max 1 u1, max 1 u1} (Subtype.{max 1 u1} (Subtype.{u1} α p) (fun (x : Subtype.{u1} α p) => q (Subtype.val.{u1} α p x))) (Subtype.{u1} α (fun (x : α) => And (p x) (q x)))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_subtype_equiv_subtype_inter Equiv.subtypeSubtypeEquivSubtypeInterₓ'. -/
/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps]
def subtypeSubtypeEquivSubtypeInter {α : Type u} (p q : α → Prop) :
    { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
  (subtypeSubtypeEquivSubtypeExists p _).trans <| subtype_equiv_right fun x => exists_prop
#align equiv.subtype_subtype_equiv_subtype_inter Equiv.subtypeSubtypeEquivSubtypeInter

/- warning: equiv.subtype_subtype_equiv_subtype -> Equiv.subtypeSubtypeEquivSubtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {q : α -> Prop}, (forall {x : α}, (q x) -> (p x)) -> (Equiv.{succ u1, succ u1} (Subtype.{succ u1} (Subtype.{succ u1} α p) (fun (x : Subtype.{succ u1} α p) => q (Subtype.val.{succ u1} α p x))) (Subtype.{succ u1} α q))
but is expected to have type
  forall {α : Sort.{u1}} {p : α -> Prop} {q : α -> Prop}, (forall {x : α}, (q x) -> (p x)) -> (Equiv.{max 1 u1, max 1 u1} (Subtype.{max 1 u1} (Subtype.{u1} α p) (fun (x : Subtype.{u1} α p) => q (Subtype.val.{u1} α p x))) (Subtype.{u1} α q))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_subtype_equiv_subtype Equiv.subtypeSubtypeEquivSubtypeₓ'. -/
/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps]
def subtypeSubtypeEquivSubtype {α : Type u} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
    { x : Subtype p // q x.1 } ≃ Subtype q :=
  (subtypeSubtypeEquivSubtypeInter p _).trans <| subtype_equiv_right fun x => and_iff_right_of_imp h
#align equiv.subtype_subtype_equiv_subtype Equiv.subtypeSubtypeEquivSubtype

#print Equiv.subtypeUnivEquiv /-
/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symmApply]
def subtypeUnivEquiv {α : Type u} {p : α → Prop} (h : ∀ x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun x => Subtype.eq rfl, fun x => rfl⟩
#align equiv.subtype_univ_equiv Equiv.subtypeUnivEquiv
-/

/- warning: equiv.subtype_sigma_equiv -> Equiv.subtypeSigmaEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Type.{u2}) (q : α -> Prop), Equiv.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α p) (fun (y : Sigma.{u1, u2} α p) => q (Sigma.fst.{u1, u2} α p y))) (Sigma.{u1, u2} (Subtype.{succ u1} α q) (fun (x : Subtype.{succ u1} α q) => p (Subtype.val.{succ u1} α q x)))
but is expected to have type
  forall {α : Type.{u2}} (p : α -> Type.{u1}) (q : α -> Prop), Equiv.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α p) (fun (y : Sigma.{u2, u1} α p) => q (Sigma.fst.{u2, u1} α p y))) (Sigma.{u2, u1} (Subtype.{succ u2} α q) (fun (x : Subtype.{succ u2} α q) => p (Subtype.val.{succ u2} α q x)))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_sigma_equiv Equiv.subtypeSigmaEquivₓ'. -/
/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtypeSigmaEquiv {α : Type u} (p : α → Type v) (q : α → Prop) :
    { y : Sigma p // q y.1 } ≃ Σx : Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun ⟨⟨x, h⟩, y⟩ => rfl,
    fun ⟨⟨x, y⟩, h⟩ => rfl⟩
#align equiv.subtype_sigma_equiv Equiv.subtypeSigmaEquiv

/- warning: equiv.sigma_subtype_equiv_of_subset -> Equiv.sigmaSubtypeEquivOfSubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Type.{u2}) (q : α -> Prop), (forall (x : α), (p x) -> (q x)) -> (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u1, u2} (Subtype.{succ u1} α q) (fun (x : Subtype.{succ u1} α q) => p ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α q) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α q) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α q) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α q) α (coeSubtype.{succ u1} α (fun (x : α) => q x))))) x))) (Sigma.{u1, u2} α (fun (x : α) => p x)))
but is expected to have type
  forall {α : Type.{u2}} (p : α -> Type.{u1}) (q : α -> Prop), (forall (x : α), (p x) -> (q x)) -> (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u2, u1} (Subtype.{succ u2} α q) (fun (x : Subtype.{succ u2} α q) => p (Subtype.val.{succ u2} α q x))) (Sigma.{u2, u1} α (fun (x : α) => p x)))
Case conversion may be inaccurate. Consider using '#align equiv.sigma_subtype_equiv_of_subset Equiv.sigmaSubtypeEquivOfSubsetₓ'. -/
/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigmaSubtypeEquivOfSubset {α : Type u} (p : α → Type v) (q : α → Prop) (h : ∀ x, p x → q x) :
    (Σx : Subtype q, p x) ≃ Σx : α, p x :=
  (subtypeSigmaEquiv p q).symm.trans <| subtype_univ_equiv fun x => h x.1 x.2
#align equiv.sigma_subtype_equiv_of_subset Equiv.sigmaSubtypeEquivOfSubset

#print Equiv.sigmaSubtypeFiberEquiv /-
/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigmaSubtypeFiberEquiv {α : Type u} {β : Type v} (f : α → β) (p : β → Prop) (h : ∀ x, p (f x)) :
    (Σy : Subtype p, { x : α // f x = y }) ≃ α :=
  calc
    _ ≃ Σy : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun y ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f
    
#align equiv.sigma_subtype_fiber_equiv Equiv.sigmaSubtypeFiberEquiv
-/

#print Equiv.sigmaSubtypeFiberEquivSubtype /-
/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigmaSubtypeFiberEquivSubtype {α : Type u} {β : Type v} (f : α → β) {p : α → Prop}
    {q : β → Prop} (h : ∀ x, p x ↔ q (f x)) : (Σy : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
  calc
    (Σy : Subtype q, { x : α // f x = y }) ≃
        Σy : Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } :=
      by
      apply sigma_congr_right
      intro y
      symm
      refine' (subtype_subtype_equiv_subtype_exists _ _).trans (subtype_equiv_right _)
      intro x
      exact
        ⟨fun ⟨hp, h'⟩ => congr_arg Subtype.val h', fun h' =>
          ⟨(h x).2 (h'.symm ▸ y.2), Subtype.eq h'⟩⟩
    _ ≃ Subtype p := sigmaFiberEquiv fun x : Subtype p => (⟨f x, (h x).1 x.property⟩ : Subtype q)
    
#align equiv.sigma_subtype_fiber_equiv_subtype Equiv.sigmaSubtypeFiberEquivSubtype
-/

/- warning: equiv.sigma_option_equiv_of_some -> Equiv.sigmaOptionEquivOfSome is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : (Option.{u1} α) -> Type.{u2}), ((p (Option.none.{u1} α)) -> False) -> (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u1, u2} (Option.{u1} α) (fun (x : Option.{u1} α) => p x)) (Sigma.{u1, u2} α (fun (x : α) => p (Option.some.{u1} α x))))
but is expected to have type
  forall {α : Type.{u2}} (p : (Option.{u2} α) -> Type.{u1}), ((p (Option.none.{u2} α)) -> False) -> (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u2, u1} (Option.{u2} α) (fun (x : Option.{u2} α) => p x)) (Sigma.{u2, u1} α (fun (x : α) => p (Option.some.{u2} α x))))
Case conversion may be inaccurate. Consider using '#align equiv.sigma_option_equiv_of_some Equiv.sigmaOptionEquivOfSomeₓ'. -/
/-- A sigma type over an `option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigmaOptionEquivOfSome {α : Type u} (p : Option α → Type v) (h : p none → False) :
    (Σx : Option α, p x) ≃ Σx : α, p (some x) :=
  haveI h' : ∀ x, p x → x.isSome := by
    intro x
    cases x
    · intro n
      exfalso
      exact h n
    · intro s
      exact rfl
  (sigma_subtype_equiv_of_subset _ _ h').symm.trans (sigma_congr_left' (option_is_some_equiv α))
#align equiv.sigma_option_equiv_of_some Equiv.sigmaOptionEquivOfSome

#print Equiv.piEquivSubtypeSigma /-
/-- The `pi`-type `Π i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`sigma` type such that for all `i` we have `(f i).fst = i`. -/
def piEquivSubtypeSigma (ι : Type _) (π : ι → Type _) :
    (∀ i, π i) ≃ { f : ι → Σi, π i // ∀ i, (f i).1 = i } :=
  ⟨fun f => ⟨fun i => ⟨i, f i⟩, fun i => rfl⟩, fun f i => by rw [← f.2 i]; exact (f.1 i).2, fun f =>
    funext fun i => rfl, fun ⟨f, hf⟩ =>
    Subtype.eq <|
      funext fun i =>
        Sigma.eq (hf i).symm <| eq_of_hEq <| ndrec_hEq_of_hEq _ <| ndrec_hEq_of_hEq _ <| HEq.refl _⟩
#align equiv.pi_equiv_subtype_sigma Equiv.piEquivSubtypeSigma
-/

/- warning: equiv.subtype_pi_equiv_pi -> Equiv.subtypePiEquivPi is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}} {p : forall (a : α), (β a) -> Prop}, Equiv.{max 1 (imax u1 u2), max u1 1 u2} (Subtype.{imax u1 u2} (forall (a : α), β a) (fun (f : forall (a : α), β a) => forall (a : α), p a (f a))) (forall (a : α), Subtype.{u2} (β a) (fun (b : β a) => p a b))
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}} {p : forall (a : α), (β a) -> Prop}, Equiv.{max 1 (imax u2 u1), max (max 1 u1) u2} (Subtype.{imax u2 u1} (forall (a : α), β a) (fun (f : forall (a : α), β a) => forall (a : α), p a (f a))) (forall (a : α), Subtype.{u1} (β a) (fun (b : β a) => p a b))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_pi_equiv_pi Equiv.subtypePiEquivPiₓ'. -/
/-- The set of functions `f : Π a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the set of functions `Π a, {b : β a // p a b}`. -/
def subtypePiEquivPi {α : Sort u} {β : α → Sort v} {p : ∀ a, β a → Prop} :
    { f : ∀ a, β a // ∀ a, p a (f a) } ≃ ∀ a, { b : β a // p a b } :=
  ⟨fun f a => ⟨f.1 a, f.2 a⟩, fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩,
    by
    rintro ⟨f, h⟩
    rfl, by
    rintro f
    funext a
    exact Subtype.ext_val rfl⟩
#align equiv.subtype_pi_equiv_pi Equiv.subtypePiEquivPi

#print Equiv.subtypeProdEquivProd /-
/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtypeProdEquivProd {α : Type u} {β : Type v} {p : α → Prop} {q : β → Prop} :
    { c : α × β // p c.1 ∧ q c.2 } ≃ { a // p a } × { b // q b } :=
  ⟨fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩,
    fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl, fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl⟩
#align equiv.subtype_prod_equiv_prod Equiv.subtypeProdEquivProd
-/

#print Equiv.subtypeProdEquivSigmaSubtype /-
/-- A subtype of a `prod` is equivalent to a sigma type whose fibers are subtypes. -/
def subtypeProdEquivSigmaSubtype {α β : Type _} (p : α → β → Prop) :
    { x : α × β // p x.1 x.2 } ≃ Σa, { b : β // p a b }
    where
  toFun x := ⟨x.1.1, x.1.2, x.Prop⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.Prop⟩
  left_inv x := by ext <;> rfl
  right_inv := fun ⟨a, b, pab⟩ => rfl
#align equiv.subtype_prod_equiv_sigma_subtype Equiv.subtypeProdEquivSigmaSubtype
-/

#print Equiv.piEquivPiSubtypeProd /-
/-- The type `Π (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps]
def piEquivPiSubtypeProd {α : Type _} (p : α → Prop) (β : α → Type _) [DecidablePred p] :
    (∀ i : α, β i) ≃ (∀ i : { x // p x }, β i) × ∀ i : { x // ¬p x }, β i
    where
  toFun f := (fun x => f x, fun x => f x)
  invFun f x := if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩
  right_inv := by
    rintro ⟨f, g⟩
    ext1 <;>
      · ext y
        rcases y with ⟨⟩
        simp only [y_property, dif_pos, dif_neg, not_false_iff, Subtype.coe_mk]
        rfl
  left_inv f := by
    ext x
    by_cases h : p x <;>
      · simp only [h, dif_neg, dif_pos, not_false_iff]
        rfl
#align equiv.pi_equiv_pi_subtype_prod Equiv.piEquivPiSubtypeProd
-/

#print Equiv.piSplitAt /-
/-- A product of types can be split as the binary product of one of the types and the product
  of all the remaining types. -/
@[simps]
def piSplitAt {α : Type _} [DecidableEq α] (i : α) (β : α → Type _) :
    (∀ j, β j) ≃ β i × ∀ j : { j // j ≠ i }, β j
    where
  toFun f := ⟨f i, fun j => f j⟩
  invFun f j := if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩
  right_inv f := by
    ext
    exacts[dif_pos rfl, (dif_neg x.2).trans (by cases x <;> rfl)]
  left_inv f := by
    ext
    dsimp only
    split_ifs
    · subst h
    · rfl
#align equiv.pi_split_at Equiv.piSplitAt
-/

#print Equiv.funSplitAt /-
/-- A product of copies of a type can be split as the binary product of one copy and the product
  of all the remaining copies. -/
@[simps]
def funSplitAt {α : Type _} [DecidableEq α] (i : α) (β : Type _) :
    (α → β) ≃ β × ({ j // j ≠ i } → β) :=
  piSplitAt i _
#align equiv.fun_split_at Equiv.funSplitAt
-/

end

section SubtypeEquivCodomain

variable {X : Type _} {Y : Type _} [DecidableEq X] {x : X}

/- warning: equiv.subtype_equiv_codomain -> Equiv.subtypeEquivCodomain is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} X] {x : X} (f : (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y), Equiv.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y
but is expected to have type
  forall {X : Sort.{u1}} [Y : DecidableEq.{u1} X] {_inst_1 : X} {x : Sort.{u2}} (f : (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x), Equiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_codomain Equiv.subtypeEquivCodomainₓ'. -/
/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) : { g : X → Y // g ∘ coe = f } ≃ Y :=
  (subtypePreimage _ f).trans <|
    @funUnique { x' // ¬x' ≠ x } _ <|
      show Unique { x' // ¬x' ≠ x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from
            { default := ⟨x, rfl⟩
              uniq := fun ⟨x', h⟩ => Subtype.val_injective h })
          (subtype_equiv_right fun a => not_not)
#align equiv.subtype_equiv_codomain Equiv.subtypeEquivCodomain

/- warning: equiv.coe_subtype_equiv_codomain -> Equiv.coe_subtypeEquivCodomain is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} X] {x : X} (f : (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y), Eq.{max (max 1 (succ u1) (succ u2)) (succ u2)} ((fun (_x : Equiv.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y) => (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) -> Y) (Equiv.subtypeEquivCodomain.{u1, u2} X Y (fun (a : X) (b : X) => _inst_1 a b) x f)) (coeFn.{max 1 (max (max 1 (succ u1) (succ u2)) (succ u2)) (succ u2) 1 (succ u1) (succ u2), max (max 1 (succ u1) (succ u2)) (succ u2)} (Equiv.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y) (fun (_x : Equiv.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y) => (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) -> Y) (Equiv.hasCoeToFun.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y) (Equiv.subtypeEquivCodomain.{u1, u2} X Y (fun (a : X) (b : X) => _inst_1 a b) x f)) (fun (g : Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) => (fun (a : Sort.{max 1 (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (HasLiftT.mk.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeBase.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeSubtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))))) g x)
but is expected to have type
  forall {X : Sort.{u1}} [Y : DecidableEq.{u1} X] {_inst_1 : X} {x : Sort.{u2}} (f : (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x), Eq.{imax (max 1 (imax u1 u2)) u2} (forall (a : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) => x) a) (FunLike.coe.{max (max 1 u2) (imax u1 u2), max 1 (imax u1 u2), u2} (Equiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x) (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (fun (_x : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) => x) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) (imax u1 u2), max 1 (imax u1 u2), u2} (Equiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x) (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x (EquivLike.toEmbeddingLike.{max (max 1 u2) (imax u1 u2), max 1 (imax u1 u2), u2} (Equiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x) (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x (Equiv.instEquivLikeEquiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x))) (Equiv.subtypeEquivCodomain.{u1, u2} X (fun (a : X) (b : X) => Y a b) _inst_1 x f)) (fun (g : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) => Subtype.val.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f) g _inst_1)
Case conversion may be inaccurate. Consider using '#align equiv.coe_subtype_equiv_codomain Equiv.coe_subtypeEquivCodomainₓ'. -/
@[simp]
theorem coe_subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) :
    (subtypeEquivCodomain f : { g : X → Y // g ∘ coe = f } → Y) = fun g => (g : X → Y) x :=
  rfl
#align equiv.coe_subtype_equiv_codomain Equiv.coe_subtypeEquivCodomain

/- warning: equiv.subtype_equiv_codomain_apply -> Equiv.subtypeEquivCodomain_apply is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} X] {x : X} (f : (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (g : Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)), Eq.{succ u2} Y (coeFn.{max 1 (max (max 1 (succ u1) (succ u2)) (succ u2)) (succ u2) 1 (succ u1) (succ u2), max (max 1 (succ u1) (succ u2)) (succ u2)} (Equiv.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y) (fun (_x : Equiv.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y) => (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) -> Y) (Equiv.hasCoeToFun.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y) (Equiv.subtypeEquivCodomain.{u1, u2} X Y (fun (a : X) (b : X) => _inst_1 a b) x f) g) ((fun (a : Sort.{max 1 (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (HasLiftT.mk.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeBase.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeSubtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))))) g x)
but is expected to have type
  forall {X : Sort.{u1}} [Y : DecidableEq.{u1} X] {_inst_1 : X} {x : Sort.{u2}} (f : (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (g : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)), Eq.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) => x) g) (FunLike.coe.{max (max 1 u2) (imax u1 u2), max 1 (imax u1 u2), u2} (Equiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x) (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (fun (_x : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) => x) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) (imax u1 u2), max 1 (imax u1 u2), u2} (Equiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x) (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x (EquivLike.toEmbeddingLike.{max (max 1 u2) (imax u1 u2), max 1 (imax u1 u2), u2} (Equiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x) (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x (Equiv.instEquivLikeEquiv.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x))) (Equiv.subtypeEquivCodomain.{u1, u2} X (fun (a : X) (b : X) => Y a b) _inst_1 x f) g) (Subtype.val.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f) g _inst_1)
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_codomain_apply Equiv.subtypeEquivCodomain_applyₓ'. -/
@[simp]
theorem subtypeEquivCodomain_apply (f : { x' // x' ≠ x } → Y) (g : { g : X → Y // g ∘ coe = f }) :
    subtypeEquivCodomain f g = (g : X → Y) x :=
  rfl
#align equiv.subtype_equiv_codomain_apply Equiv.subtypeEquivCodomain_apply

/- warning: equiv.coe_subtype_equiv_codomain_symm -> Equiv.coe_subtypeEquivCodomain_symm is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} X] {x : X} (f : (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y), Eq.{max (succ u2) 1 (succ u1) (succ u2)} ((fun (_x : Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) => Y -> (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.symm.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y (Equiv.subtypeEquivCodomain.{u1, u2} X Y (fun (a : X) (b : X) => _inst_1 a b) x f))) (coeFn.{max 1 (max (succ u2) 1 (succ u1) (succ u2)) (max 1 (succ u1) (succ u2)) (succ u2), max (succ u2) 1 (succ u1) (succ u2)} (Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (fun (_x : Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) => Y -> (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.hasCoeToFun.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.symm.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y (Equiv.subtypeEquivCodomain.{u1, u2} X Y (fun (a : X) (b : X) => _inst_1 a b) x f))) (fun (y : Y) => Subtype.mk.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f) (fun (x' : X) => dite.{succ u2} Y (Ne.{succ u1} X x' x) (Ne.decidable.{succ u1} X (fun (a : X) (b : X) => _inst_1 a b) x' x) (fun (h : Ne.{succ u1} X x' x) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x' h)) (fun (h : Not (Ne.{succ u1} X x' x)) => y)) (funext.{succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) (fun (x : Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) => Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y (fun (x' : X) => dite.{succ u2} Y (Ne.{succ u1} X x' x) (Ne.decidable.{succ u1} X (fun (a : X) (b : X) => _inst_1 a b) x' x) (fun (h : Ne.{succ u1} X x' x) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x' h)) (fun (h : Not (Ne.{succ u1} X x' x)) => y)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f (fun (x' : Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) => id.{0} (Eq.{succ u2} Y (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y (fun (x' : X) => dite.{succ u2} Y (Ne.{succ u1} X x' x) (Ne.decidable.{succ u1} X (fun (a : X) (b : X) => _inst_1 a b) x' x) (fun (h : Ne.{succ u1} X x' x) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x' h)) (fun (h : Not (Ne.{succ u1} X x' x)) => y)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)))))) x') (f x')) (Eq.mpr.{0} (Eq.{succ u2} Y (dite.{succ u2} Y (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) (Ne.decidable.{succ u1} X _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x) (fun (h : Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') h)) (fun (h : Not (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x))) => y)) (f x')) (Eq.{succ u2} Y (f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x'))) (f x')) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ u2} Y (dite.{succ u2} Y (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) (Ne.decidable.{succ u1} X _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x) (fun (h : Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') h)) (fun (h : Not (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x))) => y)) (f x')) (Eq.{succ u2} Y (f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x'))) (f x'))) (Eq.ndrec.{0, succ u2} Y (dite.{succ u2} Y (Ne.{succ u1} X (Subtype.val.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x') x) (Ne.decidable.{succ u1} X (fun (a : X) (b : X) => _inst_1 a b) (Subtype.val.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x') x) (fun (h : Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') h)) (fun (h : Not (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x))) => y)) (fun (_a : Y) => Eq.{1} Prop (Eq.{succ u2} Y (dite.{succ u2} Y (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) (Ne.decidable.{succ u1} X _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x) (fun (h : Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') h)) (fun (h : Not (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x))) => y)) (f x')) (Eq.{succ u2} Y _a (f x'))) (rfl.{1} Prop (Eq.{succ u2} Y (dite.{succ u2} Y (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) (Ne.decidable.{succ u1} X _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x) (fun (h : Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') h)) (fun (h : Not (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x))) => y)) (f x'))) (f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x'))) (dif_pos.{succ u2} (Ne.{succ u1} X (Subtype.val.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x') x) (Ne.decidable.{succ u1} X (fun (a : X) (b : X) => _inst_1 a b) (Subtype.val.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x') x) (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x') Y (fun (h : Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x)) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') h)) (fun (h : Not (Not (Eq.{succ u1} X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') x))) => y)))) (Eq.mpr.{0} (Eq.{succ u2} Y (f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x'))) (f x')) (Eq.{succ u2} Y (f x') (f x')) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ u2} Y (f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x'))) (f x')) (Eq.{succ u2} Y (f x') (f x'))) (Eq.ndrec.{0, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (a : X) => Not (Eq.{succ u1} X a x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (a : X) => Not (Eq.{succ u1} X a x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (a : X) => Not (Eq.{succ u1} X a x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (a : X) => Not (Eq.{succ u1} X a x))) X (coeSubtype.{succ u1} X (fun (a : X) => Not (Eq.{succ u1} X a x)))))) x') (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x')) (fun (_a : Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) => Eq.{1} Prop (Eq.{succ u2} Y (f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x'))) (f x')) (Eq.{succ u2} Y (f _a) (f x'))) (rfl.{1} Prop (Eq.{succ u2} Y (f (Subtype.mk.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x))) X (coeSubtype.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)))))) x') (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x'))) (f x'))) x' (Subtype.coe_eta.{succ u1} X (fun (x' : X) => Not (Eq.{succ u1} X x' x)) x' (Subtype.property.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x')))) (rfl.{succ u2} Y (f x')))))))
but is expected to have type
  forall {X : Sort.{u1}} [Y : DecidableEq.{u1} X] {_inst_1 : X} {x : Sort.{u2}} (f : (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x), Eq.{max (max 1 u2) (imax u1 u2)} (forall (a : x), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : x) => Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) a) (FunLike.coe.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (fun (_x : x) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : x) => Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (EquivLike.toEmbeddingLike.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (Equiv.instEquivLikeEquiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))))) (Equiv.symm.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x (Equiv.subtypeEquivCodomain.{u1, u2} X (fun (a : X) (b : X) => Y a b) _inst_1 x f))) (fun (y : x) => Subtype.mk.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f) (fun (x' : X) => dite.{u2} x (Ne.{u1} X x' _inst_1) (instDecidableNot (Eq.{u1} X x' _inst_1) (Y x' _inst_1)) (fun (h : Ne.{u1} X x' _inst_1) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' h)) (fun (h : Not (Ne.{u1} X x' _inst_1)) => y)) (funext.{max 1 u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) (fun (x_1 : Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) => x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x (fun (x' : X) => dite.{u2} x (Ne.{u1} X x' _inst_1) (instDecidableNot (Eq.{u1} X x' _inst_1) (Y x' _inst_1)) (fun (h : Ne.{u1} X x' _inst_1) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' h)) (fun (h : Not (Ne.{u1} X x' _inst_1)) => y)) (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f (fun (x' : Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) => Eq.mpr.{0} (Eq.{u2} x (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x (fun (x' : X) => dite.{u2} x (Ne.{u1} X x' _inst_1) (instDecidableNot (Eq.{u1} X x' _inst_1) (Y x' _inst_1)) (fun (h : Ne.{u1} X x' _inst_1) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' h)) (fun (h : Not (Ne.{u1} X x' _inst_1)) => y)) (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) x') (f x')) ((Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) -> (Eq.{u2} x y (f x'))) (id.{0} (Eq.{1} Prop (Eq.{u2} x (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x (fun (x' : X) => dite.{u2} x (Ne.{u1} X x' _inst_1) (instDecidableNot (Eq.{u1} X x' _inst_1) (Y x' _inst_1)) (fun (h : Ne.{u1} X x' _inst_1) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' h)) (fun (h : Not (Ne.{u1} X x' _inst_1)) => y)) (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) x') (f x')) ((Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) -> (Eq.{u2} x y (f x')))) (Eq.trans.{1} Prop (Eq.{u2} x (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Not (Eq.{u1} X x_1 _inst_1)) (instDecidableNot (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1)) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)) (fun (h : Not (Not (Eq.{u1} X x_1 _inst_1))) => y)) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) x') (f x')) (Eq.{u2} x (dite.{u2} x (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Y (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (fun (h : Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) => y) (fun (h : Not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) => f x')) (f x')) ((Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) -> (Eq.{u2} x y (f x'))) (congrFun.{u2, 1} x (fun (a._@.Init.Prelude._hyg.170 : x) => Prop) (Eq.{u2} x (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Not (Eq.{u1} X x_1 _inst_1)) (instDecidableNot (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1)) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)) (fun (h : Not (Not (Eq.{u1} X x_1 _inst_1))) => y)) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) x')) (Eq.{u2} x (dite.{u2} x (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Y (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (fun (h : Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) => y) (fun (h : Not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) => f x'))) (congrArg.{u2, max 1 u2} x (x -> Prop) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Not (Eq.{u1} X x_1 _inst_1)) (instDecidableNot (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1)) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)) (fun (h : Not (Not (Eq.{u1} X x_1 _inst_1))) => y)) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) x') (dite.{u2} x (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Y (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (fun (h : Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) => y) (fun (h : Not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) => f x')) (Eq.{u2} x) (Eq.trans.{u2} x (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Not (Eq.{u1} X x_1 _inst_1)) (instDecidableNot (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1)) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)) (fun (h : Not (Not (Eq.{u1} X x_1 _inst_1))) => y)) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) x') (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1) (fun (h : Eq.{u1} X x_1 _inst_1) => y) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h))) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) x') (dite.{u2} x (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Y (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (fun (h : Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) => y) (fun (h : Not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) => f x')) (congrFun.{max 1 u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) (fun (a._@.Init.Prelude._hyg.25 : Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) => x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Not (Eq.{u1} X x_1 _inst_1)) (instDecidableNot (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1)) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)) (fun (h : Not (Not (Eq.{u1} X x_1 _inst_1))) => y)) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)))) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1) (fun (h : Eq.{u1} X x_1 _inst_1) => y) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h))) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)))) (congrFun.{imax (max 1 u1) u1, imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) -> X) (fun (g : (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) -> X) => (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Not (Eq.{u1} X x_1 _inst_1)) (instDecidableNot (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1)) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)) (fun (h : Not (Not (Eq.{u1} X x_1 _inst_1))) => y))) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x (fun (x_1 : X) => dite.{u2} x (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1) (fun (h : Eq.{u1} X x_1 _inst_1) => y) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)))) (congrArg.{imax u1 u2, imax (imax (max 1 u1) u1) (max 1 u1) u2} (X -> x) (((Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) -> X) -> (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) -> x) (fun (x_1 : X) => dite.{u2} x (Not (Eq.{u1} X x_1 _inst_1)) (instDecidableNot (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1)) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)) (fun (h : Not (Not (Eq.{u1} X x_1 _inst_1))) => y)) (fun (x_1 : X) => dite.{u2} x (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1) (fun (h : Eq.{u1} X x_1 _inst_1) => y) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h))) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1))) X x) (funext.{u1, u2} X (fun (x_1 : X) => x) (fun (x_1 : X) => dite.{u2} x (Not (Eq.{u1} X x_1 _inst_1)) (instDecidableNot (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1)) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h)) (fun (h : Not (Not (Eq.{u1} X x_1 _inst_1))) => y)) (fun (x_1 : X) => dite.{u2} x (Eq.{u1} X x_1 _inst_1) (Y x_1 _inst_1) (fun (h : Eq.{u1} X x_1 _inst_1) => y) (fun (h : Not (Eq.{u1} X x_1 _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x_1 h))) (fun (x' : X) => dite_not.{u2} x (Eq.{u1} X x' _inst_1) (Y x' _inst_1) (fun (h : Not (Eq.{u1} X x' _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' h)) (fun (h : Not (Not (Eq.{u1} X x' _inst_1))) => y)))) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)))) x') (dite_congr.{u2} (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) x (Y (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Y (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (fun (h : Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) => y) (fun (h : Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) => y) (fun (h : Not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') h)) (fun (h : Not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) => f x') (Eq.refl.{1} Prop (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) (fun (h : Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) => Eq.refl.{u2} x y) (fun (h : Not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) => congrArg.{max 1 u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) x (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) (Subtype.val.{u1} X (fun (a : X) => Ne.{u1} X a _inst_1) x') (Eq.mpr_not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Eq.refl.{1} Prop (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) h)) x' f (Subtype.coe_eta.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' (Eq.mpr_not (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Eq.refl.{1} Prop (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1)) h)))))) (f x')) (Mathlib.Logic.Equiv.Basic._auxLemma.3.{u2} x (Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) (Y (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) y (f x')))) (fun (w : Eq.{u1} X (Subtype.val.{u1} X (fun (x' : X) => Not (Eq.{u1} X x' _inst_1)) x') _inst_1) => False.elim.{0} (Eq.{u2} x y (f x')) (Subtype.property.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' w)))))
Case conversion may be inaccurate. Consider using '#align equiv.coe_subtype_equiv_codomain_symm Equiv.coe_subtypeEquivCodomain_symmₓ'. -/
theorem coe_subtypeEquivCodomain_symm (f : { x' // x' ≠ x } → Y) :
    ((subtypeEquivCodomain f).symm : Y → { g : X → Y // g ∘ coe = f }) = fun y =>
      ⟨fun x' => if h : x' ≠ x then f ⟨x', h⟩ else y,
        by
        funext x'
        dsimp
        erw [dif_pos x'.2, Subtype.coe_eta]⟩ :=
  rfl
#align equiv.coe_subtype_equiv_codomain_symm Equiv.coe_subtypeEquivCodomain_symm

/- warning: equiv.subtype_equiv_codomain_symm_apply -> Equiv.subtypeEquivCodomain_symm_apply is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} X] {x : X} (f : (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (y : Y) (x' : X), Eq.{succ u2} Y ((fun (a : Sort.{max 1 (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (HasLiftT.mk.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeBase.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeSubtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))))) (coeFn.{max 1 (max (succ u2) 1 (succ u1) (succ u2)) (max 1 (succ u1) (succ u2)) (succ u2), max (succ u2) 1 (succ u1) (succ u2)} (Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (fun (_x : Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) => Y -> (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.hasCoeToFun.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.symm.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y (Equiv.subtypeEquivCodomain.{u1, u2} X Y (fun (a : X) (b : X) => _inst_1 a b) x f)) y) x') (dite.{succ u2} Y (Ne.{succ u1} X x' x) (Ne.decidable.{succ u1} X (fun (a : X) (b : X) => _inst_1 a b) x' x) (fun (h : Ne.{succ u1} X x' x) => f (Subtype.mk.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x' h)) (fun (h : Not (Ne.{succ u1} X x' x)) => y))
but is expected to have type
  forall {X : Sort.{u1}} [Y : DecidableEq.{u1} X] {_inst_1 : X} {x : Sort.{u2}} (f : (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (y : x) (x' : X), Eq.{u2} x (Subtype.val.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f) (FunLike.coe.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (fun (_x : x) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : x) => Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (EquivLike.toEmbeddingLike.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (Equiv.instEquivLikeEquiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))))) (Equiv.symm.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x (Equiv.subtypeEquivCodomain.{u1, u2} X (fun (a : X) (b : X) => Y a b) _inst_1 x f)) y) x') (dite.{u2} x (Ne.{u1} X x' _inst_1) (instDecidableNot (Eq.{u1} X x' _inst_1) (Y x' _inst_1)) (fun (h : Ne.{u1} X x' _inst_1) => f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' h)) (fun (h : Not (Ne.{u1} X x' _inst_1)) => y))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_codomain_symm_apply Equiv.subtypeEquivCodomain_symm_applyₓ'. -/
@[simp]
theorem subtypeEquivCodomain_symm_apply (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
  rfl
#align equiv.subtype_equiv_codomain_symm_apply Equiv.subtypeEquivCodomain_symm_apply

/- warning: equiv.subtype_equiv_codomain_symm_apply_eq -> Equiv.subtypeEquivCodomain_symm_apply_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} X] {x : X} (f : (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (y : Y), Eq.{succ u2} Y ((fun (a : Sort.{max 1 (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (HasLiftT.mk.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeBase.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeSubtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))))) (coeFn.{max 1 (max (succ u2) 1 (succ u1) (succ u2)) (max 1 (succ u1) (succ u2)) (succ u2), max (succ u2) 1 (succ u1) (succ u2)} (Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (fun (_x : Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) => Y -> (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.hasCoeToFun.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.symm.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y (Equiv.subtypeEquivCodomain.{u1, u2} X Y (fun (a : X) (b : X) => _inst_1 a b) x f)) y) x) y
but is expected to have type
  forall {X : Sort.{u1}} [Y : DecidableEq.{u1} X] {_inst_1 : X} {x : Sort.{u2}} (f : (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (y : x), Eq.{u2} x (Subtype.val.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f) (FunLike.coe.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (fun (_x : x) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : x) => Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (EquivLike.toEmbeddingLike.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (Equiv.instEquivLikeEquiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))))) (Equiv.symm.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x (Equiv.subtypeEquivCodomain.{u1, u2} X (fun (a : X) (b : X) => Y a b) _inst_1 x f)) y) _inst_1) y
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_codomain_symm_apply_eq Equiv.subtypeEquivCodomain_symm_apply_eqₓ'. -/
@[simp]
theorem subtypeEquivCodomain_symm_apply_eq (f : { x' // x' ≠ x } → Y) (y : Y) :
    ((subtypeEquivCodomain f).symm y : X → Y) x = y :=
  dif_neg (not_not.mpr rfl)
#align equiv.subtype_equiv_codomain_symm_apply_eq Equiv.subtypeEquivCodomain_symm_apply_eq

/- warning: equiv.subtype_equiv_codomain_symm_apply_ne -> Equiv.subtypeEquivCodomain_symm_apply_ne is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} X] {x : X} (f : (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (y : Y) (x' : X) (h : Ne.{succ u1} X x' x), Eq.{succ u2} Y ((fun (a : Sort.{max 1 (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (HasLiftT.mk.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeBase.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) (X -> Y) (coeSubtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))))) (coeFn.{max 1 (max (succ u2) 1 (succ u1) (succ u2)) (max 1 (succ u1) (succ u2)) (succ u2), max (succ u2) 1 (succ u1) (succ u2)} (Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (fun (_x : Equiv.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) => Y -> (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.hasCoeToFun.{succ u2, max 1 (succ u1) (succ u2)} Y (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f))) (Equiv.symm.{max 1 (succ u1) (succ u2), succ u2} (Subtype.{max (succ u1) (succ u2)} (X -> Y) (fun (g : X -> Y) => Eq.{max (succ u1) (succ u2)} ((Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) -> Y) (Function.comp.{succ u1, succ u1, succ u2} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X Y g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeBase.{succ u1, succ u1} (Subtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x)) X (coeSubtype.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x))))))) f)) Y (Equiv.subtypeEquivCodomain.{u1, u2} X Y (fun (a : X) (b : X) => _inst_1 a b) x f)) y) x') (f (Subtype.mk.{succ u1} X (fun (x' : X) => Ne.{succ u1} X x' x) x' h))
but is expected to have type
  forall {X : Sort.{u1}} [Y : DecidableEq.{u1} X] {_inst_1 : X} {x : Sort.{u2}} (f : (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (y : x) (x' : X) (h : Ne.{u1} X x' _inst_1), Eq.{u2} x (Subtype.val.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f) (FunLike.coe.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (fun (_x : x) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : x) => Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (EquivLike.toEmbeddingLike.{max (max 1 u2) (imax u1 u2), u2, max 1 (imax u1 u2)} (Equiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))) x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) (Equiv.instEquivLikeEquiv.{u2, max 1 (imax u1 u2)} x (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f))))) (Equiv.symm.{max 1 (imax u1 u2), u2} (Subtype.{imax u1 u2} (X -> x) (fun (g : X -> x) => Eq.{imax (max 1 u1) u2} ((Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) -> x) (Function.comp.{max 1 u1, u1, u2} (Subtype.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1)) X x g (Subtype.val.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1))) f)) x (Equiv.subtypeEquivCodomain.{u1, u2} X (fun (a : X) (b : X) => Y a b) _inst_1 x f)) y) x') (f (Subtype.mk.{u1} X (fun (x' : X) => Ne.{u1} X x' _inst_1) x' h))
Case conversion may be inaccurate. Consider using '#align equiv.subtype_equiv_codomain_symm_apply_ne Equiv.subtypeEquivCodomain_symm_apply_neₓ'. -/
theorem subtypeEquivCodomain_symm_apply_ne (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X)
    (h : x' ≠ x) : ((subtypeEquivCodomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
  dif_pos h
#align equiv.subtype_equiv_codomain_symm_apply_ne Equiv.subtypeEquivCodomain_symm_apply_ne

end SubtypeEquivCodomain

#print Equiv.ofBijective /-
/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps apply]
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β
    where
  toFun := f
  invFun := Function.surjInv hf.Surjective
  left_inv := Function.leftInverse_surjInv hf
  right_inv := Function.rightInverse_surjInv _
#align equiv.of_bijective Equiv.ofBijective
-/

/- warning: equiv.of_bijective_apply_symm_apply -> Equiv.ofBijective_apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (f : α -> β) (hf : Function.Bijective.{u1, u2} α β f) (x : β), Eq.{u2} β (f (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β (Equiv.ofBijective.{u1, u2} α β f hf)) x)) x
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (f : α -> β) (hf : Function.Bijective.{u2, u1} α β f) (x : β), Eq.{u1} β (f (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β (Equiv.ofBijective.{u2, u1} α β f hf)) x)) x
Case conversion may be inaccurate. Consider using '#align equiv.of_bijective_apply_symm_apply Equiv.ofBijective_apply_symm_applyₓ'. -/
theorem ofBijective_apply_symm_apply (f : α → β) (hf : Bijective f) (x : β) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x
#align equiv.of_bijective_apply_symm_apply Equiv.ofBijective_apply_symm_apply

/- warning: equiv.of_bijective_symm_apply_apply -> Equiv.ofBijective_symm_apply_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (f : α -> β) (hf : Function.Bijective.{u1, u2} α β f) (x : α), Eq.{u1} α (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β (Equiv.ofBijective.{u1, u2} α β f hf)) (f x)) x
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (f : α -> β) (hf : Function.Bijective.{u2, u1} α β f) (x : α), Eq.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (f x)) (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β (Equiv.ofBijective.{u2, u1} α β f hf)) (f x)) x
Case conversion may be inaccurate. Consider using '#align equiv.of_bijective_symm_apply_apply Equiv.ofBijective_symm_apply_applyₓ'. -/
@[simp]
theorem ofBijective_symm_apply_apply (f : α → β) (hf : Bijective f) (x : α) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x
#align equiv.of_bijective_symm_apply_apply Equiv.ofBijective_symm_apply_apply

instance : CanLift (α → β) (α ≃ β) coeFn Bijective where prf f hf := ⟨ofBijective f hf, rfl⟩

section

variable {α' β' : Type _} (e : Perm α') {p : β' → Prop} [DecidablePred p] (f : α' ≃ Subtype p)

#print Equiv.Perm.extendDomain /-
/-- Extend the domain of `e : equiv.perm α` to one that is over `β` via `f : α → subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `set.range f` fixed. For this use-case `equiv` given by `f` can
be constructed by `equiv.of_left_inverse'` or `equiv.of_left_inverse` when there is a known
inverse, or `equiv.of_injective` in the general case.`.
-/
def Perm.extendDomain : Perm β' :=
  (permCongr f e).subtypeCongr (Equiv.refl _)
#align equiv.perm.extend_domain Equiv.Perm.extendDomain
-/

#print Equiv.Perm.extendDomain_apply_image /-
@[simp]
theorem Perm.extendDomain_apply_image (a : α') : e.extendDomain f (f a) = f (e a) := by
  simp [perm.extend_domain]
#align equiv.perm.extend_domain_apply_image Equiv.Perm.extendDomain_apply_image
-/

#print Equiv.Perm.extendDomain_apply_subtype /-
theorem Perm.extendDomain_apply_subtype {b : β'} (h : p b) :
    e.extendDomain f b = f (e (f.symm ⟨b, h⟩)) := by simp [perm.extend_domain, h]
#align equiv.perm.extend_domain_apply_subtype Equiv.Perm.extendDomain_apply_subtype
-/

#print Equiv.Perm.extendDomain_apply_not_subtype /-
theorem Perm.extendDomain_apply_not_subtype {b : β'} (h : ¬p b) : e.extendDomain f b = b := by
  simp [perm.extend_domain, h]
#align equiv.perm.extend_domain_apply_not_subtype Equiv.Perm.extendDomain_apply_not_subtype
-/

#print Equiv.Perm.extendDomain_refl /-
@[simp]
theorem Perm.extendDomain_refl : Perm.extendDomain (Equiv.refl _) f = Equiv.refl _ := by
  simp [perm.extend_domain]
#align equiv.perm.extend_domain_refl Equiv.Perm.extendDomain_refl
-/

#print Equiv.Perm.extendDomain_symm /-
@[simp]
theorem Perm.extendDomain_symm : (e.extendDomain f).symm = Perm.extendDomain e.symm f :=
  rfl
#align equiv.perm.extend_domain_symm Equiv.Perm.extendDomain_symm
-/

/- warning: equiv.perm.extend_domain_trans -> Equiv.Perm.extendDomain_trans is a dubious translation:
lean 3 declaration is
  forall {α' : Type.{u1}} {β' : Type.{u2}} {p : β' -> Prop} [_inst_1 : DecidablePred.{succ u2} β' p] (f : Equiv.{succ u1, succ u2} α' (Subtype.{succ u2} β' p)) (e : Equiv.Perm.{succ u1} α') (e' : Equiv.Perm.{succ u1} α'), Eq.{succ u2} (Equiv.{succ u2, succ u2} β' β') (Equiv.trans.{succ u2, succ u2, succ u2} β' β' β' (Equiv.Perm.extendDomain.{u1, u2} α' β' e p (fun (a : β') => _inst_1 a) f) (Equiv.Perm.extendDomain.{u1, u2} α' β' e' p (fun (a : β') => _inst_1 a) f)) (Equiv.Perm.extendDomain.{u1, u2} α' β' (Equiv.trans.{succ u1, succ u1, succ u1} α' α' α' e e') p (fun (a : β') => _inst_1 a) f)
but is expected to have type
  forall {α' : Type.{u2}} {β' : Type.{u1}} {p : β' -> Prop} [_inst_1 : DecidablePred.{succ u1} β' p] (f : Equiv.{succ u2, succ u1} α' (Subtype.{succ u1} β' p)) (e : Equiv.Perm.{succ u2} α') (e' : Equiv.Perm.{succ u2} α'), Eq.{succ u1} (Equiv.{succ u1, succ u1} β' β') (Equiv.trans.{succ u1, succ u1, succ u1} β' β' β' (Equiv.Perm.extendDomain.{u2, u1} α' β' e p (fun (a : β') => _inst_1 a) f) (Equiv.Perm.extendDomain.{u2, u1} α' β' e' p (fun (a : β') => _inst_1 a) f)) (Equiv.Perm.extendDomain.{u2, u1} α' β' (Equiv.trans.{succ u2, succ u2, succ u2} α' α' α' e e') p (fun (a : β') => _inst_1 a) f)
Case conversion may be inaccurate. Consider using '#align equiv.perm.extend_domain_trans Equiv.Perm.extendDomain_transₓ'. -/
theorem Perm.extendDomain_trans (e e' : Perm α') :
    (e.extendDomain f).trans (e'.extendDomain f) = Perm.extendDomain (e.trans e') f := by
  simp [perm.extend_domain, perm_congr_trans]
#align equiv.perm.extend_domain_trans Equiv.Perm.extendDomain_trans

end

#print Equiv.subtypeQuotientEquivQuotientSubtype /-
/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtypeQuotientEquivQuotientSubtype (p₁ : α → Prop) [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)]
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y) : { x // p₂ x } ≃ Quotient s₂
    where
  toFun a :=
    Quotient.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab =>
        hfunext (by rw [Quotient.sound hab]) fun h₁ h₂ _ =>
          hEq_of_eq (Quotient.sound ((h _ _).2 hab)))
      a.2
  invFun a :=
    Quotient.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun a b hab =>
      Subtype.ext_val (Quotient.sound ((h _ _).1 hab))
  left_inv := fun ⟨a, ha⟩ => Quotient.inductionOn a (fun a ha => rfl) ha
  right_inv a := Quotient.inductionOn a fun ⟨a, ha⟩ => rfl
#align equiv.subtype_quotient_equiv_quotient_subtype Equiv.subtypeQuotientEquivQuotientSubtype
-/

#print Equiv.subtypeQuotientEquivQuotientSubtype_mk /-
@[simp]
theorem subtypeQuotientEquivQuotientSubtype_mk (p₁ : α → Prop) [s₁ : Setoid α]
    [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y) (x hx) :
    subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ :=
  rfl
#align equiv.subtype_quotient_equiv_quotient_subtype_mk Equiv.subtypeQuotientEquivQuotientSubtype_mk
-/

#print Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk /-
@[simp]
theorem subtypeQuotientEquivQuotientSubtype_symm_mk (p₁ : α → Prop) [s₁ : Setoid α]
    [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, @Setoid.r _ s₂ x y ↔ (x : α) ≈ y) (x) :
    (subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.Prop⟩ :=
  rfl
#align equiv.subtype_quotient_equiv_quotient_subtype_symm_mk Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk
-/

section Swap

variable [DecidableEq α]

#print Equiv.swapCore /-
/-- A helper function for `equiv.swap`. -/
def swapCore (a b r : α) : α :=
  if r = a then b else if r = b then a else r
#align equiv.swap_core Equiv.swapCore
-/

#print Equiv.swapCore_self /-
theorem swapCore_self (r a : α) : swapCore a a r = r :=
  by
  unfold swap_core
  split_ifs <;> cc
#align equiv.swap_core_self Equiv.swapCore_self
-/

#print Equiv.swapCore_swapCore /-
theorem swapCore_swapCore (r a b : α) : swapCore a b (swapCore a b r) = r :=
  by
  unfold swap_core
  split_ifs <;> cc
#align equiv.swap_core_swap_core Equiv.swapCore_swapCore
-/

#print Equiv.swapCore_comm /-
theorem swapCore_comm (r a b : α) : swapCore a b r = swapCore b a r :=
  by
  unfold swap_core
  split_ifs <;> cc
#align equiv.swap_core_comm Equiv.swapCore_comm
-/

#print Equiv.swap /-
/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : Perm α :=
  ⟨swapCore a b, swapCore a b, fun r => swapCore_swapCore r a b, fun r => swapCore_swapCore r a b⟩
#align equiv.swap Equiv.swap
-/

#print Equiv.swap_self /-
@[simp]
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
  ext fun r => swapCore_self r a
#align equiv.swap_self Equiv.swap_self
-/

#print Equiv.swap_comm /-
theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext fun r => swapCore_comm r _ _
#align equiv.swap_comm Equiv.swap_comm
-/

#print Equiv.swap_apply_def /-
theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl
#align equiv.swap_apply_def Equiv.swap_apply_def
-/

#print Equiv.swap_apply_left /-
@[simp]
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl
#align equiv.swap_apply_left Equiv.swap_apply_left
-/

#print Equiv.swap_apply_right /-
@[simp]
theorem swap_apply_right (a b : α) : swap a b b = a := by
  by_cases h : b = a <;> simp [swap_apply_def, h]
#align equiv.swap_apply_right Equiv.swap_apply_right
-/

#print Equiv.swap_apply_of_ne_of_ne /-
theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x := by
  simp (config := { contextual := true }) [swap_apply_def]
#align equiv.swap_apply_of_ne_of_ne Equiv.swap_apply_of_ne_of_ne
-/

#print Equiv.swap_swap /-
@[simp]
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _ :=
  ext fun x => swapCore_swapCore _ _ _
#align equiv.swap_swap Equiv.swap_swap
-/

#print Equiv.symm_swap /-
@[simp]
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl
#align equiv.symm_swap Equiv.symm_swap
-/

#print Equiv.swap_eq_refl_iff /-
@[simp]
theorem swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y :=
  by
  refine' ⟨fun h => (Equiv.refl _).Injective _, fun h => h ▸ swap_self _⟩
  rw [← h, swap_apply_left, h, refl_apply]
#align equiv.swap_eq_refl_iff Equiv.swap_eq_refl_iff
-/

#print Equiv.swap_comp_apply /-
theorem swap_comp_apply {a b x : α} (π : Perm α) :
    π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x :=
  by
  cases π
  rfl
#align equiv.swap_comp_apply Equiv.swap_comp_apply
-/

#print Equiv.swap_eq_update /-
theorem swap_eq_update (i j : α) : (Equiv.swap i j : α → α) = update (update id j i) i j :=
  funext fun x => by rw [update_apply _ i j, update_apply _ j i, Equiv.swap_apply_def, id.def]
#align equiv.swap_eq_update Equiv.swap_eq_update
-/

/- warning: equiv.comp_swap_eq_update -> Equiv.comp_swap_eq_update is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] (i : α) (j : α) (f : α -> β), Eq.{imax u1 u2} (α -> β) (Function.comp.{u1, u1, u2} α α β f (coeFn.{max 1 u1, u1} (Equiv.Perm.{u1} α) (fun (_x : Equiv.{u1, u1} α α) => α -> α) (Equiv.hasCoeToFun.{u1, u1} α α) (Equiv.swap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i j))) (Function.update.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_1 a b) (Function.update.{u1, u2} α (fun (a : α) => β) (fun (a : α) (b : α) => _inst_1 a b) f j (f i)) i (f j))
but is expected to have type
  forall {α : Sort.{u1}} [β : DecidableEq.{u1} α] {_inst_1 : Sort.{u2}} (i : α) (j : α) (f : α -> _inst_1), Eq.{imax u1 u2} (α -> _inst_1) (Function.comp.{u1, u1, u2} α α _inst_1 f (FunLike.coe.{max 1 u1, u1, u1} (Equiv.Perm.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} α) α α (EquivLike.toEmbeddingLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} α) α α (Equiv.instEquivLikeEquiv.{u1, u1} α α))) (Equiv.swap.{u1} α (fun (a : α) (b : α) => β a b) i j))) (Function.update.{u1, u2} α (fun (ᾰ : α) => _inst_1) (fun (a : α) (b : α) => β a b) (Function.update.{u1, u2} α (fun (a : α) => _inst_1) (fun (a : α) (b : α) => β a b) f j (f i)) i (f j))
Case conversion may be inaccurate. Consider using '#align equiv.comp_swap_eq_update Equiv.comp_swap_eq_updateₓ'. -/
theorem comp_swap_eq_update (i j : α) (f : α → β) :
    f ∘ Equiv.swap i j = update (update f j (f i)) i (f j) := by
  rw [swap_eq_update, comp_update, comp_update, comp.right_id]
#align equiv.comp_swap_eq_update Equiv.comp_swap_eq_update

/- warning: equiv.symm_trans_swap_trans -> Equiv.symm_trans_swap_trans is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] [_inst_2 : DecidableEq.{u2} β] (a : α) (b : α) (e : Equiv.{u1, u2} α β), Eq.{max 1 u2} (Equiv.{u2, u2} β β) (Equiv.trans.{u2, u1, u2} β α β (Equiv.trans.{u2, u1, u1} β α α (Equiv.symm.{u1, u2} α β e) (Equiv.swap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b)) e) (Equiv.swap.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e a) (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e b))
but is expected to have type
  forall {α : Sort.{u1}} [β : DecidableEq.{u1} α] {_inst_1 : Sort.{u2}} [_inst_2 : DecidableEq.{u2} _inst_1] (a : α) (b : α) (e : Equiv.{u1, u2} α _inst_1), Eq.{max 1 u2} (Equiv.{u2, u2} _inst_1 _inst_1) (Equiv.trans.{u2, u1, u2} _inst_1 α _inst_1 (Equiv.trans.{u2, u1, u1} _inst_1 α α (Equiv.symm.{u1, u2} α _inst_1 e) (Equiv.swap.{u1} α (fun (a : α) (b : α) => β a b) a b)) e) (Equiv.swap.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => _inst_1) a) (fun (a : _inst_1) (b : _inst_1) => _inst_2 a b) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => _inst_1) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α _inst_1 (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α _inst_1 (Equiv.instEquivLikeEquiv.{u1, u2} α _inst_1))) e a) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => _inst_1) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α _inst_1 (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α _inst_1 (Equiv.instEquivLikeEquiv.{u1, u2} α _inst_1))) e b))
Case conversion may be inaccurate. Consider using '#align equiv.symm_trans_swap_trans Equiv.symm_trans_swap_transₓ'. -/
@[simp]
theorem symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) :
    (e.symm.trans (swap a b)).trans e = swap (e a) (e b) :=
  Equiv.ext fun x =>
    by
    have : ∀ a, e.symm x = a ↔ x = e a := fun a =>
      by
      rw [@eq_comm _ (e.symm x)]
      constructor <;> intros <;> simp_all
    simp [swap_apply_def, this]
    split_ifs <;> simp
#align equiv.symm_trans_swap_trans Equiv.symm_trans_swap_trans

/- warning: equiv.trans_swap_trans_symm -> Equiv.trans_swap_trans_symm is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] [_inst_2 : DecidableEq.{u2} β] (a : β) (b : β) (e : Equiv.{u1, u2} α β), Eq.{max 1 u1} (Equiv.{u1, u1} α α) (Equiv.trans.{u1, u2, u1} α β α (Equiv.trans.{u1, u2, u2} α β β e (Equiv.swap.{u2} β (fun (a : β) (b : β) => _inst_2 a b) a b)) (Equiv.symm.{u1, u2} α β e)) (Equiv.swap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) a) (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))
but is expected to have type
  forall {α : Sort.{u1}} [β : DecidableEq.{u1} α] {_inst_1 : Sort.{u2}} [_inst_2 : DecidableEq.{u2} _inst_1] (a : _inst_1) (b : _inst_1) (e : Equiv.{u1, u2} α _inst_1), Eq.{max 1 u1} (Equiv.{u1, u1} α α) (Equiv.trans.{u1, u2, u1} α _inst_1 α (Equiv.trans.{u1, u2, u2} α _inst_1 _inst_1 e (Equiv.swap.{u2} _inst_1 (fun (a : _inst_1) (b : _inst_1) => _inst_2 a b) a b)) (Equiv.symm.{u1, u2} α _inst_1 e)) (Equiv.swap.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : _inst_1) => α) a) (fun (a : α) (b : α) => β a b) (FunLike.coe.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} _inst_1 α) _inst_1 (fun (_x : _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : _inst_1) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} _inst_1 α) _inst_1 α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} _inst_1 α) _inst_1 α (Equiv.instEquivLikeEquiv.{u2, u1} _inst_1 α))) (Equiv.symm.{u1, u2} α _inst_1 e) a) (FunLike.coe.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} _inst_1 α) _inst_1 (fun (_x : _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : _inst_1) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} _inst_1 α) _inst_1 α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} _inst_1 α) _inst_1 α (Equiv.instEquivLikeEquiv.{u2, u1} _inst_1 α))) (Equiv.symm.{u1, u2} α _inst_1 e) b))
Case conversion may be inaccurate. Consider using '#align equiv.trans_swap_trans_symm Equiv.trans_swap_trans_symmₓ'. -/
@[simp]
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
    (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm
#align equiv.trans_swap_trans_symm Equiv.trans_swap_trans_symm

#print Equiv.swap_apply_self /-
@[simp]
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a := by
  rw [← Equiv.trans_apply, Equiv.swap_swap, Equiv.refl_apply]
#align equiv.swap_apply_self Equiv.swap_apply_self
-/

/- warning: equiv.apply_swap_eq_self -> Equiv.apply_swap_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] {v : α -> β} {i : α} {j : α}, (Eq.{u2} β (v i) (v j)) -> (forall (k : α), Eq.{u2} β (v (coeFn.{max 1 u1, u1} (Equiv.Perm.{u1} α) (fun (_x : Equiv.{u1, u1} α α) => α -> α) (Equiv.hasCoeToFun.{u1, u1} α α) (Equiv.swap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) k)) (v k))
but is expected to have type
  forall {α : Sort.{u1}} [β : DecidableEq.{u1} α] {_inst_1 : Sort.{u2}} {v : α -> _inst_1} {i : α} {j : α}, (Eq.{u2} _inst_1 (v i) (v j)) -> (forall (k : α), Eq.{u2} _inst_1 (v (FunLike.coe.{max 1 u1, u1, u1} (Equiv.Perm.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} α) α α (EquivLike.toEmbeddingLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} α) α α (Equiv.instEquivLikeEquiv.{u1, u1} α α))) (Equiv.swap.{u1} α (fun (a : α) (b : α) => β a b) i j) k)) (v k))
Case conversion may be inaccurate. Consider using '#align equiv.apply_swap_eq_self Equiv.apply_swap_eq_selfₓ'. -/
/-- A function is invariant to a swap if it is equal at both elements -/
theorem apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) : v (swap i j k) = v k :=
  by
  by_cases hi : k = i; · rw [hi, swap_apply_left, hv]
  by_cases hj : k = j; · rw [hj, swap_apply_right, hv]
  rw [swap_apply_of_ne_of_ne hi hj]
#align equiv.apply_swap_eq_self Equiv.apply_swap_eq_self

#print Equiv.swap_apply_eq_iff /-
theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w := by
  rw [apply_eq_iff_eq_symm_apply, symm_swap]
#align equiv.swap_apply_eq_iff Equiv.swap_apply_eq_iff
-/

#print Equiv.swap_apply_ne_self_iff /-
theorem swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) :=
  by
  by_cases hab : a = b
  · simp [hab]
  by_cases hax : x = a
  · simp [hax, eq_comm]
  by_cases hbx : x = b
  · simp [hbx]
  simp [hab, hax, hbx, swap_apply_of_ne_of_ne]
#align equiv.swap_apply_ne_self_iff Equiv.swap_apply_ne_self_iff
-/

namespace Perm

/- warning: equiv.perm.sum_congr_swap_refl -> Equiv.Perm.sumCongr_swap_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : DecidableEq.{succ u2} β] (i : α) (j : α), Eq.{max 1 (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.sumCongr.{u1, u2} α β (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_2 a b) i j) (Equiv.refl.{succ u2} β)) (Equiv.swap.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => Sum.decidableEq.{u1, u2} α (fun (a : α) (b : α) => _inst_2 a b) β (fun (a : β) (b : β) => _inst_3 a b) a b) (Sum.inl.{u1, u2} α β i) (Sum.inl.{u1, u2} α β j))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : DecidableEq.{succ u1} β] (i : α) (j : α), Eq.{max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.sumCongr.{u2, u1} α β (Equiv.swap.{succ u2} α (fun (a : α) (b : α) => _inst_2 a b) i j) (Equiv.refl.{succ u1} β)) (Equiv.swap.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (fun (a : Sum.{u2, u1} α β) (b : Sum.{u2, u1} α β) => Sum.instDecidableEqSum.{u2, u1} α β (fun (a : α) (b : α) => _inst_2 a b) (fun (a : β) (b : β) => _inst_3 a b) a b) (Sum.inl.{u2, u1} α β i) (Sum.inl.{u2, u1} α β j))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_swap_refl Equiv.Perm.sumCongr_swap_reflₓ'. -/
@[simp]
theorem sumCongr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
    Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i) (Sum.inl j) :=
  by
  ext x
  cases x
  · simp [Sum.map, swap_apply_def]
    split_ifs <;> rfl
  · simp [Sum.map, swap_apply_of_ne_of_ne]
#align equiv.perm.sum_congr_swap_refl Equiv.Perm.sumCongr_swap_refl

/- warning: equiv.perm.sum_congr_refl_swap clashes with equiv.perm.sumCongr_refl_swap -> Equiv.Perm.sumCongr_refl_swap
warning: equiv.perm.sum_congr_refl_swap -> Equiv.Perm.sumCongr_refl_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : DecidableEq.{succ u2} β] (i : β) (j : β), Eq.{max 1 (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.sumCongr.{u1, u2} α β (Equiv.refl.{succ u1} α) (Equiv.swap.{succ u2} β (fun (a : β) (b : β) => _inst_3 a b) i j)) (Equiv.swap.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => Sum.decidableEq.{u1, u2} α (fun (a : α) (b : α) => _inst_2 a b) β (fun (a : β) (b : β) => _inst_3 a b) a b) (Sum.inr.{u1, u2} α β i) (Sum.inr.{u1, u2} α β j))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : DecidableEq.{succ u1} β] (i : β) (j : β), Eq.{max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.sumCongr.{u2, u1} α β (Equiv.refl.{succ u2} α) (Equiv.swap.{succ u1} β (fun (a : β) (b : β) => _inst_3 a b) i j)) (Equiv.swap.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (fun (a : Sum.{u2, u1} α β) (b : Sum.{u2, u1} α β) => Sum.instDecidableEqSum.{u2, u1} α β (fun (a : α) (b : α) => _inst_2 a b) (fun (a : β) (b : β) => _inst_3 a b) a b) (Sum.inr.{u2, u1} α β i) (Sum.inr.{u2, u1} α β j))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_refl_swap Equiv.Perm.sumCongr_refl_swapₓ'. -/
@[simp]
theorem sumCongr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
    Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) :=
  by
  ext x
  cases x
  · simp [Sum.map, swap_apply_of_ne_of_ne]
  · simp [Sum.map, swap_apply_def]
    split_ifs <;> rfl
#align equiv.perm.sum_congr_refl_swap Equiv.Perm.sumCongr_refl_swap

end Perm

/- warning: equiv.set_value -> Equiv.setValue is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α], (Equiv.{u1, u2} α β) -> α -> β -> (Equiv.{u1, u2} α β)
but is expected to have type
  forall {α : Sort.{u1}} [β : DecidableEq.{u1} α] {_inst_1 : Sort.{u2}}, (Equiv.{u1, u2} α _inst_1) -> α -> _inst_1 -> (Equiv.{u1, u2} α _inst_1)
Case conversion may be inaccurate. Consider using '#align equiv.set_value Equiv.setValueₓ'. -/
/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f
#align equiv.set_value Equiv.setValue

/- warning: equiv.set_value_eq -> Equiv.setValue_eq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] (f : Equiv.{u1, u2} α β) (a : α) (b : β), Eq.{u2} β (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) (Equiv.setValue.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) f a b) a) b
but is expected to have type
  forall {α : Sort.{u1}} [β : DecidableEq.{u1} α] {_inst_1 : Sort.{u2}} (f : Equiv.{u1, u2} α _inst_1) (a : α) (b : _inst_1), Eq.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => _inst_1) a) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => _inst_1) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α _inst_1 (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α _inst_1) α _inst_1 (Equiv.instEquivLikeEquiv.{u1, u2} α _inst_1))) (Equiv.setValue.{u1, u2} α (fun (a : α) (b : α) => β a b) _inst_1 f a b) a) b
Case conversion may be inaccurate. Consider using '#align equiv.set_value_eq Equiv.setValue_eqₓ'. -/
@[simp]
theorem setValue_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b :=
  by
  dsimp [set_value]
  simp [swap_apply_left]
#align equiv.set_value_eq Equiv.setValue_eq

end Swap

end Equiv

namespace Function.Involutive

#print Function.Involutive.toPerm /-
/-- Convert an involutive function `f` to a permutation with `to_fun = inv_fun = f`. -/
def toPerm (f : α → α) (h : Involutive f) : Equiv.Perm α :=
  ⟨f, f, h.LeftInverse, h.RightInverse⟩
#align function.involutive.to_perm Function.Involutive.toPerm
-/

#print Function.Involutive.coe_toPerm /-
@[simp]
theorem coe_toPerm {f : α → α} (h : Involutive f) : (h.toPerm f : α → α) = f :=
  rfl
#align function.involutive.coe_to_perm Function.Involutive.coe_toPerm
-/

#print Function.Involutive.toPerm_symm /-
@[simp]
theorem toPerm_symm {f : α → α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm f :=
  rfl
#align function.involutive.to_perm_symm Function.Involutive.toPerm_symm
-/

#print Function.Involutive.toPerm_involutive /-
theorem toPerm_involutive {f : α → α} (h : Involutive f) : Involutive (h.toPerm f) :=
  h
#align function.involutive.to_perm_involutive Function.Involutive.toPerm_involutive
-/

end Function.Involutive

#print PLift.eq_up_iff_down_eq /-
theorem PLift.eq_up_iff_down_eq {x : PLift α} {y : α} : x = PLift.up y ↔ x.down = y :=
  Equiv.plift.eq_symm_apply
#align plift.eq_up_iff_down_eq PLift.eq_up_iff_down_eq
-/

/- warning: function.injective.map_swap -> Function.Injective.map_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (x : α) (y : α) (z : α), Eq.{succ u2} β (f (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) z)) (coeFn.{succ u2, succ u2} (Equiv.Perm.{succ u2} β) (fun (_x : Equiv.{succ u2, succ u2} β β) => β -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} β β) (Equiv.swap.{succ u2} β (fun (a : β) (b : β) => _inst_2 a b) (f x) (f y)) (f z)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : DecidableEq.{u2} α] [_inst_2 : DecidableEq.{u1} β] {f : α -> β}, (Function.Injective.{u2, u1} α β f) -> (forall (x : α) (y : α) (z : α), Eq.{u1} β (f (FunLike.coe.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α α (EquivLike.toEmbeddingLike.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α α (Equiv.instEquivLikeEquiv.{u2, u2} α α))) (Equiv.swap.{u2} α (fun (a : α) (b : α) => _inst_1 a b) x y) z)) (FunLike.coe.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => β) _x) (EmbeddingLike.toFunLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β β (EquivLike.toEmbeddingLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β β (Equiv.instEquivLikeEquiv.{u1, u1} β β))) (Equiv.swap.{u1} β (fun (a : β) (b : β) => _inst_2 a b) (f x) (f y)) (f z)))
Case conversion may be inaccurate. Consider using '#align function.injective.map_swap Function.Injective.map_swapₓ'. -/
theorem Function.Injective.map_swap {α β : Type _} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y z : α) : f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) :=
  by
  conv_rhs => rw [Equiv.swap_apply_def]
  split_ifs with h₁ h₂
  · rw [hf h₁, Equiv.swap_apply_left]
  · rw [hf h₂, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne (mt (congr_arg f) h₁) (mt (congr_arg f) h₂)]
#align function.injective.map_swap Function.Injective.map_swap

namespace Equiv

section

variable (P : α → Sort w) (e : α ≃ β)

#print Equiv.piCongrLeft' /-
/-- Transport dependent functions through an equivalence of the base space.
-/
@[simps]
def piCongrLeft' : (∀ a, P a) ≃ ∀ b, P (e.symm b)
    where
  toFun f x := f (e.symm x)
  invFun f x := by rw [← e.symm_apply_apply x]; exact f (e x)
  left_inv f :=
    funext fun x =>
      eq_of_hEq
        ((eq_rec_hEq _ _).trans
          (by
            dsimp
            rw [e.symm_apply_apply]))
  right_inv f := funext fun x => eq_of_hEq ((eq_rec_hEq _ _).trans (by rw [e.apply_symm_apply]))
#align equiv.Pi_congr_left' Equiv.piCongrLeft'
-/

end

section

variable (P : β → Sort w) (e : α ≃ β)

/- warning: equiv.Pi_congr_left -> Equiv.piCongrLeft is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (P : β -> Sort.{u3}) (e : Equiv.{u1, u2} α β), Equiv.{imax u1 u3, imax u2 u3} (forall (a : α), P (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e a)) (forall (b : β), P b)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u3}} (P : α -> Sort.{u1}) (e : Equiv.{u3, u2} β α), Equiv.{imax u3 u1, imax u2 u1} (forall (a : β), P (FunLike.coe.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} β α) β α (Equiv.instEquivLikeEquiv.{u3, u2} β α))) e a)) (forall (b : α), P b)
Case conversion may be inaccurate. Consider using '#align equiv.Pi_congr_left Equiv.piCongrLeftₓ'. -/
/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def piCongrLeft : (∀ a, P (e a)) ≃ ∀ b, P b :=
  (piCongrLeft' P e.symm).symm
#align equiv.Pi_congr_left Equiv.piCongrLeft

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ a : α, W a ≃ Z (h₁ a))

/- warning: equiv.Pi_congr -> Equiv.piCongr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u1, u2} α β), (forall (a : α), Equiv.{u3, u4} (W a) (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a))) -> (Equiv.{imax u1 u3, imax u2 u4} (forall (a : α), W a) (forall (b : β), Z b))
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u4}} {W : α -> Sort.{u1}} {Z : β -> Sort.{u2}} (h₁ : Equiv.{u3, u4} α β), (forall (a : α), Equiv.{u1, u2} (W a) (Z (FunLike.coe.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} α β) α β (Equiv.instEquivLikeEquiv.{u3, u4} α β))) h₁ a))) -> (Equiv.{imax u3 u1, imax u4 u2} (forall (a : α), W a) (forall (b : β), Z b))
Case conversion may be inaccurate. Consider using '#align equiv.Pi_congr Equiv.piCongrₓ'. -/
/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def piCongr : (∀ a, W a) ≃ ∀ b, Z b :=
  (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)
#align equiv.Pi_congr Equiv.piCongr

#print Equiv.coe_piCongr_symm /-
@[simp]
theorem coe_piCongr_symm :
    ((h₁.piCongr h₂).symm : (∀ b, Z b) → ∀ a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl
#align equiv.coe_Pi_congr_symm Equiv.coe_piCongr_symm
-/

/- warning: equiv.Pi_congr_symm_apply -> Equiv.piCongr_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u1, u2} α β) (h₂ : forall (a : α), Equiv.{u3, u4} (W a) (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a))) (f : forall (b : β), Z b), Eq.{imax u1 u3} (forall (a : α), W a) (coeFn.{max 1 (imax (imax u2 u4) u1 u3) (imax (imax u1 u3) u2 u4), imax (imax u2 u4) u1 u3} (Equiv.{imax u2 u4, imax u1 u3} (forall (b : β), Z b) (forall (a : α), W a)) (fun (_x : Equiv.{imax u2 u4, imax u1 u3} (forall (b : β), Z b) (forall (a : α), W a)) => (forall (b : β), Z b) -> (forall (a : α), W a)) (Equiv.hasCoeToFun.{imax u2 u4, imax u1 u3} (forall (b : β), Z b) (forall (a : α), W a)) (Equiv.symm.{imax u1 u3, imax u2 u4} (forall (a : α), W a) (forall (b : β), Z b) (Equiv.piCongr.{u1, u2, u3, u4} α β (fun (a : α) => W a) Z h₁ h₂)) f) (fun (a : α) => coeFn.{max 1 (imax u4 u3) (imax u3 u4), imax u4 u3} (Equiv.{u4, u3} (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a)) (W a)) (fun (_x : Equiv.{u4, u3} (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a)) (W a)) => (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a)) -> (W a)) (Equiv.hasCoeToFun.{u4, u3} (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a)) (W a)) (Equiv.symm.{u3, u4} (W a) (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a)) (h₂ a)) (f (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u2, u1} α β) (h₂ : forall (a : α), Equiv.{u3, u4} (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a))) (f : forall (b : β), Z b), Eq.{imax u2 u3} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (b : β), Z b) => forall (a : α), W a) f) (FunLike.coe.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u1 u4, imax u2 u3} (Equiv.{imax u1 u4, imax u2 u3} (forall (b : β), Z b) (forall (a : α), W a)) (forall (b : β), Z b) (fun (_x : forall (b : β), Z b) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (b : β), Z b) => forall (a : α), W a) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u1 u4, imax u2 u3} (Equiv.{imax u1 u4, imax u2 u3} (forall (b : β), Z b) (forall (a : α), W a)) (forall (b : β), Z b) (forall (b : α), W b) (EquivLike.toEmbeddingLike.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u1 u4, imax u2 u3} (Equiv.{imax u1 u4, imax u2 u3} (forall (b : β), Z b) (forall (a : α), W a)) (forall (b : β), Z b) (forall (a : α), W a) (Equiv.instEquivLikeEquiv.{imax u1 u4, imax u2 u3} (forall (b : β), Z b) (forall (a : α), W a)))) (Equiv.symm.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b) (Equiv.piCongr.{u3, u4, u2, u1} α β (fun (a : α) => W a) Z h₁ h₂)) f) (fun (a : α) => FunLike.coe.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (W a)) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (fun (_x : Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) => W a) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (W a)) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (W a) (EquivLike.toEmbeddingLike.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (W a)) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (W a) (Equiv.instEquivLikeEquiv.{u4, u3} (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (W a)))) (Equiv.symm.{u3, u4} (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (h₂ a)) (f (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)))
Case conversion may be inaccurate. Consider using '#align equiv.Pi_congr_symm_apply Equiv.piCongr_symm_applyₓ'. -/
theorem piCongr_symm_apply (f : ∀ b, Z b) :
    (h₁.piCongr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl
#align equiv.Pi_congr_symm_apply Equiv.piCongr_symm_apply

/- warning: equiv.Pi_congr_apply_apply -> Equiv.piCongr_apply_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u1, u2} α β) (h₂ : forall (a : α), Equiv.{u3, u4} (W a) (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a))) (f : forall (a : α), W a) (a : α), Eq.{u4} (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a)) (coeFn.{max 1 (imax (imax u1 u3) u2 u4) (imax (imax u2 u4) u1 u3), imax (imax u1 u3) u2 u4} (Equiv.{imax u1 u3, imax u2 u4} (forall (a : α), (fun (a : α) => W a) a) (forall (b : β), Z b)) (fun (_x : Equiv.{imax u1 u3, imax u2 u4} (forall (a : α), (fun (a : α) => W a) a) (forall (b : β), Z b)) => (forall (a : α), (fun (a : α) => W a) a) -> (forall (b : β), Z b)) (Equiv.hasCoeToFun.{imax u1 u3, imax u2 u4} (forall (a : α), (fun (a : α) => W a) a) (forall (b : β), Z b)) (Equiv.piCongr.{u1, u2, u3, u4} α β (fun (a : α) => W a) Z h₁ h₂) f (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a)) (coeFn.{max 1 (imax u3 u4) (imax u4 u3), imax u3 u4} (Equiv.{u3, u4} (W a) (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a))) (fun (_x : Equiv.{u3, u4} (W a) (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a))) => (W a) -> (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a))) (Equiv.hasCoeToFun.{u3, u4} (W a) (Z (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) h₁ a))) (h₂ a) (f a))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u2, u1} α β) (h₂ : forall (a : α), Equiv.{u3, u4} (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a))) (f : forall (a : α), W a) (a : α), Eq.{u4} (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (FunLike.coe.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u2 u3, imax u1 u4} (Equiv.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b)) (forall (a : α), W a) (fun (_x : forall (a : α), W a) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (a : α), W a) => forall (b : β), Z b) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u2 u3, imax u1 u4} (Equiv.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b)) (forall (a : α), W a) (forall (a : β), Z a) (EquivLike.toEmbeddingLike.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u2 u3, imax u1 u4} (Equiv.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b)) (forall (a : α), W a) (forall (b : β), Z b) (Equiv.instEquivLikeEquiv.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b)))) (Equiv.piCongr.{u3, u4, u2, u1} α β (fun (a : α) => W a) Z h₁ h₂) f (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (FunLike.coe.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a))) (W a) (fun (_x : W a) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : W a) => Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a))) (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (EquivLike.toEmbeddingLike.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a))) (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a)) (Equiv.instEquivLikeEquiv.{u3, u4} (W a) (Z (FunLike.coe.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) h₁ a))))) (h₂ a) (f a))
Case conversion may be inaccurate. Consider using '#align equiv.Pi_congr_apply_apply Equiv.piCongr_apply_applyₓ'. -/
@[simp]
theorem piCongr_apply_apply (f : ∀ a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a) :=
  by
  change cast _ ((h₂ (h₁.symm (h₁ a))) (f (h₁.symm (h₁ a)))) = (h₂ a) (f a)
  generalize_proofs hZa
  revert hZa
  rw [h₁.symm_apply_apply a]
  simp
#align equiv.Pi_congr_apply_apply Equiv.piCongr_apply_apply

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ b : β, W (h₁.symm b) ≃ Z b)

/- warning: equiv.Pi_congr' -> Equiv.piCongr' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u1, u2} α β), (forall (b : β), Equiv.{u3, u4} (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (Z b)) -> (Equiv.{imax u1 u3, imax u2 u4} (forall (a : α), W a) (forall (b : β), Z b))
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u4}} {W : α -> Sort.{u1}} {Z : β -> Sort.{u2}} (h₁ : Equiv.{u3, u4} α β), (forall (b : β), Equiv.{u1, u2} (W (FunLike.coe.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} β α) β α (Equiv.instEquivLikeEquiv.{u4, u3} β α))) (Equiv.symm.{u3, u4} α β h₁) b)) (Z b)) -> (Equiv.{imax u3 u1, imax u4 u2} (forall (a : α), W a) (forall (b : β), Z b))
Case conversion may be inaccurate. Consider using '#align equiv.Pi_congr' Equiv.piCongr'ₓ'. -/
/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def piCongr' : (∀ a, W a) ≃ ∀ b, Z b :=
  (piCongr h₁.symm fun b => (h₂ b).symm).symm
#align equiv.Pi_congr' Equiv.piCongr'

/- warning: equiv.coe_Pi_congr' -> Equiv.coe_piCongr' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u1, u2} α β) (h₂ : forall (b : β), Equiv.{u3, u4} (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (Z b)), Eq.{imax (imax u1 u3) u2 u4} ((fun (_x : Equiv.{imax u1 u3, imax u2 u4} (forall (a : α), W a) (forall (b : β), (fun (b : β) => Z b) b)) => (forall (a : α), W a) -> (forall (b : β), (fun (b : β) => Z b) b)) (Equiv.piCongr'.{u1, u2, u3, u4} α β W (fun (b : β) => Z b) h₁ h₂)) (coeFn.{max 1 (imax (imax u1 u3) u2 u4) (imax (imax u2 u4) u1 u3), imax (imax u1 u3) u2 u4} (Equiv.{imax u1 u3, imax u2 u4} (forall (a : α), W a) (forall (b : β), (fun (b : β) => Z b) b)) (fun (_x : Equiv.{imax u1 u3, imax u2 u4} (forall (a : α), W a) (forall (b : β), (fun (b : β) => Z b) b)) => (forall (a : α), W a) -> (forall (b : β), (fun (b : β) => Z b) b)) (Equiv.hasCoeToFun.{imax u1 u3, imax u2 u4} (forall (a : α), W a) (forall (b : β), (fun (b : β) => Z b) b)) (Equiv.piCongr'.{u1, u2, u3, u4} α β W (fun (b : β) => Z b) h₁ h₂)) (fun (f : forall (a : α), W a) (b : β) => coeFn.{max 1 (imax u3 u4) (imax u4 u3), imax u3 u4} (Equiv.{u3, u4} (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (Z b)) (fun (_x : Equiv.{u3, u4} (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (Z b)) => (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) -> (Z b)) (Equiv.hasCoeToFun.{u3, u4} (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (Z b)) (h₂ b) (f (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u2, u1} α β) (h₂ : forall (b : β), Equiv.{u3, u4} (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b)), Eq.{imax (imax u2 u3) u1 u4} (forall (a : forall (a : α), W a), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (a : α), W a) => forall (b : β), Z b) a) (FunLike.coe.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u2 u3, imax u1 u4} (Equiv.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b)) (forall (a : α), W a) (fun (_x : forall (a : α), W a) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (a : α), W a) => forall (b : β), Z b) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u2 u3, imax u1 u4} (Equiv.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b)) (forall (a : α), W a) (forall (a : β), Z a) (EquivLike.toEmbeddingLike.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u2 u3, imax u1 u4} (Equiv.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b)) (forall (a : α), W a) (forall (b : β), Z b) (Equiv.instEquivLikeEquiv.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b)))) (Equiv.piCongr'.{u3, u4, u2, u1} α β W (fun (b : β) => Z b) h₁ h₂)) (fun (f : forall (a : α), W a) (b : β) => FunLike.coe.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b)) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (fun (_x : W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) => Z b) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b)) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b) (EquivLike.toEmbeddingLike.{max (max 1 u3) u4, u3, u4} (Equiv.{u3, u4} (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b)) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b) (Equiv.instEquivLikeEquiv.{u3, u4} (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b)))) (h₂ b) (f (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)))
Case conversion may be inaccurate. Consider using '#align equiv.coe_Pi_congr' Equiv.coe_piCongr'ₓ'. -/
@[simp]
theorem coe_piCongr' :
    (h₁.piCongr' h₂ : (∀ a, W a) → ∀ b, Z b) = fun f b => h₂ b <| f <| h₁.symm b :=
  rfl
#align equiv.coe_Pi_congr' Equiv.coe_piCongr'

#print Equiv.piCongr'_apply /-
theorem piCongr'_apply (f : ∀ a, W a) : h₁.piCongr' h₂ f = fun b => h₂ b <| f <| h₁.symm b :=
  rfl
#align equiv.Pi_congr'_apply Equiv.piCongr'_apply
-/

/- warning: equiv.Pi_congr'_symm_apply_symm_apply -> Equiv.piCongr'_symm_apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u1, u2} α β) (h₂ : forall (b : β), Equiv.{u3, u4} (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (Z b)) (f : forall (b : β), Z b) (b : β), Eq.{u3} (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (coeFn.{max 1 (imax (imax u2 u4) u1 u3) (imax (imax u1 u3) u2 u4), imax (imax u2 u4) u1 u3} (Equiv.{imax u2 u4, imax u1 u3} (forall (b : β), Z b) (forall (a : α), W a)) (fun (_x : Equiv.{imax u2 u4, imax u1 u3} (forall (b : β), Z b) (forall (a : α), W a)) => (forall (b : β), Z b) -> (forall (a : α), W a)) (Equiv.hasCoeToFun.{imax u2 u4, imax u1 u3} (forall (b : β), Z b) (forall (a : α), W a)) (Equiv.symm.{imax u1 u3, imax u2 u4} (forall (a : α), W a) (forall (b : β), Z b) (Equiv.piCongr'.{u1, u2, u3, u4} α β W (fun (b : β) => Z b) h₁ h₂)) f (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (coeFn.{max 1 (imax u4 u3) (imax u3 u4), imax u4 u3} (Equiv.{u4, u3} (Z b) (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b))) (fun (_x : Equiv.{u4, u3} (Z b) (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b))) => (Z b) -> (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b))) (Equiv.hasCoeToFun.{u4, u3} (Z b) (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b))) (Equiv.symm.{u3, u4} (W (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β h₁) b)) (Z b) (h₂ b)) (f b))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {W : α -> Sort.{u3}} {Z : β -> Sort.{u4}} (h₁ : Equiv.{u2, u1} α β) (h₂ : forall (b : β), Equiv.{u3, u4} (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b)) (f : forall (b : β), Z b) (b : β), Eq.{u3} (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (FunLike.coe.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u1 u4, imax u2 u3} (Equiv.{imax u1 u4, imax u2 u3} (forall (b : β), Z b) (forall (a : α), W a)) (forall (b : β), Z b) (fun (_x : forall (b : β), Z b) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (b : β), Z b) => forall (a : α), W a) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u1 u4, imax u2 u3} (Equiv.{imax u1 u4, imax u2 u3} (forall (b : β), Z b) (forall (a : α), W a)) (forall (b : β), Z b) (forall (b : α), W b) (EquivLike.toEmbeddingLike.{max (max 1 (imax u2 u3)) (imax u1 u4), imax u1 u4, imax u2 u3} (Equiv.{imax u1 u4, imax u2 u3} (forall (b : β), Z b) (forall (a : α), W a)) (forall (b : β), Z b) (forall (a : α), W a) (Equiv.instEquivLikeEquiv.{imax u1 u4, imax u2 u3} (forall (b : β), Z b) (forall (a : α), W a)))) (Equiv.symm.{imax u2 u3, imax u1 u4} (forall (a : α), W a) (forall (b : β), Z b) (Equiv.piCongr'.{u3, u4, u2, u1} α β W (fun (b : β) => Z b) h₁ h₂)) f (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (FunLike.coe.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} (Z b) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b))) (Z b) (fun (_x : Z b) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Z b) => W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} (Z b) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b))) (Z b) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (EquivLike.toEmbeddingLike.{max (max 1 u3) u4, u4, u3} (Equiv.{u4, u3} (Z b) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b))) (Z b) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Equiv.instEquivLikeEquiv.{u4, u3} (Z b) (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b))))) (Equiv.symm.{u3, u4} (W (FunLike.coe.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u1, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β h₁) b)) (Z b) (h₂ b)) (f b))
Case conversion may be inaccurate. Consider using '#align equiv.Pi_congr'_symm_apply_symm_apply Equiv.piCongr'_symm_apply_symm_applyₓ'. -/
@[simp]
theorem piCongr'_symm_apply_symm_apply (f : ∀ b, Z b) (b : β) :
    (h₁.piCongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) :=
  by
  change cast _ ((h₂ (h₁ (h₁.symm b))).symm (f (h₁ (h₁.symm b)))) = (h₂ b).symm (f b)
  generalize_proofs hWb
  revert hWb
  generalize hb : h₁ (h₁.symm b) = b'
  rw [h₁.apply_symm_apply b] at hb
  subst hb
  simp
#align equiv.Pi_congr'_symm_apply_symm_apply Equiv.piCongr'_symm_apply_symm_apply

end

section BinaryOp

variable {α₁ β₁ : Type _} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

/- warning: equiv.semiconj_conj -> Equiv.semiconj_conj is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} (e : Equiv.{succ u1, succ u2} α₁ β₁) (f : α₁ -> α₁), Function.Semiconj.{u1, u2} α₁ β₁ (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α₁ β₁) (fun (_x : Equiv.{succ u1, succ u2} α₁ β₁) => α₁ -> β₁) (Equiv.hasCoeToFun.{succ u1, succ u2} α₁ β₁) e) f (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (α₁ -> α₁) (β₁ -> β₁)) (fun (_x : Equiv.{succ u1, succ u2} (α₁ -> α₁) (β₁ -> β₁)) => (α₁ -> α₁) -> β₁ -> β₁) (Equiv.hasCoeToFun.{succ u1, succ u2} (α₁ -> α₁) (β₁ -> β₁)) (Equiv.conj.{succ u1, succ u2} α₁ β₁ e) f)
but is expected to have type
  forall {α₁ : Type.{u2}} {β₁ : Type.{u1}} (e : Equiv.{succ u2, succ u1} α₁ β₁) (f : α₁ -> α₁), Function.Semiconj.{u2, u1} α₁ β₁ (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₁ β₁) α₁ (fun (_x : α₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁) => β₁) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₁ β₁) α₁ β₁ (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₁ β₁) α₁ β₁ (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α₁ β₁))) e) f (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} (α₁ -> α₁) (β₁ -> β₁)) (α₁ -> α₁) (fun (_x : α₁ -> α₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁ -> α₁) => β₁ -> β₁) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} (α₁ -> α₁) (β₁ -> β₁)) (α₁ -> α₁) (β₁ -> β₁) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} (α₁ -> α₁) (β₁ -> β₁)) (α₁ -> α₁) (β₁ -> β₁) (Equiv.instEquivLikeEquiv.{succ u2, succ u1} (α₁ -> α₁) (β₁ -> β₁)))) (Equiv.conj.{succ u2, succ u1} α₁ β₁ e) f)
Case conversion may be inaccurate. Consider using '#align equiv.semiconj_conj Equiv.semiconj_conjₓ'. -/
theorem semiconj_conj (f : α₁ → α₁) : Semiconj e f (e.conj f) := fun x => by simp
#align equiv.semiconj_conj Equiv.semiconj_conj

/- warning: equiv.semiconj₂_conj -> Equiv.semiconj₂_conj is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} (e : Equiv.{succ u1, succ u2} α₁ β₁) (f : α₁ -> α₁ -> α₁), Function.Semiconj₂.{u1, u2} α₁ β₁ (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α₁ β₁) (fun (_x : Equiv.{succ u1, succ u2} α₁ β₁) => α₁ -> β₁) (Equiv.hasCoeToFun.{succ u1, succ u2} α₁ β₁) e) f (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁)) (fun (_x : Equiv.{succ u1, succ u2} (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁)) => (α₁ -> α₁ -> α₁) -> β₁ -> β₁ -> β₁) (Equiv.hasCoeToFun.{succ u1, succ u2} (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁)) (Equiv.arrowCongr.{succ u1, succ u1, succ u2, succ u2} α₁ (α₁ -> α₁) β₁ (β₁ -> β₁) e (Equiv.conj.{succ u1, succ u2} α₁ β₁ e)) f)
but is expected to have type
  forall {α₁ : Type.{u2}} {β₁ : Type.{u1}} (e : Equiv.{succ u2, succ u1} α₁ β₁) (f : α₁ -> α₁ -> α₁), Function.Semiconj₂.{u2, u1} α₁ β₁ (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₁ β₁) α₁ (fun (_x : α₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁) => β₁) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₁ β₁) α₁ β₁ (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₁ β₁) α₁ β₁ (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α₁ β₁))) e) f (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁)) (α₁ -> α₁ -> α₁) (fun (_x : α₁ -> α₁ -> α₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁ -> α₁ -> α₁) => β₁ -> β₁ -> β₁) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁)) (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁)) (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁) (Equiv.instEquivLikeEquiv.{succ u2, succ u1} (α₁ -> α₁ -> α₁) (β₁ -> β₁ -> β₁)))) (Equiv.arrowCongr.{succ u2, succ u2, succ u1, succ u1} α₁ (α₁ -> α₁) β₁ (β₁ -> β₁) e (Equiv.conj.{succ u2, succ u1} α₁ β₁ e)) f)
Case conversion may be inaccurate. Consider using '#align equiv.semiconj₂_conj Equiv.semiconj₂_conjₓ'. -/
theorem semiconj₂_conj : Semiconj₂ e f (e.arrowCongr e.conj f) := fun x y => by simp
#align equiv.semiconj₂_conj Equiv.semiconj₂_conj

instance [IsAssociative α₁ f] : IsAssociative β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).is_associative_right e.Surjective

instance [IsIdempotent α₁ f] : IsIdempotent β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).is_idempotent_right e.Surjective

instance [IsLeftCancel α₁ f] : IsLeftCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.Surjective.forall₃.2 fun x y z => by simpa using @IsLeftCancel.left_cancel _ f _ x y z⟩

instance [IsRightCancel α₁ f] : IsRightCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.Surjective.forall₃.2 fun x y z => by simpa using @IsRightCancel.right_cancel _ f _ x y z⟩

end BinaryOp

end Equiv

/- warning: function.injective.swap_apply -> Function.Injective.swap_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] [_inst_2 : DecidableEq.{u2} β] {f : α -> β}, (Function.Injective.{u1, u2} α β f) -> (forall (x : α) (y : α) (z : α), Eq.{u2} β (coeFn.{max 1 u2, u2} (Equiv.Perm.{u2} β) (fun (_x : Equiv.{u2, u2} β β) => β -> β) (Equiv.hasCoeToFun.{u2, u2} β β) (Equiv.swap.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (f x) (f y)) (f z)) (f (coeFn.{max 1 u1, u1} (Equiv.Perm.{u1} α) (fun (_x : Equiv.{u1, u1} α α) => α -> α) (Equiv.hasCoeToFun.{u1, u1} α α) (Equiv.swap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) z)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : DecidableEq.{u2} α] [_inst_2 : DecidableEq.{u1} β] {f : α -> β}, (Function.Injective.{u2, u1} α β f) -> (forall (x : α) (y : α) (z : α), Eq.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => β) (f z)) (FunLike.coe.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => β) _x) (EmbeddingLike.toFunLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β β (EquivLike.toEmbeddingLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β β (Equiv.instEquivLikeEquiv.{u1, u1} β β))) (Equiv.swap.{u1} β (fun (a : β) (b : β) => _inst_2 a b) (f x) (f y)) (f z)) (f (FunLike.coe.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α α (EquivLike.toEmbeddingLike.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α α (Equiv.instEquivLikeEquiv.{u2, u2} α α))) (Equiv.swap.{u2} α (fun (a : α) (b : α) => _inst_1 a b) x y) z)))
Case conversion may be inaccurate. Consider using '#align function.injective.swap_apply Function.Injective.swap_applyₓ'. -/
theorem Function.Injective.swap_apply [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y z : α) : Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  by
  by_cases hx : z = x; · simp [hx]
  by_cases hy : z = y; · simp [hy]
  rw [Equiv.swap_apply_of_ne_of_ne hx hy, Equiv.swap_apply_of_ne_of_ne (hf.ne hx) (hf.ne hy)]
#align function.injective.swap_apply Function.Injective.swap_apply

/- warning: function.injective.swap_comp -> Function.Injective.swap_comp is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] [_inst_2 : DecidableEq.{u2} β] {f : α -> β}, (Function.Injective.{u1, u2} α β f) -> (forall (x : α) (y : α), Eq.{imax u1 u2} (α -> β) (Function.comp.{u1, u2, u2} α β β (coeFn.{max 1 u2, u2} (Equiv.Perm.{u2} β) (fun (_x : Equiv.{u2, u2} β β) => β -> β) (Equiv.hasCoeToFun.{u2, u2} β β) (Equiv.swap.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (f x) (f y))) f) (Function.comp.{u1, u1, u2} α α β f (coeFn.{max 1 u1, u1} (Equiv.Perm.{u1} α) (fun (_x : Equiv.{u1, u1} α α) => α -> α) (Equiv.hasCoeToFun.{u1, u1} α α) (Equiv.swap.{u1} α (fun (a : α) (b : α) => _inst_1 a b) x y))))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : DecidableEq.{u2} α] [_inst_2 : DecidableEq.{u1} β] {f : α -> β}, (Function.Injective.{u2, u1} α β f) -> (forall (x : α) (y : α), Eq.{imax u2 u1} (α -> β) (Function.comp.{u2, u1, u1} α β β (FunLike.coe.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => β) _x) (EmbeddingLike.toFunLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β β (EquivLike.toEmbeddingLike.{max 1 u1, u1, u1} (Equiv.Perm.{u1} β) β β (Equiv.instEquivLikeEquiv.{u1, u1} β β))) (Equiv.swap.{u1} β (fun (a : β) (b : β) => _inst_2 a b) (f x) (f y))) f) (Function.comp.{u2, u2, u1} α α β f (FunLike.coe.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α α (EquivLike.toEmbeddingLike.{max 1 u2, u2, u2} (Equiv.Perm.{u2} α) α α (Equiv.instEquivLikeEquiv.{u2, u2} α α))) (Equiv.swap.{u2} α (fun (a : α) (b : α) => _inst_1 a b) x y))))
Case conversion may be inaccurate. Consider using '#align function.injective.swap_comp Function.Injective.swap_compₓ'. -/
theorem Function.Injective.swap_comp [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y : α) : Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  funext fun z => hf.swap_apply _ _ _
#align function.injective.swap_comp Function.Injective.swap_comp

#print subsingletonProdSelfEquiv /-
/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
def subsingletonProdSelfEquiv {α : Type _} [Subsingleton α] : α × α ≃ α
    where
  toFun p := p.1
  invFun a := (a, a)
  left_inv p := Subsingleton.elim _ _
  right_inv p := Subsingleton.elim _ _
#align subsingleton_prod_self_equiv subsingletonProdSelfEquiv
-/

#print equivOfSubsingletonOfSubsingleton /-
/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α → β) (g : β → α) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv_of_subsingleton_of_subsingleton equivOfSubsingletonOfSubsingleton
-/

/- warning: equiv.punit_of_nonempty_of_subsingleton -> Equiv.punitOfNonemptyOfSubsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u2}} [h : Nonempty.{u2} α] [_inst_1 : Subsingleton.{u2} α], Equiv.{u2, u1} α PUnit.{u1}
but is expected to have type
  forall {α : Sort.{u1}} [h : Nonempty.{u1} α] [_inst_1 : Subsingleton.{u1} α], Equiv.{u1, u2} α PUnit.{u2}
Case conversion may be inaccurate. Consider using '#align equiv.punit_of_nonempty_of_subsingleton Equiv.punitOfNonemptyOfSubsingletonₓ'. -/
/-- A nonempty subsingleton type is (noncomputably) equivalent to `punit`. -/
noncomputable def Equiv.punitOfNonemptyOfSubsingleton {α : Sort _} [h : Nonempty α]
    [Subsingleton α] : α ≃ PUnit.{v} :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some
#align equiv.punit_of_nonempty_of_subsingleton Equiv.punitOfNonemptyOfSubsingleton

#print uniqueUniqueEquiv /-
/-- `unique (unique α)` is equivalent to `unique α`. -/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h
      uniq := fun _ => Subsingleton.elim _ _ }
#align unique_unique_equiv uniqueUniqueEquiv
-/

namespace Function

/- warning: function.update_comp_equiv -> Function.update_comp_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {α' : Sort.{u3}} [_inst_1 : DecidableEq.{u3} α'] [_inst_2 : DecidableEq.{u1} α] (f : α -> β) (g : Equiv.{u3, u1} α' α) (a : α) (v : β), Eq.{imax u3 u2} (α' -> β) (Function.comp.{u3, u1, u2} α' α β (Function.update.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_2 a b) f a v) (coeFn.{max 1 (imax u3 u1) (imax u1 u3), imax u3 u1} (Equiv.{u3, u1} α' α) (fun (_x : Equiv.{u3, u1} α' α) => α' -> α) (Equiv.hasCoeToFun.{u3, u1} α' α) g)) (Function.update.{u3, u2} α' (fun (ᾰ : α') => β) (fun (a : α') (b : α') => _inst_1 a b) (Function.comp.{u3, u1, u2} α' α β f (coeFn.{max 1 (imax u3 u1) (imax u1 u3), imax u3 u1} (Equiv.{u3, u1} α' α) (fun (_x : Equiv.{u3, u1} α' α) => α' -> α) (Equiv.hasCoeToFun.{u3, u1} α' α) g)) (coeFn.{max 1 (imax u1 u3) (imax u3 u1), imax u1 u3} (Equiv.{u1, u3} α α') (fun (_x : Equiv.{u1, u3} α α') => α -> α') (Equiv.hasCoeToFun.{u1, u3} α α') (Equiv.symm.{u3, u1} α' α g) a) v)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {α' : Sort.{u1}} [_inst_1 : DecidableEq.{u3} α] [_inst_2 : DecidableEq.{u2} β] (f : β -> α') (g : Equiv.{u3, u2} α β) (a : β) (v : α'), Eq.{imax u3 u1} (α -> α') (Function.comp.{u3, u2, u1} α β α' (Function.update.{u2, u1} β (fun (ᾰ : β) => α') (fun (a : β) (b : β) => _inst_2 a b) f a v) (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) g)) (Function.update.{u3, u1} α (fun (ᾰ : α) => α') (fun (a : α) (b : α) => _inst_1 a b) (Function.comp.{u3, u2, u1} α β α' f (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) g)) (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β g) a) v)
Case conversion may be inaccurate. Consider using '#align function.update_comp_equiv Function.update_comp_equivₓ'. -/
theorem update_comp_equiv {α β α' : Sort _} [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) : update f a v ∘ g = update (f ∘ g) (g.symm a) v := by
  rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]
#align function.update_comp_equiv Function.update_comp_equiv

/- warning: function.update_apply_equiv_apply -> Function.update_apply_equiv_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {α' : Sort.{u3}} [_inst_1 : DecidableEq.{u3} α'] [_inst_2 : DecidableEq.{u1} α] (f : α -> β) (g : Equiv.{u3, u1} α' α) (a : α) (v : β) (a' : α'), Eq.{u2} β (Function.update.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_2 a b) f a v (coeFn.{max 1 (imax u3 u1) (imax u1 u3), imax u3 u1} (Equiv.{u3, u1} α' α) (fun (_x : Equiv.{u3, u1} α' α) => α' -> α) (Equiv.hasCoeToFun.{u3, u1} α' α) g a')) (Function.update.{u3, u2} α' (fun (ᾰ : α') => β) (fun (a : α') (b : α') => _inst_1 a b) (Function.comp.{u3, u1, u2} α' α β f (coeFn.{max 1 (imax u3 u1) (imax u1 u3), imax u3 u1} (Equiv.{u3, u1} α' α) (fun (_x : Equiv.{u3, u1} α' α) => α' -> α) (Equiv.hasCoeToFun.{u3, u1} α' α) g)) (coeFn.{max 1 (imax u1 u3) (imax u3 u1), imax u1 u3} (Equiv.{u1, u3} α α') (fun (_x : Equiv.{u1, u3} α α') => α -> α') (Equiv.hasCoeToFun.{u1, u3} α α') (Equiv.symm.{u3, u1} α' α g) a) v a')
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {α' : Sort.{u1}} [_inst_1 : DecidableEq.{u3} α] [_inst_2 : DecidableEq.{u2} β] (f : β -> α') (g : Equiv.{u3, u2} α β) (a : β) (v : α') (a' : α), Eq.{u1} α' (Function.update.{u2, u1} β (fun (ᾰ : β) => α') (fun (a : β) (b : β) => _inst_2 a b) f a v (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) g a')) (Function.update.{u3, u1} α (fun (ᾰ : α) => α') (fun (a : α) (b : α) => _inst_1 a b) (Function.comp.{u3, u2, u1} α β α' f (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) g)) (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β g) a) v a')
Case conversion may be inaccurate. Consider using '#align function.update_apply_equiv_apply Function.update_apply_equiv_applyₓ'. -/
theorem update_apply_equiv_apply {α β α' : Sort _} [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'
#align function.update_apply_equiv_apply Function.update_apply_equiv_apply

/- warning: function.Pi_congr_left'_update -> Function.piCongrLeft'_update is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] [_inst_2 : DecidableEq.{u2} β] (P : α -> Sort.{u3}) (e : Equiv.{u1, u2} α β) (f : forall (a : α), P a) (b : β) (x : P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)), Eq.{imax u2 u3} (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (coeFn.{max 1 (imax (imax u1 u3) u2 u3) (imax (imax u2 u3) u1 u3), imax (imax u1 u3) u2 u3} (Equiv.{imax u1 u3, imax u2 u3} (forall (a : α), P a) (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))) (fun (_x : Equiv.{imax u1 u3, imax u2 u3} (forall (a : α), P a) (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))) => (forall (a : α), P a) -> (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))) (Equiv.hasCoeToFun.{imax u1 u3, imax u2 u3} (forall (a : α), P a) (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))) (Equiv.piCongrLeft'.{u1, u2, u3} α β P e) (Function.update.{u1, u3} α (fun (a : α) => P a) (fun (a : α) (b : α) => _inst_1 a b) f (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b) x)) (Function.update.{u2, u3} β (fun (b : β) => P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (fun (a : β) (b : β) => _inst_2 a b) (coeFn.{max 1 (imax (imax u1 u3) u2 u3) (imax (imax u2 u3) u1 u3), imax (imax u1 u3) u2 u3} (Equiv.{imax u1 u3, imax u2 u3} (forall (a : α), P a) (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))) (fun (_x : Equiv.{imax u1 u3, imax u2 u3} (forall (a : α), P a) (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))) => (forall (a : α), P a) -> (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))) (Equiv.hasCoeToFun.{imax u1 u3, imax u2 u3} (forall (a : α), P a) (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b))) (Equiv.piCongrLeft'.{u1, u2, u3} α β P e) f) b x)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u3} α] [_inst_2 : DecidableEq.{u2} β] (P : α -> Sort.{u1}) (e : Equiv.{u3, u2} α β) (f : forall (a : α), P a) (b : β) (x : P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)), Eq.{imax u2 u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (a : α), P a) => forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (Function.update.{u3, u1} α (fun (a : α) => P a) (fun (a : α) (b : α) => _inst_1 a b) f (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b) x)) (FunLike.coe.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u3 u1, imax u2 u1} (Equiv.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b))) (forall (a : α), P a) (fun (_x : forall (a : α), P a) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (a : α), P a) => forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u3 u1, imax u2 u1} (Equiv.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b))) (forall (a : α), P a) (forall (a : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) a)) (EquivLike.toEmbeddingLike.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u3 u1, imax u2 u1} (Equiv.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b))) (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (Equiv.instEquivLikeEquiv.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b))))) (Equiv.piCongrLeft'.{u3, u2, u1} α β P e) (Function.update.{u3, u1} α (fun (a : α) => P a) (fun (a : α) (b : α) => _inst_1 a b) f (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b) x)) (Function.update.{u2, u1} β (fun (b : β) => P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (fun (a : β) (b : β) => _inst_2 a b) (FunLike.coe.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u3 u1, imax u2 u1} (Equiv.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b))) (forall (a : α), P a) (fun (_x : forall (a : α), P a) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (a : α), P a) => forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u3 u1, imax u2 u1} (Equiv.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b))) (forall (a : α), P a) (forall (a : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) a)) (EquivLike.toEmbeddingLike.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u3 u1, imax u2 u1} (Equiv.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b))) (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (Equiv.instEquivLikeEquiv.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b))))) (Equiv.piCongrLeft'.{u3, u2, u1} α β P e) f) b x)
Case conversion may be inaccurate. Consider using '#align function.Pi_congr_left'_update Function.piCongrLeft'_updateₓ'. -/
theorem piCongrLeft'_update [DecidableEq α] [DecidableEq β] (P : α → Sort _) (e : α ≃ β)
    (f : ∀ a, P a) (b : β) (x : P (e.symm b)) :
    e.piCongrLeft' P (update f (e.symm b) x) = update (e.piCongrLeft' P f) b x :=
  by
  ext b'
  rcases eq_or_ne b' b with (rfl | h)
  · simp
  · simp [h]
#align function.Pi_congr_left'_update Function.piCongrLeft'_update

/- warning: function.Pi_congr_left'_symm_update -> Function.piCongrLeft'_symm_update is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u1} α] [_inst_2 : DecidableEq.{u2} β] (P : α -> Sort.{u3}) (e : Equiv.{u1, u2} α β) (f : forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (b : β) (x : P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)), Eq.{imax u1 u3} (forall (a : α), P a) (coeFn.{max 1 (imax (imax u2 u3) u1 u3) (imax (imax u1 u3) u2 u3), imax (imax u2 u3) u1 u3} (Equiv.{imax u2 u3, imax u1 u3} (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (forall (a : α), P a)) (fun (_x : Equiv.{imax u2 u3, imax u1 u3} (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (forall (a : α), P a)) => (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) -> (forall (a : α), P a)) (Equiv.hasCoeToFun.{imax u2 u3, imax u1 u3} (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (forall (a : α), P a)) (Equiv.symm.{imax u1 u3, imax u2 u3} (forall (a : α), P a) (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (Equiv.piCongrLeft'.{u1, u2, u3} α β P e)) (Function.update.{u2, u3} β (fun (b : β) => P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (fun (a : β) (b : β) => _inst_2 a b) f b x)) (Function.update.{u1, u3} α (fun (a : α) => P a) (fun (a : α) (b : α) => _inst_1 a b) (coeFn.{max 1 (imax (imax u2 u3) u1 u3) (imax (imax u1 u3) u2 u3), imax (imax u2 u3) u1 u3} (Equiv.{imax u2 u3, imax u1 u3} (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (forall (a : α), P a)) (fun (_x : Equiv.{imax u2 u3, imax u1 u3} (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (forall (a : α), P a)) => (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) -> (forall (a : α), P a)) (Equiv.hasCoeToFun.{imax u2 u3, imax u1 u3} (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (forall (a : α), P a)) (Equiv.symm.{imax u1 u3, imax u2 u3} (forall (a : α), P a) (forall (b : β), P (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b)) (Equiv.piCongrLeft'.{u1, u2, u3} α β P e)) f) (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) b) x)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} [_inst_1 : DecidableEq.{u3} α] [_inst_2 : DecidableEq.{u2} β] (P : α -> Sort.{u1}) (e : Equiv.{u3, u2} α β) (f : forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (b : β) (x : P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)), Eq.{imax u3 u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) => forall (a : α), P a) (Function.update.{u2, u1} β (fun (b : β) => P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (fun (a : β) (b : β) => _inst_2 a b) f b x)) (FunLike.coe.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u2 u1, imax u3 u1} (Equiv.{imax u2 u1, imax u3 u1} (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a)) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (fun (_x : forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) => forall (a : α), P a) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u2 u1, imax u3 u1} (Equiv.{imax u2 u1, imax u3 u1} (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a)) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (b : α), P b) (EquivLike.toEmbeddingLike.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u2 u1, imax u3 u1} (Equiv.{imax u2 u1, imax u3 u1} (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a)) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a) (Equiv.instEquivLikeEquiv.{imax u2 u1, imax u3 u1} (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a)))) (Equiv.symm.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (Equiv.piCongrLeft'.{u3, u2, u1} α β P e)) (Function.update.{u2, u1} β (fun (b : β) => P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (fun (a : β) (b : β) => _inst_2 a b) f b x)) (Function.update.{u3, u1} α (fun (a : α) => P a) (fun (a : α) (b : α) => _inst_1 a b) (FunLike.coe.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u2 u1, imax u3 u1} (Equiv.{imax u2 u1, imax u3 u1} (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a)) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (fun (_x : forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) => forall (a : α), P a) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u2 u1, imax u3 u1} (Equiv.{imax u2 u1, imax u3 u1} (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a)) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (b : α), P b) (EquivLike.toEmbeddingLike.{max (max 1 (imax u3 u1)) (imax u2 u1), imax u2 u1, imax u3 u1} (Equiv.{imax u2 u1, imax u3 u1} (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a)) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a) (Equiv.instEquivLikeEquiv.{imax u2 u1, imax u3 u1} (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (forall (a : α), P a)))) (Equiv.symm.{imax u3 u1, imax u2 u1} (forall (a : α), P a) (forall (b : β), P (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b)) (Equiv.piCongrLeft'.{u3, u2, u1} α β P e)) f) (FunLike.coe.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e) b) x)
Case conversion may be inaccurate. Consider using '#align function.Pi_congr_left'_symm_update Function.piCongrLeft'_symm_updateₓ'. -/
theorem piCongrLeft'_symm_update [DecidableEq α] [DecidableEq β] (P : α → Sort _) (e : α ≃ β)
    (f : ∀ b, P (e.symm b)) (b : β) (x : P (e.symm b)) :
    (e.piCongrLeft' P).symm (update f b x) = update ((e.piCongrLeft' P).symm f) (e.symm b) x := by
  simp [(e.Pi_congr_left' P).symm_apply_eq, Pi_congr_left'_update]
#align function.Pi_congr_left'_symm_update Function.piCongrLeft'_symm_update

end Function

