/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module data.list.prod_sigma
! leanprover-community/mathlib commit be24ec5de6701447e5df5ca75400ffee19d65659
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic

/-!
# Lists in product and sigma types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic properties of `list.product` and `list.sigma`, which are list constructions
living in `prod` and `sigma` types respectively. Their definitions can be found in
[`data.list.defs`](./defs). Beware, this is not about `list.prod`, the multiplicative product.
-/


variable {α β : Type _}

namespace List

/-! ### product -/


#print List.nil_product /-
@[simp]
theorem nil_product (l : List β) : product (@nil α) l = [] :=
  rfl
#align list.nil_product List.nil_product
-/

/- warning: list.product_cons -> List.product_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.product.{u1, u2} α β (List.cons.{u1} α a l₁) l₂) (Append.append.{max u1 u2} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.hasAppend.{max u1 u2} (Prod.{u1, u2} α β)) (List.map.{u2, max u1 u2} β (Prod.{u1, u2} α β) (fun (b : β) => Prod.mk.{u1, u2} α β a b) l₂) (List.product.{u1, u2} α β l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (l₁ : List.{u2} α) (l₂ : List.{u1} β), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.product.{u2, u1} α β (List.cons.{u2} α a l₁) l₂) (HAppend.hAppend.{max u2 u1, max u2 u1, max u2 u1} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.{max u1 u2} (Prod.{u2, u1} α β)) (instHAppend.{max u2 u1} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.instAppendList.{max u2 u1} (Prod.{u2, u1} α β))) (List.map.{u1, max u1 u2} β (Prod.{u2, u1} α β) (fun (b : β) => Prod.mk.{u2, u1} α β a b) l₂) (List.product.{u2, u1} α β l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.product_cons List.product_consₓ'. -/
@[simp]
theorem product_cons (a : α) (l₁ : List α) (l₂ : List β) :
    product (a :: l₁) l₂ = map (fun b => (a, b)) l₂ ++ product l₁ l₂ :=
  rfl
#align list.product_cons List.product_cons

/- warning: list.product_nil -> List.product_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α), Eq.{succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.product.{u1, u2} α β l (List.nil.{u2} β)) (List.nil.{max u1 u2} (Prod.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.product.{u2, u1} α β l (List.nil.{u1} β)) (List.nil.{max u2 u1} (Prod.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align list.product_nil List.product_nilₓ'. -/
@[simp]
theorem product_nil : ∀ l : List α, product l (@nil β) = []
  | [] => rfl
  | a :: l => by rw [product_cons, product_nil] <;> rfl
#align list.product_nil List.product_nil

/- warning: list.mem_product -> List.mem_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : List.{u1} α} {l₂ : List.{u2} β} {a : α} {b : β}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (List.product.{u1, u2} α β l₁ l₂)) (And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₁) (Membership.Mem.{u2, u2} β (List.{u2} β) (List.hasMem.{u2} β) b l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l₁ : List.{u2} α} {l₂ : List.{u1} β} {a : α} {b : β}, Iff (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.instMembershipList.{max u2 u1} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b) (List.product.{u2, u1} α β l₁ l₂)) (And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₁) (Membership.mem.{u1, u1} β (List.{u1} β) (List.instMembershipList.{u1} β) b l₂))
Case conversion may be inaccurate. Consider using '#align list.mem_product List.mem_productₓ'. -/
@[simp]
theorem mem_product {l₁ : List α} {l₂ : List β} {a : α} {b : β} :
    (a, b) ∈ product l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := by
  simp only [product, mem_bind, mem_map, Prod.ext_iff, exists_prop, and_left_comm, exists_and_left,
    exists_eq_left, exists_eq_right]
#align list.mem_product List.mem_product

/- warning: list.length_product -> List.length_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{1} Nat (List.length.{max u1 u2} (Prod.{u1, u2} α β) (List.product.{u1, u2} α β l₁ l₂)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (List.length.{u1} α l₁) (List.length.{u2} β l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l₁ : List.{u2} α) (l₂ : List.{u1} β), Eq.{1} Nat (List.length.{max u1 u2} (Prod.{u2, u1} α β) (List.product.{u2, u1} α β l₁ l₂)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (List.length.{u2} α l₁) (List.length.{u1} β l₂))
Case conversion may be inaccurate. Consider using '#align list.length_product List.length_productₓ'. -/
theorem length_product (l₁ : List α) (l₂ : List β) :
    length (product l₁ l₂) = length l₁ * length l₂ := by
  induction' l₁ with x l₁ IH <;> [exact (zero_mul _).symm,
    simp only [length, product_cons, length_append, IH, right_distrib, one_mul, length_map,
      add_comm]]
#align list.length_product List.length_product

/-! ### sigma -/


variable {σ : α → Type _}

#print List.nil_sigma /-
@[simp]
theorem nil_sigma (l : ∀ a, List (σ a)) : (@nil α).Sigma l = [] :=
  rfl
#align list.nil_sigma List.nil_sigma
-/

/- warning: list.sigma_cons -> List.sigma_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (a : α) (l₁ : List.{u1} α) (l₂ : forall (a : α), List.{u2} (σ a)), Eq.{succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (List.sigma.{u1, u2} α (fun (a : α) => σ a) (List.cons.{u1} α a l₁) l₂) (Append.append.{max u1 u2} (List.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (List.hasAppend.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (List.map.{u2, max u1 u2} (σ a) (Sigma.{u1, u2} α (fun (a : α) => σ a)) (Sigma.mk.{u1, u2} α (fun (a : α) => σ a) a) (l₂ a)) (List.sigma.{u1, u2} α (fun (a : α) => σ a) l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (a : α) (l₁ : List.{u2} α) (l₂ : forall (a : α), List.{u1} (σ a)), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (List.sigma.{u2, u1} α (fun (a : α) => σ a) (List.cons.{u2} α a l₁) l₂) (HAppend.hAppend.{max u2 u1, max u2 u1, max u2 u1} (List.{max u2 u1} (Sigma.{u2, u1} α σ)) (List.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (List.{max u2 u1} (Sigma.{u2, u1} α σ)) (instHAppend.{max u2 u1} (List.{max u2 u1} (Sigma.{u2, u1} α σ)) (List.instAppendList.{max u2 u1} (Sigma.{u2, u1} α σ))) (List.map.{u1, max u2 u1} (σ a) (Sigma.{u2, u1} α σ) (Sigma.mk.{u2, u1} α σ a) (l₂ a)) (List.sigma.{u2, u1} α (fun (a : α) => σ a) l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.sigma_cons List.sigma_consₓ'. -/
@[simp]
theorem sigma_cons (a : α) (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (a :: l₁).Sigma l₂ = map (Sigma.mk a) (l₂ a) ++ l₁.Sigma l₂ :=
  rfl
#align list.sigma_cons List.sigma_cons

/- warning: list.sigma_nil -> List.sigma_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (l : List.{u1} α), Eq.{succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (List.sigma.{u1, u2} α (fun (a : α) => σ a) l (fun (a : α) => List.nil.{u2} (σ a))) (List.nil.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (l : List.{u2} α), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (List.sigma.{u2, u1} α (fun (a : α) => σ a) l (fun (a : α) => List.nil.{u1} (σ a))) (List.nil.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)))
Case conversion may be inaccurate. Consider using '#align list.sigma_nil List.sigma_nilₓ'. -/
@[simp]
theorem sigma_nil : ∀ l : List α, (l.Sigma fun a => @nil (σ a)) = []
  | [] => rfl
  | a :: l => by rw [sigma_cons, sigma_nil] <;> rfl
#align list.sigma_nil List.sigma_nil

/- warning: list.mem_sigma -> List.mem_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} {l₁ : List.{u1} α} {l₂ : forall (a : α), List.{u2} (σ a)} {a : α} {b : σ a}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} α (fun {a : α} => σ a)) (List.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (List.hasMem.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Sigma.mk.{u1, u2} α (fun {a : α} => σ a) a b) (List.sigma.{u1, u2} α (fun (a : α) => σ a) l₁ l₂)) (And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₁) (Membership.Mem.{u2, u2} (σ a) (List.{u2} (σ a)) (List.hasMem.{u2} (σ a)) b (l₂ a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} {l₁ : List.{u2} α} {l₂ : forall (a : α), List.{u1} (σ a)} {a : α} {b : σ a}, Iff (Membership.mem.{max u1 u2, max u2 u1} (Sigma.{u2, u1} α σ) (List.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (List.instMembershipList.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Sigma.mk.{u2, u1} α σ a b) (List.sigma.{u2, u1} α (fun (a : α) => σ a) l₁ l₂)) (And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₁) (Membership.mem.{u1, u1} (σ a) (List.{u1} (σ a)) (List.instMembershipList.{u1} (σ a)) b (l₂ a)))
Case conversion may be inaccurate. Consider using '#align list.mem_sigma List.mem_sigmaₓ'. -/
@[simp]
theorem mem_sigma {l₁ : List α} {l₂ : ∀ a, List (σ a)} {a : α} {b : σ a} :
    Sigma.mk a b ∈ l₁.Sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a := by
  simp only [List.sigma, mem_bind, mem_map, exists_prop, exists_and_left, and_left_comm,
    exists_eq_left, heq_iff_eq, exists_eq_right]
#align list.mem_sigma List.mem_sigma

/- warning: list.length_sigma -> List.length_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (l₁ : List.{u1} α) (l₂ : forall (a : α), List.{u2} (σ a)), Eq.{1} Nat (List.length.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)) (List.sigma.{u1, u2} α (fun (a : α) => σ a) l₁ l₂)) (List.sum.{0} Nat Nat.hasAdd Nat.hasZero (List.map.{u1, 0} α Nat (fun (a : α) => List.length.{u2} (σ a) (l₂ a)) l₁))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (l₁ : List.{u2} α) (l₂ : forall (a : α), List.{u1} (σ a)), Eq.{1} Nat (List.length.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)) (List.sigma.{u2, u1} α (fun (a : α) => σ a) l₁ l₂)) (List.sum.{0} Nat instAddNat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (List.map.{u2, 0} α Nat (fun (a : α) => List.length.{u1} (σ a) (l₂ a)) l₁))
Case conversion may be inaccurate. Consider using '#align list.length_sigma List.length_sigmaₓ'. -/
theorem length_sigma (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.Sigma l₂) = (l₁.map fun a => length (l₂ a)).Sum := by
  induction' l₁ with x l₁ IH <;> [rfl,
    simp only [map, sigma_cons, length_append, length_map, IH, sum_cons]]
#align list.length_sigma List.length_sigma

end List

