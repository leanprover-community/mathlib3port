/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.sigma
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Finset.Sigma

/-!
# fintype instances for sigma types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

open Finset Function

instance {α : Type _} (β : α → Type _) [Fintype α] [∀ a, Fintype (β a)] : Fintype (Sigma β) :=
  ⟨univ.Sigma fun _ => univ, fun ⟨a, b⟩ => by simp⟩

/- warning: finset.univ_sigma_univ -> Finset.univ_sigma_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : forall (a : α), Fintype.{u2} (β a)], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (i : α) => β i))) (Finset.sigma.{u1, u2} α (fun (a : α) => β a) (Finset.univ.{u1} α _inst_1) (fun (a : α) => Finset.univ.{u2} (β a) (_inst_2 a))) (Finset.univ.{max u1 u2} (Sigma.{u1, u2} α (fun (i : α) => β i)) (Sigma.fintype.{u1, u2} α (fun (i : α) => β i) _inst_1 (fun (a : α) => _inst_2 a)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : forall (a : α), Fintype.{u1} (β a)], Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sigma.{u2, u1} α (fun (i : α) => β i))) (Finset.sigma.{u2, u1} α (fun (a : α) => β a) (Finset.univ.{u2} α _inst_1) (fun (a : α) => Finset.univ.{u1} (β a) (_inst_2 a))) (Finset.univ.{max u2 u1} (Sigma.{u2, u1} α (fun (i : α) => β i)) (instFintypeSigma.{u2, u1} α (fun (i : α) => β i) _inst_1 (fun (a : α) => _inst_2 a)))
Case conversion may be inaccurate. Consider using '#align finset.univ_sigma_univ Finset.univ_sigma_univₓ'. -/
@[simp]
theorem Finset.univ_sigma_univ {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] :
    ((univ : Finset α).Sigma fun a => (univ : Finset (β a))) = univ :=
  rfl
#align finset.univ_sigma_univ Finset.univ_sigma_univ

#print PSigma.fintype /-
instance PSigma.fintype {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] :
    Fintype (Σ'a, β a) :=
  Fintype.ofEquiv _ (Equiv.psigmaEquivSigma _).symm
#align psigma.fintype PSigma.fintype
-/

