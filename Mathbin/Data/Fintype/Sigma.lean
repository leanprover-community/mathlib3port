/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Fintype.Basic
import Data.Finset.Sigma

#align_import data.fintype.sigma from "leanprover-community/mathlib"@"cc70d9141824ea8982d1562ce009952f2c3ece30"

/-!
# fintype instances for sigma types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

open scoped Nat

universe u v

variable {α β γ : Type _}

open Finset Function

instance {α : Type _} (β : α → Type _) [Fintype α] [∀ a, Fintype (β a)] : Fintype (Sigma β) :=
  ⟨univ.Sigma fun _ => univ, fun ⟨a, b⟩ => by simp⟩

#print Finset.univ_sigma_univ /-
@[simp]
theorem Finset.univ_sigma_univ {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] :
    ((univ : Finset α).Sigma fun a => (univ : Finset (β a))) = univ :=
  rfl
#align finset.univ_sigma_univ Finset.univ_sigma_univ
-/

#print PSigma.instFintype /-
instance PSigma.instFintype {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] :
    Fintype (Σ' a, β a) :=
  Fintype.ofEquiv _ (Equiv.psigmaEquivSigma _).symm
#align psigma.fintype PSigma.instFintype
-/

