/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathbin.GroupTheory.Index
import Mathbin.LinearAlgebra.Quotient

/-!
# Ideal norms
This file will define the absolute ideal norm `ideal.abs_norm (I : ideal R) : ℕ` as the cardinality
of the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions
 * `submodule.card_quot (S : submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
   This maps `⊥` to `0` and `⊤` to `1`.

## TODO
 * `ideal.abs_norm (I : ideal R)`: the absolute ideal norm, defined as
   the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.
   (In an upcoming PR!)

 * Define the relative norm.

-/


open BigOperators

namespace Submodule

variable {R M : Type _} [Ring R] [AddCommGroup M] [Module R M]

section

/-- The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `ideal.abs_norm`.
-/
noncomputable def cardQuot (S : Submodule R M) : ℕ :=
  AddSubgroup.index S.toAddSubgroup
#align submodule.card_quot Submodule.cardQuot

@[simp]
theorem card_quot_apply (S : Submodule R M) [Fintype (M ⧸ S)] : cardQuot S = Fintype.card (M ⧸ S) :=
  AddSubgroup.index_eq_card _
#align submodule.card_quot_apply Submodule.card_quot_apply

variable (R M)

@[simp]
theorem card_quot_bot [Infinite M] : cardQuot (⊥ : Submodule R M) = 0 :=
  AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite
#align submodule.card_quot_bot Submodule.card_quot_bot

@[simp]
theorem card_quot_top : cardQuot (⊤ : Submodule R M) = 1 :=
  AddSubgroup.index_top
#align submodule.card_quot_top Submodule.card_quot_top

variable {R M}

@[simp]
theorem card_quot_eq_one_iff {P : Submodule R M} : cardQuot P = 1 ↔ P = ⊤ :=
  AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])
#align submodule.card_quot_eq_one_iff Submodule.card_quot_eq_one_iff

end

end Submodule

