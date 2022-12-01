/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.BigOperators.Basic

/-!
# Finite sums over modules over a ring
-/


open BigOperators

universe u v

variable {α R k S M M₂ M₃ ι : Type _}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x y : M)

variable {R M}

theorem List.sum_smul {l : List R} {x : M} : l.Sum • x = (l.map fun r => r • x).Sum :=
  ((smulAddHom R M).flip x).map_list_sum l
#align list.sum_smul List.sum_smul

theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.Sum • x = (l.map fun r => r • x).Sum :=
  ((smulAddHom R M).flip x).map_multiset_sum l
#align multiset.sum_smul Multiset.sum_smul

theorem Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} :
    (∑ i in s, f i) • x = ∑ i in s, f i • x :=
  ((smulAddHom R M).flip x).map_sum f s
#align finset.sum_smul Finset.sum_smul

end AddCommMonoid

theorem Finset.cast_card [CommSemiring R] (s : Finset α) : (s.card : R) = ∑ a in s, 1 := by
  rw [Finset.sum_const, Nat.smul_one_eq_coe]
#align finset.cast_card Finset.cast_card

