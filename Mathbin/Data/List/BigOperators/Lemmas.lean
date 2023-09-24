/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import Data.List.BigOperators.Basic
import Algebra.Group.Opposite
import Algebra.GroupPower.Basic
import Algebra.GroupWithZero.Commute
import Algebra.GroupWithZero.Divisibility
import Algebra.Order.WithZero
import Algebra.Ring.Basic
import Algebra.Ring.Divisibility
import Algebra.Ring.Commute
import Data.Int.Units
import Data.Set.Basic

#align_import data.list.big_operators.lemmas from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-! # Lemmas about `list.sum` and `list.prod` requiring extra algebra imports 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


open MulOpposite List

variable {ι α M N P M₀ G R : Type _}

namespace Commute

#print Commute.list_sum_right /-
theorem list_sum_right [NonUnitalNonAssocSemiring R] (a : R) (l : List R)
    (h : ∀ b ∈ l, Commute a b) : Commute a l.Sum :=
  by
  induction' l with x xs ih
  · exact Commute.zero_right _
  · rw [List.sum_cons]
    exact (h _ <| mem_cons_self _ _).addRight (ih fun j hj => h _ <| mem_cons_of_mem _ hj)
#align commute.list_sum_right Commute.list_sum_right
-/

#print Commute.list_sum_left /-
theorem list_sum_left [NonUnitalNonAssocSemiring R] (b : R) (l : List R)
    (h : ∀ a ∈ l, Commute a b) : Commute l.Sum b :=
  (Commute.list_sum_right _ _ fun x hx => (h _ hx).symm).symm
#align commute.list_sum_left Commute.list_sum_left
-/

end Commute

namespace List

#print List.pow_card_le_prod /-
@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod [Monoid M] [Preorder M]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass M M (· * ·) (· ≤ ·)]
    (l : List M) (n : M) (h : ∀ x ∈ l, n ≤ x) : n ^ l.length ≤ l.Prod :=
  @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h
#align list.pow_card_le_prod List.pow_card_le_prod
#align list.card_nsmul_le_sum List.card_nsmul_le_sum
-/

#print List.prod_eq_one_iff /-
@[to_additive]
theorem prod_eq_one_iff [CanonicallyOrderedMonoid M] (l : List M) :
    l.Prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le _, fun h => by
    rw [eq_replicate.2 ⟨rfl, h⟩, prod_replicate, one_pow]⟩
#align list.prod_eq_one_iff List.prod_eq_one_iff
#align list.sum_eq_zero_iff List.sum_eq_zero_iff
-/

#print List.neg_one_mem_of_prod_eq_neg_one /-
/-- If a product of integers is `-1`, then at least one factor must be `-1`. -/
theorem neg_one_mem_of_prod_eq_neg_one {l : List ℤ} (h : l.Prod = -1) : (-1 : ℤ) ∈ l :=
  by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact
    Or.resolve_left
        (int.is_unit_iff.mp
          (prod_is_unit_iff.mp (h.symm ▸ IsUnit.neg isUnit_one : IsUnit l.prod) x h₁))
        h₂ ▸
      h₁
#align list.neg_one_mem_of_prod_eq_neg_one List.neg_one_mem_of_prod_eq_neg_one
-/

#print List.length_le_sum_of_one_le /-
/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.Sum :=
  by
  induction' L with j L IH h; · simp
  rw [sum_cons, length, add_comm]
  exact add_le_add (h _ (Set.mem_insert _ _)) (IH fun i hi => h i (Set.mem_union_right _ hi))
#align list.length_le_sum_of_one_le List.length_le_sum_of_one_le
-/

#print List.dvd_prod /-
theorem dvd_prod [CommMonoid M] {a} {l : List M} (ha : a ∈ l) : a ∣ l.Prod :=
  by
  let ⟨s, t, h⟩ := mem_split ha
  rw [h, prod_append, prod_cons, mul_left_comm]; exact dvd_mul_right _ _
#align list.dvd_prod List.dvd_prod
-/

#print List.dvd_sum /-
theorem dvd_sum [Semiring R] {a} {l : List R} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.Sum :=
  by
  induction' l with x l ih
  · exact dvd_zero _
  · rw [List.sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun x hx => h x (mem_cons_of_mem _ hx))
#align list.dvd_sum List.dvd_sum
-/

section Alternating

variable [CommGroup α]

#print List.alternatingProd_append /-
@[to_additive]
theorem alternatingProd_append :
    ∀ l₁ l₂ : List α,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternating_prod_cons, alternating_prod_append, length_cons, pow_succ,
      neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]
#align list.alternating_prod_append List.alternatingProd_append
#align list.alternating_sum_append List.alternatingSum_append
-/

#print List.alternatingProd_reverse /-
@[to_additive]
theorem alternatingProd_reverse :
    ∀ l : List α, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)
  | [] => by simp only [alternating_prod_nil, one_zpow, reverse_nil]
  | a :: l =>
    by
    simp_rw [reverse_cons, alternating_prod_append, alternating_prod_reverse,
      alternating_prod_singleton, alternating_prod_cons, length_reverse, length, pow_succ, neg_mul,
      one_mul, zpow_neg, inv_inv]
    rw [mul_comm, ← div_eq_mul_inv, div_zpow]
#align list.alternating_prod_reverse List.alternatingProd_reverse
#align list.alternating_sum_reverse List.alternatingSum_reverse
-/

end Alternating

#print List.sum_map_mul_left /-
theorem sum_map_mul_left [NonUnitalNonAssocSemiring R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => r * f b).Sum = r * (L.map f).Sum :=
  sum_map_hom L f <| AddMonoidHom.mulLeft r
#align list.sum_map_mul_left List.sum_map_mul_left
-/

#print List.sum_map_mul_right /-
theorem sum_map_mul_right [NonUnitalNonAssocSemiring R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => f b * r).Sum = (L.map f).Sum * r :=
  sum_map_hom L f <| AddMonoidHom.mulRight r
#align list.sum_map_mul_right List.sum_map_mul_right
-/

end List

namespace MulOpposite

open List

variable [Monoid M]

#print MulOpposite.op_list_prod /-
theorem op_list_prod : ∀ l : List M, op l.Prod = (l.map op).reverse.Prod
  | [] => rfl
  | x :: xs => by
    rw [List.prod_cons, List.map_cons, List.reverse_cons', List.prod_concat, op_mul, op_list_prod]
#align mul_opposite.op_list_prod MulOpposite.op_list_prod
-/

#print MulOpposite.unop_list_prod /-
theorem MulOpposite.unop_list_prod (l : List Mᵐᵒᵖ) : l.Prod.unop = (l.map unop).reverse.Prod := by
  rw [← op_inj, op_unop, MulOpposite.op_list_prod, map_reverse, map_map, reverse_reverse,
    op_comp_unop, map_id]
#align mul_opposite.unop_list_prod MulOpposite.unop_list_prod
-/

end MulOpposite

section MonoidHom

variable [Monoid M] [Monoid N]

#print unop_map_list_prod /-
/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
theorem unop_map_list_prod {F : Type _} [MonoidHomClass F M Nᵐᵒᵖ] (f : F) (l : List M) :
    (f l.Prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.Prod := by
  rw [map_list_prod f l, MulOpposite.unop_list_prod, List.map_map]
#align unop_map_list_prod unop_map_list_prod
-/

namespace MonoidHom

#print MonoidHom.unop_map_list_prod /-
/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements.

Deprecated, use `_root_.unop_map_list_prod` instead. -/
protected theorem unop_map_list_prod (f : M →* Nᵐᵒᵖ) (l : List M) :
    (f l.Prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.Prod :=
  unop_map_list_prod f l
#align monoid_hom.unop_map_list_prod MonoidHom.unop_map_list_prod
-/

end MonoidHom

end MonoidHom

