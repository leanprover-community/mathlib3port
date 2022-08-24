/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.MonoidAlgebra.Basic

/-!
# Lemmas about the `sup` and `inf` of the support of `add_monoid_algebra`

## TODO
The current plan is to state and prove lemmas about `finset.sup (finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized for some yet-to-be-defined `degree`s.
-/


variable {R A T B ι : Type _}

namespace AddMonoidAlgebra

open Classical BigOperators

/-! ### Results about the `finset.sup` and `finset.inf` of `finsupp.support` -/


section GeneralResultsAssumingSemilatticeSup

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

section Semiringₓ

variable [Semiringₓ R]

section ExplicitDegrees

/-!

In this section, we use `degb` and `degt` to denote "degree functions" on `A` with values in
a type with *b*ot or *t*op respectively.
-/


variable (degb : A → B) (degt : A → T) (f g : AddMonoidAlgebra R A)

theorem sup_support_add_le : (f + g).Support.sup degb ≤ f.Support.sup degb⊔g.Support.sup degb :=
  (Finset.sup_mono Finsupp.support_add).trans_eq Finset.sup_union

theorem le_inf_support_add : f.Support.inf degt⊓g.Support.inf degt ≤ (f + g).Support.inf degt :=
  sup_support_add_le (fun a : A => OrderDual.toDual (degt a)) f g

end ExplicitDegrees

section AddOnly

variable [Add A] [Add B] [Add T] [CovariantClass B B (· + ·) (· ≤ ·)]
  [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] [CovariantClass T T (· + ·) (· ≤ ·)]
  [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]

theorem sup_support_mul_le {degb : A → B} (degbm : ∀ {a b}, degb (a + b) ≤ degb a + degb b)
    (f g : AddMonoidAlgebra R A) : (f * g).Support.sup degb ≤ f.Support.sup degb + g.Support.sup degb := by
  refine' (Finset.sup_mono <| support_mul _ _).trans _
  simp_rw [Finset.sup_bUnion, Finset.sup_singleton]
  refine' Finset.sup_le fun fd fds => Finset.sup_le fun gd gds => degbm.trans <| add_le_add _ _ <;>
    exact Finset.le_sup ‹_›

theorem le_inf_support_mul {degt : A → T} (degtm : ∀ {a b}, degt a + degt b ≤ degt (a + b))
    (f g : AddMonoidAlgebra R A) : f.Support.inf degt + g.Support.inf degt ≤ (f * g).Support.inf degt :=
  OrderDual.of_dual_le_of_dual.mpr <| sup_support_mul_le (fun a b => OrderDual.of_dual_le_of_dual.mp degtm) f g

end AddOnly

section AddMonoids

variable [AddMonoidₓ A] [AddMonoidₓ B] [CovariantClass B B (· + ·) (· ≤ ·)]
  [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] [AddMonoidₓ T] [CovariantClass T T (· + ·) (· ≤ ·)]
  [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)] {degb : A → B} {degt : A → T}

theorem sup_support_list_prod_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) :
    ∀ l : List (AddMonoidAlgebra R A),
      l.Prod.Support.sup degb ≤ (l.map fun f : AddMonoidAlgebra R A => f.Support.sup degb).Sum
  | [] => by
    rw [List.map_nil, Finset.sup_le_iff, List.prod_nil, List.sum_nil]
    exact fun a ha => by
      rwa [finset.mem_singleton.mp (Finsupp.support_single_subset ha)]
  | f :: fs => by
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact (sup_support_mul_le degbm _ _).trans (add_le_add_left (sup_support_list_prod_le _) _)

theorem le_inf_support_list_prod (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (l : List (AddMonoidAlgebra R A)) :
    (l.map fun f : AddMonoidAlgebra R A => f.Support.inf degt).Sum ≤ l.Prod.Support.inf degt :=
  OrderDual.of_dual_le_of_dual.mpr <|
    sup_support_list_prod_le (OrderDual.of_dual_le_of_dual.mp degt0)
      (fun a b => OrderDual.of_dual_le_of_dual.mp (degtm _ _)) l

theorem sup_support_pow_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (n : ℕ)
    (f : AddMonoidAlgebra R A) : (f ^ n).Support.sup degb ≤ n • f.Support.sup degb := by
  rw [← List.prod_repeat, ← List.sum_repeat]
  refine' (sup_support_list_prod_le degb0 degbm _).trans_eq _
  rw [List.map_repeat]

theorem le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (n : ℕ)
    (f : AddMonoidAlgebra R A) : n • f.Support.inf degt ≤ (f ^ n).Support.inf degt :=
  OrderDual.of_dual_le_of_dual.mpr <|
    sup_support_pow_le (OrderDual.of_dual_le_of_dual.mp degt0) (fun a b => OrderDual.of_dual_le_of_dual.mp (degtm _ _))
      n f

end AddMonoids

end Semiringₓ

section CommutativeLemmas

variable [CommSemiringₓ R] [AddCommMonoidₓ A] [AddCommMonoidₓ B] [CovariantClass B B (· + ·) (· ≤ ·)]
  [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] [AddCommMonoidₓ T] [CovariantClass T T (· + ·) (· ≤ ·)]
  [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)] {degb : A → B} {degt : A → T}

theorem sup_support_multiset_prod_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (m : Multiset (AddMonoidAlgebra R A)) :
    m.Prod.Support.sup degb ≤ (m.map fun f : AddMonoidAlgebra R A => f.Support.sup degb).Sum := by
  induction m using Quot.induction_on
  rw [Multiset.quot_mk_to_coe'', Multiset.coe_map, Multiset.coe_sum, Multiset.coe_prod]
  exact sup_support_list_prod_le degb0 degbm m

theorem le_inf_support_multiset_prod (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (m : Multiset (AddMonoidAlgebra R A)) :
    (m.map fun f : AddMonoidAlgebra R A => f.Support.inf degt).Sum ≤ m.Prod.Support.inf degt :=
  OrderDual.of_dual_le_of_dual.mpr <|
    sup_support_multiset_prod_le (OrderDual.of_dual_le_of_dual.mp degt0)
      (fun a b => OrderDual.of_dual_le_of_dual.mp (degtm _ _)) m

theorem sup_support_finset_prod_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (s : Finset ι)
    (f : ι → AddMonoidAlgebra R A) : (∏ i in s, f i).Support.sup degb ≤ ∑ i in s, (f i).Support.sup degb :=
  (sup_support_multiset_prod_le degb0 degbm _).trans_eq <| congr_arg _ <| Multiset.map_map _ _ _

theorem le_inf_support_finset_prod (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (s : Finset ι)
    (f : ι → AddMonoidAlgebra R A) : (∑ i in s, (f i).Support.inf degt) ≤ (∏ i in s, f i).Support.inf degt :=
  le_of_eq_of_leₓ
    (by
      rw [Multiset.map_map] <;> rfl)
    (le_inf_support_multiset_prod degt0 degtm _)

end CommutativeLemmas

end GeneralResultsAssumingSemilatticeSup

end AddMonoidAlgebra

